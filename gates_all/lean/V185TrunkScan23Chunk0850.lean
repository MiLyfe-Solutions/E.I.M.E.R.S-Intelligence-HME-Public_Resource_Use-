import V185TrunkScan23Chunk0849

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5031066 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5031066 : Nat := 118140960795 + 5031066 * 2 ^ 59
def prefixEnd_5031066 : Nat := 4983230072969 + 3 ^ 40 * 5031066 * 2
def baseEnd_5031066 : Nat := 2583355062493118164837555

theorem tailTrace_5031066 : CollatzResearch.WordTrace tailWord_5031066 prefixEnd_5031066 2583355062493118164837555 := by
  unfold tailWord_5031066
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874512997828648627626263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122332034660876396340336701 45874512997828648627626263)
  ·
    refine ⟨68811769496742972941439395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45874512997828648627626263 68811769496742972941439395)
    ·
      refine ⟨103217654245114459412159093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68811769496742972941439395 103217654245114459412159093)
      ·
        refine ⟨9676655085479480569889915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103217654245114459412159093 9676655085479480569889915)
        ·
          refine ⟨14514982628219220854834873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676655085479480569889915 14514982628219220854834873)
          ·
            refine ⟨10886236971164415641126155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14514982628219220854834873 10886236971164415641126155)
            ·
              refine ⟨16329355456746623461689233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886236971164415641126155 16329355456746623461689233)
              ·
                refine ⟨12247016592559967596266925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16329355456746623461689233 12247016592559967596266925)
                ·
                  refine ⟨4592631222209987848600097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12247016592559967596266925 4592631222209987848600097)
                  ·
                    refine ⟨3444473416657490886450073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4592631222209987848600097 3444473416657490886450073)
                    ·
                      refine ⟨2583355062493118164837555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444473416657490886450073 2583355062493118164837555)
                      ·
                        rfl

theorem cell23_5031066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5031066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031066 prefixEnd_5031066 := by exact prefixLift 5031066
  have htrace : WordTrace (prefixWord ++ tailWord_5031066) baseStart_5031066 baseEnd_5031066 := by
    simpa [prefixWord, tailWord_5031066, baseEnd_5031066] using wordTrace_append hprefix tailTrace_5031066
  have hstable : (prefixWord ++ tailWord_5031066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031066).length < 2 ^ (prefixWord ++ tailWord_5031066).sum := by decide
  have hdescent : baseEnd_5031066 < baseStart_5031066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031110 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5031110 : Nat := 118140960795 + 5031110 * 2 ^ 59
def prefixEnd_5031110 : Nat := 4983230072969 + 3 ^ 40 * 5031110 * 2
def baseEnd_5031110 : Nat := 861125885213971997562451

theorem tailTrace_5031110 : CollatzResearch.WordTrace tailWord_5031110 prefixEnd_5031110 861125885213971997562451 := by
  unfold tailWord_5031110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734364275098599688284587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122333104535436793350071189 5734364275098599688284587)
  ·
    refine ⟨8601546412647899532426881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734364275098599688284587 8601546412647899532426881)
    ·
      refine ⟨6451159809485924649320161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8601546412647899532426881 6451159809485924649320161)
      ·
        refine ⟨4838369857114443486990121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6451159809485924649320161 4838369857114443486990121)
        ·
          refine ⟨3628777392835832615242591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838369857114443486990121 3628777392835832615242591)
          ·
            refine ⟨5443166089253748922863887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628777392835832615242591 5443166089253748922863887)
            ·
              refine ⟨8164749133880623384295831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443166089253748922863887 8164749133880623384295831)
              ·
                refine ⟨12247123700820935076443747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164749133880623384295831 12247123700820935076443747)
                ·
                  refine ⟨18370685551231402614665621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12247123700820935076443747 18370685551231402614665621)
                  ·
                    refine ⟨861125885213971997562451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18370685551231402614665621 861125885213971997562451)
                    ·
                      rfl

theorem cell23_5031110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5031110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031110 prefixEnd_5031110 := by exact prefixLift 5031110
  have htrace : WordTrace (prefixWord ++ tailWord_5031110) baseStart_5031110 baseEnd_5031110 := by
    simpa [prefixWord, tailWord_5031110, baseEnd_5031110] using wordTrace_append hprefix tailTrace_5031110
  have hstable : (prefixWord ++ tailWord_5031110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031110).length < 2 ^ (prefixWord ++ tailWord_5031110).sum := by decide
  have hdescent : baseEnd_5031110 < baseStart_5031110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031135 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5031135 : Nat := 118140960795 + 5031135 * 2 ^ 59
def prefixEnd_5031135 : Nat := 4983230072969 + 3 ^ 40 * 5031135 * 2
def baseEnd_5031135 : Nat := 2583390492658278394874737

theorem tailTrace_5031135 : CollatzResearch.WordTrace tailWord_5031135 prefixEnd_5031135 2583390492658278394874737 := by
  unfold tailWord_5031135
  simp only [CollatzResearch.WordTrace]
  refine ⟨183500568628064619294766859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122333712418709746196511239 183500568628064619294766859)
  ·
    refine ⟨275250852942096928942150289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183500568628064619294766859 275250852942096928942150289)
    ·
      refine ⟨206438139706572696706612717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275250852942096928942150289 206438139706572696706612717)
      ·
        refine ⟨77414302389964761264979769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206438139706572696706612717 77414302389964761264979769)
        ·
          refine ⟨58060726792473570948734827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77414302389964761264979769 58060726792473570948734827)
          ·
            refine ⟨87091090188710356423102241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58060726792473570948734827 87091090188710356423102241)
            ·
              refine ⟨65318317641532767317326681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87091090188710356423102241 65318317641532767317326681)
              ·
                refine ⟨48988738231149575487995011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65318317641532767317326681 48988738231149575487995011)
                ·
                  refine ⟨73483107346724363231992517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48988738231149575487995011 73483107346724363231992517)
                  ·
                    refine ⟨13778082627510818105998597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73483107346724363231992517 13778082627510818105998597)
                    ·
                      refine ⟨2583390492658278394874737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13778082627510818105998597 2583390492658278394874737)
                      ·
                        rfl

theorem cell23_5031135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5031135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031135 prefixEnd_5031135 := by exact prefixLift 5031135
  have htrace : WordTrace (prefixWord ++ tailWord_5031135) baseStart_5031135 baseEnd_5031135 := by
    simpa [prefixWord, tailWord_5031135, baseEnd_5031135] using wordTrace_append hprefix tailTrace_5031135
  have hstable : (prefixWord ++ tailWord_5031135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031135).length < 2 ^ (prefixWord ++ tailWord_5031135).sum := by decide
  have hdescent : baseEnd_5031135 < baseStart_5031135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031185 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_5031185 : Nat := 118140960795 + 5031185 * 2 ^ 59
def prefixEnd_5031185 : Nat := 4983230072969 + 3 ^ 40 * 5031185 * 2
def baseEnd_5031185 : Nat := 2583416166691003199249507

theorem tailTrace_5031185 : CollatzResearch.WordTrace tailWord_5031185 prefixEnd_5031185 2583416166691003199249507 := by
  unfold tailWord_5031185
  simp only [CollatzResearch.WordTrace]
  refine ⟨183502392277883477834087009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122334928185255651889391339 183502392277883477834087009)
  ·
    refine ⟨137626794208412608375565257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183502392277883477834087009 137626794208412608375565257)
    ·
      refine ⟨103220095656309456281673943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137626794208412608375565257 103220095656309456281673943)
      ·
        refine ⟨154830143484464184422510915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103220095656309456281673943 154830143484464184422510915)
        ·
          refine ⟨232245215226696276633766373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154830143484464184422510915 232245215226696276633766373)
          ·
            refine ⟨43545977855005551868831195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232245215226696276633766373 43545977855005551868831195)
            ·
              refine ⟨65318966782508327803246793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43545977855005551868831195 65318966782508327803246793)
              ·
                refine ⟨48989225086881245852435095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65318966782508327803246793 48989225086881245852435095)
                ·
                  refine ⟨73483837630321868778652643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48989225086881245852435095 73483837630321868778652643)
                  ·
                    refine ⟨110225756445482803167978965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73483837630321868778652643 110225756445482803167978965)
                    ·
                      refine ⟨2583416166691003199249507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110225756445482803167978965 2583416166691003199249507)
                      ·
                        rfl

theorem cell23_5031185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_5031185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031185 prefixEnd_5031185 := by exact prefixLift 5031185
  have htrace : WordTrace (prefixWord ++ tailWord_5031185) baseStart_5031185 baseEnd_5031185 := by
    simpa [prefixWord, tailWord_5031185, baseEnd_5031185] using wordTrace_append hprefix tailTrace_5031185
  have hstable : (prefixWord ++ tailWord_5031185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031185).length < 2 ^ (prefixWord ++ tailWord_5031185).sum := by decide
  have hdescent : baseEnd_5031185 < baseStart_5031185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031192 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_5031192 : Nat := 118140960795 + 5031192 * 2 ^ 59
def prefixEnd_5031192 : Nat := 4983230072969 + 3 ^ 40 * 5031192 * 2
def baseEnd_5031192 : Nat := 861139920351861557287325

theorem tailTrace_5031192 : CollatzResearch.WordTrace tailWord_5031192 prefixEnd_5031192 861139920351861557287325 := by
  unfold tailWord_5031192
  simp only [CollatzResearch.WordTrace]
  refine ⟨91751323794429059014795915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122335098392572078686394553 91751323794429059014795915)
  ·
    refine ⟨137626985691643588522193873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91751323794429059014795915 137626985691643588522193873)
    ·
      refine ⟨103220239268732691391645405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137626985691643588522193873 103220239268732691391645405)
      ·
        refine ⟨38707589725774759271867027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103220239268732691391645405 38707589725774759271867027)
        ·
          refine ⟨58061384588662138907800541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38707589725774759271867027 58061384588662138907800541)
          ·
            refine ⟨21773019220748302090425203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58061384588662138907800541 21773019220748302090425203)
            ·
              refine ⟨32659528831122453135637805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21773019220748302090425203 32659528831122453135637805)
              ·
                refine ⟨12247323311670919925864177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32659528831122453135637805 12247323311670919925864177)
                ·
                  refine ⟨9185492483753189944398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12247323311670919925864177 9185492483753189944398133)
                  ·
                    refine ⟨861139920351861557287325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9185492483753189944398133 861139920351861557287325)
                    ·
                      rfl

theorem cell23_5031192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_5031192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031192 prefixEnd_5031192 := by exact prefixLift 5031192
  have htrace : WordTrace (prefixWord ++ tailWord_5031192) baseStart_5031192 baseEnd_5031192 := by
    simpa [prefixWord, tailWord_5031192, baseEnd_5031192] using wordTrace_append hprefix tailTrace_5031192
  have hstable : (prefixWord ++ tailWord_5031192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031192).length < 2 ^ (prefixWord ++ tailWord_5031192).sum := by decide
  have hdescent : baseEnd_5031192 < baseStart_5031192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031213 : List Nat := [1, 5, 3, 1, 1, 1, 4, 2, 5]
def baseStart_5031213 : Nat := 118140960795 + 5031213 * 2 ^ 59
def prefixEnd_5031213 : Nat := 4983230072969 + 3 ^ 40 * 5031213 * 2
def baseEnd_5031213 : Nat := 287047838238814343299931

theorem tailTrace_5031213 : CollatzResearch.WordTrace tailWord_5031213 prefixEnd_5031213 287047838238814343299931 := by
  unfold tailWord_5031213
  simp only [CollatzResearch.WordTrace]
  refine ⟨183503413521782038616106293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122335609014521359077404195 183503413521782038616106293)
  ·
    refine ⟨17203445017667066120259965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183503413521782038616106293 17203445017667066120259965)
    ·
      refine ⟨6451291881625149795097487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17203445017667066120259965 6451291881625149795097487)
      ·
        refine ⟨9676937822437724692646231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451291881625149795097487 9676937822437724692646231)
        ·
          refine ⟨14515406733656587038969347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676937822437724692646231 14515406733656587038969347)
          ·
            refine ⟨21773110100484880558454021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14515406733656587038969347 21773110100484880558454021)
            ·
              refine ⟨4082458143840915104710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21773110100484880558454021 4082458143840915104710129)
              ·
                refine ⟨3061843607880686328532597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082458143840915104710129 3061843607880686328532597)
                ·
                  refine ⟨287047838238814343299931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061843607880686328532597 287047838238814343299931)
                  ·
                    rfl

theorem cell23_5031213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_5031213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031213 prefixEnd_5031213 := by exact prefixLift 5031213
  have htrace : WordTrace (prefixWord ++ tailWord_5031213) baseStart_5031213 baseEnd_5031213 := by
    simpa [prefixWord, tailWord_5031213, baseEnd_5031213] using wordTrace_append hprefix tailTrace_5031213
  have hstable : (prefixWord ++ tailWord_5031213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031213).length < 2 ^ (prefixWord ++ tailWord_5031213).sum := by decide
  have hdescent : baseEnd_5031213 < baseStart_5031213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031215 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_5031215 : Nat := 118140960795 + 5031215 * 2 ^ 59
def prefixEnd_5031215 : Nat := 4983230072969 + 3 ^ 40 * 5031215 * 2
def baseEnd_5031215 : Nat := 2583431571110638081874369

theorem tailTrace_5031215 : CollatzResearch.WordTrace tailWord_5031215 prefixEnd_5031215 2583431571110638081874369 := by
  unfold tailWord_5031215
  simp only [CollatzResearch.WordTrace]
  refine ⟨183503486467774792957679099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122335657645183195305119399 183503486467774792957679099)
  ·
    refine ⟨275255229701662189436518649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183503486467774792957679099 275255229701662189436518649)
    ·
      refine ⟨206441422276246642077388987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275255229701662189436518649 206441422276246642077388987)
      ·
        refine ⟨309662133414369963116083481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206441422276246642077388987 309662133414369963116083481)
        ·
          refine ⟨232246600060777472337062611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309662133414369963116083481 232246600060777472337062611)
          ·
            refine ⟨348369900091166208505593917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232246600060777472337062611 348369900091166208505593917)
            ·
              refine ⟨130638712534187328189597719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348369900091166208505593917 130638712534187328189597719)
              ·
                refine ⟨195958068801280992284396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130638712534187328189597719 195958068801280992284396579)
                ·
                  refine ⟨293937103201921488426594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195958068801280992284396579 293937103201921488426594869)
                  ·
                    refine ⟨27556603425180139539993269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 293937103201921488426594869 27556603425180139539993269)
                    ·
                      refine ⟨2583431571110638081874369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27556603425180139539993269 2583431571110638081874369)
                      ·
                        rfl

theorem cell23_5031215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_5031215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031215 prefixEnd_5031215 := by exact prefixLift 5031215
  have htrace : WordTrace (prefixWord ++ tailWord_5031215) baseStart_5031215 baseEnd_5031215 := by
    simpa [prefixWord, tailWord_5031215, baseEnd_5031215] using wordTrace_append hprefix tailTrace_5031215
  have hstable : (prefixWord ++ tailWord_5031215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031215).length < 2 ^ (prefixWord ++ tailWord_5031215).sum := by decide
  have hdescent : baseEnd_5031215 < baseStart_5031215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031232 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_5031232 : Nat := 118140960795 + 5031232 * 2 ^ 59
def prefixEnd_5031232 : Nat := 4983230072969 + 3 ^ 40 * 5031232 * 2
def baseEnd_5031232 : Nat := 2583440300281764515361791

theorem tailTrace_5031232 : CollatzResearch.WordTrace tailWord_5031232 prefixEnd_5031232 2583440300281764515361791 := by
  unfold tailWord_5031232
  simp only [CollatzResearch.WordTrace]
  refine ⟨91752053254356602430523975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122336071005808803240698633 91752053254356602430523975)
  ·
    refine ⟨137628079881534903645785963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91752053254356602430523975 137628079881534903645785963)
    ·
      refine ⟨206442119822302355468678945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137628079881534903645785963 206442119822302355468678945)
      ·
        refine ⟨154831589866726766601509209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206442119822302355468678945 154831589866726766601509209)
        ·
          refine ⟨116123692400045074951131907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154831589866726766601509209 116123692400045074951131907)
          ·
            refine ⟨174185538600067612426697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116123692400045074951131907 174185538600067612426697861)
            ·
              refine ⟨32659788487512677330005849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174185538600067612426697861 32659788487512677330005849)
              ·
                refine ⟨24494841365634507997504387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32659788487512677330005849 24494841365634507997504387)
                ·
                  refine ⟨36742262048451761996256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24494841365634507997504387 36742262048451761996256581)
                  ·
                    refine ⟨6889174134084705374298109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36742262048451761996256581 6889174134084705374298109)
                    ·
                      refine ⟨2583440300281764515361791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889174134084705374298109 2583440300281764515361791)
                      ·
                        rfl

theorem cell23_5031232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_5031232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031232 prefixEnd_5031232 := by exact prefixLift 5031232
  have htrace : WordTrace (prefixWord ++ tailWord_5031232) baseStart_5031232 baseEnd_5031232 := by
    simpa [prefixWord, tailWord_5031232, baseEnd_5031232] using wordTrace_append hprefix tailTrace_5031232
  have hstable : (prefixWord ++ tailWord_5031232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031232).length < 2 ^ (prefixWord ++ tailWord_5031232).sum := by decide
  have hdescent : baseEnd_5031232 < baseStart_5031232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031235 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 10]
def baseStart_5031235 : Nat := 118140960795 + 5031235 * 2 ^ 59
def prefixEnd_5031235 : Nat := 4983230072969 + 3 ^ 40 * 5031235 * 2
def baseEnd_5031235 : Nat := 287049093413747555958253

theorem tailTrace_5031235 : CollatzResearch.WordTrace tailWord_5031235 prefixEnd_5031235 287049093413747555958253 := by
  unfold tailWord_5031235
  simp only [CollatzResearch.WordTrace]
  refine ⟨183504215927702336373407159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122336143951801557582271439 183504215927702336373407159)
  ·
    refine ⟨275256323891553504560110739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183504215927702336373407159 275256323891553504560110739)
    ·
      refine ⟨412884485837330256840166109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275256323891553504560110739 412884485837330256840166109)
      ·
        refine ⟨154831682188998846315062291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412884485837330256840166109 154831682188998846315062291)
        ·
          refine ⟨232247523283498269472593437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154831682188998846315062291 232247523283498269472593437)
          ·
            refine ⟨87092821231311851052222539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232247523283498269472593437 87092821231311851052222539)
            ·
              refine ⟨130639231846967776578333809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87092821231311851052222539 130639231846967776578333809)
              ·
                refine ⟨97979423885225832433750357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130639231846967776578333809 97979423885225832433750357)
                ·
                  refine ⟨287049093413747555958253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97979423885225832433750357 287049093413747555958253)
                  ·
                    rfl

theorem cell23_5031235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 10].length) (baseStart_5031235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031235 prefixEnd_5031235 := by exact prefixLift 5031235
  have htrace : WordTrace (prefixWord ++ tailWord_5031235) baseStart_5031235 baseEnd_5031235 := by
    simpa [prefixWord, tailWord_5031235, baseEnd_5031235] using wordTrace_append hprefix tailTrace_5031235
  have hstable : (prefixWord ++ tailWord_5031235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031235).length < 2 ^ (prefixWord ++ tailWord_5031235).sum := by decide
  have hdescent : baseEnd_5031235 < baseStart_5031235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031239 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 3, 4]
def baseStart_5031239 : Nat := 118140960795 + 5031239 * 2 ^ 59
def prefixEnd_5031239 : Nat := 4983230072969 + 3 ^ 40 * 5031239 * 2
def baseEnd_5031239 : Nat := 861147964882115329324753

theorem tailTrace_5031239 : CollatzResearch.WordTrace tailWord_5031239 prefixEnd_5031239 861147964882115329324753 := by
  unfold tailWord_5031239
  simp only [CollatzResearch.WordTrace]
  refine ⟨183504361819687845056552771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122336241213125230037701847 183504361819687845056552771)
  ·
    refine ⟨275256542729531767584829157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183504361819687845056552771 275256542729531767584829157)
    ·
      refine ⟨51610601761787206422155467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275256542729531767584829157 51610601761787206422155467)
      ·
        refine ⟨77415902642680809633233201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51610601761787206422155467 77415902642680809633233201)
        ·
          refine ⟨58061926982010607224924901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77415902642680809633233201 58061926982010607224924901)
          ·
            refine ⟨10886611309126988854673419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58061926982010607224924901 10886611309126988854673419)
            ·
              refine ⟨16329916963690483282010129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886611309126988854673419 16329916963690483282010129)
              ·
                refine ⟨12247437722767862461507597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16329916963690483282010129 12247437722767862461507597)
                ·
                  refine ⟨4592789146037948423065349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12247437722767862461507597 4592789146037948423065349)
                  ·
                    refine ⟨861147964882115329324753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592789146037948423065349 861147964882115329324753)
                    ·
                      rfl

theorem cell23_5031239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_5031239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031239 prefixEnd_5031239 := by exact prefixLift 5031239
  have htrace : WordTrace (prefixWord ++ tailWord_5031239) baseStart_5031239 baseEnd_5031239 := by
    simpa [prefixWord, tailWord_5031239, baseEnd_5031239] using wordTrace_append hprefix tailTrace_5031239
  have hstable : (prefixWord ++ tailWord_5031239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031239).length < 2 ^ (prefixWord ++ tailWord_5031239).sum := by decide
  have hdescent : baseEnd_5031239 < baseStart_5031239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031252 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5031252 : Nat := 118140960795 + 5031252 * 2 ^ 59
def prefixEnd_5031252 : Nat := 4983230072969 + 3 ^ 40 * 5031252 * 2
def baseEnd_5031252 : Nat := 287050063321650493012411

theorem tailTrace_5031252 : CollatzResearch.WordTrace tailWord_5031252 prefixEnd_5031252 287050063321650493012411 := by
  unfold tailWord_5031252
  simp only [CollatzResearch.WordTrace]
  refine ⟨91752417984320374138388005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122336557312427165517850673 91752417984320374138388005)
  ·
    refine ⟨17203578372060070150947751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91752417984320374138388005 17203578372060070150947751)
    ·
      refine ⟨25805367558090105226421627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17203578372060070150947751 25805367558090105226421627)
      ·
        refine ⟨38708051337135157839632441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25805367558090105226421627 38708051337135157839632441)
        ·
          refine ⟨29031038502851368379724331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38708051337135157839632441 29031038502851368379724331)
          ·
            refine ⟨43546557754277052569586497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29031038502851368379724331 43546557754277052569586497)
            ·
              refine ⟨32659918315707789427189873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43546557754277052569586497 32659918315707789427189873)
              ·
                refine ⟨24494938736780842070392405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32659918315707789427189873 24494938736780842070392405)
                ·
                  refine ⟨287050063321650493012411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24494938736780842070392405 287050063321650493012411)
                  ·
                    rfl

theorem cell23_5031252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5031252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031252 prefixEnd_5031252 := by exact prefixLift 5031252
  have htrace : WordTrace (prefixWord ++ tailWord_5031252) baseStart_5031252 baseEnd_5031252 := by
    simpa [prefixWord, tailWord_5031252, baseEnd_5031252] using wordTrace_append hprefix tailTrace_5031252
  have hstable : (prefixWord ++ tailWord_5031252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031252).length < 2 ^ (prefixWord ++ tailWord_5031252).sum := by decide
  have hdescent : baseEnd_5031252 < baseStart_5031252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031256 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 1, 4]
def baseStart_5031256 : Nat := 118140960795 + 5031256 * 2 ^ 59
def prefixEnd_5031256 : Nat := 4983230072969 + 3 ^ 40 * 5031256 * 2
def baseEnd_5031256 : Nat := 861150874605824140487227

theorem tailTrace_5031256 : CollatzResearch.WordTrace tailWord_5031256 prefixEnd_5031256 861150874605824140487227 := by
  unfold tailWord_5031256
  simp only [CollatzResearch.WordTrace]
  refine ⟨91752490930313128479960811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122336654573750837973281081 91752490930313128479960811)
  ·
    refine ⟨137628736395469692719941217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91752490930313128479960811 137628736395469692719941217)
    ·
      refine ⟨103221552296602269539955913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137628736395469692719941217 103221552296602269539955913)
      ·
        refine ⟨77416164222451702154966935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103221552296602269539955913 77416164222451702154966935)
        ·
          refine ⟨116124246333677553232450403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77416164222451702154966935 116124246333677553232450403)
          ·
            refine ⟨174186369500516329848675605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116124246333677553232450403 174186369500516329848675605)
            ·
              refine ⟨8164986070336702961656669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174186369500516329848675605 8164986070336702961656669)
              ·
                refine ⟨3061869776376263610621251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8164986070336702961656669 3061869776376263610621251)
                ·
                  refine ⟨4592804664564395415931877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061869776376263610621251 4592804664564395415931877)
                  ·
                    refine ⟨861150874605824140487227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592804664564395415931877 861150874605824140487227)
                    ·
                      rfl

theorem cell23_5031256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_5031256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031256 prefixEnd_5031256 := by exact prefixLift 5031256
  have htrace : WordTrace (prefixWord ++ tailWord_5031256) baseStart_5031256 baseEnd_5031256 := by
    simpa [prefixWord, tailWord_5031256, baseEnd_5031256] using wordTrace_append hprefix tailTrace_5031256
  have hstable : (prefixWord ++ tailWord_5031256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031256).length < 2 ^ (prefixWord ++ tailWord_5031256).sum := by decide
  have hdescent : baseEnd_5031256 < baseStart_5031256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031289 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 5, 2]
def baseStart_5031289 : Nat := 118140960795 + 5031289 * 2 ^ 59
def prefixEnd_5031289 : Nat := 4983230072969 + 3 ^ 40 * 5031289 * 2
def baseEnd_5031289 : Nat := 2583469568679070792349029

theorem tailTrace_5031289 : CollatzResearch.WordTrace tailWord_5031289 prefixEnd_5031289 2583469568679070792349029 := by
  unfold tailWord_5031289
  simp only [CollatzResearch.WordTrace]
  refine ⟨183506185469506703595872921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122337456979671135730581947 183506185469506703595872921)
  ·
    refine ⟨137629639102130027696904691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183506185469506703595872921 137629639102130027696904691)
    ·
      refine ⟨206444458653195041545357037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137629639102130027696904691 206444458653195041545357037)
      ·
        refine ⟨77416671994948140579508889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206444458653195041545357037 77416671994948140579508889)
        ·
          refine ⟨58062503996211105434631667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77416671994948140579508889 58062503996211105434631667)
          ·
            refine ⟨87093755994316658151947501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58062503996211105434631667 87093755994316658151947501)
            ·
              refine ⟨32660158497868746806980313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87093755994316658151947501 32660158497868746806980313)
              ·
                refine ⟨24495118873401560105235235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32660158497868746806980313 24495118873401560105235235)
                ·
                  refine ⟨36742678310102340157852853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24495118873401560105235235 36742678310102340157852853)
                  ·
                    refine ⟨3444626091572094389798705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36742678310102340157852853 3444626091572094389798705)
                    ·
                      refine ⟨2583469568679070792349029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444626091572094389798705 2583469568679070792349029)
                      ·
                        rfl

theorem cell23_5031289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_5031289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031289 prefixEnd_5031289 := by exact prefixLift 5031289
  have htrace : WordTrace (prefixWord ++ tailWord_5031289) baseStart_5031289 baseEnd_5031289 := by
    simpa [prefixWord, tailWord_5031289, baseEnd_5031289] using wordTrace_append hprefix tailTrace_5031289
  have hstable : (prefixWord ++ tailWord_5031289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031289).length < 2 ^ (prefixWord ++ tailWord_5031289).sum := by decide
  have hdescent : baseEnd_5031289 < baseStart_5031289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031299 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 1, 5]
def baseStart_5031299 : Nat := 118140960795 + 5031299 * 2 ^ 59
def prefixEnd_5031299 : Nat := 4983230072969 + 3 ^ 40 * 5031299 * 2
def baseEnd_5031299 : Nat := 861158234495205251074661

theorem tailTrace_5031299 : CollatzResearch.WordTrace tailWord_5031299 prefixEnd_5031299 861158234495205251074661 := by
  unfold tailWord_5031299
  simp only [CollatzResearch.WordTrace]
  refine ⟨183506550199470475303736951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122337700132980316869157967 183506550199470475303736951)
  ·
    refine ⟨275259825299205712955605427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183506550199470475303736951 275259825299205712955605427)
    ·
      refine ⟨412889737948808569433408141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275259825299205712955605427 412889737948808569433408141)
      ·
        refine ⟨154833651730803213537528053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412889737948808569433408141 154833651730803213537528053)
        ·
          refine ⟨14515654849762801269143255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154833651730803213537528053 14515654849762801269143255)
          ·
            refine ⟨21773482274644201903714883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14515654849762801269143255 21773482274644201903714883)
            ·
              refine ⟨32660223411966302855572325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21773482274644201903714883 32660223411966302855572325)
              ·
                refine ⟨6123791889743681785419811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32660223411966302855572325 6123791889743681785419811)
                ·
                  refine ⟨9185687834615522678129717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123791889743681785419811 9185687834615522678129717)
                  ·
                    refine ⟨861158234495205251074661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9185687834615522678129717 861158234495205251074661)
                    ·
                      rfl

theorem cell23_5031299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 5].length) (baseStart_5031299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031299 prefixEnd_5031299 := by exact prefixLift 5031299
  have htrace : WordTrace (prefixWord ++ tailWord_5031299) baseStart_5031299 baseEnd_5031299 := by
    simpa [prefixWord, tailWord_5031299, baseEnd_5031299] using wordTrace_append hprefix tailTrace_5031299
  have hstable : (prefixWord ++ tailWord_5031299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031299).length < 2 ^ (prefixWord ++ tailWord_5031299).sum := by decide
  have hdescent : baseEnd_5031299 < baseStart_5031299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031316 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5031316 : Nat := 118140960795 + 5031316 * 2 ^ 59
def prefixEnd_5031316 : Nat := 4983230072969 + 3 ^ 40 * 5031316 * 2
def baseEnd_5031316 : Nat := 861161144218914062237135

theorem tailTrace_5031316 : CollatzResearch.WordTrace tailWord_5031316 prefixEnd_5031316 861161144218914062237135 := by
  unfold tailWord_5031316
  simp only [CollatzResearch.WordTrace]
  refine ⟨91753585120204443603552901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122338113493605924804737201 91753585120204443603552901)
  ·
    refine ⟨17203797210038333175666169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91753585120204443603552901 17203797210038333175666169)
    ·
      refine ⟨12902847907528749881749627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17203797210038333175666169 12902847907528749881749627)
      ·
        refine ⟨19354271861293124822624441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12902847907528749881749627 19354271861293124822624441)
        ·
          refine ⟨14515703895969843616968331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19354271861293124822624441 14515703895969843616968331)
          ·
            refine ⟨21773555843954765425452497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14515703895969843616968331 21773555843954765425452497)
            ·
              refine ⟨16330166882966074069089373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21773555843954765425452497 16330166882966074069089373)
              ·
                refine ⟨6123812581112277775908515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16330166882966074069089373 6123812581112277775908515)
                ·
                  refine ⟨9185718871668416663862773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123812581112277775908515 9185718871668416663862773)
                  ·
                    refine ⟨861161144218914062237135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9185718871668416663862773 861161144218914062237135)
                    ·
                      rfl

theorem cell23_5031316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5031316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031316 prefixEnd_5031316 := by exact prefixLift 5031316
  have htrace : WordTrace (prefixWord ++ tailWord_5031316) baseStart_5031316 baseEnd_5031316 := by
    simpa [prefixWord, tailWord_5031316, baseEnd_5031316] using wordTrace_append hprefix tailTrace_5031316
  have hstable : (prefixWord ++ tailWord_5031316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031316).length < 2 ^ (prefixWord ++ tailWord_5031316).sum := by decide
  have hdescent : baseEnd_5031316 < baseStart_5031316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031349 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5031349 : Nat := 118140960795 + 5031349 * 2 ^ 59
def prefixEnd_5031349 : Nat := 4983230072969 + 3 ^ 40 * 5031349 * 2
def baseEnd_5031349 : Nat := 2583500377518340557598753

theorem tailTrace_5031349 : CollatzResearch.WordTrace tailWord_5031349 prefixEnd_5031349 2583500377518340557598753 := by
  unfold tailWord_5031349
  simp only [CollatzResearch.WordTrace]
  refine ⟨183508373849289333843057101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122338915899526222562038067 183508373849289333843057101)
  ·
    refine ⟨68815640193483500191146413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183508373849289333843057101 68815640193483500191146413)
    ·
      refine ⟨25805865072556312571679905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68815640193483500191146413 25805865072556312571679905)
      ·
        refine ⟨19354398804417234428759929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25805865072556312571679905 19354398804417234428759929)
        ·
          refine ⟨14515799103312925821569947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19354398804417234428759929 14515799103312925821569947)
          ·
            refine ⟨21773698654969388732354921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14515799103312925821569947 21773698654969388732354921)
            ·
              refine ⟨16330273991227041549266191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21773698654969388732354921 16330273991227041549266191)
              ·
                refine ⟨24495410986840562323899287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330273991227041549266191 24495410986840562323899287)
                ·
                  refine ⟨36743116480260843485848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24495410986840562323899287 36743116480260843485848931)
                  ·
                    refine ⟨55114674720391265228773397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36743116480260843485848931 55114674720391265228773397)
                    ·
                      refine ⟨2583500377518340557598753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55114674720391265228773397 2583500377518340557598753)
                      ·
                        rfl

theorem cell23_5031349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5031349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031349 prefixEnd_5031349 := by exact prefixLift 5031349
  have htrace : WordTrace (prefixWord ++ tailWord_5031349) baseStart_5031349 baseEnd_5031349 := by
    simpa [prefixWord, tailWord_5031349, baseEnd_5031349] using wordTrace_append hprefix tailTrace_5031349
  have hstable : (prefixWord ++ tailWord_5031349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031349).length < 2 ^ (prefixWord ++ tailWord_5031349).sum := by decide
  have hdescent : baseEnd_5031349 < baseStart_5031349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031353 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5031353 : Nat := 118140960795 + 5031353 * 2 ^ 59
def prefixEnd_5031353 : Nat := 4983230072969 + 3 ^ 40 * 5031353 * 2
def baseEnd_5031353 : Nat := 2583502431440958541948735

theorem tailTrace_5031353 : CollatzResearch.WordTrace tailWord_5031353 prefixEnd_5031353 2583502431440958541948735 := by
  unfold tailWord_5031353
  simp only [CollatzResearch.WordTrace]
  refine ⟨183508519741274842526202713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122339013160849895017468475 183508519741274842526202713)
  ·
    refine ⟨137631389805956131894652035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183508519741274842526202713 137631389805956131894652035)
    ·
      refine ⟨206447084708934197841978053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137631389805956131894652035 206447084708934197841978053)
      ·
        refine ⟨38708828382925162095370885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206447084708934197841978053 38708828382925162095370885)
        ·
          refine ⟨7257905321798467892882041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38708828382925162095370885 7257905321798467892882041)
          ·
            refine ⟨5443428991348850919661531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7257905321798467892882041 5443428991348850919661531)
            ·
              refine ⟨8165143487023276379492297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443428991348850919661531 8165143487023276379492297)
              ·
                refine ⟨6123857615267457284619223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8165143487023276379492297 6123857615267457284619223)
                ·
                  refine ⟨9185786422901185926928835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123857615267457284619223 9185786422901185926928835)
                  ·
                    refine ⟨13778679634351778890393253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9185786422901185926928835 13778679634351778890393253)
                    ·
                      refine ⟨2583502431440958541948735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13778679634351778890393253 2583502431440958541948735)
                      ·
                        rfl

theorem cell23_5031353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5031353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031353 prefixEnd_5031353 := by exact prefixLift 5031353
  have htrace : WordTrace (prefixWord ++ tailWord_5031353) baseStart_5031353 baseEnd_5031353 := by
    simpa [prefixWord, tailWord_5031353, baseEnd_5031353] using wordTrace_append hprefix tailTrace_5031353
  have hstable : (prefixWord ++ tailWord_5031353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031353).length < 2 ^ (prefixWord ++ tailWord_5031353).sum := by decide
  have hdescent : baseEnd_5031353 < baseStart_5031353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031389 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5031389 : Nat := 118140960795 + 5031389 * 2 ^ 59
def prefixEnd_5031389 : Nat := 4983230072969 + 3 ^ 40 * 5031389 * 2
def baseEnd_5031389 : Nat := 861173638914840133699523

theorem tailTrace_5031389 : CollatzResearch.WordTrace tailWord_5031389 prefixEnd_5031389 861173638914840133699523 := by
  unfold tailWord_5031389
  simp only [CollatzResearch.WordTrace]
  refine ⟨183509832769144420674513221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122339888512762947116342147 183509832769144420674513221)
  ·
    refine ⟨34408093644214578876471229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183509832769144420674513221 34408093644214578876471229)
    ·
      refine ⟨12903035116580467078676711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34408093644214578876471229 12903035116580467078676711)
      ·
        refine ⟨19354552674870700618015067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12903035116580467078676711 19354552674870700618015067)
        ·
          refine ⟨29031829012306050927022601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19354552674870700618015067 29031829012306050927022601)
          ·
            refine ⟨21773871759229538195266951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29031829012306050927022601 21773871759229538195266951)
            ·
              refine ⟨32660807638844307292900427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21773871759229538195266951 32660807638844307292900427)
              ·
                refine ⟨48991211458266460939350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32660807638844307292900427 48991211458266460939350641)
                ·
                  refine ⟨36743408593699845704512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48991211458266460939350641 36743408593699845704512981)
                  ·
                    refine ⟨861173638914840133699523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36743408593699845704512981 861173638914840133699523)
                    ·
                      rfl

theorem cell23_5031389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5031389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031389 prefixEnd_5031389 := by exact prefixLift 5031389
  have htrace : WordTrace (prefixWord ++ tailWord_5031389) baseStart_5031389 baseEnd_5031389 := by
    simpa [prefixWord, tailWord_5031389, baseEnd_5031389] using wordTrace_append hprefix tailTrace_5031389
  have hstable : (prefixWord ++ tailWord_5031389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031389).length < 2 ^ (prefixWord ++ tailWord_5031389).sum := by decide
  have hdescent : baseEnd_5031389 < baseStart_5031389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031437 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5031437 : Nat := 118140960795 + 5031437 * 2 ^ 59
def prefixEnd_5031437 : Nat := 4983230072969 + 3 ^ 40 * 5031437 * 2
def baseEnd_5031437 : Nat := 2583545563815936213298349

theorem tailTrace_5031437 : CollatzResearch.WordTrace tailWord_5031437 prefixEnd_5031437 2583545563815936213298349 := by
  unfold tailWord_5031437
  simp only [CollatzResearch.WordTrace]
  refine ⟨183511583472970524872260565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122341055648647016581507043 183511583472970524872260565)
  ·
    refine ⟨4301052737647746676693607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 183511583472970524872260565 4301052737647746676693607)
    ·
      refine ⟨6451579106471620015040411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301052737647746676693607 6451579106471620015040411)
      ·
        refine ⟨9677368659707430022560617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451579106471620015040411 9677368659707430022560617)
        ·
          refine ⟨7258026494780572516920463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9677368659707430022560617 7258026494780572516920463)
          ·
            refine ⟨10887039742170858775380695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258026494780572516920463 10887039742170858775380695)
            ·
              refine ⟨16330559613256288163071043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887039742170858775380695 16330559613256288163071043)
              ·
                refine ⟨24495839419884432244606565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330559613256288163071043 24495839419884432244606565)
                ·
                  refine ⟨4592969891228331045863731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24495839419884432244606565 4592969891228331045863731)
                  ·
                    refine ⟨6889454836842496568795597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4592969891228331045863731 6889454836842496568795597)
                    ·
                      refine ⟨2583545563815936213298349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889454836842496568795597 2583545563815936213298349)
                      ·
                        rfl

theorem cell23_5031437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5031437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031437 prefixEnd_5031437 := by exact prefixLift 5031437
  have htrace : WordTrace (prefixWord ++ tailWord_5031437) baseStart_5031437 baseEnd_5031437 := by
    simpa [prefixWord, tailWord_5031437, baseEnd_5031437] using wordTrace_append hprefix tailTrace_5031437
  have hstable : (prefixWord ++ tailWord_5031437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031437).length < 2 ^ (prefixWord ++ tailWord_5031437).sum := by decide
  have hdescent : baseEnd_5031437 < baseStart_5031437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031443 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 4, 2, 2]
def baseStart_5031443 : Nat := 118140960795 + 5031443 * 2 ^ 59
def prefixEnd_5031443 : Nat := 4983230072969 + 3 ^ 40 * 5031443 * 2
def baseEnd_5031443 : Nat := 2583548644699863189823321

theorem tailTrace_5031443 : CollatzResearch.WordTrace tailWord_5031443 prefixEnd_5031443 2583548644699863189823321 := by
  unfold tailWord_5031443
  simp only [CollatzResearch.WordTrace]
  refine ⟨183511802310948787896978983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122341201540632525264652655 183511802310948787896978983)
  ·
    refine ⟨275267703466423181845468475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183511802310948787896978983 275267703466423181845468475)
    ·
      refine ⟨412901555199634772768202713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275267703466423181845468475 412901555199634772768202713)
      ·
        refine ⟨309676166399726079576152035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412901555199634772768202713 309676166399726079576152035)
        ·
          refine ⟨464514249599589119364228053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309676166399726079576152035 464514249599589119364228053)
          ·
            refine ⟨10887052724990369985099095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 464514249599589119364228053 10887052724990369985099095)
            ·
              refine ⟨16330579087485554977648643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887052724990369985099095 16330579087485554977648643)
              ·
                refine ⟨24495868631228332466472965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330579087485554977648643 24495868631228332466472965)
                ·
                  refine ⟨4592975368355312337463681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24495868631228332466472965 4592975368355312337463681)
                  ·
                    refine ⟨3444731526266484253097761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4592975368355312337463681 3444731526266484253097761)
                    ·
                      refine ⟨2583548644699863189823321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444731526266484253097761 2583548644699863189823321)
                      ·
                        rfl

theorem cell23_5031443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2, 2].length) (baseStart_5031443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031443 prefixEnd_5031443 := by exact prefixLift 5031443
  have htrace : WordTrace (prefixWord ++ tailWord_5031443) baseStart_5031443 baseEnd_5031443 := by
    simpa [prefixWord, tailWord_5031443, baseEnd_5031443] using wordTrace_append hprefix tailTrace_5031443
  have hstable : (prefixWord ++ tailWord_5031443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031443).length < 2 ^ (prefixWord ++ tailWord_5031443).sum := by decide
  have hdescent : baseEnd_5031443 < baseStart_5031443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031454 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5031454 : Nat := 118140960795 + 5031454 * 2 ^ 59
def prefixEnd_5031454 : Nat := 4983230072969 + 3 ^ 40 * 5031454 * 2
def baseEnd_5031454 : Nat := 2583554292987062646785771

theorem tailTrace_5031454 : CollatzResearch.WordTrace tailWord_5031454 prefixEnd_5031454 2583554292987062646785771 := by
  unfold tailWord_5031454
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939025439238617096953677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122341469009272624517086277 22939025439238617096953677)
  ·
    refine ⟨8602134539714481411357629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22939025439238617096953677 8602134539714481411357629)
    ·
      refine ⟨3225800452392930529259111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8602134539714481411357629 3225800452392930529259111)
      ·
        refine ⟨4838700678589395793888667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225800452392930529259111 4838700678589395793888667)
        ·
          refine ⟨7258051017884093690833001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838700678589395793888667 7258051017884093690833001)
          ·
            refine ⟨5443538263413070268124751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7258051017884093690833001 5443538263413070268124751)
            ·
              refine ⟨8165307395119605402187127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443538263413070268124751 8165307395119605402187127)
              ·
                refine ⟨12247961092679408103280691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8165307395119605402187127 12247961092679408103280691)
                ·
                  refine ⟨18371941639019112154921037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12247961092679408103280691 18371941639019112154921037)
                  ·
                    refine ⟨6889478114632167058095389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18371941639019112154921037 6889478114632167058095389)
                    ·
                      refine ⟨2583554292987062646785771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889478114632167058095389 2583554292987062646785771)
                      ·
                        rfl

theorem cell23_5031454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5031454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031454 prefixEnd_5031454 := by exact prefixLift 5031454
  have htrace : WordTrace (prefixWord ++ tailWord_5031454) baseStart_5031454 baseEnd_5031454 := by
    simpa [prefixWord, tailWord_5031454, baseEnd_5031454] using wordTrace_append hprefix tailTrace_5031454
  have hstable : (prefixWord ++ tailWord_5031454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031454).length < 2 ^ (prefixWord ++ tailWord_5031454).sum := by decide
  have hdescent : baseEnd_5031454 < baseStart_5031454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031456 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5031456 : Nat := 118140960795 + 5031456 * 2 ^ 59
def prefixEnd_5031456 : Nat := 4983230072969 + 3 ^ 40 * 5031456 * 2
def baseEnd_5031456 : Nat := 2583555319948371638960761

theorem tailTrace_5031456 : CollatzResearch.WordTrace tailWord_5031456 prefixEnd_5031456 2583555319948371638960761 := by
  unfold tailWord_5031456
  simp only [CollatzResearch.WordTrace]
  refine ⟨91756138229950845558601111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122341517639934460744801481 91756138229950845558601111)
  ·
    refine ⟨137634207344926268337901667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91756138229950845558601111 137634207344926268337901667)
    ·
      refine ⟨206451311017389402506852501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137634207344926268337901667 206451311017389402506852501)
      ·
        refine ⟨9677405203940128242508711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206451311017389402506852501 9677405203940128242508711)
        ·
          refine ⟨14516107805910192363763067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677405203940128242508711 14516107805910192363763067)
          ·
            refine ⟨21774161708865288545644601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14516107805910192363763067 21774161708865288545644601)
            ·
              refine ⟨16330621281648966409233451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21774161708865288545644601 16330621281648966409233451)
              ·
                refine ⟨24495931922473449613850177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330621281648966409233451 24495931922473449613850177)
                ·
                  refine ⟨18371948941855087210387633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24495931922473449613850177 18371948941855087210387633)
                  ·
                    refine ⟨13778961706391315407790725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18371948941855087210387633 13778961706391315407790725)
                    ·
                      refine ⟨2583555319948371638960761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13778961706391315407790725 2583555319948371638960761)
                      ·
                        rfl

theorem cell23_5031456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5031456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031456 prefixEnd_5031456 := by exact prefixLift 5031456
  have htrace : WordTrace (prefixWord ++ tailWord_5031456) baseStart_5031456 baseEnd_5031456 := by
    simpa [prefixWord, tailWord_5031456, baseEnd_5031456] using wordTrace_append hprefix tailTrace_5031456
  have hstable : (prefixWord ++ tailWord_5031456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031456).length < 2 ^ (prefixWord ++ tailWord_5031456).sum := by decide
  have hdescent : baseEnd_5031456 < baseStart_5031456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031479 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 7]
def baseStart_5031479 : Nat := 118140960795 + 5031479 * 2 ^ 59
def prefixEnd_5031479 : Nat := 4983230072969 + 3 ^ 40 * 5031479 * 2
def baseEnd_5031479 : Nat := 861189043334475016324385

theorem tailTrace_5031479 : CollatzResearch.WordTrace tailWord_5031479 prefixEnd_5031479 861189043334475016324385 := by
  unfold tailWord_5031479
  simp only [CollatzResearch.WordTrace]
  refine ⟨183513115338818366045289491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122342076892545577363526327 183513115338818366045289491)
  ·
    refine ⟨275269673008227549067934237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183513115338818366045289491 275269673008227549067934237)
    ·
      refine ⟨103226127378085330900475339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275269673008227549067934237 103226127378085330900475339)
      ·
        refine ⟨154839191067127996350713009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103226127378085330900475339 154839191067127996350713009)
        ·
          refine ⟨116129393300345997263034757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154839191067127996350713009 116129393300345997263034757)
          ·
            refine ⟨21774261243814874486819017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116129393300345997263034757 21774261243814874486819017)
            ·
              refine ⟨16330695932861155865114263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21774261243814874486819017 16330695932861155865114263)
              ·
                refine ⟨24496043899291733797671395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330695932861155865114263 24496043899291733797671395)
                ·
                  refine ⟨36744065848937600696507093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24496043899291733797671395 36744065848937600696507093)
                  ·
                    refine ⟨861189043334475016324385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36744065848937600696507093 861189043334475016324385)
                    ·
                      rfl

theorem cell23_5031479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_5031479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031479 prefixEnd_5031479 := by exact prefixLift 5031479
  have htrace : WordTrace (prefixWord ++ tailWord_5031479) baseStart_5031479 baseEnd_5031479 := by
    simpa [prefixWord, tailWord_5031479, baseEnd_5031479] using wordTrace_append hprefix tailTrace_5031479
  have hstable : (prefixWord ++ tailWord_5031479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031479).length < 2 ^ (prefixWord ++ tailWord_5031479).sum := by decide
  have hdescent : baseEnd_5031479 < baseStart_5031479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031506 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5031506 : Nat := 118140960795 + 5031506 * 2 ^ 59
def prefixEnd_5031506 : Nat := 4983230072969 + 3 ^ 40 * 5031506 * 2
def baseEnd_5031506 : Nat := 2583580993981096443335531

theorem tailTrace_5031506 : CollatzResearch.WordTrace tailWord_5031506 prefixEnd_5031506 2583580993981096443335531 := by
  unfold tailWord_5031506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45878525027430137414130593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122342733406480366437681581 45878525027430137414130593)
  ·
    refine ⟨34408893770572603060597945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45878525027430137414130593 34408893770572603060597945)
    ·
      refine ⟨25806670327929452295448459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34408893770572603060597945 25806670327929452295448459)
      ·
        refine ⟨38710005491894178443172689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25806670327929452295448459 38710005491894178443172689)
        ·
          refine ⟨29032504118920633832379517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38710005491894178443172689 29032504118920633832379517)
          ·
            refine ⟨10887189044595237687142319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29032504118920633832379517 10887189044595237687142319)
            ·
              refine ⟨16330783566892856530713479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10887189044595237687142319 16330783566892856530713479)
              ·
                refine ⟨24496175350339284796070219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16330783566892856530713479 24496175350339284796070219)
                ·
                  refine ⟨36744263025508927194105329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24496175350339284796070219 36744263025508927194105329)
                  ·
                    refine ⟨27558197269131695395578997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36744263025508927194105329 27558197269131695395578997)
                    ·
                      refine ⟨2583580993981096443335531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27558197269131695395578997 2583580993981096443335531)
                      ·
                        rfl

theorem cell23_5031506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5031506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031506 prefixEnd_5031506 := by exact prefixLift 5031506
  have htrace : WordTrace (prefixWord ++ tailWord_5031506) baseStart_5031506 baseEnd_5031506 := by
    simpa [prefixWord, tailWord_5031506, baseEnd_5031506] using wordTrace_append hprefix tailTrace_5031506
  have hstable : (prefixWord ++ tailWord_5031506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031506).length < 2 ^ (prefixWord ++ tailWord_5031506).sum := by decide
  have hdescent : baseEnd_5031506 < baseStart_5031506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031529 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_5031529 : Nat := 118140960795 + 5031529 * 2 ^ 59
def prefixEnd_5031529 : Nat := 4983230072969 + 3 ^ 40 * 5031529 * 2
def baseEnd_5031529 : Nat := 2583592804036149853347925

theorem tailTrace_5031529 : CollatzResearch.WordTrace tailWord_5031529 prefixEnd_5031529 2583592804036149853347925 := by
  unfold tailWord_5031529
  simp only [CollatzResearch.WordTrace]
  refine ⟨183514938988637224584609641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122343292659091483056406427 183514938988637224584609641)
  ·
    refine ⟨137636204241477918438457231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183514938988637224584609641 137636204241477918438457231)
    ·
      refine ⟨206454306362216877657685847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137636204241477918438457231 206454306362216877657685847)
      ·
        refine ⟨309681459543325316486528771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206454306362216877657685847 309681459543325316486528771)
        ·
          refine ⟨464522189314987974729793157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309681459543325316486528771 464522189314987974729793157)
          ·
            refine ⟨87097910496560245261836217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 464522189314987974729793157 87097910496560245261836217)
            ·
              refine ⟨65323432872420183946377163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87097910496560245261836217 65323432872420183946377163)
              ·
                refine ⟨97985149308630275919565745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65323432872420183946377163 97985149308630275919565745)
                ·
                  refine ⟨73488861981472706939674309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97985149308630275919565745 73488861981472706939674309)
                  ·
                    refine ⟨13779161621526132551188933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73488861981472706939674309 13779161621526132551188933)
                    ·
                      refine ⟨2583592804036149853347925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13779161621526132551188933 2583592804036149853347925)
                      ·
                        rfl

theorem cell23_5031529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_5031529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031529 prefixEnd_5031529 := by exact prefixLift 5031529
  have htrace : WordTrace (prefixWord ++ tailWord_5031529) baseStart_5031529 baseEnd_5031529 := by
    simpa [prefixWord, tailWord_5031529, baseEnd_5031529] using wordTrace_append hprefix tailTrace_5031529
  have hstable : (prefixWord ++ tailWord_5031529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031529).length < 2 ^ (prefixWord ++ tailWord_5031529).sum := by decide
  have hdescent : baseEnd_5031529 < baseStart_5031529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031543 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 1, 4]
def baseStart_5031543 : Nat := 118140960795 + 5031543 * 2 ^ 59
def prefixEnd_5031543 : Nat := 4983230072969 + 3 ^ 40 * 5031543 * 2
def baseEnd_5031543 : Nat := 861199997588437599524287

theorem tailTrace_5031543 : CollatzResearch.WordTrace tailWord_5031543 prefixEnd_5031543 861199997588437599524287 := by
  unfold tailWord_5031543
  simp only [CollatzResearch.WordTrace]
  refine ⟨183515449610586504975619283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122343633073724336650412855 183515449610586504975619283)
  ·
    refine ⟨275273174415879757463428925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183515449610586504975619283 275273174415879757463428925)
    ·
      refine ⟨103227440405954909048785847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275273174415879757463428925 103227440405954909048785847)
      ·
        refine ⟨154841160608932363573178771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103227440405954909048785847 154841160608932363573178771)
        ·
          refine ⟨232261740913398545359768157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154841160608932363573178771 232261740913398545359768157)
          ·
            refine ⟨87098152842524454509913059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232261740913398545359768157 87098152842524454509913059)
            ·
              refine ⟨130647229263786681764869589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87098152842524454509913059 130647229263786681764869589)
              ·
                refine ⟨3062044435870000353864131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130647229263786681764869589 3062044435870000353864131)
                ·
                  refine ⟨4593066653805000530796197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062044435870000353864131 4593066653805000530796197)
                  ·
                    refine ⟨861199997588437599524287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593066653805000530796197 861199997588437599524287)
                    ·
                      rfl

theorem cell23_5031543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_5031543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031543 prefixEnd_5031543 := by exact prefixLift 5031543
  have htrace : WordTrace (prefixWord ++ tailWord_5031543) baseStart_5031543 baseEnd_5031543 := by
    simpa [prefixWord, tailWord_5031543, baseEnd_5031543] using wordTrace_append hprefix tailTrace_5031543
  have hstable : (prefixWord ++ tailWord_5031543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031543).length < 2 ^ (prefixWord ++ tailWord_5031543).sum := by decide
  have hdescent : baseEnd_5031543 < baseStart_5031543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031553 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_5031553 : Nat := 118140960795 + 5031553 * 2 ^ 59
def prefixEnd_5031553 : Nat := 4983230072969 + 3 ^ 40 * 5031553 * 2
def baseEnd_5031553 : Nat := 2583605127571857759447815

theorem tailTrace_5031553 : CollatzResearch.WordTrace tailWord_5031553 prefixEnd_5031553 2583605127571857759447815 := by
  unfold tailWord_5031553
  simp only [CollatzResearch.WordTrace]
  refine ⟨183515814340550276683483313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122343876227033517788988875 183515814340550276683483313)
  ·
    refine ⟨137636860755412707512612485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183515814340550276683483313 137636860755412707512612485)
    ·
      refine ⟨25806911391639882658614841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137636860755412707512612485 25806911391639882658614841)
      ·
        refine ⟨19355183543729911993961131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25806911391639882658614841 19355183543729911993961131)
        ·
          refine ⟨29032775315594867990941697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19355183543729911993961131 29032775315594867990941697)
          ·
            refine ⟨21774581486696150993206273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29032775315594867990941697 21774581486696150993206273)
            ·
              refine ⟨16330936115022113244904705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21774581486696150993206273 16330936115022113244904705)
              ·
                refine ⟨12248202086266584933678529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16330936115022113244904705 12248202086266584933678529)
                ·
                  refine ⟨9186151564699938700258897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12248202086266584933678529 9186151564699938700258897)
                  ·
                    refine ⟨6889613673524954025194173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9186151564699938700258897 6889613673524954025194173)
                    ·
                      refine ⟨2583605127571857759447815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889613673524954025194173 2583605127571857759447815)
                      ·
                        rfl

theorem cell23_5031553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_5031553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031553 prefixEnd_5031553 := by exact prefixLift 5031553
  have htrace : WordTrace (prefixWord ++ tailWord_5031553) baseStart_5031553 baseEnd_5031553 := by
    simpa [prefixWord, tailWord_5031553, baseEnd_5031553] using wordTrace_append hprefix tailTrace_5031553
  have hstable : (prefixWord ++ tailWord_5031553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031553).length < 2 ^ (prefixWord ++ tailWord_5031553).sum := by decide
  have hdescent : baseEnd_5031553 < baseStart_5031553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031600 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 1, 1, 3]
def baseStart_5031600 : Nat := 118140960795 + 5031600 * 2 ^ 59
def prefixEnd_5031600 : Nat := 4983230072969 + 3 ^ 40 * 5031600 * 2
def baseEnd_5031600 : Nat := 2583629261162619075560099

theorem tailTrace_5031600 : CollatzResearch.WordTrace tailWord_5031600 prefixEnd_5031600 2583629261162619075560099 := by
  unfold tailWord_5031600
  simp only [CollatzResearch.WordTrace]
  refine ⟨91758764285690001855222127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122345019047586669140296169 91758764285690001855222127)
  ·
    refine ⟨137638146428535002782833191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91758764285690001855222127 137638146428535002782833191)
    ·
      refine ⟨206457219642802504174249787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137638146428535002782833191 206457219642802504174249787)
      ·
        refine ⟨309685829464203756261374681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206457219642802504174249787 309685829464203756261374681)
        ·
          refine ⟨232264372098152817196031011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309685829464203756261374681 232264372098152817196031011)
          ·
            refine ⟨348396558147229225794046517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232264372098152817196031011 348396558147229225794046517)
            ·
              refine ⟨32662177326302739918191861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 348396558147229225794046517 32662177326302739918191861)
              ·
                refine ⟨3062079124340881867330487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32662177326302739918191861 3062079124340881867330487)
                ·
                  refine ⟨4593118686511322800995731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062079124340881867330487 4593118686511322800995731)
                  ·
                    refine ⟨6889678029766984201493597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593118686511322800995731 6889678029766984201493597)
                    ·
                      refine ⟨2583629261162619075560099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889678029766984201493597 2583629261162619075560099)
                      ·
                        rfl

theorem cell23_5031600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 1, 3].length) (baseStart_5031600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031600 prefixEnd_5031600 := by exact prefixLift 5031600
  have htrace : WordTrace (prefixWord ++ tailWord_5031600) baseStart_5031600 baseEnd_5031600 := by
    simpa [prefixWord, tailWord_5031600, baseEnd_5031600] using wordTrace_append hprefix tailTrace_5031600
  have hstable : (prefixWord ++ tailWord_5031600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031600).length < 2 ^ (prefixWord ++ tailWord_5031600).sum := by decide
  have hdescent : baseEnd_5031600 < baseStart_5031600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031633 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_5031633 : Nat := 118140960795 + 5031633 * 2 ^ 59
def prefixEnd_5031633 : Nat := 4983230072969 + 3 ^ 40 * 5031633 * 2
def baseEnd_5031633 : Nat := 861215402008072482149149

theorem tailTrace_5031633 : CollatzResearch.WordTrace tailWord_5031633 prefixEnd_5031633 861215402008072482149149 := by
  unfold tailWord_5031633
  simp only [CollatzResearch.WordTrace]
  refine ⟨183518732180260450346395553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122345821453506966897597035 183518732180260450346395553)
  ·
    refine ⟨137639049135195337759796665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183518732180260450346395553 137639049135195337759796665)
    ·
      refine ⟨103229286851396503319847499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137639049135195337759796665 103229286851396503319847499)
      ·
        refine ⟨154843930277094754979771249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103229286851396503319847499 154843930277094754979771249)
        ·
          refine ⟨116132947707821066234828437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154843930277094754979771249 116132947707821066234828437)
          ·
            refine ⟨5443731923804112479757583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116132947707821066234828437 5443731923804112479757583)
            ·
              refine ⟨8165597885706168719636375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443731923804112479757583 8165597885706168719636375)
              ·
                refine ⟨12248396828559253079454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8165597885706168719636375 12248396828559253079454563)
                ·
                  refine ⟨18372595242838879619181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12248396828559253079454563 18372595242838879619181845)
                  ·
                    refine ⟨861215402008072482149149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18372595242838879619181845 861215402008072482149149)
                    ·
                      rfl

theorem cell23_5031633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_5031633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031633 prefixEnd_5031633 := by exact prefixLift 5031633
  have htrace : WordTrace (prefixWord ++ tailWord_5031633) baseStart_5031633 baseEnd_5031633 := by
    simpa [prefixWord, tailWord_5031633, baseEnd_5031633] using wordTrace_append hprefix tailTrace_5031633
  have hstable : (prefixWord ++ tailWord_5031633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031633).length < 2 ^ (prefixWord ++ tailWord_5031633).sum := by decide
  have hdescent : baseEnd_5031633 < baseStart_5031633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031640 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_5031640 : Nat := 118140960795 + 5031640 * 2 ^ 59
def prefixEnd_5031640 : Nat := 4983230072969 + 3 ^ 40 * 5031640 * 2
def baseEnd_5031640 : Nat := 2583649800388798919059915

theorem tailTrace_5031640 : CollatzResearch.WordTrace tailWord_5031640 prefixEnd_5031640 2583649800388798919059915 := by
  unfold tailWord_5031640
  simp only [CollatzResearch.WordTrace]
  refine ⟨91759493745617545270950187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122345991660823393694600249 91759493745617545270950187)
  ·
    refine ⟨137639240618426317906425281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91759493745617545270950187 137639240618426317906425281)
    ·
      refine ⟨103229430463819738429818961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137639240618426317906425281 103229430463819738429818961)
      ·
        refine ⟨77422072847864803822364221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103229430463819738429818961 77422072847864803822364221)
        ·
          refine ⟨29033277317949301433386583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77422072847864803822364221 29033277317949301433386583)
          ·
            refine ⟨43549915976923952150079875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29033277317949301433386583 43549915976923952150079875)
            ·
              refine ⟨65324873965385928225119813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43549915976923952150079875 65324873965385928225119813)
              ·
                refine ⟨12248413868509861542209965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65324873965385928225119813 12248413868509861542209965)
                ·
                  refine ⟨4593155200691198078328737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12248413868509861542209965 4593155200691198078328737)
                  ·
                    refine ⟨3444866400518398558746553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4593155200691198078328737 3444866400518398558746553)
                    ·
                      refine ⟨2583649800388798919059915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444866400518398558746553 2583649800388798919059915)
                      ·
                        rfl

theorem cell23_5031640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_5031640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031640 prefixEnd_5031640 := by exact prefixLift 5031640
  have htrace : WordTrace (prefixWord ++ tailWord_5031640) baseStart_5031640 baseEnd_5031640 := by
    simpa [prefixWord, tailWord_5031640, baseEnd_5031640] using wordTrace_append hprefix tailTrace_5031640
  have hstable : (prefixWord ++ tailWord_5031640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031640).length < 2 ^ (prefixWord ++ tailWord_5031640).sum := by decide
  have hdescent : baseEnd_5031640 < baseStart_5031640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031651 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5031651 : Nat := 118140960795 + 5031651 * 2 ^ 59
def prefixEnd_5031651 : Nat := 4983230072969 + 3 ^ 40 * 5031651 * 2
def baseEnd_5031651 : Nat := 2583655448675998376022365

theorem tailTrace_5031651 : CollatzResearch.WordTrace tailWord_5031651 prefixEnd_5031651 2583655448675998376022365 := by
  unfold tailWord_5031651
  simp only [CollatzResearch.WordTrace]
  refine ⟨183519388694195239420550807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122346259129463492947033871 183519388694195239420550807)
  ·
    refine ⟨275279083041292859130826211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183519388694195239420550807 275279083041292859130826211)
    ·
      refine ⟨412918624561939288696239317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275279083041292859130826211 412918624561939288696239317)
      ·
        refine ⟨9677780263170452078818109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 412918624561939288696239317 9677780263170452078818109)
        ·
          refine ⟨3629167598688919529556791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9677780263170452078818109 3629167598688919529556791)
          ·
            refine ⟨5443751398033379294335187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629167598688919529556791 5443751398033379294335187)
            ·
              refine ⟨8165627097050068941502781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443751398033379294335187 8165627097050068941502781)
              ·
                refine ⟨3062110161393775853063543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165627097050068941502781 3062110161393775853063543)
                ·
                  refine ⟨4593165242090663779595315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062110161393775853063543 4593165242090663779595315)
                  ·
                    refine ⟨6889747863135995669392973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593165242090663779595315 6889747863135995669392973)
                    ·
                      refine ⟨2583655448675998376022365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889747863135995669392973 2583655448675998376022365)
                      ·
                        rfl

theorem cell23_5031651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5031651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031651 prefixEnd_5031651 := by exact prefixLift 5031651
  have htrace : WordTrace (prefixWord ++ tailWord_5031651) baseStart_5031651 baseEnd_5031651 := by
    simpa [prefixWord, tailWord_5031651, baseEnd_5031651] using wordTrace_append hprefix tailTrace_5031651
  have hstable : (prefixWord ++ tailWord_5031651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031651).length < 2 ^ (prefixWord ++ tailWord_5031651).sum := by decide
  have hdescent : baseEnd_5031651 < baseStart_5031651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031668 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5031668 : Nat := 118140960795 + 5031668 * 2 ^ 59
def prefixEnd_5031668 : Nat := 4983230072969 + 3 ^ 40 * 5031668 * 2
def baseEnd_5031668 : Nat := 2583664177847124809509787

theorem tailTrace_5031668 : CollatzResearch.WordTrace tailWord_5031668 prefixEnd_5031668 2583664177847124809509787 := by
  unfold tailWord_5031668
  simp only [CollatzResearch.WordTrace]
  refine ⟨91760004367566825661959829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122346672490089100882613105 91760004367566825661959829)
  ·
    refine ⟨4301250204729694952904367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91760004367566825661959829 4301250204729694952904367)
    ·
      refine ⟨6451875307094542429356551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301250204729694952904367 6451875307094542429356551)
      ·
        refine ⟨9677812960641813644034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451875307094542429356551 9677812960641813644034827)
        ·
          refine ⟨14516719440962720466052241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677812960641813644034827 14516719440962720466052241)
          ·
            refine ⟨10887539580722040349539181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14516719440962720466052241 10887539580722040349539181)
            ·
              refine ⟨4082827342770765131077193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10887539580722040349539181 4082827342770765131077193)
              ·
                refine ⟨3062120507078073848307895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082827342770765131077193 3062120507078073848307895)
                ·
                  refine ⟨4593180760617110772461843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062120507078073848307895 4593180760617110772461843)
                  ·
                    refine ⟨6889771140925666158692765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593180760617110772461843 6889771140925666158692765)
                    ·
                      refine ⟨2583664177847124809509787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6889771140925666158692765 2583664177847124809509787)
                      ·
                        rfl

theorem cell23_5031668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5031668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031668 prefixEnd_5031668 := by exact prefixLift 5031668
  have htrace : WordTrace (prefixWord ++ tailWord_5031668) baseStart_5031668 baseEnd_5031668 := by
    simpa [prefixWord, tailWord_5031668, baseEnd_5031668] using wordTrace_append hprefix tailTrace_5031668
  have hstable : (prefixWord ++ tailWord_5031668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031668).length < 2 ^ (prefixWord ++ tailWord_5031668).sum := by decide
  have hdescent : baseEnd_5031668 < baseStart_5031668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031676 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_5031676 : Nat := 118140960795 + 5031676 * 2 ^ 59
def prefixEnd_5031676 : Nat := 4983230072969 + 3 ^ 40 * 5031676 * 2
def baseEnd_5031676 : Nat := 861222761897453592736583

theorem tailTrace_5031676 : CollatzResearch.WordTrace tailWord_5031676 prefixEnd_5031676 861222761897453592736583 := by
  unfold tailWord_5031676
  simp only [CollatzResearch.WordTrace]
  refine ⟨91760150259552334345105441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122346867012736445793473921 91760150259552334345105441)
  ·
    refine ⟨68820112694664250758829081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91760150259552334345105441 68820112694664250758829081)
    ·
      refine ⟨51615084520998188069121811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68820112694664250758829081 51615084520998188069121811)
      ·
        refine ⟨77422626781497282103682717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51615084520998188069121811 77422626781497282103682717)
        ·
          refine ⟨29033485043061480788881019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77422626781497282103682717 29033485043061480788881019)
          ·
            refine ⟨43550227564592221183321529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29033485043061480788881019 43550227564592221183321529)
            ·
              refine ⟨32662670673444165887491147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43550227564592221183321529 32662670673444165887491147)
              ·
                refine ⟨48994006010166248831236721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32662670673444165887491147 48994006010166248831236721)
                ·
                  refine ⟨36745504507624686623427541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48994006010166248831236721 36745504507624686623427541)
                  ·
                    refine ⟨861222761897453592736583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36745504507624686623427541 861222761897453592736583)
                    ·
                      rfl

theorem cell23_5031676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_5031676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031676 prefixEnd_5031676 := by exact prefixLift 5031676
  have htrace : WordTrace (prefixWord ++ tailWord_5031676) baseStart_5031676 baseEnd_5031676 := by
    simpa [prefixWord, tailWord_5031676, baseEnd_5031676] using wordTrace_append hprefix tailTrace_5031676
  have hstable : (prefixWord ++ tailWord_5031676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031676).length < 2 ^ (prefixWord ++ tailWord_5031676).sum := by decide
  have hdescent : baseEnd_5031676 < baseStart_5031676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031747 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 2, 2, 2]
def baseStart_5031747 : Nat := 118140960795 + 5031747 * 2 ^ 59
def prefixEnd_5031747 : Nat := 4983230072969 + 3 ^ 40 * 5031747 * 2
def baseEnd_5031747 : Nat := 2583704742818830000421923

theorem tailTrace_5031747 : CollatzResearch.WordTrace tailWord_5031747 prefixEnd_5031747 2583704742818830000421923 := by
  unfold tailWord_5031747
  simp only [CollatzResearch.WordTrace]
  refine ⟨183522890101847447816045495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122348593401231631877363663 183522890101847447816045495)
  ·
    refine ⟨275284335152771171724068243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183522890101847447816045495 275284335152771171724068243)
    ·
      refine ⟨412926502729156757586102365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275284335152771171724068243 412926502729156757586102365)
      ·
        refine ⟨154847438523433784094788387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412926502729156757586102365 154847438523433784094788387)
        ·
          refine ⟨232271157785150676142182581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154847438523433784094788387 232271157785150676142182581)
          ·
            refine ⟨21775421042357875888329617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232271157785150676142182581 21775421042357875888329617)
            ·
              refine ⟨16331565781768406916247213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21775421042357875888329617 16331565781768406916247213)
              ·
                refine ⟨6124337168163152593592705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16331565781768406916247213 6124337168163152593592705)
                ·
                  refine ⟨4593252876122364445194529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124337168163152593592705 4593252876122364445194529)
                  ·
                    refine ⟨3444939657091773333895897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4593252876122364445194529 3444939657091773333895897)
                    ·
                      refine ⟨2583704742818830000421923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444939657091773333895897 2583704742818830000421923)
                      ·
                        rfl

theorem cell23_5031747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_5031747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031747 prefixEnd_5031747 := by exact prefixLift 5031747
  have htrace : WordTrace (prefixWord ++ tailWord_5031747) baseStart_5031747 baseEnd_5031747 := by
    simpa [prefixWord, tailWord_5031747, baseEnd_5031747] using wordTrace_append hprefix tailTrace_5031747
  have hstable : (prefixWord ++ tailWord_5031747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031747).length < 2 ^ (prefixWord ++ tailWord_5031747).sum := by decide
  have hdescent : baseEnd_5031747 < baseStart_5031747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031770 : List Nat := [3, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_5031770 : Nat := 118140960795 + 5031770 * 2 ^ 59
def prefixEnd_5031770 : Nat := 4983230072969 + 3 ^ 40 * 5031770 * 2
def baseEnd_5031770 : Nat := 287079616985987045603813

theorem tailTrace_5031770 : CollatzResearch.WordTrace tailWord_5031770 prefixEnd_5031770 287079616985987045603813 := by
  unfold tailWord_5031770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45880932245191030686033191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122349152653842748496088509 45880932245191030686033191)
  ·
    refine ⟨68821398367786546029049787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45880932245191030686033191 68821398367786546029049787)
    ·
      refine ⟨103232097551679819043574681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68821398367786546029049787 103232097551679819043574681)
      ·
        refine ⟨77424073163759864282681011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103232097551679819043574681 77424073163759864282681011)
        ·
          refine ⟨116136109745639796424021517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77424073163759864282681011 116136109745639796424021517)
          ·
            refine ⟨43551041154614923659008069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116136109745639796424021517 43551041154614923659008069)
            ·
              refine ⟨8165820216490298186064013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43551041154614923659008069 8165820216490298186064013)
              ·
                refine ⟨3062182581183861819774005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165820216490298186064013 3062182581183861819774005)
                ·
                  refine ⟨287079616985987045603813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3062182581183861819774005 287079616985987045603813)
                  ·
                    rfl

theorem cell23_5031770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_5031770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031770 prefixEnd_5031770 := by exact prefixLift 5031770
  have htrace : WordTrace (prefixWord ++ tailWord_5031770) baseStart_5031770 baseEnd_5031770 := by
    simpa [prefixWord, tailWord_5031770, baseEnd_5031770] using wordTrace_append hprefix tailTrace_5031770
  have hstable : (prefixWord ++ tailWord_5031770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031770).length < 2 ^ (prefixWord ++ tailWord_5031770).sum := by decide
  have hdescent : baseEnd_5031770 < baseStart_5031770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031783 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 4, 5]
def baseStart_5031783 : Nat := 118140960795 + 5031783 * 2 ^ 59
def prefixEnd_5031783 : Nat := 4983230072969 + 3 ^ 40 * 5031783 * 2
def baseEnd_5031783 : Nat := 861241076040797286523919

theorem tailTrace_5031783 : CollatzResearch.WordTrace tailWord_5031783 prefixEnd_5031783 861241076040797286523919 := by
  unfold tailWord_5031783
  simp only [CollatzResearch.WordTrace]
  refine ⟨183524203129717025964356003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122349468753144683976237335 183524203129717025964356003)
  ·
    refine ⟨275286304694575538946534005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183524203129717025964356003 275286304694575538946534005)
    ·
      refine ⟨25808091065116456776237563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275286304694575538946534005 25808091065116456776237563)
      ·
        refine ⟨38712136597674685164356345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25808091065116456776237563 38712136597674685164356345)
        ·
          refine ⟨29034102448256013873267259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38712136597674685164356345 29034102448256013873267259)
          ·
            refine ⟨43551153672384020809900889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29034102448256013873267259 43551153672384020809900889)
            ·
              refine ⟨32663365254288015607425667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43551153672384020809900889 32663365254288015607425667)
              ·
                refine ⟨48995047881432023411138501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32663365254288015607425667 48995047881432023411138501)
                ·
                  refine ⟨9186571477768504389588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48995047881432023411138501 9186571477768504389588469)
                  ·
                    refine ⟨861241076040797286523919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9186571477768504389588469 861241076040797286523919)
                    ·
                      rfl

theorem cell23_5031783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_5031783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031783 prefixEnd_5031783 := by exact prefixLift 5031783
  have htrace : WordTrace (prefixWord ++ tailWord_5031783) baseStart_5031783 baseEnd_5031783 := by
    simpa [prefixWord, tailWord_5031783, baseEnd_5031783] using wordTrace_append hprefix tailTrace_5031783
  have hstable : (prefixWord ++ tailWord_5031783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031783).length < 2 ^ (prefixWord ++ tailWord_5031783).sum := by decide
  have hdescent : baseEnd_5031783 < baseStart_5031783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031798 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5031798 : Nat := 118140960795 + 5031798 * 2 ^ 59
def prefixEnd_5031798 : Nat := 4983230072969 + 3 ^ 40 * 5031798 * 2
def baseEnd_5031798 : Nat := 2583730930332209300884189

theorem tailTrace_5031798 : CollatzResearch.WordTrace tailWord_5031798 prefixEnd_5031798 2583730930332209300884189 := by
  unfold tailWord_5031798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470296889041417720384503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122349833483108455684101365 11470296889041417720384503)
  ·
    refine ⟨17205445333562126580576755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11470296889041417720384503 17205445333562126580576755)
    ·
      refine ⟨25808168000343189870865133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17205445333562126580576755 25808168000343189870865133)
      ·
        refine ⟨9678063000128696201574425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25808168000343189870865133 9678063000128696201574425)
        ·
          refine ⟨7258547250096522151180819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9678063000128696201574425 7258547250096522151180819)
          ·
            refine ⟨10887820875144783226771229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258547250096522151180819 10887820875144783226771229)
            ·
              refine ⟨4082932828179293710039211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10887820875144783226771229 4082932828179293710039211)
              ·
                refine ⟨6124399242268940565058817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082932828179293710039211 6124399242268940565058817)
                ·
                  refine ⟨4593299431701705423794113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124399242268940565058817 4593299431701705423794113)
                  ·
                    refine ⟨3444974573776279067845585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4593299431701705423794113 3444974573776279067845585)
                    ·
                      refine ⟨2583730930332209300884189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444974573776279067845585 2583730930332209300884189)
                      ·
                        rfl

theorem cell23_5031798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5031798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031798 prefixEnd_5031798 := by exact prefixLift 5031798
  have htrace : WordTrace (prefixWord ++ tailWord_5031798) baseStart_5031798 baseEnd_5031798 := by
    simpa [prefixWord, tailWord_5031798, baseEnd_5031798] using wordTrace_append hprefix tailTrace_5031798
  have hstable : (prefixWord ++ tailWord_5031798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031798).length < 2 ^ (prefixWord ++ tailWord_5031798).sum := by decide
  have hdescent : baseEnd_5031798 < baseStart_5031798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031843 : List Nat := [1, 1, 1, 4, 1, 2, 1, 6, 6]
def baseStart_5031843 : Nat := 118140960795 + 5031843 * 2 ^ 59
def prefixEnd_5031843 : Nat := 4983230072969 + 3 ^ 40 * 5031843 * 2
def baseEnd_5031843 : Nat := 287083781884629069424609

theorem tailTrace_5031843 : CollatzResearch.WordTrace tailWord_5031843 prefixEnd_5031843 287083781884629069424609 := by
  unfold tailWord_5031843
  simp only [CollatzResearch.WordTrace]
  refine ⟨183526391509499656211540183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122350927672999770807693455 183526391509499656211540183)
  ·
    refine ⟨275289587264249484317310275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183526391509499656211540183 275289587264249484317310275)
    ·
      refine ⟨412934380896374226475965413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275289587264249484317310275 412934380896374226475965413)
      ·
        refine ⟨77425196418070167464243515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412934380896374226475965413 77425196418070167464243515)
        ·
          refine ⟨116137794627105251196365273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77425196418070167464243515 116137794627105251196365273)
          ·
            refine ⟨87103345970328938397273955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116137794627105251196365273 87103345970328938397273955)
            ·
              refine ⟨130655018955493407595910933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87103345970328938397273955 130655018955493407595910933)
              ·
                refine ⟨6124454013538753481058325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130655018955493407595910933 6124454013538753481058325)
                ·
                  refine ⟨287083781884629069424609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6124454013538753481058325 287083781884629069424609)
                  ·
                    rfl

theorem cell23_5031843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 6].length) (baseStart_5031843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031843 prefixEnd_5031843 := by exact prefixLift 5031843
  have htrace : WordTrace (prefixWord ++ tailWord_5031843) baseStart_5031843 baseEnd_5031843 := by
    simpa [prefixWord, tailWord_5031843, baseEnd_5031843] using wordTrace_append hprefix tailTrace_5031843
  have hstable : (prefixWord ++ tailWord_5031843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031843).length < 2 ^ (prefixWord ++ tailWord_5031843).sum := by decide
  have hdescent : baseEnd_5031843 < baseStart_5031843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031847 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 3, 4]
def baseStart_5031847 : Nat := 118140960795 + 5031847 * 2 ^ 59
def prefixEnd_5031847 : Nat := 4983230072969 + 3 ^ 40 * 5031847 * 2
def baseEnd_5031847 : Nat := 861252030294759869723821

theorem tailTrace_5031847 : CollatzResearch.WordTrace tailWord_5031847 prefixEnd_5031847 861252030294759869723821 := by
  unfold tailWord_5031847
  simp only [CollatzResearch.WordTrace]
  refine ⟨183526537401485164894685795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122351024934323443263123863 183526537401485164894685795)
  ·
    refine ⟨275289806102227747342028693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183526537401485164894685795 275289806102227747342028693)
    ·
      refine ⟨12904209661041925656657595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 275289806102227747342028693 12904209661041925656657595)
      ·
        refine ⟨19356314491562888484986393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904209661041925656657595 19356314491562888484986393)
        ·
          refine ⟨14517235868672166363739795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19356314491562888484986393 14517235868672166363739795)
          ·
            refine ⟨21775853803008249545609693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14517235868672166363739795 21775853803008249545609693)
            ·
              refine ⟨8165945176128093579603635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21775853803008249545609693 8165945176128093579603635)
              ·
                refine ⟨12248917764192140369405453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8165945176128093579603635 12248917764192140369405453)
                ·
                  refine ⟨4593344161572052638527045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12248917764192140369405453 4593344161572052638527045)
                  ·
                    refine ⟨861252030294759869723821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593344161572052638527045 861252030294759869723821)
                    ·
                      rfl

theorem cell23_5031847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_5031847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031847 prefixEnd_5031847 := by exact prefixLift 5031847
  have htrace : WordTrace (prefixWord ++ tailWord_5031847) baseStart_5031847 baseEnd_5031847 := by
    simpa [prefixWord, tailWord_5031847, baseEnd_5031847] using wordTrace_append hprefix tailTrace_5031847
  have hstable : (prefixWord ++ tailWord_5031847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031847).length < 2 ^ (prefixWord ++ tailWord_5031847).sum := by decide
  have hdescent : baseEnd_5031847 < baseStart_5031847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031894 : List Nat := [5, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_5031894 : Nat := 118140960795 + 5031894 * 2 ^ 59
def prefixEnd_5031894 : Nat := 4983230072969 + 3 ^ 40 * 5031894 * 2
def baseEnd_5031894 : Nat := 287086691608337880587083

theorem tailTrace_5031894 : CollatzResearch.WordTrace tailWord_5031894 prefixEnd_5031894 287086691608337880587083 := by
  unfold tailWord_5031894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470515727019680745102921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122352167754876594614431157 11470515727019680745102921)
  ·
    refine ⟨8602886795264760558827191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11470515727019680745102921 8602886795264760558827191)
    ·
      refine ⟨12904330192897140838240787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8602886795264760558827191 12904330192897140838240787)
      ·
        refine ⟨19356495289345711257361181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904330192897140838240787 19356495289345711257361181)
        ·
          refine ⟨7258685733504641721510443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19356495289345711257361181 7258685733504641721510443)
          ·
            refine ⟨10888028600256962582265665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258685733504641721510443 10888028600256962582265665)
            ·
              refine ⟨8166021450192721936699249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10888028600256962582265665 8166021450192721936699249)
              ·
                refine ⟨6124516087644541452524437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8166021450192721936699249 6124516087644541452524437)
                ·
                  refine ⟨287086691608337880587083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6124516087644541452524437 287086691608337880587083)
                  ·
                    rfl

theorem cell23_5031894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_5031894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031894 prefixEnd_5031894 := by exact prefixLift 5031894
  have htrace : WordTrace (prefixWord ++ tailWord_5031894) baseStart_5031894 baseEnd_5031894 := by
    simpa [prefixWord, tailWord_5031894, baseEnd_5031894] using wordTrace_append hprefix tailTrace_5031894
  have hstable : (prefixWord ++ tailWord_5031894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031894).length < 2 ^ (prefixWord ++ tailWord_5031894).sum := by decide
  have hdescent : baseEnd_5031894 < baseStart_5031894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031898 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_5031898 : Nat := 118140960795 + 5031898 * 2 ^ 59
def prefixEnd_5031898 : Nat := 4983230072969 + 3 ^ 40 * 5031898 * 2
def baseEnd_5031898 : Nat := 861260759465886303211243

theorem tailTrace_5031898 : CollatzResearch.WordTrace tailWord_5031898 prefixEnd_5031898 861260759465886303211243 := by
  unfold tailWord_5031898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45882099381075100151198087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122352265016200267069861565 45882099381075100151198087)
  ·
    refine ⟨68823149071612650226797131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45882099381075100151198087 68823149071612650226797131)
    ·
      refine ⟨103234723607418975340195697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68823149071612650226797131 103234723607418975340195697)
      ·
        refine ⟨77426042705564231505146773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103234723607418975340195697 77426042705564231505146773)
        ·
          refine ⟨3629345751823323351803755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77426042705564231505146773 3629345751823323351803755)
          ·
            refine ⟨5444018627734985027705633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629345751823323351803755 5444018627734985027705633)
            ·
              refine ⟨4083013970801238770779225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444018627734985027705633 4083013970801238770779225)
              ·
                refine ⟨3062260478100929078084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083013970801238770779225 3062260478100929078084419)
                ·
                  refine ⟨4593390717151393617126629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062260478100929078084419 4593390717151393617126629)
                  ·
                    refine ⟨861260759465886303211243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593390717151393617126629 861260759465886303211243)
                    ·
                      rfl

theorem cell23_5031898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_5031898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031898 prefixEnd_5031898 := by exact prefixLift 5031898
  have htrace : WordTrace (prefixWord ++ tailWord_5031898) baseStart_5031898 baseEnd_5031898 := by
    simpa [prefixWord, tailWord_5031898, baseEnd_5031898] using wordTrace_append hprefix tailTrace_5031898
  have hstable : (prefixWord ++ tailWord_5031898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031898).length < 2 ^ (prefixWord ++ tailWord_5031898).sum := by decide
  have hdescent : baseEnd_5031898 < baseStart_5031898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031923 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_5031923 : Nat := 118140960795 + 5031923 * 2 ^ 59
def prefixEnd_5031923 : Nat := 4983230072969 + 3 ^ 40 * 5031923 * 2
def baseEnd_5031923 : Nat := 2583795115414021311821113

theorem tailTrace_5031923 : CollatzResearch.WordTrace tailWord_5031923 prefixEnd_5031923 2583795115414021311821113 := by
  unfold tailWord_5031923
  simp only [CollatzResearch.WordTrace]
  refine ⟨183529309349209829874452423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122352872899473219916301615 183529309349209829874452423)
  ·
    refine ⟨275293964023814744811678635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183529309349209829874452423 275293964023814744811678635)
    ·
      refine ⟨412940946035722117217517953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275293964023814744811678635 412940946035722117217517953)
      ·
        refine ⟨309705709526791587913138465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412940946035722117217517953 309705709526791587913138465)
        ·
          refine ⟨232279282145093690934853849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309705709526791587913138465 232279282145093690934853849)
          ·
            refine ⟨174209461608820268201140387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232279282145093690934853849 174209461608820268201140387)
            ·
              refine ⟨261314192413230402301710581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174209461608820268201140387 261314192413230402301710581)
              ·
                refine ⟨24498205538740350215785367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261314192413230402301710581 24498205538740350215785367)
                ·
                  refine ⟨36747308308110525323678051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24498205538740350215785367 36747308308110525323678051)
                  ·
                    refine ⟨55120962462165787985517077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36747308308110525323678051 55120962462165787985517077)
                    ·
                      refine ⟨2583795115414021311821113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55120962462165787985517077 2583795115414021311821113)
                      ·
                        rfl

theorem cell23_5031923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_5031923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031923 prefixEnd_5031923 := by exact prefixLift 5031923
  have htrace : WordTrace (prefixWord ++ tailWord_5031923) baseStart_5031923 baseEnd_5031923 := by
    simpa [prefixWord, tailWord_5031923, baseEnd_5031923] using wordTrace_append hprefix tailTrace_5031923
  have hstable : (prefixWord ++ tailWord_5031923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031923).length < 2 ^ (prefixWord ++ tailWord_5031923).sum := by decide
  have hdescent : baseEnd_5031923 < baseStart_5031923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031933 : List Nat := [1, 4, 1, 1, 1, 2, 2, 11]
def baseStart_5031933 : Nat := 118140960795 + 5031933 * 2 ^ 59
def prefixEnd_5031933 : Nat := 4983230072969 + 3 ^ 40 * 5031933 * 2
def baseEnd_5031933 : Nat := 95696305563724676766521

theorem tailTrace_5031933 : CollatzResearch.WordTrace tailWord_5031933 prefixEnd_5031933 95696305563724676766521 := by
  unfold tailWord_5031933
  simp only [CollatzResearch.WordTrace]
  refine ⟨183529674079173601582316453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122353116052782401054877635 183529674079173601582316453)
  ·
    refine ⟨34411813889845050296684335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183529674079173601582316453 34411813889845050296684335)
    ·
      refine ⟨51617720834767575445026503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34411813889845050296684335 51617720834767575445026503)
      ·
        refine ⟨77426581252151363167539755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51617720834767575445026503 77426581252151363167539755)
        ·
          refine ⟨116139871878227044751309633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77426581252151363167539755 116139871878227044751309633)
          ·
            refine ⟨87104903908670283563482225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116139871878227044751309633 87104903908670283563482225)
            ·
              refine ⟨65328677931502712672611669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87104903908670283563482225 65328677931502712672611669)
              ·
                refine ⟨95696305563724676766521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65328677931502712672611669 95696305563724676766521)
                ·
                  rfl

theorem cell23_5031933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 11].length) (baseStart_5031933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031933 prefixEnd_5031933 := by exact prefixLift 5031933
  have htrace : WordTrace (prefixWord ++ tailWord_5031933) baseStart_5031933 baseEnd_5031933 := by
    simpa [prefixWord, tailWord_5031933, baseEnd_5031933] using wordTrace_append hprefix tailTrace_5031933
  have hstable : (prefixWord ++ tailWord_5031933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031933).length < 2 ^ (prefixWord ++ tailWord_5031933).sum := by decide
  have hdescent : baseEnd_5031933 < baseStart_5031933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031947 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 3]
def baseStart_5031947 : Nat := 118140960795 + 5031947 * 2 ^ 59
def prefixEnd_5031947 : Nat := 4983230072969 + 3 ^ 40 * 5031947 * 2
def baseEnd_5031947 : Nat := 2583807438949729217921003

theorem tailTrace_5031947 : CollatzResearch.WordTrace tailWord_5031947 prefixEnd_5031947 2583807438949729217921003 := by
  unfold tailWord_5031947
  simp only [CollatzResearch.WordTrace]
  refine ⟨183530184701122881973326095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122353456467415254648884063 183530184701122881973326095)
  ·
    refine ⟨275295277051684322959989143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183530184701122881973326095 275295277051684322959989143)
    ·
      refine ⟨412942915577526484439983715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275295277051684322959989143 412942915577526484439983715)
      ·
        refine ⟨619414373366289726659975573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412942915577526484439983715 619414373366289726659975573)
        ·
          refine ⟨29035048751544830937186355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 619414373366289726659975573 29035048751544830937186355)
          ·
            refine ⟨43552573127317246405779533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29035048751544830937186355 43552573127317246405779533)
            ·
              refine ⟨16332214922743967402167325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43552573127317246405779533 16332214922743967402167325)
              ·
                refine ⟨6124580596028987775812747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16332214922743967402167325 6124580596028987775812747)
                ·
                  refine ⟨9186870894043481663719121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6124580596028987775812747 9186870894043481663719121)
                  ·
                    refine ⟨6890153170532611247789341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9186870894043481663719121 6890153170532611247789341)
                    ·
                      refine ⟨2583807438949729217921003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890153170532611247789341 2583807438949729217921003)
                      ·
                        rfl

theorem cell23_5031947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 3].length) (baseStart_5031947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031947 prefixEnd_5031947 := by exact prefixLift 5031947
  have htrace : WordTrace (prefixWord ++ tailWord_5031947) baseStart_5031947 baseEnd_5031947 := by
    simpa [prefixWord, tailWord_5031947, baseEnd_5031947] using wordTrace_append hprefix tailTrace_5031947
  have hstable : (prefixWord ++ tailWord_5031947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031947).length < 2 ^ (prefixWord ++ tailWord_5031947).sum := by decide
  have hdescent : baseEnd_5031947 < baseStart_5031947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031953 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_5031953 : Nat := 118140960795 + 5031953 * 2 ^ 59
def prefixEnd_5031953 : Nat := 4983230072969 + 3 ^ 40 * 5031953 * 2
def baseEnd_5031953 : Nat := 2583810519833656194445975

theorem tailTrace_5031953 : CollatzResearch.WordTrace tailWord_5031953 prefixEnd_5031953 2583810519833656194445975 := by
  unfold tailWord_5031953
  simp only [CollatzResearch.WordTrace]
  refine ⟨183530403539101144998044513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122353602359400763332029675 183530403539101144998044513)
  ·
    refine ⟨137647802654325858748533385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183530403539101144998044513 137647802654325858748533385)
    ·
      refine ⟨103235851990744394061400039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137647802654325858748533385 103235851990744394061400039)
      ·
        refine ⟨154853777986116591092100059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103235851990744394061400039 154853777986116591092100059)
        ·
          refine ⟨232280666979174886638150089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154853777986116591092100059 232280666979174886638150089)
          ·
            refine ⟨174210500234381164978612567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232280666979174886638150089 174210500234381164978612567)
            ·
              refine ⟨261315750351571747467918851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174210500234381164978612567 261315750351571747467918851)
              ·
                refine ⟨391973625527357621201878277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261315750351571747467918851 391973625527357621201878277)
                ·
                  refine ⟨73495054786379553975352177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391973625527357621201878277 73495054786379553975352177)
                  ·
                    refine ⟨55121291089784665481514133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73495054786379553975352177 55121291089784665481514133)
                    ·
                      refine ⟨2583810519833656194445975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55121291089784665481514133 2583810519833656194445975)
                      ·
                        rfl

theorem cell23_5031953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_5031953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031953 prefixEnd_5031953 := by exact prefixLift 5031953
  have htrace : WordTrace (prefixWord ++ tailWord_5031953) baseStart_5031953 baseEnd_5031953 := by
    simpa [prefixWord, tailWord_5031953, baseEnd_5031953] using wordTrace_append hprefix tailTrace_5031953
  have hstable : (prefixWord ++ tailWord_5031953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031953).length < 2 ^ (prefixWord ++ tailWord_5031953).sum := by decide
  have hdescent : baseEnd_5031953 < baseStart_5031953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031963 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 7]
def baseStart_5031963 : Nat := 118140960795 + 5031963 * 2 ^ 59
def prefixEnd_5031963 : Nat := 4983230072969 + 3 ^ 40 * 5031963 * 2
def baseEnd_5031963 : Nat := 861271884880067051773643

theorem tailTrace_5031963 : CollatzResearch.WordTrace tailWord_5031963 prefixEnd_5031963 861271884880067051773643 := by
  unfold tailWord_5031963
  simp only [CollatzResearch.WordTrace]
  refine ⟨183530768269064916705908543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122353845512709944470605695 183530768269064916705908543)
  ·
    refine ⟨275296152403597375058862815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183530768269064916705908543 275296152403597375058862815)
    ·
      refine ⟨412944228605396062588294223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275296152403597375058862815 412944228605396062588294223)
      ·
        refine ⟨619416342908094093882441335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412944228605396062588294223 619416342908094093882441335)
        ·
          refine ⟨929124514362141140823662003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619416342908094093882441335 929124514362141140823662003)
          ·
            refine ⟨1393686771543211711235493005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929124514362141140823662003 1393686771543211711235493005)
            ·
              refine ⟨522632539328704391713309877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393686771543211711235493005 522632539328704391713309877)
              ·
                refine ⟨48996800562066036723122801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522632539328704391713309877 48996800562066036723122801)
                ·
                  refine ⟨36747600421549527542342101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48996800562066036723122801 36747600421549527542342101)
                  ·
                    refine ⟨861271884880067051773643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36747600421549527542342101 861271884880067051773643)
                    ·
                      rfl

theorem cell23_5031963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_5031963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031963 prefixEnd_5031963 := by exact prefixLift 5031963
  have htrace : WordTrace (prefixWord ++ tailWord_5031963) baseStart_5031963 baseEnd_5031963 := by
    simpa [prefixWord, tailWord_5031963, baseEnd_5031963] using wordTrace_append hprefix tailTrace_5031963
  have hstable : (prefixWord ++ tailWord_5031963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031963).length < 2 ^ (prefixWord ++ tailWord_5031963).sum := by decide
  have hdescent : baseEnd_5031963 < baseStart_5031963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031983 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_5031983 : Nat := 118140960795 + 5031983 * 2 ^ 59
def prefixEnd_5031983 : Nat := 4983230072969 + 3 ^ 40 * 5031983 * 2
def baseEnd_5031983 : Nat := 2583825924253291077070837

theorem tailTrace_5031983 : CollatzResearch.WordTrace tailWord_5031983 prefixEnd_5031983 2583825924253291077070837 := by
  unfold tailWord_5031983
  simp only [CollatzResearch.WordTrace]
  refine ⟨183531497728992460121636603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122354331819328306747757735 183531497728992460121636603)
  ·
    refine ⟨275297246593488690182454905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183531497728992460121636603 275297246593488690182454905)
    ·
      refine ⟨206472934945116517636841179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275297246593488690182454905 206472934945116517636841179)
      ·
        refine ⟨309709402417674776455261769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206472934945116517636841179 309709402417674776455261769)
        ·
          refine ⟨232282051813256082341446327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309709402417674776455261769 232282051813256082341446327)
          ·
            refine ⟨348423077719884123512169491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232282051813256082341446327 348423077719884123512169491)
            ·
              refine ⟨522634616579826185268254237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348423077719884123512169491 522634616579826185268254237)
              ·
                refine ⟨195987981217434819475595339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522634616579826185268254237 195987981217434819475595339)
                ·
                  refine ⟨293981971826152229213393009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195987981217434819475595339 293981971826152229213393009)
                  ·
                    refine ⟨220486478869614171910044757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293981971826152229213393009 220486478869614171910044757)
                    ·
                      refine ⟨2583825924253291077070837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220486478869614171910044757 2583825924253291077070837)
                      ·
                        rfl

theorem cell23_5031983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_5031983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031983 prefixEnd_5031983 := by exact prefixLift 5031983
  have htrace : WordTrace (prefixWord ++ tailWord_5031983) baseStart_5031983 baseEnd_5031983 := by
    simpa [prefixWord, tailWord_5031983, baseEnd_5031983] using wordTrace_append hprefix tailTrace_5031983
  have hstable : (prefixWord ++ tailWord_5031983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031983).length < 2 ^ (prefixWord ++ tailWord_5031983).sum := by decide
  have hdescent : baseEnd_5031983 < baseStart_5031983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031987 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 3, 3, 2]
def baseStart_5031987 : Nat := 118140960795 + 5031987 * 2 ^ 59
def prefixEnd_5031987 : Nat := 4983230072969 + 3 ^ 40 * 5031987 * 2
def baseEnd_5031987 : Nat := 2583827978175909061420819

theorem tailTrace_5031987 : CollatzResearch.WordTrace tailWord_5031987 prefixEnd_5031987 2583827978175909061420819 := by
  unfold tailWord_5031987
  simp only [CollatzResearch.WordTrace]
  refine ⟨183531643620977968804782215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122354429080651979203188143 183531643620977968804782215)
  ·
    refine ⟨275297465431466953207173323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183531643620977968804782215 275297465431466953207173323)
    ·
      refine ⟨412946198147200429810759985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275297465431466953207173323 412946198147200429810759985)
      ·
        refine ⟨309709648610400322358069989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412946198147200429810759985 309709648610400322358069989)
        ·
          refine ⟨58070559114450060442138123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309709648610400322358069989 58070559114450060442138123)
          ·
            refine ⟨87105838671675090663207185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58070559114450060442138123 87105838671675090663207185)
            ·
              refine ⟨65329379003756317997405389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87105838671675090663207185 65329379003756317997405389)
              ·
                refine ⟨24498517126408619249027021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65329379003756317997405389 24498517126408619249027021)
                ·
                  refine ⟨9186943922403232218385133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24498517126408619249027021 9186943922403232218385133)
                  ·
                    refine ⟨3445103970901212081894425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9186943922403232218385133 3445103970901212081894425)
                    ·
                      refine ⟨2583827978175909061420819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445103970901212081894425 2583827978175909061420819)
                      ·
                        rfl

theorem cell23_5031987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3, 2].length) (baseStart_5031987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031987 prefixEnd_5031987 := by exact prefixLift 5031987
  have htrace : WordTrace (prefixWord ++ tailWord_5031987) baseStart_5031987 baseEnd_5031987 := by
    simpa [prefixWord, tailWord_5031987, baseEnd_5031987] using wordTrace_append hprefix tailTrace_5031987
  have hstable : (prefixWord ++ tailWord_5031987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031987).length < 2 ^ (prefixWord ++ tailWord_5031987).sum := by decide
  have hdescent : baseEnd_5031987 < baseStart_5031987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032020 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5032020 : Nat := 118140960795 + 5032020 * 2 ^ 59
def prefixEnd_5032020 : Nat := 4983230072969 + 3 ^ 40 * 5032020 * 2
def baseEnd_5032020 : Nat := 2583844923037507432308167

theorem tailTrace_5032020 : CollatzResearch.WordTrace tailWord_5032020 prefixEnd_5032020 2583844923037507432308167 := by
  unfold tailWord_5032020
  simp only [CollatzResearch.WordTrace]
  refine ⟨91766423614929207720366757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122355231486572276960489009 91766423614929207720366757)
  ·
    refine ⟨17206204427799226447568767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91766423614929207720366757 17206204427799226447568767)
    ·
      refine ⟨25809306641698839671353151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17206204427799226447568767 25809306641698839671353151)
      ·
        refine ⟨38713959962548259507029727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25809306641698839671353151 38713959962548259507029727)
        ·
          refine ⟨58070939943822389260544591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38713959962548259507029727 58070939943822389260544591)
          ·
            refine ⟨87106409915733583890816887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58070939943822389260544591 87106409915733583890816887)
            ·
              refine ⟨130659614873600375836225331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87106409915733583890816887 130659614873600375836225331)
              ·
                refine ⟨195989422310400563754337997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130659614873600375836225331 195989422310400563754337997)
                ·
                  refine ⟨73496033366400211407876749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195989422310400563754337997 73496033366400211407876749)
                  ·
                    refine ⟨27561012512400079277953781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73496033366400211407876749 27561012512400079277953781)
                    ·
                      refine ⟨2583844923037507432308167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27561012512400079277953781 2583844923037507432308167)
                      ·
                        rfl

theorem cell23_5032020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5032020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032020 prefixEnd_5032020 := by exact prefixLift 5032020
  have htrace : WordTrace (prefixWord ++ tailWord_5032020) baseStart_5032020 baseEnd_5032020 := by
    simpa [prefixWord, tailWord_5032020, baseEnd_5032020] using wordTrace_append hprefix tailTrace_5032020
  have hstable : (prefixWord ++ tailWord_5032020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032020).length < 2 ^ (prefixWord ++ tailWord_5032020).sum := by decide
  have hdescent : baseEnd_5032020 < baseStart_5032020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032028 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_5032028 : Nat := 118140960795 + 5032028 * 2 ^ 59
def prefixEnd_5032028 : Nat := 4983230072969 + 3 ^ 40 * 5032028 * 2
def baseEnd_5032028 : Nat := 2583849030882743401008131

theorem tailTrace_5032028 : CollatzResearch.WordTrace tailWord_5032028 prefixEnd_5032028 2583849030882743401008131 := by
  unfold tailWord_5032028
  simp only [CollatzResearch.WordTrace]
  refine ⟨91766569506914716403512369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122355426009219621871349825 91766569506914716403512369)
  ·
    refine ⟨68824927130186037302634277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91766569506914716403512369 68824927130186037302634277)
    ·
      refine ⟨12904673836909881994243927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68824927130186037302634277 12904673836909881994243927)
      ·
        refine ⟨19357010755364822991365891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904673836909881994243927 19357010755364822991365891)
        ·
          refine ⟨29035516133047234487048837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19357010755364822991365891 29035516133047234487048837)
          ·
            refine ⟨5444159274946356466321657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29035516133047234487048837 5444159274946356466321657)
            ·
              refine ⟨4083119456209767349741243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444159274946356466321657 4083119456209767349741243)
              ·
                refine ⟨6124679184314651024611865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083119456209767349741243 6124679184314651024611865)
                ·
                  refine ⟨4593509388235988268458899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6124679184314651024611865 4593509388235988268458899)
                  ·
                    refine ⟨6890264082353982402688349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593509388235988268458899 6890264082353982402688349)
                    ·
                      refine ⟨2583849030882743401008131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890264082353982402688349 2583849030882743401008131)
                      ·
                        rfl

theorem cell23_5032028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_5032028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032028 prefixEnd_5032028 := by exact prefixLift 5032028
  have htrace : WordTrace (prefixWord ++ tailWord_5032028) baseStart_5032028 baseEnd_5032028 := by
    simpa [prefixWord, tailWord_5032028, baseEnd_5032028] using wordTrace_append hprefix tailTrace_5032028
  have hstable : (prefixWord ++ tailWord_5032028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032028).length < 2 ^ (prefixWord ++ tailWord_5032028).sum := by decide
  have hdescent : baseEnd_5032028 < baseStart_5032028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032074 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_5032074 : Nat := 118140960795 + 5032074 * 2 ^ 59
def prefixEnd_5032074 : Nat := 4983230072969 + 3 ^ 40 * 5032074 * 2
def baseEnd_5032074 : Nat := 287096961221427802336991

theorem tailTrace_5032074 : CollatzResearch.WordTrace tailWord_5032074 prefixEnd_5032074 287096961221427802336991 := by
  unfold tailWord_5032074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45883704192915695665799819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122356544514441855108799517 45883704192915695665799819)
  ·
    refine ⟨68825556289373543498699729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45883704192915695665799819 68825556289373543498699729)
    ·
      refine ⟨51619167217030157624024797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68825556289373543498699729 51619167217030157624024797)
      ·
        refine ⟨19357187706386309109009299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51619167217030157624024797 19357187706386309109009299)
        ·
          refine ⟨29035781559579463663513949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19357187706386309109009299 29035781559579463663513949)
          ·
            refine ⟨10888418084842298873817731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29035781559579463663513949 10888418084842298873817731)
            ·
              refine ⟨16332627127263448310726597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888418084842298873817731 16332627127263448310726597)
              ·
                refine ⟨3062367586361896558261237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16332627127263448310726597 3062367586361896558261237)
                ·
                  refine ⟨287096961221427802336991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3062367586361896558261237 287096961221427802336991)
                  ·
                    rfl

theorem cell23_5032074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_5032074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032074 prefixEnd_5032074 := by exact prefixLift 5032074
  have htrace : WordTrace (prefixWord ++ tailWord_5032074) baseStart_5032074 baseEnd_5032074 := by
    simpa [prefixWord, tailWord_5032074, baseEnd_5032074] using wordTrace_append hprefix tailTrace_5032074
  have hstable : (prefixWord ++ tailWord_5032074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032074).length < 2 ^ (prefixWord ++ tailWord_5032074).sum := by decide
  have hdescent : baseEnd_5032074 < baseStart_5032074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032080 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_5032080 : Nat := 118140960795 + 5032080 * 2 ^ 59
def prefixEnd_5032080 : Nat := 4983230072969 + 3 ^ 40 * 5032080 * 2
def baseEnd_5032080 : Nat := 2583875731876777197557891

theorem tailTrace_5032080 : CollatzResearch.WordTrace tailWord_5032080 prefixEnd_5032080 2583875731876777197557891 := by
  unfold tailWord_5032080
  simp only [CollatzResearch.WordTrace]
  refine ⟨91767517804820522843958847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122356690406427363791945129 91767517804820522843958847)
  ·
    refine ⟨137651276707230784265938271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91767517804820522843958847 137651276707230784265938271)
    ·
      refine ⟨206476915060846176398907407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137651276707230784265938271 206476915060846176398907407)
      ·
        refine ⟨309715372591269264598361111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206476915060846176398907407 309715372591269264598361111)
        ·
          refine ⟨464573058886903896897541667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309715372591269264598361111 464573058886903896897541667)
          ·
            refine ⟨696859588330355845346312501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464573058886903896897541667 696859588330355845346312501)
            ·
              refine ⟨65330586405970860501216797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 696859588330355845346312501 65330586405970860501216797)
              ·
                refine ⟨24498969902239072687956299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65330586405970860501216797 24498969902239072687956299)
                ·
                  refine ⟨36748454853358609031934449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24498969902239072687956299 36748454853358609031934449)
                  ·
                    refine ⟨27561341140018956773950837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36748454853358609031934449 27561341140018956773950837)
                    ·
                      refine ⟨2583875731876777197557891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27561341140018956773950837 2583875731876777197557891)
                      ·
                        rfl

theorem cell23_5032080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_5032080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032080 prefixEnd_5032080 := by exact prefixLift 5032080
  have htrace : WordTrace (prefixWord ++ tailWord_5032080) baseStart_5032080 baseEnd_5032080 := by
    simpa [prefixWord, tailWord_5032080, baseEnd_5032080] using wordTrace_append hprefix tailTrace_5032080
  have hstable : (prefixWord ++ tailWord_5032080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032080).length < 2 ^ (prefixWord ++ tailWord_5032080).sum := by decide
  have hdescent : baseEnd_5032080 < baseStart_5032080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032120 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_5032120 : Nat := 118140960795 + 5032120 * 2 ^ 59
def prefixEnd_5032120 : Nat := 4983230072969 + 3 ^ 40 * 5032120 * 2
def baseEnd_5032120 : Nat := 2583896271102957041057707

theorem tailTrace_5032120 : CollatzResearch.WordTrace tailWord_5032120 prefixEnd_5032120 2583896271102957041057707 := by
  unfold tailWord_5032120
  simp only [CollatzResearch.WordTrace]
  refine ⟨91768247264748066259686907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122357663019664088346249209 91768247264748066259686907)
  ·
    refine ⟨137652370897122099389530361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91768247264748066259686907 137652370897122099389530361)
    ·
      refine ⟨103239278172841574542147771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137652370897122099389530361 103239278172841574542147771)
      ·
        refine ⟨154858917259262361813221657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103239278172841574542147771 154858917259262361813221657)
        ·
          refine ⟨116144187944446771359916243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154858917259262361813221657 116144187944446771359916243)
          ·
            refine ⟨174216281916670157039874365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116144187944446771359916243 174216281916670157039874365)
            ·
              refine ⟨65331105718751308889952887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174216281916670157039874365 65331105718751308889952887)
              ·
                refine ⟨97996658578126963334929331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65331105718751308889952887 97996658578126963334929331)
                ·
                  refine ⟨146994987867190445002393997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97996658578126963334929331 146994987867190445002393997)
                  ·
                    refine ⟨55123120450196416875897749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146994987867190445002393997 55123120450196416875897749)
                    ·
                      refine ⟨2583896271102957041057707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55123120450196416875897749 2583896271102957041057707)
                      ·
                        rfl

theorem cell23_5032120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_5032120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032120 prefixEnd_5032120 := by exact prefixLift 5032120
  have htrace : WordTrace (prefixWord ++ tailWord_5032120) baseStart_5032120 baseEnd_5032120 := by
    simpa [prefixWord, tailWord_5032120, baseEnd_5032120] using wordTrace_append hprefix tailTrace_5032120
  have hstable : (prefixWord ++ tailWord_5032120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032120).length < 2 ^ (prefixWord ++ tailWord_5032120).sum := by decide
  have hdescent : baseEnd_5032120 < baseStart_5032120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032127 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_5032127 : Nat := 118140960795 + 5032127 * 2 ^ 59
def prefixEnd_5032127 : Nat := 4983230072969 + 3 ^ 40 * 5032127 * 2
def baseEnd_5032127 : Nat := 2583899865467538513670175

theorem tailTrace_5032127 : CollatzResearch.WordTrace tailWord_5032127 prefixEnd_5032127 2583899865467538513670175 := by
  unfold tailWord_5032127
  simp only [CollatzResearch.WordTrace]
  refine ⟨183536749840470772714878635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122357833226980515143252423 183536749840470772714878635)
  ·
    refine ⟨275305124760706159072317953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183536749840470772714878635 275305124760706159072317953)
    ·
      refine ⟨206478843570529619304238465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275305124760706159072317953 206478843570529619304238465)
      ·
        refine ⟨154859132677897214478178849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206478843570529619304238465 154859132677897214478178849)
        ·
          refine ⟨116144349508422910858634137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154859132677897214478178849 116144349508422910858634137)
          ·
            refine ⟨87108262131317183143975603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116144349508422910858634137 87108262131317183143975603)
            ·
              refine ⟨130662393196975774715963405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87108262131317183143975603 130662393196975774715963405)
              ·
                refine ⟨48998397448865915518486277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130662393196975774715963405 48998397448865915518486277)
                ·
                  refine ⟨9187199521662359159716177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48998397448865915518486277 9187199521662359159716177)
                  ·
                    refine ⟨6890399641246769369787133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9187199521662359159716177 6890399641246769369787133)
                    ·
                      refine ⟨2583899865467538513670175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890399641246769369787133 2583899865467538513670175)
                      ·
                        rfl

theorem cell23_5032127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_5032127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032127 prefixEnd_5032127 := by exact prefixLift 5032127
  have htrace : WordTrace (prefixWord ++ tailWord_5032127) baseStart_5032127 baseEnd_5032127 := by
    simpa [prefixWord, tailWord_5032127, baseEnd_5032127] using wordTrace_append hprefix tailTrace_5032127
  have hstable : (prefixWord ++ tailWord_5032127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032127).length < 2 ^ (prefixWord ++ tailWord_5032127).sum := by decide
  have hdescent : baseEnd_5032127 < baseStart_5032127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032168 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5032168 : Nat := 118140960795 + 5032168 * 2 ^ 59
def prefixEnd_5032168 : Nat := 4983230072969 + 3 ^ 40 * 5032168 * 2
def baseEnd_5032168 : Nat := 861306972724790951085829

theorem tailTrace_5032168 : CollatzResearch.WordTrace tailWord_5032168 prefixEnd_5032168 861306972724790951085829 := by
  unfold tailWord_5032168
  simp only [CollatzResearch.WordTrace]
  refine ⟨91769122616661118358560579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122358830155548157811414105 91769122616661118358560579)
  ·
    refine ⟨137653683924991677537840869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91769122616661118358560579 137653683924991677537840869)
    ·
      refine ⟨25810065735935939538345163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137653683924991677537840869 25810065735935939538345163)
      ·
        refine ⟨38715098603903909307517745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25810065735935939538345163 38715098603903909307517745)
        ·
          refine ⟨29036323952927931980638309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38715098603903909307517745 29036323952927931980638309)
          ·
            refine ⟨5444310741173987246369683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29036323952927931980638309 5444310741173987246369683)
            ·
              refine ⟨8166466111760980869554525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444310741173987246369683 8166466111760980869554525)
              ·
                refine ⟨3062424791910367826082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8166466111760980869554525 3062424791910367826082947)
                ·
                  refine ⟨4593637187865551739124421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062424791910367826082947 4593637187865551739124421)
                  ·
                    refine ⟨861306972724790951085829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593637187865551739124421 861306972724790951085829)
                    ·
                      rfl

theorem cell23_5032168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5032168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032168 prefixEnd_5032168 := by exact prefixLift 5032168
  have htrace : WordTrace (prefixWord ++ tailWord_5032168) baseStart_5032168 baseEnd_5032168 := by
    simpa [prefixWord, tailWord_5032168, baseEnd_5032168] using wordTrace_append hprefix tailTrace_5032168
  have hstable : (prefixWord ++ tailWord_5032168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032168).length < 2 ^ (prefixWord ++ tailWord_5032168).sum := by decide
  have hdescent : baseEnd_5032168 < baseStart_5032168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032218 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_5032218 : Nat := 118140960795 + 5032218 * 2 ^ 59
def prefixEnd_5032218 : Nat := 4983230072969 + 3 ^ 40 * 5032218 * 2
def baseEnd_5032218 : Nat := 2583946592207097657632257

theorem tailTrace_5032218 : CollatzResearch.WordTrace tailWord_5032218 prefixEnd_5032218 2583946592207097657632257 := by
  unfold tailWord_5032218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885017220785273814110327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122360045922094063504294205 45885017220785273814110327)
  ·
    refine ⟨68827525831177910721165491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45885017220785273814110327 68827525831177910721165491)
    ·
      refine ⟨103241288746766866081748237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68827525831177910721165491 103241288746766866081748237)
      ·
        refine ⟨38715483280037574780655589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103241288746766866081748237 38715483280037574780655589)
        ·
          refine ⟨7259153115007045271372923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38715483280037574780655589 7259153115007045271372923)
          ·
            refine ⟨10888729672510567907059385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259153115007045271372923 10888729672510567907059385)
            ·
              refine ⟨8166547254382925930294539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10888729672510567907059385 8166547254382925930294539)
              ·
                refine ⟨12249820881574388895441809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8166547254382925930294539 12249820881574388895441809)
                ·
                  refine ⟨9187365661180791671581357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12249820881574388895441809 9187365661180791671581357)
                  ·
                    refine ⟨3445262122942796876843009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9187365661180791671581357 3445262122942796876843009)
                    ·
                      refine ⟨2583946592207097657632257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445262122942796876843009 2583946592207097657632257)
                      ·
                        rfl

theorem cell23_5032218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_5032218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032218 prefixEnd_5032218 := by exact prefixLift 5032218
  have htrace : WordTrace (prefixWord ++ tailWord_5032218) baseStart_5032218 baseEnd_5032218 := by
    simpa [prefixWord, tailWord_5032218, baseEnd_5032218] using wordTrace_append hprefix tailTrace_5032218
  have hstable : (prefixWord ++ tailWord_5032218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032218).length < 2 ^ (prefixWord ++ tailWord_5032218).sum := by decide
  have hdescent : baseEnd_5032218 < baseStart_5032218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032224 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_5032224 : Nat := 118140960795 + 5032224 * 2 ^ 59
def prefixEnd_5032224 : Nat := 4983230072969 + 3 ^ 40 * 5032224 * 2
def baseEnd_5032224 : Nat := 861316557697008211385743

theorem tailTrace_5032224 : CollatzResearch.WordTrace tailWord_5032224 prefixEnd_5032224 861316557697008211385743 := by
  unfold tailWord_5032224
  simp only [CollatzResearch.WordTrace]
  refine ⟨91770143860559679140579863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122360191814079572187439817 91770143860559679140579863)
  ·
    refine ⟨137655215790839518710869795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91770143860559679140579863 137655215790839518710869795)
    ·
      refine ⟨206482823686259278066304693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137655215790839518710869795 206482823686259278066304693)
      ·
        refine ⟨19357764720586807318716065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206482823686259278066304693 19357764720586807318716065)
        ·
          refine ⟨14518323540440105489037049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19357764720586807318716065 14518323540440105489037049)
          ·
            refine ⟨10888742655330079116777787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14518323540440105489037049 10888742655330079116777787)
            ·
              refine ⟨16333113982995118675166681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888742655330079116777787 16333113982995118675166681)
              ·
                refine ⟨12249835487246339006375011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16333113982995118675166681 12249835487246339006375011)
                ·
                  refine ⟨18374753230869508509562517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12249835487246339006375011 18374753230869508509562517)
                  ·
                    refine ⟨861316557697008211385743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18374753230869508509562517 861316557697008211385743)
                    ·
                      rfl

theorem cell23_5032224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_5032224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032224 prefixEnd_5032224 := by exact prefixLift 5032224
  have htrace : WordTrace (prefixWord ++ tailWord_5032224) baseStart_5032224 baseEnd_5032224 := by
    simpa [prefixWord, tailWord_5032224, baseEnd_5032224] using wordTrace_append hprefix tailTrace_5032224
  have hstable : (prefixWord ++ tailWord_5032224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032224).length < 2 ^ (prefixWord ++ tailWord_5032224).sum := by decide
  have hdescent : baseEnd_5032224 < baseStart_5032224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032242 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5032242 : Nat := 118140960795 + 5032242 * 2 ^ 59
def prefixEnd_5032242 : Nat := 4983230072969 + 3 ^ 40 * 5032242 * 2
def baseEnd_5032242 : Nat := 2583958915742805563732147

theorem tailTrace_5032242 : CollatzResearch.WordTrace tailWord_5032242 prefixEnd_5032242 2583958915742805563732147 := by
  unfold tailWord_5032242
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885236058763536838828745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122360629490036098236876653 45885236058763536838828745)
  ·
    refine ⟨34413927044072652629121559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45885236058763536838828745 34413927044072652629121559)
    ·
      refine ⟨51620890566108978943682339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34413927044072652629121559 51620890566108978943682339)
      ·
        refine ⟨77431335849163468415523509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51620890566108978943682339 77431335849163468415523509)
        ·
          refine ⟨7259187735859075163955329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77431335849163468415523509 7259187735859075163955329)
          ·
            refine ⟨5444390801894306372966497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259187735859075163955329 5444390801894306372966497)
            ·
              refine ⟨4083293101420729779724873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5444390801894306372966497 4083293101420729779724873)
              ·
                refine ⟨3062469826065547334793655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4083293101420729779724873 3062469826065547334793655)
                ·
                  refine ⟨4593704739098321002190483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062469826065547334793655 4593704739098321002190483)
                  ·
                    refine ⟨6890557108647481503285725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593704739098321002190483 6890557108647481503285725)
                    ·
                      refine ⟨2583958915742805563732147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890557108647481503285725 2583958915742805563732147)
                      ·
                        rfl

theorem cell23_5032242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5032242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032242 prefixEnd_5032242 := by exact prefixLift 5032242
  have htrace : WordTrace (prefixWord ++ tailWord_5032242) baseStart_5032242 baseEnd_5032242 := by
    simpa [prefixWord, tailWord_5032242, baseEnd_5032242] using wordTrace_append hprefix tailTrace_5032242
  have hstable : (prefixWord ++ tailWord_5032242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032242).length < 2 ^ (prefixWord ++ tailWord_5032242).sum := by decide
  have hdescent : baseEnd_5032242 < baseStart_5032242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032254 : List Nat := [4, 2, 1, 2, 1, 2, 3, 8]
def baseStart_5032254 : Nat := 118140960795 + 5032254 * 2 ^ 59
def prefixEnd_5032254 : Nat := 4983230072969 + 3 ^ 40 * 5032254 * 2
def baseEnd_5032254 : Nat := 95702410278172574695633

theorem tailTrace_5032254 : CollatzResearch.WordTrace tailWord_5032254 prefixEnd_5032254 95702410278172574695633 := by
  unfold tailWord_5032254
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942672738876334175593977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122360921274007115603167877 22942672738876334175593977)
  ·
    refine ⟨17207004554157250631695483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22942672738876334175593977 17207004554157250631695483)
    ·
      refine ⟨25810506831235875947543225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207004554157250631695483 25810506831235875947543225)
      ·
        refine ⟨19357880123426906960657419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25810506831235875947543225 19357880123426906960657419)
        ·
          refine ⟨29036820185140360440986129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19357880123426906960657419 29036820185140360440986129)
          ·
            refine ⟨21777615138855270330739597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29036820185140360440986129 21777615138855270330739597)
            ·
              refine ⟨8166605677070726374027349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21777615138855270330739597 8166605677070726374027349)
              ·
                refine ⟨95702410278172574695633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8166605677070726374027349 95702410278172574695633)
                ·
                  rfl

theorem cell23_5032254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_5032254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032254 prefixEnd_5032254 := by exact prefixLift 5032254
  have htrace : WordTrace (prefixWord ++ tailWord_5032254) baseStart_5032254 baseEnd_5032254 := by
    simpa [prefixWord, tailWord_5032254, baseEnd_5032254] using wordTrace_append hprefix tailTrace_5032254
  have hstable : (prefixWord ++ tailWord_5032254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032254).length < 2 ^ (prefixWord ++ tailWord_5032254).sum := by decide
  have hdescent : baseEnd_5032254 < baseStart_5032254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032264 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_5032264 : Nat := 118140960795 + 5032264 * 2 ^ 59
def prefixEnd_5032264 : Nat := 4983230072969 + 3 ^ 40 * 5032264 * 2
def baseEnd_5032264 : Nat := 2583970212317204477657045

theorem tailTrace_5032264 : CollatzResearch.WordTrace tailWord_5032264 prefixEnd_5032264 2583970212317204477657045 := by
  unfold tailWord_5032264
  simp only [CollatzResearch.WordTrace]
  refine ⟨91770873320487222556307923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122361164427316296741743897 91770873320487222556307923)
  ·
    refine ⟨137656309980730833834461885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91770873320487222556307923 137656309980730833834461885)
    ·
      refine ⟨51621116242774062687923207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137656309980730833834461885 51621116242774062687923207)
      ·
        refine ⟨77431674364161094031884811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51621116242774062687923207 77431674364161094031884811)
        ·
          refine ⟨116147511546241641047827217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77431674364161094031884811 116147511546241641047827217)
          ·
            refine ⟨87110633659681230785870413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116147511546241641047827217 87110633659681230785870413)
            ·
              refine ⟨32666487622380461544701405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87110633659681230785870413 32666487622380461544701405)
              ·
                refine ⟨12249932858392673079263027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32666487622380461544701405 12249932858392673079263027)
                ·
                  refine ⟨18374899287589009618894541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12249932858392673079263027 18374899287589009618894541)
                  ·
                    refine ⟨6890587232845878607085453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18374899287589009618894541 6890587232845878607085453)
                    ·
                      refine ⟨2583970212317204477657045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890587232845878607085453 2583970212317204477657045)
                      ·
                        rfl

theorem cell23_5032264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_5032264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032264 prefixEnd_5032264 := by exact prefixLift 5032264
  have htrace : WordTrace (prefixWord ++ tailWord_5032264) baseStart_5032264 baseEnd_5032264 := by
    simpa [prefixWord, tailWord_5032264, baseEnd_5032264] using wordTrace_append hprefix tailTrace_5032264
  have hstable : (prefixWord ++ tailWord_5032264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032264).length < 2 ^ (prefixWord ++ tailWord_5032264).sum := by decide
  have hdescent : baseEnd_5032264 < baseStart_5032264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032297 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_5032297 : Nat := 118140960795 + 5032297 * 2 ^ 59
def prefixEnd_5032297 : Nat := 4983230072969 + 3 ^ 40 * 5032297 * 2
def baseEnd_5032297 : Nat := 861329052392934282848131

theorem tailTrace_5032297 : CollatzResearch.WordTrace tailWord_5032297 prefixEnd_5032297 861329052392934282848131 := by
  unfold tailWord_5032297
  simp only [CollatzResearch.WordTrace]
  refine ⟨183542950249854891748567145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122361966833236594499044763 183542950249854891748567145)
  ·
    refine ⟨137657212687391168811425359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183542950249854891748567145 137657212687391168811425359)
    ·
      refine ⟨206485819031086753217138039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137657212687391168811425359 206485819031086753217138039)
      ·
        refine ⟨309728728546630129825707059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206485819031086753217138039 309728728546630129825707059)
        ·
          refine ⟨464593092819945194738560589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309728728546630129825707059 464593092819945194738560589)
          ·
            refine ⟨174222409807479448026960221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464593092819945194738560589 174222409807479448026960221)
            ·
              refine ⟨65333403677804793010110083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174222409807479448026960221 65333403677804793010110083)
              ·
                refine ⟨98000105516707189515165125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65333403677804793010110083 98000105516707189515165125)
                ·
                  refine ⟨18375019784382598034093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98000105516707189515165125 18375019784382598034093461)
                  ·
                    refine ⟨861329052392934282848131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18375019784382598034093461 861329052392934282848131)
                    ·
                      rfl

theorem cell23_5032297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_5032297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032297 prefixEnd_5032297 := by exact prefixLift 5032297
  have htrace : WordTrace (prefixWord ++ tailWord_5032297) baseStart_5032297 baseEnd_5032297 := by
    simpa [prefixWord, tailWord_5032297, baseEnd_5032297] using wordTrace_append hprefix tailTrace_5032297
  have hstable : (prefixWord ++ tailWord_5032297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032297).length < 2 ^ (prefixWord ++ tailWord_5032297).sum := by decide
  have hdescent : baseEnd_5032297 < baseStart_5032297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032298 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5032298 : Nat := 118140960795 + 5032298 * 2 ^ 59
def prefixEnd_5032298 : Nat := 4983230072969 + 3 ^ 40 * 5032298 * 2
def baseEnd_5032298 : Nat := 2583987670659457344631889

theorem tailTrace_5032298 : CollatzResearch.WordTrace tailWord_5032298 prefixEnd_5032298 2583987670659457344631889 := by
  unfold tailWord_5032298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45885746680712817229838387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122361991148567512612902365 45885746680712817229838387)
  ·
    refine ⟨68828620021069225844757581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45885746680712817229838387 68828620021069225844757581)
    ·
      refine ⟨25810732507900959691784093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68828620021069225844757581 25810732507900959691784093)
      ·
        refine ⟨9679024690462859884419035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25810732507900959691784093 9679024690462859884419035)
        ·
          refine ⟨14518537035694289826628553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679024690462859884419035 14518537035694289826628553)
          ·
            refine ⟨10888902776770717369971415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14518537035694289826628553 10888902776770717369971415)
            ·
              refine ⟨16333354165156076054957123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888902776770717369971415 16333354165156076054957123)
              ·
                refine ⟨24500031247734114082435685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16333354165156076054957123 24500031247734114082435685)
                ·
                  refine ⟨4593755858950146390456691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24500031247734114082435685 4593755858950146390456691)
                  ·
                    refine ⟨6890633788425219585685037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4593755858950146390456691 6890633788425219585685037)
                    ·
                      refine ⟨2583987670659457344631889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890633788425219585685037 2583987670659457344631889)
                      ·
                        rfl

theorem cell23_5032298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5032298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032298 prefixEnd_5032298 := by exact prefixLift 5032298
  have htrace : WordTrace (prefixWord ++ tailWord_5032298) baseStart_5032298 baseEnd_5032298 := by
    simpa [prefixWord, tailWord_5032298, baseEnd_5032298] using wordTrace_append hprefix tailTrace_5032298
  have hstable : (prefixWord ++ tailWord_5032298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032298).length < 2 ^ (prefixWord ++ tailWord_5032298).sum := by decide
  have hdescent : baseEnd_5032298 < baseStart_5032298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032307 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_5032307 : Nat := 118140960795 + 5032307 * 2 ^ 59
def prefixEnd_5032307 : Nat := 4983230072969 + 3 ^ 40 * 5032307 * 2
def baseEnd_5032307 : Nat := 2583992291985347809419347

theorem tailTrace_5032307 : CollatzResearch.WordTrace tailWord_5032307 prefixEnd_5032307 2583992291985347809419347 := by
  unfold tailWord_5032307
  simp only [CollatzResearch.WordTrace]
  refine ⟨183543314979818663456431175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122362209986545775637620783 183543314979818663456431175)
  ·
    refine ⟨275314972469727995184646763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183543314979818663456431175 275314972469727995184646763)
    ·
      refine ⟨412972458704591992776970145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275314972469727995184646763 412972458704591992776970145)
      ·
        refine ⟨309729344028443994582727609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412972458704591992776970145 309729344028443994582727609)
        ·
          refine ⟨232297008021332995937045707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309729344028443994582727609 232297008021332995937045707)
          ·
            refine ⟨348445512031999493905568561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232297008021332995937045707 348445512031999493905568561)
            ·
              refine ⟨261334134023999620429176421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348445512031999493905568561 261334134023999620429176421)
              ·
                refine ⟨49000150129499928830470579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261334134023999620429176421 49000150129499928830470579)
                ·
                  refine ⟨73500225194249893245705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49000150129499928830470579 73500225194249893245705869)
                  ·
                    refine ⟨27562584447843709967139701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73500225194249893245705869 27562584447843709967139701)
                    ·
                      refine ⟨2583992291985347809419347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27562584447843709967139701 2583992291985347809419347)
                      ·
                        rfl

theorem cell23_5032307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_5032307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032307 prefixEnd_5032307 := by exact prefixLift 5032307
  have htrace : WordTrace (prefixWord ++ tailWord_5032307) baseStart_5032307 baseEnd_5032307 := by
    simpa [prefixWord, tailWord_5032307, baseEnd_5032307] using wordTrace_append hprefix tailTrace_5032307
  have hstable : (prefixWord ++ tailWord_5032307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032307).length < 2 ^ (prefixWord ++ tailWord_5032307).sum := by decide
  have hdescent : baseEnd_5032307 < baseStart_5032307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032324 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5032324 : Nat := 118140960795 + 5032324 * 2 ^ 59
def prefixEnd_5032324 : Nat := 4983230072969 + 3 ^ 40 * 5032324 * 2
def baseEnd_5032324 : Nat := 2584001021156474242906769

theorem tailTrace_5032324 : CollatzResearch.WordTrace tailWord_5032324 prefixEnd_5032324 2584001021156474242906769 := by
  unfold tailWord_5032324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91771967510378537679900013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122362623347171383573200017 91771967510378537679900013)
  ·
    refine ⟨34414487816391951629962505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91771967510378537679900013 34414487816391951629962505)
    ·
      refine ⟨25810865862293963722471879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34414487816391951629962505 25810865862293963722471879)
      ·
        refine ⟨38716298793440945583707819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25810865862293963722471879 38716298793440945583707819)
        ·
          refine ⟨58074448190161418375561729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38716298793440945583707819 58074448190161418375561729)
          ·
            refine ⟨43555836142621063781671297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58074448190161418375561729 43555836142621063781671297)
            ·
              refine ⟨32666877106965797836253473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43555836142621063781671297 32666877106965797836253473)
              ·
                refine ⟨24500157830224348377190105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32666877106965797836253473 24500157830224348377190105)
                ·
                  refine ⟨18375118372668261282892579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24500157830224348377190105 18375118372668261282892579)
                  ·
                    refine ⟨27562677559002391924338869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18375118372668261282892579 27562677559002391924338869)
                    ·
                      refine ⟨2584001021156474242906769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27562677559002391924338869 2584001021156474242906769)
                      ·
                        rfl

theorem cell23_5032324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5032324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032324 prefixEnd_5032324 := by exact prefixLift 5032324
  have htrace : WordTrace (prefixWord ++ tailWord_5032324) baseStart_5032324 baseEnd_5032324 := by
    simpa [prefixWord, tailWord_5032324, baseEnd_5032324] using wordTrace_append hprefix tailTrace_5032324
  have hstable : (prefixWord ++ tailWord_5032324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032324).length < 2 ^ (prefixWord ++ tailWord_5032324).sum := by decide
  have hdescent : baseEnd_5032324 < baseStart_5032324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032337 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_5032337 : Nat := 118140960795 + 5032337 * 2 ^ 59
def prefixEnd_5032337 : Nat := 4983230072969 + 3 ^ 40 * 5032337 * 2
def baseEnd_5032337 : Nat := 2584007696404982692044209

theorem tailTrace_5032337 : CollatzResearch.WordTrace tailWord_5032337 prefixEnd_5032337 2584007696404982692044209 := by
  unfold tailWord_5032337
  simp only [CollatzResearch.WordTrace]
  refine ⟨183544409169709978580023265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122362939446473319053348843 183544409169709978580023265)
  ·
    refine ⟨137658306877282483935017449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183544409169709978580023265 137658306877282483935017449)
    ·
      refine ⟨103243730157961862951263087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137658306877282483935017449 103243730157961862951263087)
      ·
        refine ⟨154865595236942794426894631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103243730157961862951263087 154865595236942794426894631)
        ·
          refine ⟨232298392855414191640341947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154865595236942794426894631 232298392855414191640341947)
          ·
            refine ⟨348447589283121287460512921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232298392855414191640341947 348447589283121287460512921)
            ·
              refine ⟨261335691962340965595384691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348447589283121287460512921 261335691962340965595384691)
              ·
                refine ⟨392003537943511448393077037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261335691962340965595384691 392003537943511448393077037)
                ·
                  refine ⟨147001326728816793147403889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392003537943511448393077037 147001326728816793147403889)
                  ·
                    refine ⟨110250995046612594860552917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147001326728816793147403889 110250995046612594860552917)
                    ·
                      refine ⟨2584007696404982692044209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110250995046612594860552917 2584007696404982692044209)
                      ·
                        rfl

theorem cell23_5032337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_5032337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032337 prefixEnd_5032337 := by exact prefixLift 5032337
  have htrace : WordTrace (prefixWord ++ tailWord_5032337) baseStart_5032337 baseEnd_5032337 := by
    simpa [prefixWord, tailWord_5032337, baseEnd_5032337] using wordTrace_append hprefix tailTrace_5032337
  have hstable : (prefixWord ++ tailWord_5032337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032337).length < 2 ^ (prefixWord ++ tailWord_5032337).sum := by decide
  have hdescent : baseEnd_5032337 < baseStart_5032337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032354 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5032354 : Nat := 118140960795 + 5032354 * 2 ^ 59
def prefixEnd_5032354 : Nat := 4983230072969 + 3 ^ 40 * 5032354 * 2
def baseEnd_5032354 : Nat := 2584016425576109125531631

theorem tailTrace_5032354 : CollatzResearch.WordTrace tailWord_5032354 prefixEnd_5032354 2584016425576109125531631 := by
  unfold tailWord_5032354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45886257302662097620848029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122363352807098926988928077 45886257302662097620848029)
  ·
    refine ⟨17207346488498286607818011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45886257302662097620848029 17207346488498286607818011)
    ·
      refine ⟨25811019732747429911727017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207346488498286607818011 25811019732747429911727017)
      ·
        refine ⟨19358264799560572433795263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25811019732747429911727017 19358264799560572433795263)
        ·
          refine ⟨29037397199340858650692895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19358264799560572433795263 29037397199340858650692895)
          ·
            refine ⟨43556095799011287976039343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29037397199340858650692895 43556095799011287976039343)
            ·
              refine ⟨65334143698516931964059015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43556095799011287976039343 65334143698516931964059015)
              ·
                refine ⟨98001215547775397946088523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65334143698516931964059015 98001215547775397946088523)
                ·
                  refine ⟨147001823321663096919132785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98001215547775397946088523 147001823321663096919132785)
                  ·
                    refine ⟨110251367491247322689349589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147001823321663096919132785 110251367491247322689349589)
                    ·
                      refine ⟨2584016425576109125531631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110251367491247322689349589 2584016425576109125531631)
                      ·
                        rfl

theorem cell23_5032354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5032354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032354 prefixEnd_5032354 := by exact prefixLift 5032354
  have htrace : WordTrace (prefixWord ++ tailWord_5032354) baseStart_5032354 baseEnd_5032354 := by
    simpa [prefixWord, tailWord_5032354, baseEnd_5032354] using wordTrace_append hprefix tailTrace_5032354
  have hstable : (prefixWord ++ tailWord_5032354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032354).length < 2 ^ (prefixWord ++ tailWord_5032354).sum := by decide
  have hdescent : baseEnd_5032354 < baseStart_5032354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032391 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 2, 5]
def baseStart_5032391 : Nat := 118140960795 + 5032391 * 2 ^ 59
def prefixEnd_5032391 : Nat := 4983230072969 + 3 ^ 40 * 5032391 * 2
def baseEnd_5032391 : Nat := 861345141453441826922987

theorem tailTrace_5032391 : CollatzResearch.WordTrace tailWord_5032391 prefixEnd_5032391 861345141453441826922987 := by
  unfold tailWord_5032391
  simp only [CollatzResearch.WordTrace]
  refine ⟨183546378711514345802489027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122364252474342897201659351 183546378711514345802489027)
  ·
    refine ⟨275319568067271518703733541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183546378711514345802489027 275319568067271518703733541)
    ·
      refine ⟨51622419012613409756950039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275319568067271518703733541 51622419012613409756950039)
      ·
        refine ⟨77433628518920114635425059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51622419012613409756950039 77433628518920114635425059)
        ·
          refine ⟨116150442778380171953137589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77433628518920114635425059 116150442778380171953137589)
          ·
            refine ⟨10889104010473141120606649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116150442778380171953137589 10889104010473141120606649)
            ·
              refine ⟨8166828007854855840454987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889104010473141120606649 8166828007854855840454987)
              ·
                refine ⟨12250242011782283760682481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8166828007854855840454987 12250242011782283760682481)
                ·
                  refine ⟨9187681508836712820511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12250242011782283760682481 9187681508836712820511861)
                  ·
                    refine ⟨861345141453441826922987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9187681508836712820511861 861345141453441826922987)
                    ·
                      rfl

theorem cell23_5032391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_5032391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032391 prefixEnd_5032391 := by exact prefixLift 5032391
  have htrace : WordTrace (prefixWord ++ tailWord_5032391) baseStart_5032391 baseEnd_5032391 := by
    simpa [prefixWord, tailWord_5032391, baseEnd_5032391] using wordTrace_append hprefix tailTrace_5032391
  have hstable : (prefixWord ++ tailWord_5032391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032391).length < 2 ^ (prefixWord ++ tailWord_5032391).sum := by decide
  have hdescent : baseEnd_5032391 < baseStart_5032391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032438 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_5032438 : Nat := 118140960795 + 5032438 * 2 ^ 59
def prefixEnd_5032438 : Nat := 4983230072969 + 3 ^ 40 * 5032438 * 2
def baseEnd_5032438 : Nat := 861353185983695598960415

theorem tailTrace_5032438 : CollatzResearch.WordTrace tailWord_5032438 prefixEnd_5032438 861353185983695598960415 := by
  unfold tailWord_5032438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471755808896504551840623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122365395294896048552966645 11471755808896504551840623)
  ·
    refine ⟨17207633713344756827760935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11471755808896504551840623 17207633713344756827760935)
    ·
      refine ⟨25811450570017135241641403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207633713344756827760935 25811450570017135241641403)
      ·
        refine ⟨38717175855025702862462105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25811450570017135241641403 38717175855025702862462105)
        ·
          refine ⟨29037881891269277146846579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38717175855025702862462105 29037881891269277146846579)
          ·
            refine ⟨43556822836903915720269869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29037881891269277146846579 43556822836903915720269869)
            ·
              refine ⟨16333808563838968395101201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43556822836903915720269869 16333808563838968395101201)
              ·
                refine ⟨12250356422879226296325901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16333808563838968395101201 12250356422879226296325901)
                ·
                  refine ⟨4593883658579709861122213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12250356422879226296325901 4593883658579709861122213)
                  ·
                    refine ⟨861353185983695598960415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593883658579709861122213 861353185983695598960415)
                    ·
                      rfl

theorem cell23_5032438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_5032438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032438 prefixEnd_5032438 := by exact prefixLift 5032438
  have htrace : WordTrace (prefixWord ++ tailWord_5032438) baseStart_5032438 baseEnd_5032438 := by
    simpa [prefixWord, tailWord_5032438, baseEnd_5032438] using wordTrace_append hprefix tailTrace_5032438
  have hstable : (prefixWord ++ tailWord_5032438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032438).length < 2 ^ (prefixWord ++ tailWord_5032438).sum := by decide
  have hdescent : baseEnd_5032438 < baseStart_5032438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032468 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 8]
def baseStart_5032468 : Nat := 118140960795 + 5032468 * 2 ^ 59
def prefixEnd_5032468 : Nat := 4983230072969 + 3 ^ 40 * 5032468 * 2
def baseEnd_5032468 : Nat := 287119440263413519945123

theorem tailTrace_5032468 : CollatzResearch.WordTrace tailWord_5032468 prefixEnd_5032468 287119440263413519945123 := by
  unfold tailWord_5032468
  simp only [CollatzResearch.WordTrace]
  refine ⟨91774593566117693976521029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122366124754823591968694705 91774593566117693976521029)
  ·
    refine ⟨17207736293647067620597693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91774593566117693976521029 17207736293647067620597693)
    ·
      refine ⟨6452901110117650357724135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17207736293647067620597693 6452901110117650357724135)
      ·
        refine ⟨9679351665176475536586203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452901110117650357724135 9679351665176475536586203)
        ·
          refine ⟨14519027497764713304879305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679351665176475536586203 14519027497764713304879305)
          ·
            refine ⟨10889270623323534978659479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14519027497764713304879305 10889270623323534978659479)
            ·
              refine ⟨16333905934985302467989219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10889270623323534978659479 16333905934985302467989219)
              ·
                refine ⟨24500858902477953701983829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16333905934985302467989219 24500858902477953701983829)
                ·
                  refine ⟨287119440263413519945123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24500858902477953701983829 287119440263413519945123)
                  ·
                    rfl

theorem cell23_5032468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_5032468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032468 prefixEnd_5032468 := by exact prefixLift 5032468
  have htrace : WordTrace (prefixWord ++ tailWord_5032468) baseStart_5032468 baseEnd_5032468 := by
    simpa [prefixWord, tailWord_5032468, baseEnd_5032468] using wordTrace_append hprefix tailTrace_5032468
  have hstable : (prefixWord ++ tailWord_5032468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032468).length < 2 ^ (prefixWord ++ tailWord_5032468).sum := by decide
  have hdescent : baseEnd_5032468 < baseStart_5032468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032511 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 6, 4]
def baseStart_5032511 : Nat := 118140960795 + 5032511 * 2 ^ 59
def prefixEnd_5032511 : Nat := 4983230072969 + 3 ^ 40 * 5032511 * 2
def baseEnd_5032511 : Nat := 861365680679621670422803

theorem tailTrace_5032511 : CollatzResearch.WordTrace tailWord_5032511 prefixEnd_5032511 861365680679621670422803 := by
  unfold tailWord_5032511
  simp only [CollatzResearch.WordTrace]
  refine ⟨183550755471079606296857387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122367170314053070864571591 183550755471079606296857387)
  ·
    refine ⟨275326133206619409445286081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183550755471079606296857387 275326133206619409445286081)
    ·
      refine ⟨206494599904964557083964561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275326133206619409445286081 206494599904964557083964561)
      ·
        refine ⟨154870949928723417812973421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206494599904964557083964561 154870949928723417812973421)
        ·
          refine ⟨58076606223271281679865033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154870949928723417812973421 58076606223271281679865033)
          ·
            refine ⟨43557454667453461259898775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58076606223271281679865033 43557454667453461259898775)
            ·
              refine ⟨65336182001180191889848163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43557454667453461259898775 65336182001180191889848163)
              ·
                refine ⟨98004273001770287834772245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65336182001180191889848163 98004273001770287834772245)
                ·
                  refine ⟨4593950296957982242254949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98004273001770287834772245 4593950296957982242254949)
                  ·
                    refine ⟨861365680679621670422803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593950296957982242254949 861365680679621670422803)
                    ·
                      rfl

theorem cell23_5032511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_5032511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032511 prefixEnd_5032511 := by exact prefixLift 5032511
  have htrace : WordTrace (prefixWord ++ tailWord_5032511) baseStart_5032511 baseEnd_5032511 := by
    simpa [prefixWord, tailWord_5032511, baseEnd_5032511] using wordTrace_append hprefix tailTrace_5032511
  have hstable : (prefixWord ++ tailWord_5032511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032511).length < 2 ^ (prefixWord ++ tailWord_5032511).sum := by decide
  have hdescent : baseEnd_5032511 < baseStart_5032511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032521 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_5032521 : Nat := 118140960795 + 5032521 * 2 ^ 59
def prefixEnd_5032521 : Nat := 4983230072969 + 3 ^ 40 * 5032521 * 2
def baseEnd_5032521 : Nat := 2584102176845409972143363

theorem tailTrace_5032521 : CollatzResearch.WordTrace tailWord_5032521 prefixEnd_5032521 2584102176845409972143363 := by
  unfold tailWord_5032521
  simp only [CollatzResearch.WordTrace]
  refine ⟨183551120201043378004721417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122367413467362252003147611 183551120201043378004721417)
  ·
    refine ⟨137663340150782533503541063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183551120201043378004721417 137663340150782533503541063)
    ·
      refine ⟨206495010226173800255311595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137663340150782533503541063 206495010226173800255311595)
      ·
        refine ⟨309742515339260700382967393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206495010226173800255311595 309742515339260700382967393)
        ·
          refine ⟨232306886504445525287225545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309742515339260700382967393 232306886504445525287225545)
          ·
            refine ⟨174230164878334143965419159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232306886504445525287225545 174230164878334143965419159)
            ·
              refine ⟨261345247317501215948128739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174230164878334143965419159 261345247317501215948128739)
              ·
                refine ⟨392017870976251823922193109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261345247317501215948128739 392017870976251823922193109)
                ·
                  refine ⟨9187918851005902123176401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 392017870976251823922193109 9187918851005902123176401)
                  ·
                    refine ⟨6890939138254426592382301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9187918851005902123176401 6890939138254426592382301)
                    ·
                      refine ⟨2584102176845409972143363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6890939138254426592382301 2584102176845409972143363)
                      ·
                        rfl

theorem cell23_5032521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_5032521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032521 prefixEnd_5032521 := by exact prefixLift 5032521
  have htrace : WordTrace (prefixWord ++ tailWord_5032521) baseStart_5032521 baseEnd_5032521 := by
    simpa [prefixWord, tailWord_5032521, baseEnd_5032521] using wordTrace_append hprefix tailTrace_5032521
  have hstable : (prefixWord ++ tailWord_5032521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032521).length < 2 ^ (prefixWord ++ tailWord_5032521).sum := by decide
  have hdescent : baseEnd_5032521 < baseStart_5032521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032545 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_5032545 : Nat := 118140960795 + 5032545 * 2 ^ 59
def prefixEnd_5032545 : Nat := 4983230072969 + 3 ^ 40 * 5032545 * 2
def baseEnd_5032545 : Nat := 861371500127039292747751

theorem tailTrace_5032545 : CollatzResearch.WordTrace tailWord_5032545 prefixEnd_5032545 861371500127039292747751 := by
  unfold tailWord_5032545
  simp only [CollatzResearch.WordTrace]
  refine ⟨183551995552956430103595089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122367997035304286735730059 183551995552956430103595089)
  ·
    refine ⟨137663996664717322577696317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183551995552956430103595089 137663996664717322577696317)
    ·
      refine ⟨51623998749268995966636119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137663996664717322577696317 51623998749268995966636119)
      ·
        refine ⟨77435998123903493949954179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51623998749268995966636119 77435998123903493949954179)
        ·
          refine ⟨116153997185855240924931269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77435998123903493949954179 116153997185855240924931269)
          ·
            refine ⟨21778874472347857673424613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116153997185855240924931269 21778874472347857673424613)
            ·
              refine ⟨4083538963565223313767115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21778874472347857673424613 4083538963565223313767115)
              ·
                refine ⟨6125308445347834970650673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083538963565223313767115 6125308445347834970650673)
                ·
                  refine ⟨4593981334010876227988005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6125308445347834970650673 4593981334010876227988005)
                  ·
                    refine ⟨861371500127039292747751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4593981334010876227988005 861371500127039292747751)
                    ·
                      rfl

theorem cell23_5032545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_5032545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032545 prefixEnd_5032545 := by exact prefixLift 5032545
  have htrace : WordTrace (prefixWord ++ tailWord_5032545) baseStart_5032545 baseEnd_5032545 := by
    simpa [prefixWord, tailWord_5032545, baseEnd_5032545] using wordTrace_append hprefix tailTrace_5032545
  have hstable : (prefixWord ++ tailWord_5032545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032545).length < 2 ^ (prefixWord ++ tailWord_5032545).sum := by decide
  have hdescent : baseEnd_5032545 < baseStart_5032545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032552 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5032552 : Nat := 118140960795 + 5032552 * 2 ^ 59
def prefixEnd_5032552 : Nat := 4983230072969 + 3 ^ 40 * 5032552 * 2
def baseEnd_5032552 : Nat := 2584118094745699350855721

theorem tailTrace_5032552 : CollatzResearch.WordTrace tailWord_5032552 prefixEnd_5032552 2584118094745699350855721 := by
  unfold tailWord_5032552
  simp only [CollatzResearch.WordTrace]
  refine ⟨91776125431965535149549955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122368167242620713532733273 91776125431965535149549955)
  ·
    refine ⟨137664188147948302724324933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91776125431965535149549955 137664188147948302724324933)
    ·
      refine ⟨25812035277740306760810925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137664188147948302724324933 25812035277740306760810925)
      ·
        refine ⟨9679513229152615035304097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25812035277740306760810925 9679513229152615035304097)
        ·
          refine ⟨7259634921864461276478073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9679513229152615035304097 7259634921864461276478073)
          ·
            refine ⟨5444726191398345957358555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7259634921864461276478073 5444726191398345957358555)
            ·
              refine ⟨8167089287097518936037833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444726191398345957358555 8167089287097518936037833)
              ·
                refine ⟨6125316965323139202028375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8167089287097518936037833 6125316965323139202028375)
                ·
                  refine ⟨9187975447984708803042563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6125316965323139202028375 9187975447984708803042563)
                  ·
                    refine ⟨13781963171977063204563845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9187975447984708803042563 13781963171977063204563845)
                    ·
                      refine ⟨2584118094745699350855721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13781963171977063204563845 2584118094745699350855721)
                      ·
                        rfl

theorem cell23_5032552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5032552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032552 prefixEnd_5032552 := by exact prefixLift 5032552
  have htrace : WordTrace (prefixWord ++ tailWord_5032552) baseStart_5032552 baseEnd_5032552 := by
    simpa [prefixWord, tailWord_5032552, baseEnd_5032552] using wordTrace_append hprefix tailTrace_5032552
  have hstable : (prefixWord ++ tailWord_5032552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032552).length < 2 ^ (prefixWord ++ tailWord_5032552).sum := by decide
  have hdescent : baseEnd_5032552 < baseStart_5032552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032565 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5032565 : Nat := 118140960795 + 5032565 * 2 ^ 59
def prefixEnd_5032565 : Nat := 4983230072969 + 3 ^ 40 * 5032565 * 2
def baseEnd_5032565 : Nat := 2584124769994207799993161

theorem tailTrace_5032565 : CollatzResearch.WordTrace tailWord_5032565 prefixEnd_5032565 2584124769994207799993161 := by
  unfold tailWord_5032565
  simp only [CollatzResearch.WordTrace]
  refine ⟨183552725012883973519323149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122368483341922649012882099 183552725012883973519323149)
  ·
    refine ⟨68832271879831490069746181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183552725012883973519323149 68832271879831490069746181)
    ·
      refine ⟨12906050977468404388077409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68832271879831490069746181 12906050977468404388077409)
      ·
        refine ⟨9679538233101303291058057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12906050977468404388077409 9679538233101303291058057)
        ·
          refine ⟨7259653674825977468293543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9679538233101303291058057 7259653674825977468293543)
          ·
            refine ⟨10889480512238966202440315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259653674825977468293543 10889480512238966202440315)
            ·
              refine ⟨16334220768358449303660473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10889480512238966202440315 16334220768358449303660473)
              ·
                refine ⟨12250665576268836977745355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16334220768358449303660473 12250665576268836977745355)
                ·
                  refine ⟨18375998364403255466618033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12250665576268836977745355 18375998364403255466618033)
                  ·
                    refine ⟨13781998773302441599963525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18375998364403255466618033 13781998773302441599963525)
                    ·
                      refine ⟨2584124769994207799993161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13781998773302441599963525 2584124769994207799993161)
                      ·
                        rfl

theorem cell23_5032565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5032565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032565 prefixEnd_5032565 := by exact prefixLift 5032565
  have htrace : WordTrace (prefixWord ++ tailWord_5032565) baseStart_5032565 baseEnd_5032565 := by
    simpa [prefixWord, tailWord_5032565, baseEnd_5032565] using wordTrace_append hprefix tailTrace_5032565
  have hstable : (prefixWord ++ tailWord_5032565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032565).length < 2 ^ (prefixWord ++ tailWord_5032565).sum := by decide
  have hdescent : baseEnd_5032565 < baseStart_5032565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032601 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_5032601 : Nat := 118140960795 + 5032601 * 2 ^ 59
def prefixEnd_5032601 : Nat := 4983230072969 + 3 ^ 40 * 5032601 * 2
def baseEnd_5032601 : Nat := 861381085099256553047665

theorem tailTrace_5032601 : CollatzResearch.WordTrace tailWord_5032601 prefixEnd_5032601 861381085099256553047665 := by
  unfold tailWord_5032601
  simp only [CollatzResearch.WordTrace]
  refine ⟨183554038040753551667633657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122369358693835701111755771 183554038040753551667633657)
  ·
    refine ⟨137665528530565163750725243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183554038040753551667633657 137665528530565163750725243)
    ·
      refine ⟨206498292795847745626087865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137665528530565163750725243 206498292795847745626087865)
      ·
        refine ⟨154873719596885809219565899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206498292795847745626087865 154873719596885809219565899)
        ·
          refine ⟨232310579395328713829348849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154873719596885809219565899 232310579395328713829348849)
          ·
            refine ⟨174232934546496535372011637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232310579395328713829348849 174232934546496535372011637)
            ·
              refine ⟨16334337613734050191126091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174232934546496535372011637 16334337613734050191126091)
              ·
                refine ⟨24501506420601075286689137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16334337613734050191126091 24501506420601075286689137)
                ·
                  refine ⟨18376129815450806465016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24501506420601075286689137 18376129815450806465016853)
                  ·
                    refine ⟨861381085099256553047665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18376129815450806465016853 861381085099256553047665)
                    ·
                      rfl

theorem cell23_5032601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_5032601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032601 prefixEnd_5032601 := by exact prefixLift 5032601
  have htrace : WordTrace (prefixWord ++ tailWord_5032601) baseStart_5032601 baseEnd_5032601 := by
    simpa [prefixWord, tailWord_5032601, baseEnd_5032601] using wordTrace_append hprefix tailTrace_5032601
  have hstable : (prefixWord ++ tailWord_5032601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032601).length < 2 ^ (prefixWord ++ tailWord_5032601).sum := by decide
  have hdescent : baseEnd_5032601 < baseStart_5032601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032602 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5032602 : Nat := 118140960795 + 5032602 * 2 ^ 59
def prefixEnd_5032602 : Nat := 4983230072969 + 3 ^ 40 * 5032602 * 2
def baseEnd_5032602 : Nat := 2584143768778424155230491

theorem tailTrace_5032602 : CollatzResearch.WordTrace tailWord_5032602 prefixEnd_5032602 2584143768778424155230491 := by
  unfold tailWord_5032602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45888518628437482209605015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122369383009166619225613373 45888518628437482209605015)
  ·
    refine ⟨68832777942656223314407523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45888518628437482209605015 68832777942656223314407523)
    ·
      refine ⟨103249166913984334971611285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68832777942656223314407523 103249166913984334971611285)
      ·
        refine ⟨4839804699093015701794279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103249166913984334971611285 4839804699093015701794279)
        ·
          refine ⟨7259707048639523552691419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4839804699093015701794279 7259707048639523552691419)
          ·
            refine ⟨10889560572959285329037129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259707048639523552691419 10889560572959285329037129)
            ·
              refine ⟨8167170429719463996777847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889560572959285329037129 8167170429719463996777847)
              ·
                refine ⟨12250755644579195995166771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167170429719463996777847 12250755644579195995166771)
                ·
                  refine ⟨18376133466868793992750157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12250755644579195995166771 18376133466868793992750157)
                  ·
                    refine ⟨6891050050075797747281309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18376133466868793992750157 6891050050075797747281309)
                    ·
                      refine ⟨2584143768778424155230491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891050050075797747281309 2584143768778424155230491)
                      ·
                        rfl

theorem cell23_5032602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5032602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032602 prefixEnd_5032602 := by exact prefixLift 5032602
  have htrace : WordTrace (prefixWord ++ tailWord_5032602) baseStart_5032602 baseEnd_5032602 := by
    simpa [prefixWord, tailWord_5032602, baseEnd_5032602] using wordTrace_append hprefix tailTrace_5032602
  have hstable : (prefixWord ++ tailWord_5032602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032602).length < 2 ^ (prefixWord ++ tailWord_5032602).sum := by decide
  have hdescent : baseEnd_5032602 < baseStart_5032602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032611 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5032611 : Nat := 118140960795 + 5032611 * 2 ^ 59
def prefixEnd_5032611 : Nat := 4983230072969 + 3 ^ 40 * 5032611 * 2
def baseEnd_5032611 : Nat := 2584148390104314620017949

theorem tailTrace_5032611 : CollatzResearch.WordTrace tailWord_5032611 prefixEnd_5032611 2584148390104314620017949 := by
  unfold tailWord_5032611
  simp only [CollatzResearch.WordTrace]
  refine ⟨183554402770717323375497687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122369601847144882250331791 183554402770717323375497687)
  ·
    refine ⟨275331604156075985063246531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183554402770717323375497687 275331604156075985063246531)
    ·
      refine ⟨412997406234113977594869797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275331604156075985063246531 412997406234113977594869797)
      ·
        refine ⟨77437013668896370799038087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412997406234113977594869797 77437013668896370799038087)
        ·
          refine ⟨116155520503344556198557131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77437013668896370799038087 116155520503344556198557131)
          ·
            refine ⟨174233280755016834297835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116155520503344556198557131 174233280755016834297835697)
            ·
              refine ⟨130674960566262625723376773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174233280755016834297835697 130674960566262625723376773)
              ·
                refine ⟨24501555106174242323133145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130674960566262625723376773 24501555106174242323133145)
                ·
                  refine ⟨18376166329630681742349859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24501555106174242323133145 18376166329630681742349859)
                  ·
                    refine ⟨27564249494446022613524789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18376166329630681742349859 27564249494446022613524789)
                    ·
                      refine ⟨2584148390104314620017949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27564249494446022613524789 2584148390104314620017949)
                      ·
                        rfl

theorem cell23_5032611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5032611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032611 prefixEnd_5032611 := by exact prefixLift 5032611
  have htrace : WordTrace (prefixWord ++ tailWord_5032611) baseStart_5032611 baseEnd_5032611 := by
    simpa [prefixWord, tailWord_5032611, baseEnd_5032611] using wordTrace_append hprefix tailTrace_5032611
  have hstable : (prefixWord ++ tailWord_5032611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032611).length < 2 ^ (prefixWord ++ tailWord_5032611).sum := by decide
  have hdescent : baseEnd_5032611 < baseStart_5032611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032629 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5032629 : Nat := 118140960795 + 5032629 * 2 ^ 59
def prefixEnd_5032629 : Nat := 4983230072969 + 3 ^ 40 * 5032629 * 2
def baseEnd_5032629 : Nat := 2584157632756095549592867

theorem tailTrace_5032629 : CollatzResearch.WordTrace tailWord_5032629 prefixEnd_5032629 2584157632756095549592867 := by
  unfold tailWord_5032629
  simp only [CollatzResearch.WordTrace]
  refine ⟨183555059284652112449652941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122370039523101408299768627 183555059284652112449652941)
  ·
    refine ⟨68833147231744542168619853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183555059284652112449652941 68833147231744542168619853)
    ·
      refine ⟨25812430211904203313232445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68833147231744542168619853 25812430211904203313232445)
      ·
        refine ⟨9679661329464076242462167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25812430211904203313232445 9679661329464076242462167)
        ·
          refine ⟨14519491994196114363693251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679661329464076242462167 14519491994196114363693251)
          ·
            refine ⟨21779237991294171545539877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14519491994196114363693251 21779237991294171545539877)
            ·
              refine ⟨4083607123367657164788727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21779237991294171545539877 4083607123367657164788727)
              ·
                refine ⟨6125410685051485747183091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083607123367657164788727 6125410685051485747183091)
                ·
                  refine ⟨9188116027577228620774637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6125410685051485747183091 9188116027577228620774637)
                  ·
                    refine ⟨3445543510341460732790489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9188116027577228620774637 3445543510341460732790489)
                    ·
                      refine ⟨2584157632756095549592867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445543510341460732790489 2584157632756095549592867)
                      ·
                        rfl

theorem cell23_5032629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5032629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032629 prefixEnd_5032629 := by exact prefixLift 5032629
  have htrace : WordTrace (prefixWord ++ tailWord_5032629) baseStart_5032629 baseEnd_5032629 := by
    simpa [prefixWord, tailWord_5032629, baseEnd_5032629] using wordTrace_append hprefix tailTrace_5032629
  have hstable : (prefixWord ++ tailWord_5032629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032629).length < 2 ^ (prefixWord ++ tailWord_5032629).sum := by decide
  have hdescent : baseEnd_5032629 < baseStart_5032629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032638 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5032638 : Nat := 118140960795 + 5032638 * 2 ^ 59
def prefixEnd_5032638 : Nat := 4983230072969 + 3 ^ 40 * 5032638 * 2
def baseEnd_5032638 : Nat := 2584162254081986014380325

theorem tailTrace_5032638 : CollatzResearch.WordTrace tailWord_5032638 prefixEnd_5032638 2584162254081986014380325 := by
  unfold tailWord_5032638
  simp only [CollatzResearch.WordTrace]
  refine ⟨22944423442702438373341321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122370258361079671324487045 22944423442702438373341321)
  ·
    refine ⟨17208317582026828780005991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22944423442702438373341321 17208317582026828780005991)
    ·
      refine ⟨25812476373040243170008987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17208317582026828780005991 25812476373040243170008987)
      ·
        refine ⟨38718714559560364755013481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25812476373040243170008987 38718714559560364755013481)
        ·
          refine ⟨29039035919670273566260111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38718714559560364755013481 29039035919670273566260111)
          ·
            refine ⟨43558553879505410349390167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29039035919670273566260111 43558553879505410349390167)
            ·
              refine ⟨65337830819258115524085251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43558553879505410349390167 65337830819258115524085251)
              ·
                refine ⟨98006746228887173286127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65337830819258115524085251 98006746228887173286127877)
                ·
                  refine ⟨18376264917916344991148977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98006746228887173286127877 18376264917916344991148977)
                  ·
                    refine ⟨13782198688437258743361733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18376264917916344991148977 13782198688437258743361733)
                    ·
                      refine ⟨2584162254081986014380325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13782198688437258743361733 2584162254081986014380325)
                      ·
                        rfl

theorem cell23_5032638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5032638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032638 prefixEnd_5032638 := by exact prefixLift 5032638
  have htrace : WordTrace (prefixWord ++ tailWord_5032638) baseStart_5032638 baseEnd_5032638 := by
    simpa [prefixWord, tailWord_5032638, baseEnd_5032638] using wordTrace_append hprefix tailTrace_5032638
  have hstable : (prefixWord ++ tailWord_5032638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032638).length < 2 ^ (prefixWord ++ tailWord_5032638).sum := by decide
  have hdescent : baseEnd_5032638 < baseStart_5032638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032648 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 7]
def baseStart_5032648 : Nat := 118140960795 + 5032648 * 2 ^ 59
def prefixEnd_5032648 : Nat := 4983230072969 + 3 ^ 40 * 5032648 * 2
def baseEnd_5032648 : Nat := 287129709876503441695031

theorem tailTrace_5032648 : CollatzResearch.WordTrace tailWord_5032648 prefixEnd_5032648 287129709876503441695031 := by
  unfold tailWord_5032648
  simp only [CollatzResearch.WordTrace]
  refine ⟨91777876135791639347297299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122370501514388852463063065 91777876135791639347297299)
  ·
    refine ⟨137666814203687459020945949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91777876135791639347297299 137666814203687459020945949)
    ·
      refine ⟨51625055326382797132854731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137666814203687459020945949 51625055326382797132854731)
      ·
        refine ⟨77437582989574195699282097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51625055326382797132854731 77437582989574195699282097)
        ·
          refine ⟨58078187242180646774461573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77437582989574195699282097 58078187242180646774461573)
          ·
            refine ⟨10889660107908871270211545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58078187242180646774461573 10889660107908871270211545)
            ·
              refine ⟨8167245080931653452658659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889660107908871270211545 8167245080931653452658659)
              ·
                refine ⟨12250867621397480178987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167245080931653452658659 12250867621397480178987989)
                ·
                  refine ⟨287129709876503441695031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12250867621397480178987989 287129709876503441695031)
                  ·
                    rfl

theorem cell23_5032648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_5032648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032648 prefixEnd_5032648 := by exact prefixLift 5032648
  have htrace : WordTrace (prefixWord ++ tailWord_5032648) baseStart_5032648 baseEnd_5032648 := by
    simpa [prefixWord, tailWord_5032648, baseEnd_5032648] using wordTrace_append hprefix tailTrace_5032648
  have hstable : (prefixWord ++ tailWord_5032648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032648).length < 2 ^ (prefixWord ++ tailWord_5032648).sum := by decide
  have hdescent : baseEnd_5032648 < baseStart_5032648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032698 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_5032698 : Nat := 118140960795 + 5032698 * 2 ^ 59
def prefixEnd_5032698 : Nat := 4983230072969 + 3 ^ 40 * 5032698 * 2
def baseEnd_5032698 : Nat := 2584193062921255779630049

theorem tailTrace_5032698 : CollatzResearch.WordTrace tailWord_5032698 prefixEnd_5032698 2584193062921255779630049 := by
  unfold tailWord_5032698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45889393980350534308478687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122371717280934758155943165 45889393980350534308478687)
  ·
    refine ⟨68834090970525801462718031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45889393980350534308478687 68834090970525801462718031)
    ·
      refine ⟨103251136455788702194077047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68834090970525801462718031 103251136455788702194077047)
      ·
        refine ⟨154876704683683053291115571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103251136455788702194077047 154876704683683053291115571)
        ·
          refine ⟨232315057025524579936673357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154876704683683053291115571 232315057025524579936673357)
          ·
            refine ⟨87118146384571717476252509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232315057025524579936673357 87118146384571717476252509)
            ·
              refine ⟨32669304894214394053594691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87118146384571717476252509 32669304894214394053594691)
              ·
                refine ⟨49003957341321591080392037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32669304894214394053594691 49003957341321591080392037)
                ·
                  refine ⟨9188242001497798327573507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49003957341321591080392037 9188242001497798327573507)
                  ·
                    refine ⟨13782363002246697491360261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9188242001497798327573507 13782363002246697491360261)
                    ·
                      refine ⟨2584193062921255779630049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13782363002246697491360261 2584193062921255779630049)
                      ·
                        rfl

theorem cell23_5032698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_5032698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032698 prefixEnd_5032698 := by exact prefixLift 5032698
  have htrace : WordTrace (prefixWord ++ tailWord_5032698) baseStart_5032698 baseEnd_5032698 := by
    simpa [prefixWord, tailWord_5032698, baseEnd_5032698] using wordTrace_append hprefix tailTrace_5032698
  have hstable : (prefixWord ++ tailWord_5032698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032698).length < 2 ^ (prefixWord ++ tailWord_5032698).sum := by decide
  have hdescent : baseEnd_5032698 < baseStart_5032698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032731 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_5032731 : Nat := 118140960795 + 5032731 * 2 ^ 59
def prefixEnd_5032731 : Nat := 4983230072969 + 3 ^ 40 * 5032731 * 2
def baseEnd_5032731 : Nat := 2584210007782854150517397

theorem tailTrace_5032731 : CollatzResearch.WordTrace tailWord_5032731 prefixEnd_5032731 2584210007782854150517397 := by
  unfold tailWord_5032731
  simp only [CollatzResearch.WordTrace]
  refine ⟨183558779530282583869866047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122372519686855055913244031 183558779530282583869866047)
  ·
    refine ⟨275338169295423875804799071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183558779530282583869866047 275338169295423875804799071)
    ·
      refine ⟨413007253943135813707198607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275338169295423875804799071 413007253943135813707198607)
      ·
        refine ⟨619510880914703720560797911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413007253943135813707198607 619510880914703720560797911)
        ·
          refine ⟨929266321372055580841196867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619510880914703720560797911 929266321372055580841196867)
          ·
            refine ⟨1393899482058083371261795301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929266321372055580841196867 1393899482058083371261795301)
            ·
              refine ⟨261356152885890632111586619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1393899482058083371261795301 261356152885890632111586619)
              ·
                refine ⟨392034229328835948167379929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261356152885890632111586619 392034229328835948167379929)
                ·
                  refine ⟨294025671996626961125534947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392034229328835948167379929 294025671996626961125534947)
                  ·
                    refine ⟨441038507994940441688302421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294025671996626961125534947 441038507994940441688302421)
                    ·
                      refine ⟨2584210007782854150517397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 441038507994940441688302421 2584210007782854150517397)
                      ·
                        rfl

theorem cell23_5032731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_5032731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032731 prefixEnd_5032731 := by exact prefixLift 5032731
  have htrace : WordTrace (prefixWord ++ tailWord_5032731) baseStart_5032731 baseEnd_5032731 := by
    simpa [prefixWord, tailWord_5032731, baseEnd_5032731] using wordTrace_append hprefix tailTrace_5032731
  have hstable : (prefixWord ++ tailWord_5032731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032731).length < 2 ^ (prefixWord ++ tailWord_5032731).sum := by decide
  have hdescent : baseEnd_5032731 < baseStart_5032731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032735 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_5032735 : Nat := 118140960795 + 5032735 * 2 ^ 59
def prefixEnd_5032735 : Nat := 4983230072969 + 3 ^ 40 * 5032735 * 2
def baseEnd_5032735 : Nat := 2584212061705472134867379

theorem tailTrace_5032735 : CollatzResearch.WordTrace tailWord_5032735 prefixEnd_5032735 2584212061705472134867379 := by
  unfold tailWord_5032735
  simp only [CollatzResearch.WordTrace]
  refine ⟨183558925422268092553011659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122372616948178728368674439 183558925422268092553011659)
  ·
    refine ⟨275338388133402138829517489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183558925422268092553011659 275338388133402138829517489)
    ·
      refine ⟨206503791100051604122138117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275338388133402138829517489 206503791100051604122138117)
      ·
        refine ⟨38719460831259675772900897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206503791100051604122138117 38719460831259675772900897)
        ·
          refine ⟨29039595623444756829675673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38719460831259675772900897 29039595623444756829675673)
          ·
            refine ⟨21779696717583567622256755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29039595623444756829675673 21779696717583567622256755)
            ·
              refine ⟨32669545076375351433385133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21779696717583567622256755 32669545076375351433385133)
              ·
                refine ⟨12251079403640756787519425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32669545076375351433385133 12251079403640756787519425)
                ·
                  refine ⟨9188309552730567590639569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12251079403640756787519425 9188309552730567590639569)
                  ·
                    refine ⟨6891232164547925692979677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9188309552730567590639569 6891232164547925692979677)
                    ·
                      refine ⟨2584212061705472134867379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891232164547925692979677 2584212061705472134867379)
                      ·
                        rfl

theorem cell23_5032735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_5032735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032735 prefixEnd_5032735 := by exact prefixLift 5032735
  have htrace : WordTrace (prefixWord ++ tailWord_5032735) baseStart_5032735 baseEnd_5032735 := by
    simpa [prefixWord, tailWord_5032735, baseEnd_5032735] using wordTrace_append hprefix tailTrace_5032735
  have hstable : (prefixWord ++ tailWord_5032735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032735).length < 2 ^ (prefixWord ++ tailWord_5032735).sum := by decide
  have hdescent : baseEnd_5032735 < baseStart_5032735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032755 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 6]
def baseStart_5032755 : Nat := 118140960795 + 5032755 * 2 ^ 59
def prefixEnd_5032755 : Nat := 4983230072969 + 3 ^ 40 * 5032755 * 2
def baseEnd_5032755 : Nat := 287135814590951339624143

theorem tailTrace_5032755 : CollatzResearch.WordTrace tailWord_5032755 prefixEnd_5032755 287135814590951339624143 := by
  unfold tailWord_5032755
  simp only [CollatzResearch.WordTrace]
  refine ⟨183559654882195635968739719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122373103254797090645826479 183559654882195635968739719)
  ·
    refine ⟨275339482323293453953109579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183559654882195635968739719 275339482323293453953109579)
    ·
      refine ⟨413009223484940180929664369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275339482323293453953109579 413009223484940180929664369)
      ·
        refine ⟨309756917613705135697248277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413009223484940180929664369 309756917613705135697248277)
        ·
          refine ⟨14519855513142428235808513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309756917613705135697248277 14519855513142428235808513)
          ·
            refine ⟨10889891634856821176856385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14519855513142428235808513 10889891634856821176856385)
            ·
              refine ⟨8167418726142615882642289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889891634856821176856385 8167418726142615882642289)
              ·
                refine ⟨6125564044606961911981717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8167418726142615882642289 6125564044606961911981717)
                ·
                  refine ⟨287135814590951339624143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6125564044606961911981717 287135814590951339624143)
                  ·
                    rfl

theorem cell23_5032755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 6].length) (baseStart_5032755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032755 prefixEnd_5032755 := by exact prefixLift 5032755
  have htrace : WordTrace (prefixWord ++ tailWord_5032755) baseStart_5032755 baseEnd_5032755 := by
    simpa [prefixWord, tailWord_5032755, baseEnd_5032755] using wordTrace_append hprefix tailTrace_5032755
  have hstable : (prefixWord ++ tailWord_5032755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032755).length < 2 ^ (prefixWord ++ tailWord_5032755).sum := by decide
  have hdescent : baseEnd_5032755 < baseStart_5032755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032775 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_5032775 : Nat := 118140960795 + 5032775 * 2 ^ 59
def prefixEnd_5032775 : Nat := 4983230072969 + 3 ^ 40 * 5032775 * 2
def baseEnd_5032775 : Nat := 2584232600931651978367195

theorem tailTrace_5032775 : CollatzResearch.WordTrace tailWord_5032775 prefixEnd_5032775 2584232600931651978367195 := by
  unfold tailWord_5032775
  simp only [CollatzResearch.WordTrace]
  refine ⟨183560384342123179384467779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122373589561415452922978519 183560384342123179384467779)
  ·
    refine ⟨275340576513184769076701669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183560384342123179384467779 275340576513184769076701669)
    ·
      refine ⟨51626358096222144201881563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275340576513184769076701669 51626358096222144201881563)
      ·
        refine ⟨77439537144333216302822345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51626358096222144201881563 77439537144333216302822345)
        ·
          refine ⟨58079652858249912227116759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77439537144333216302822345 58079652858249912227116759)
          ·
            refine ⟨87119479287374868340675139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58079652858249912227116759 87119479287374868340675139)
            ·
              refine ⟨130679218931062302511012709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87119479287374868340675139 130679218931062302511012709)
              ·
                refine ⟨24502353549574181720814883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130679218931062302511012709 24502353549574181720814883)
                ·
                  refine ⟨36753530324361272581222325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24502353549574181720814883 36753530324361272581222325)
                  ·
                    refine ⟨3445643467908869304489593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36753530324361272581222325 3445643467908869304489593)
                    ·
                      refine ⟨2584232600931651978367195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445643467908869304489593 2584232600931651978367195)
                      ·
                        rfl

theorem cell23_5032775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_5032775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032775 prefixEnd_5032775 := by exact prefixLift 5032775
  have htrace : WordTrace (prefixWord ++ tailWord_5032775) baseStart_5032775 baseEnd_5032775 := by
    simpa [prefixWord, tailWord_5032775, baseEnd_5032775] using wordTrace_append hprefix tailTrace_5032775
  have hstable : (prefixWord ++ tailWord_5032775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032775).length < 2 ^ (prefixWord ++ tailWord_5032775).sum := by decide
  have hdescent : baseEnd_5032775 < baseStart_5032775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032799 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 1, 1, 3]
def baseStart_5032799 : Nat := 118140960795 + 5032799 * 2 ^ 59
def prefixEnd_5032799 : Nat := 4983230072969 + 3 ^ 40 * 5032799 * 2
def baseEnd_5032799 : Nat := 2584244924467359884467085

theorem tailTrace_5032799 : CollatzResearch.WordTrace tailWord_5032799 prefixEnd_5032799 2584244924467359884467085 := by
  unfold tailWord_5032799
  simp only [CollatzResearch.WordTrace]
  refine ⟨183561259694036231483341451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122374173129357487655560967 183561259694036231483341451)
  ·
    refine ⟨275341889541054347225012177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183561259694036231483341451 275341889541054347225012177)
    ·
      refine ⟨206506417155790760418759133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275341889541054347225012177 206506417155790760418759133)
      ·
        refine ⟨77439906433421535157034675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206506417155790760418759133 77439906433421535157034675)
        ·
          refine ⟨116159859650132302735552013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77439906433421535157034675 116159859650132302735552013)
          ·
            refine ⟨43559947368799613525832005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116159859650132302735552013 43559947368799613525832005)
            ·
              refine ⟨8167490131649927536093501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43559947368799613525832005 8167490131649927536093501)
              ·
                refine ⟨3062808799368722826035063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8167490131649927536093501 3062808799368722826035063)
                ·
                  refine ⟨4594213199053084239052595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062808799368722826035063 4594213199053084239052595)
                  ·
                    refine ⟨6891319798579626358578893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594213199053084239052595 6891319798579626358578893)
                    ·
                      refine ⟨2584244924467359884467085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891319798579626358578893 2584244924467359884467085)
                      ·
                        rfl

theorem cell23_5032799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_5032799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032799 prefixEnd_5032799 := by exact prefixLift 5032799
  have htrace : WordTrace (prefixWord ++ tailWord_5032799) baseStart_5032799 baseEnd_5032799 := by
    simpa [prefixWord, tailWord_5032799, baseEnd_5032799] using wordTrace_append hprefix tailTrace_5032799
  have hstable : (prefixWord ++ tailWord_5032799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032799).length < 2 ^ (prefixWord ++ tailWord_5032799).sum := by decide
  have hdescent : baseEnd_5032799 < baseStart_5032799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032825 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_5032825 : Nat := 118140960795 + 5032825 * 2 ^ 59
def prefixEnd_5032825 : Nat := 4983230072969 + 3 ^ 40 * 5032825 * 2
def baseEnd_5032825 : Nat := 2584258274964376782741965

theorem tailTrace_5032825 : CollatzResearch.WordTrace tailWord_5032825 prefixEnd_5032825 2584258274964376782741965 := by
  unfold tailWord_5032825
  simp only [CollatzResearch.WordTrace]
  refine ⟨183562207991942037923787929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122374805327961358615858619 183562207991942037923787929)
  ·
    refine ⟨137671655993956528442840947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183562207991942037923787929 137671655993956528442840947)
    ·
      refine ⟨206507483990934792664261421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137671655993956528442840947 206507483990934792664261421)
      ·
        refine ⟨77440306496600547249098033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206507483990934792664261421 77440306496600547249098033)
        ·
          refine ⟨58080229872450410436823525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77440306496600547249098033 58080229872450410436823525)
          ·
            refine ⟨10890043101084451956904411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58080229872450410436823525 10890043101084451956904411)
            ·
              refine ⟨16335064651626677935356617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10890043101084451956904411 16335064651626677935356617)
              ·
                refine ⟨12251298488720008451517463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16335064651626677935356617 12251298488720008451517463)
                ·
                  refine ⟨18376947733080012677276195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12251298488720008451517463 18376947733080012677276195)
                  ·
                    refine ⟨27565421599620019015914293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18376947733080012677276195 27565421599620019015914293)
                    ·
                      refine ⟨2584258274964376782741965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27565421599620019015914293 2584258274964376782741965)
                      ·
                        rfl

theorem cell23_5032825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_5032825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032825 prefixEnd_5032825 := by exact prefixLift 5032825
  have htrace : WordTrace (prefixWord ++ tailWord_5032825) baseStart_5032825 baseEnd_5032825 := by
    simpa [prefixWord, tailWord_5032825, baseEnd_5032825] using wordTrace_append hprefix tailTrace_5032825
  have hstable : (prefixWord ++ tailWord_5032825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032825).length < 2 ^ (prefixWord ++ tailWord_5032825).sum := by decide
  have hdescent : baseEnd_5032825 < baseStart_5032825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032839 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_5032839 : Nat := 118140960795 + 5032839 * 2 ^ 59
def prefixEnd_5032839 : Nat := 4983230072969 + 3 ^ 40 * 5032839 * 2
def baseEnd_5032839 : Nat := 2584265463693539727966901

theorem tailTrace_5032839 : CollatzResearch.WordTrace tailWord_5032839 prefixEnd_5032839 2584265463693539727966901 := by
  unfold tailWord_5032839
  simp only [CollatzResearch.WordTrace]
  refine ⟨183562718613891318314797571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122375145742594212209865047 183562718613891318314797571)
  ·
    refine ⟨275344077920836977472196357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183562718613891318314797571 275344077920836977472196357)
    ·
      refine ⟨51627014610156933276036817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275344077920836977472196357 51627014610156933276036817)
      ·
        refine ⟨38720260957617699957027613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51627014610156933276036817 38720260957617699957027613)
        ·
          refine ⟨14520097859106637483885355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38720260957617699957027613 14520097859106637483885355)
          ·
            refine ⟨21780146788659956225828033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14520097859106637483885355 21780146788659956225828033)
            ·
              refine ⟨16335110091494967169371025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21780146788659956225828033 16335110091494967169371025)
              ·
                refine ⟨12251332568621225377028269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16335110091494967169371025 12251332568621225377028269)
                ·
                  refine ⟨4594249713232959516385601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12251332568621225377028269 4594249713232959516385601)
                  ·
                    refine ⟨3445687284924719637289201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4594249713232959516385601 3445687284924719637289201)
                    ·
                      refine ⟨2584265463693539727966901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445687284924719637289201 2584265463693539727966901)
                      ·
                        rfl

theorem cell23_5032839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_5032839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032839 prefixEnd_5032839 := by exact prefixLift 5032839
  have htrace : WordTrace (prefixWord ++ tailWord_5032839) baseStart_5032839 baseEnd_5032839 := by
    simpa [prefixWord, tailWord_5032839, baseEnd_5032839] using wordTrace_append hprefix tailTrace_5032839
  have hstable : (prefixWord ++ tailWord_5032839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032839).length < 2 ^ (prefixWord ++ tailWord_5032839).sum := by decide
  have hdescent : baseEnd_5032839 < baseStart_5032839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032850 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5032850 : Nat := 118140960795 + 5032850 * 2 ^ 59
def prefixEnd_5032850 : Nat := 4983230072969 + 3 ^ 40 * 5032850 * 2
def baseEnd_5032850 : Nat := 2584271111980739184929351

theorem tailTrace_5032850 : CollatzResearch.WordTrace tailWord_5032850 prefixEnd_5032850 2584271111980739184929351 := by
  unfold tailWord_5032850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45890779954212866798362001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122375413211234311462298669 45890779954212866798362001)
  ·
    refine ⟨34418084965659650098771501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45890779954212866798362001 34418084965659650098771501)
    ·
      refine ⟨12906781862122368787039313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34418084965659650098771501 12906781862122368787039313)
      ·
        refine ⟨9680086396591776590279485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12906781862122368787039313 9680086396591776590279485)
        ·
          refine ⟨3630032398721916221354807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9680086396591776590279485 3630032398721916221354807)
          ·
            refine ⟨5445048598082874332032211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630032398721916221354807 5445048598082874332032211)
            ·
              refine ⟨8167572897124311498048317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445048598082874332032211 8167572897124311498048317)
              ·
                refine ⟨3062839836421616811768119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8167572897124311498048317 3062839836421616811768119)
                ·
                  refine ⟨4594259754632425217652179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062839836421616811768119 4594259754632425217652179)
                  ·
                    refine ⟨6891389631948637826478269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594259754632425217652179 6891389631948637826478269)
                    ·
                      refine ⟨2584271111980739184929351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891389631948637826478269 2584271111980739184929351)
                      ·
                        rfl

theorem cell23_5032850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5032850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032850 prefixEnd_5032850 := by exact prefixLift 5032850
  have htrace : WordTrace (prefixWord ++ tailWord_5032850) baseStart_5032850 baseEnd_5032850 := by
    simpa [prefixWord, tailWord_5032850, baseEnd_5032850] using wordTrace_append hprefix tailTrace_5032850
  have hstable : (prefixWord ++ tailWord_5032850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032850).length < 2 ^ (prefixWord ++ tailWord_5032850).sum := by decide
  have hdescent : baseEnd_5032850 < baseStart_5032850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032855 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_5032855 : Nat := 118140960795 + 5032855 * 2 ^ 59
def prefixEnd_5032855 : Nat := 4983230072969 + 3 ^ 40 * 5032855 * 2
def baseEnd_5032855 : Nat := 2584273679384011665366827

theorem tailTrace_5032855 : CollatzResearch.WordTrace tailWord_5032855 prefixEnd_5032855 2584273679384011665366827 := by
  unfold tailWord_5032855
  simp only [CollatzResearch.WordTrace]
  refine ⟨183563302181833353047380019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122375534787888902031586679 183563302181833353047380019)
  ·
    refine ⟨275344953272750029571070029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183563302181833353047380019 275344953272750029571070029)
    ·
      refine ⟨103254357477281261089151261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275344953272750029571070029 103254357477281261089151261)
      ·
        refine ⟨38720384053980472908431723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103254357477281261089151261 38720384053980472908431723)
        ·
          refine ⟨58080576080970709362647585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38720384053980472908431723 58080576080970709362647585)
          ·
            refine ⟨43560432060728032021985689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58080576080970709362647585 43560432060728032021985689)
            ·
              refine ⟨32670324045546024016489267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43560432060728032021985689 32670324045546024016489267)
              ·
                refine ⟨49005486068319036024733901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32670324045546024016489267 49005486068319036024733901)
                ·
                  refine ⟨18377057275619638509275213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49005486068319036024733901 18377057275619638509275213)
                  ·
                    refine ⟨6891396478357364440978205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18377057275619638509275213 6891396478357364440978205)
                    ·
                      refine ⟨2584273679384011665366827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891396478357364440978205 2584273679384011665366827)
                      ·
                        rfl

theorem cell23_5032855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_5032855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032855 prefixEnd_5032855 := by exact prefixLift 5032855
  have htrace : WordTrace (prefixWord ++ tailWord_5032855) baseStart_5032855 baseEnd_5032855 := by
    simpa [prefixWord, tailWord_5032855, baseEnd_5032855] using wordTrace_append hprefix tailTrace_5032855
  have hstable : (prefixWord ++ tailWord_5032855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032855).length < 2 ^ (prefixWord ++ tailWord_5032855).sum := by decide
  have hdescent : baseEnd_5032855 < baseStart_5032855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032889 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5032889 : Nat := 118140960795 + 5032889 * 2 ^ 59
def prefixEnd_5032889 : Nat := 4983230072969 + 3 ^ 40 * 5032889 * 2
def baseEnd_5032889 : Nat := 2584291137726264532341671

theorem tailTrace_5032889 : CollatzResearch.WordTrace tailWord_5032889 prefixEnd_5032889 2584291137726264532341671 := by
  unfold tailWord_5032889
  simp only [CollatzResearch.WordTrace]
  refine ⟨183564542263710176854117721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122376361509140117902745147 183564542263710176854117721)
  ·
    refine ⟨137673406697782632640588291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183564542263710176854117721 137673406697782632640588291)
    ·
      refine ⟨206510110046673948960882437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137673406697782632640588291 206510110046673948960882437)
      ·
        refine ⟨38720645633751365430165457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206510110046673948960882437 38720645633751365430165457)
        ·
          refine ⟨29040484225313524072624093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38720645633751365430165457 29040484225313524072624093)
          ·
            refine ⟨10890181584492571527234035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29040484225313524072624093 10890181584492571527234035)
            ·
              refine ⟨16335272376738857290851053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10890181584492571527234035 16335272376738857290851053)
              ·
                refine ⟨6125727141277071484069145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16335272376738857290851053 6125727141277071484069145)
                ·
                  refine ⟨4594295355957803613051859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6125727141277071484069145 4594295355957803613051859)
                  ·
                    refine ⟨6891443033936705419577789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594295355957803613051859 6891443033936705419577789)
                    ·
                      refine ⟨2584291137726264532341671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891443033936705419577789 2584291137726264532341671)
                      ·
                        rfl

theorem cell23_5032889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5032889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032889 prefixEnd_5032889 := by exact prefixLift 5032889
  have htrace : WordTrace (prefixWord ++ tailWord_5032889) baseStart_5032889 baseEnd_5032889 := by
    simpa [prefixWord, tailWord_5032889, baseEnd_5032889] using wordTrace_append hprefix tailTrace_5032889
  have hstable : (prefixWord ++ tailWord_5032889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032889).length < 2 ^ (prefixWord ++ tailWord_5032889).sum := by decide
  have hdescent : baseEnd_5032889 < baseStart_5032889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5032965 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_5032965 : Nat := 118140960795 + 5032965 * 2 ^ 59
def prefixEnd_5032965 : Nat := 4983230072969 + 3 ^ 40 * 5032965 * 2
def baseEnd_5032965 : Nat := 861443387418668744997107

theorem tailTrace_5032965 : CollatzResearch.WordTrace tailWord_5032965 prefixEnd_5032965 861443387418668744997107 := by
  unfold tailWord_5032965
  simp only [CollatzResearch.WordTrace]
  refine ⟨183567314211434841833884349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122378209474289894555922899 183567314211434841833884349)
  ·
    refine ⟨68837742829288065687706631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183567314211434841833884349 68837742829288065687706631)
    ·
      refine ⟨103256614243932098531559947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68837742829288065687706631 103256614243932098531559947)
      ·
        refine ⟨154884921365898147797339921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103256614243932098531559947 154884921365898147797339921)
        ·
          refine ⟨116163691024423610848004941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154884921365898147797339921 116163691024423610848004941)
          ·
            refine ⟨43561384134158854068001853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116163691024423610848004941 43561384134158854068001853)
            ·
              refine ⟨16335519050309570275500695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43561384134158854068001853 16335519050309570275500695)
              ·
                refine ⟨24503278575464355413251043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16335519050309570275500695 24503278575464355413251043)
                ·
                  refine ⟨36754917863196533119876565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24503278575464355413251043 36754917863196533119876565)
                  ·
                    refine ⟨861443387418668744997107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36754917863196533119876565 861443387418668744997107)
                    ·
                      rfl

theorem cell23_5032965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_5032965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5032965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5032965 prefixEnd_5032965 := by exact prefixLift 5032965
  have htrace : WordTrace (prefixWord ++ tailWord_5032965) baseStart_5032965 baseEnd_5032965 := by
    simpa [prefixWord, tailWord_5032965, baseEnd_5032965] using wordTrace_append hprefix tailTrace_5032965
  have hstable : (prefixWord ++ tailWord_5032965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5032965).length < 2 ^ (prefixWord ++ tailWord_5032965).sum := by decide
  have hdescent : baseEnd_5032965 < baseStart_5032965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5032965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033015 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_5033015 : Nat := 118140960795 + 5033015 * 2 ^ 59
def prefixEnd_5033015 : Nat := 4983230072969 + 3 ^ 40 * 5033015 * 2
def baseEnd_5033015 : Nat := 2584355836288731039366091

theorem tailTrace_5033015 : CollatzResearch.WordTrace tailWord_5033015 prefixEnd_5033015 2584355836288731039366091 := by
  unfold tailWord_5033015
  simp only [CollatzResearch.WordTrace]
  refine ⟨183569137861253700373204499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122379425240835800248802999 183569137861253700373204499)
  ·
    refine ⟨275353706791880550559806749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183569137861253700373204499 275353706791880550559806749)
    ·
      refine ⟨103257640046955206459927531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275353706791880550559806749 103257640046955206459927531)
      ·
        refine ⟨154886460070432809689891297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103257640046955206459927531 154886460070432809689891297)
        ·
          refine ⟨116164845052824607267418473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154886460070432809689891297 116164845052824607267418473)
          ·
            refine ⟨87123633789618455450563855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116164845052824607267418473 87123633789618455450563855)
            ·
              refine ⟨130685450684427683175845783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87123633789618455450563855 130685450684427683175845783)
              ·
                refine ⟨196028176026641524763768675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130685450684427683175845783 196028176026641524763768675)
                ·
                  refine ⟨294042264039962287145653013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196028176026641524763768675 294042264039962287145653013)
                  ·
                    refine ⟨13783231126873232209952485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 294042264039962287145653013 13783231126873232209952485)
                    ·
                      refine ⟨2584355836288731039366091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13783231126873232209952485 2584355836288731039366091)
                      ·
                        rfl

theorem cell23_5033015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_5033015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033015 prefixEnd_5033015 := by exact prefixLift 5033015
  have htrace : WordTrace (prefixWord ++ tailWord_5033015) baseStart_5033015 baseEnd_5033015 := by
    simpa [prefixWord, tailWord_5033015, baseEnd_5033015] using wordTrace_append hprefix tailTrace_5033015
  have hstable : (prefixWord ++ tailWord_5033015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033015).length < 2 ^ (prefixWord ++ tailWord_5033015).sum := by decide
  have hdescent : baseEnd_5033015 < baseStart_5033015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033042 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_5033042 : Nat := 118140960795 + 5033042 * 2 ^ 59
def prefixEnd_5033042 : Nat := 4983230072969 + 3 ^ 40 * 5033042 * 2
def baseEnd_5033042 : Nat := 287152188918489159303163

theorem tailTrace_5033042 : CollatzResearch.WordTrace tailWord_5033042 prefixEnd_5033042 287152188918489159303163 := by
  unfold tailWord_5033042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45892530658038970996109345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122380081754770589322958253 45892530658038970996109345)
  ·
    refine ⟨34419397993529228247082009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45892530658038970996109345 34419397993529228247082009)
    ·
      refine ⟨25814548495146921185311507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34419397993529228247082009 25814548495146921185311507)
      ·
        refine ⟨38721822742720381777967261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25814548495146921185311507 38721822742720381777967261)
        ·
          refine ⟨14520683528520143166737723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38721822742720381777967261 14520683528520143166737723)
          ·
            refine ⟨21781025292780214750106585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14520683528520143166737723 21781025292780214750106585)
            ·
              refine ⟨16335768969585161062579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21781025292780214750106585 16335768969585161062579939)
              ·
                refine ⟨24503653454377741593869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16335768969585161062579939 24503653454377741593869909)
                ·
                  refine ⟨287152188918489159303163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24503653454377741593869909 287152188918489159303163)
                  ·
                    rfl

theorem cell23_5033042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_5033042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033042 prefixEnd_5033042 := by exact prefixLift 5033042
  have htrace : WordTrace (prefixWord ++ tailWord_5033042) baseStart_5033042 baseEnd_5033042 := by
    simpa [prefixWord, tailWord_5033042, baseEnd_5033042] using wordTrace_append hprefix tailTrace_5033042
  have hstable : (prefixWord ++ tailWord_5033042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033042).length < 2 ^ (prefixWord ++ tailWord_5033042).sum := by decide
  have hdescent : baseEnd_5033042 < baseStart_5033042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033072 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_5033072 : Nat := 118140960795 + 5033072 * 2 ^ 59
def prefixEnd_5033072 : Nat := 4983230072969 + 3 ^ 40 * 5033072 * 2
def baseEnd_5033072 : Nat := 861461701562012438784443

theorem tailTrace_5033072 : CollatzResearch.WordTrace tailWord_5033072 prefixEnd_5033072 861461701562012438784443 := by
  unfold tailWord_5033072
  simp only [CollatzResearch.WordTrace]
  refine ⟨91785608411023599554014735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122380811214698132738686313 91785608411023599554014735)
  ·
    refine ⟨137678412616535399331022103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91785608411023599554014735 137678412616535399331022103)
    ·
      refine ⟨206517618924803098996533155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137678412616535399331022103 206517618924803098996533155)
      ·
        refine ⟨309776428387204648494799733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206517618924803098996533155 309776428387204648494799733)
        ·
          refine ⟨29041540161300435796387475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309776428387204648494799733 29041540161300435796387475)
          ·
            refine ⟨43562310241950653694581213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29041540161300435796387475 43562310241950653694581213)
            ·
              refine ⟨16335866340731495135467955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43562310241950653694581213 16335866340731495135467955)
              ·
                refine ⟨24503799511097242703201933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16335866340731495135467955 24503799511097242703201933)
                ·
                  refine ⟨9188924816661466013700725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24503799511097242703201933 9188924816661466013700725)
                  ·
                    refine ⟨861461701562012438784443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9188924816661466013700725 861461701562012438784443)
                    ·
                      rfl

theorem cell23_5033072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_5033072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033072 prefixEnd_5033072 := by exact prefixLift 5033072
  have htrace : WordTrace (prefixWord ++ tailWord_5033072) baseStart_5033072 baseEnd_5033072 := by
    simpa [prefixWord, tailWord_5033072, baseEnd_5033072] using wordTrace_append hprefix tailTrace_5033072
  have hstable : (prefixWord ++ tailWord_5033072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033072).length < 2 ^ (prefixWord ++ tailWord_5033072).sum := by decide
  have hdescent : baseEnd_5033072 < baseStart_5033072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033130 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5033130 : Nat := 118140960795 + 5033130 * 2 ^ 59
def prefixEnd_5033130 : Nat := 4983230072969 + 3 ^ 40 * 5033130 * 2
def baseEnd_5033130 : Nat := 2584414886563998089428063

theorem tailTrace_5033130 : CollatzResearch.WordTrace tailWord_5033130 prefixEnd_5033130 2584414886563998089428063 := by
  unfold tailWord_5033130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45893333063959268753410211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122382221503891383342427229 45893333063959268753410211)
  ·
    refine ⟨68839999595938903130115317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45893333063959268753410211 68839999595938903130115317)
    ·
      refine ⟨6453749962119272168448311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68839999595938903130115317 6453749962119272168448311)
      ·
        refine ⟨9680624943178908252672467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453749962119272168448311 9680624943178908252672467)
        ·
          refine ⟨14520937414768362379008701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680624943178908252672467 14520937414768362379008701)
          ·
            refine ⟨5445351530538135892128263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14520937414768362379008701 5445351530538135892128263)
            ·
              refine ⟨8168027295807203838192395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445351530538135892128263 8168027295807203838192395)
              ·
                refine ⟨12252040943710805757288593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168027295807203838192395 12252040943710805757288593)
                ·
                  refine ⟨9189030707783104317966445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12252040943710805757288593 9189030707783104317966445)
                  ·
                    refine ⟨3445886515418664119237417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9189030707783104317966445 3445886515418664119237417)
                    ·
                      refine ⟨2584414886563998089428063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445886515418664119237417 2584414886563998089428063)
                      ·
                        rfl

theorem cell23_5033130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5033130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033130 prefixEnd_5033130 := by exact prefixLift 5033130
  have htrace : WordTrace (prefixWord ++ tailWord_5033130) baseStart_5033130 baseEnd_5033130 := by
    simpa [prefixWord, tailWord_5033130, baseEnd_5033130] using wordTrace_append hprefix tailTrace_5033130
  have hstable : (prefixWord ++ tailWord_5033130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033130).length < 2 ^ (prefixWord ++ tailWord_5033130).sum := by decide
  have hdescent : baseEnd_5033130 < baseStart_5033130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033153 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5033153 : Nat := 118140960795 + 5033153 * 2 ^ 59
def prefixEnd_5033153 : Nat := 4983230072969 + 3 ^ 40 * 5033153 * 2
def baseEnd_5033153 : Nat := 861475565539683833146819

theorem tailTrace_5033153 : CollatzResearch.WordTrace tailWord_5033153 prefixEnd_5033153 861475565539683833146819 := by
  unfold tailWord_5033153
  simp only [CollatzResearch.WordTrace]
  refine ⟨183574171134753749941728113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122382780756502499961152075 183574171134753749941728113)
  ·
    refine ⟨137680628351065312456296085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183574171134753749941728113 137680628351065312456296085)
    ·
      refine ⟨6453779453956186521388879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137680628351065312456296085 6453779453956186521388879)
      ·
        refine ⟨9680669180934279782083319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6453779453956186521388879 9680669180934279782083319)
        ·
          refine ⟨14521003771401419673124979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9680669180934279782083319 14521003771401419673124979)
          ·
            refine ⟨21781505657102129509687469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14521003771401419673124979 21781505657102129509687469)
            ·
              refine ⟨8168064621413298566132801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21781505657102129509687469 8168064621413298566132801)
              ·
                refine ⟨6126048466059973924599601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8168064621413298566132801 6126048466059973924599601)
                ·
                  refine ⟨4594536349544980443449701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126048466059973924599601 4594536349544980443449701)
                  ·
                    refine ⟨861475565539683833146819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4594536349544980443449701 861475565539683833146819)
                    ·
                      rfl

theorem cell23_5033153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5033153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033153 prefixEnd_5033153 := by exact prefixLift 5033153
  have htrace : WordTrace (prefixWord ++ tailWord_5033153) baseStart_5033153 baseEnd_5033153 := by
    simpa [prefixWord, tailWord_5033153, baseEnd_5033153] using wordTrace_append hprefix tailTrace_5033153
  have hstable : (prefixWord ++ tailWord_5033153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033153).length < 2 ^ (prefixWord ++ tailWord_5033153).sum := by decide
  have hdescent : baseEnd_5033153 < baseStart_5033153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033233 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_5033233 : Nat := 118140960795 + 5033233 * 2 ^ 59
def prefixEnd_5033233 : Nat := 4983230072969 + 3 ^ 40 * 5033233 * 2
def baseEnd_5033233 : Nat := 2584467775071411186440089

theorem tailTrace_5033233 : CollatzResearch.WordTrace tailWord_5033233 prefixEnd_5033233 2584467775071411186440089 := by
  unfold tailWord_5033233
  simp only [CollatzResearch.WordTrace]
  refine ⟨183577088974463923604640353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122384725982975949069760235 183577088974463923604640353)
  ·
    refine ⟨137682816730847942703480265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183577088974463923604640353 137682816730847942703480265)
    ·
      refine ⟨103262112548135957027610199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137682816730847942703480265 103262112548135957027610199)
      ·
        refine ⟨154893168822203935541415299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103262112548135957027610199 154893168822203935541415299)
        ·
          refine ⟨232339753233305903312122949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154893168822203935541415299 232339753233305903312122949)
          ·
            refine ⟨43563703731244856871023053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232339753233305903312122949 43563703731244856871023053)
            ·
              refine ⟨16336388899216821326633645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43563703731244856871023053 16336388899216821326633645)
              ·
                refine ⟨6126145837206307997487617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16336388899216821326633645 6126145837206307997487617)
                ·
                  refine ⟨4594609377904730998115713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126145837206307997487617 4594609377904730998115713)
                  ·
                    refine ⟨3445957033428548248586785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4594609377904730998115713 3445957033428548248586785)
                    ·
                      refine ⟨2584467775071411186440089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445957033428548248586785 2584467775071411186440089)
                      ·
                        rfl

theorem cell23_5033233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_5033233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033233 prefixEnd_5033233 := by exact prefixLift 5033233
  have htrace : WordTrace (prefixWord ++ tailWord_5033233) baseStart_5033233 baseEnd_5033233 := by
    simpa [prefixWord, tailWord_5033233, baseEnd_5033233] using wordTrace_append hprefix tailTrace_5033233
  have hstable : (prefixWord ++ tailWord_5033233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033233).length < 2 ^ (prefixWord ++ tailWord_5033233).sum := by decide
  have hdescent : baseEnd_5033233 < baseStart_5033233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033249 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5033249 : Nat := 118140960795 + 5033249 * 2 ^ 59
def prefixEnd_5033249 : Nat := 4983230072969 + 3 ^ 40 * 5033249 * 2
def baseEnd_5033249 : Nat := 2584475990761883123840015

theorem tailTrace_5033249 : CollatzResearch.WordTrace tailWord_5033249 prefixEnd_5033249 2584475990761883123840015 := by
  unfold tailWord_5033249
  simp only [CollatzResearch.WordTrace]
  refine ⟨183577672542405958337222801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122385115028270638891481867 183577672542405958337222801)
  ·
    refine ⟨137683254406804468752917101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183577672542405958337222801 137683254406804468752917101)
    ·
      refine ⟨51631220402551675782343913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137683254406804468752917101 51631220402551675782343913)
      ·
        refine ⟨38723415301913756836757935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51631220402551675782343913 38723415301913756836757935)
        ·
          refine ⟨58085122952870635255136903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38723415301913756836757935 58085122952870635255136903)
          ·
            refine ⟨87127684429305952882705355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58085122952870635255136903 87127684429305952882705355)
            ·
              refine ⟨130691526643958929324058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87127684429305952882705355 130691526643958929324058033)
              ·
                refine ⟨98018644982969196993043525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130691526643958929324058033 98018644982969196993043525)
                ·
                  refine ⟨18378495934306724436195661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98018644982969196993043525 18378495934306724436195661)
                  ·
                    refine ⟨6891935975365021663573373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18378495934306724436195661 6891935975365021663573373)
                    ·
                      refine ⟨2584475990761883123840015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6891935975365021663573373 2584475990761883123840015)
                      ·
                        rfl

theorem cell23_5033249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5033249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033249 prefixEnd_5033249 := by exact prefixLift 5033249
  have htrace : WordTrace (prefixWord ++ tailWord_5033249) baseStart_5033249 baseEnd_5033249 := by
    simpa [prefixWord, tailWord_5033249, baseEnd_5033249] using wordTrace_append hprefix tailTrace_5033249
  have hstable : (prefixWord ++ tailWord_5033249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033249).length < 2 ^ (prefixWord ++ tailWord_5033249).sum := by decide
  have hdescent : baseEnd_5033249 < baseStart_5033249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033273 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 5]
def baseStart_5033273 : Nat := 118140960795 + 5033273 * 2 ^ 59
def prefixEnd_5033273 : Nat := 4983230072969 + 3 ^ 40 * 5033273 * 2
def baseEnd_5033273 : Nat := 287165368255287892215545

theorem tailTrace_5033273 : CollatzResearch.WordTrace tailWord_5033273 prefixEnd_5033273 287165368255287892215545 := by
  unfold tailWord_5033273
  simp only [CollatzResearch.WordTrace]
  refine ⟨183578547894319010436096473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122385698596212673624064315 183578547894319010436096473)
  ·
    refine ⟨137683910920739257827072355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183578547894319010436096473 137683910920739257827072355)
    ·
      refine ⟨206525866381108886740608533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137683910920739257827072355 206525866381108886740608533)
      ·
        refine ⟨9680899986614479065966025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206525866381108886740608533 9680899986614479065966025)
        ·
          refine ⟨7260674989960859299474519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9680899986614479065966025 7260674989960859299474519)
          ·
            refine ⟨10891012484941288949211779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260674989960859299474519 10891012484941288949211779)
            ·
              refine ⟨16336518727411933423817669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10891012484941288949211779 16336518727411933423817669)
              ·
                refine ⟨3063097261389737516965813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16336518727411933423817669 3063097261389737516965813)
                ·
                  refine ⟨287165368255287892215545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3063097261389737516965813 287165368255287892215545)
                  ·
                    rfl

theorem cell23_5033273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 5].length) (baseStart_5033273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033273 prefixEnd_5033273 := by exact prefixLift 5033273
  have htrace : WordTrace (prefixWord ++ tailWord_5033273) baseStart_5033273 baseEnd_5033273 := by
    simpa [prefixWord, tailWord_5033273, baseEnd_5033273] using wordTrace_append hprefix tailTrace_5033273
  have hstable : (prefixWord ++ tailWord_5033273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033273).length < 2 ^ (prefixWord ++ tailWord_5033273).sum := by decide
  have hdescent : baseEnd_5033273 < baseStart_5033273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033276 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_5033276 : Nat := 118140960795 + 5033276 * 2 ^ 59
def prefixEnd_5033276 : Nat := 4983230072969 + 3 ^ 40 * 5033276 * 2
def baseEnd_5033276 : Nat := 2584489854739554518202391

theorem tailTrace_5033276 : CollatzResearch.WordTrace tailWord_5033276 prefixEnd_5033276 2584489854739554518202391 := by
  unfold tailWord_5033276
  simp only [CollatzResearch.WordTrace]
  refine ⟨91789328656654070974227841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122385771542205427965637121 91789328656654070974227841)
  ·
    refine ⟨68841996492490553230670881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91789328656654070974227841 68841996492490553230670881)
    ·
      refine ⟨51631497369367914923003161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68841996492490553230670881 51631497369367914923003161)
      ·
        refine ⟨38723623027025936192252371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51631497369367914923003161 38723623027025936192252371)
        ·
          refine ⟨58085434540538904288378557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38723623027025936192252371 58085434540538904288378557)
          ·
            refine ⟨21782037952702089108141959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58085434540538904288378557 21782037952702089108141959)
            ·
              refine ⟨32673056929053133662212939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21782037952702089108141959 32673056929053133662212939)
              ·
                refine ⟨49009585393579700493319409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32673056929053133662212939 49009585393579700493319409)
                ·
                  refine ⟨36757189045184775369989557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49009585393579700493319409 36757189045184775369989557)
                  ·
                    refine ⟨3445986472986072690936521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36757189045184775369989557 3445986472986072690936521)
                    ·
                      refine ⟨2584489854739554518202391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3445986472986072690936521 2584489854739554518202391)
                      ·
                        rfl

theorem cell23_5033276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_5033276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033276 prefixEnd_5033276 := by exact prefixLift 5033276
  have htrace : WordTrace (prefixWord ++ tailWord_5033276) baseStart_5033276 baseEnd_5033276 := by
    simpa [prefixWord, tailWord_5033276, baseEnd_5033276] using wordTrace_append hprefix tailTrace_5033276
  have hstable : (prefixWord ++ tailWord_5033276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033276).length < 2 ^ (prefixWord ++ tailWord_5033276).sum := by decide
  have hdescent : baseEnd_5033276 < baseStart_5033276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033279 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_5033279 : Nat := 118140960795 + 5033279 * 2 ^ 59
def prefixEnd_5033279 : Nat := 4983230072969 + 3 ^ 40 * 5033279 * 2
def baseEnd_5033279 : Nat := 2584491395181518006464877

theorem tailTrace_5033279 : CollatzResearch.WordTrace tailWord_5033279 prefixEnd_5033279 2584491395181518006464877 := by
  unfold tailWord_5033279
  simp only [CollatzResearch.WordTrace]
  refine ⟨183578766732297273460814891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122385844488198182307209927 183578766732297273460814891)
  ·
    refine ⟨275368150098445910191222337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183578766732297273460814891 275368150098445910191222337)
    ·
      refine ⟨206526112573834432643416753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275368150098445910191222337 206526112573834432643416753)
      ·
        refine ⟨154894584430375824482562565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206526112573834432643416753 154894584430375824482562565)
        ·
          refine ⟨29042734580695467090480481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154894584430375824482562565 29042734580695467090480481)
          ·
            refine ⟨21782050935521600317860361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29042734580695467090480481 21782050935521600317860361)
            ·
              refine ⟨16336538201641200238395271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21782050935521600317860361 16336538201641200238395271)
              ·
                refine ⟨24504807302461800357592907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16336538201641200238395271 24504807302461800357592907)
                ·
                  refine ⟨36757210953692700536389361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24504807302461800357592907 36757210953692700536389361)
                  ·
                    refine ⟨27567908215269525402292021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36757210953692700536389361 27567908215269525402292021)
                    ·
                      refine ⟨2584491395181518006464877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27567908215269525402292021 2584491395181518006464877)
                      ·
                        rfl

theorem cell23_5033279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_5033279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033279 prefixEnd_5033279 := by exact prefixLift 5033279
  have htrace : WordTrace (prefixWord ++ tailWord_5033279) baseStart_5033279 baseEnd_5033279 := by
    simpa [prefixWord, tailWord_5033279, baseEnd_5033279] using wordTrace_append hprefix tailTrace_5033279
  have hstable : (prefixWord ++ tailWord_5033279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033279).length < 2 ^ (prefixWord ++ tailWord_5033279).sum := by decide
  have hdescent : baseEnd_5033279 < baseStart_5033279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033289 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_5033289 : Nat := 118140960795 + 5033289 * 2 ^ 59
def prefixEnd_5033289 : Nat := 4983230072969 + 3 ^ 40 * 5033289 * 2
def baseEnd_5033289 : Nat := 2584496529988062967339831

theorem tailTrace_5033289 : CollatzResearch.WordTrace tailWord_5033289 prefixEnd_5033289 2584496529988062967339831 := by
  unfold tailWord_5033289
  simp only [CollatzResearch.WordTrace]
  refine ⟨183579131462261045168678921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122386087641507363445785947 183579131462261045168678921)
  ·
    refine ⟨137684348596695783876509191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183579131462261045168678921 137684348596695783876509191)
    ·
      refine ⟨206526522895043675814763787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137684348596695783876509191 206526522895043675814763787)
      ·
        refine ⟨309789784342565513722145681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206526522895043675814763787 309789784342565513722145681)
        ·
          refine ⟨232342338256924135291609261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309789784342565513722145681 232342338256924135291609261)
          ·
            refine ⟨87128376846346550734353473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232342338256924135291609261 87128376846346550734353473)
            ·
              refine ⟨65346282634759913050765105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87128376846346550734353473 65346282634759913050765105)
              ·
                refine ⟨49009711976069934788073829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65346282634759913050765105 49009711976069934788073829)
                ·
                  refine ⟨9189320995513112772763843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49009711976069934788073829 9189320995513112772763843)
                  ·
                    refine ⟨13783981493269669159145765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9189320995513112772763843 13783981493269669159145765)
                    ·
                      refine ⟨2584496529988062967339831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13783981493269669159145765 2584496529988062967339831)
                      ·
                        rfl

theorem cell23_5033289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_5033289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033289 prefixEnd_5033289 := by exact prefixLift 5033289
  have htrace : WordTrace (prefixWord ++ tailWord_5033289) baseStart_5033289 baseEnd_5033289 := by
    simpa [prefixWord, tailWord_5033289, baseEnd_5033289] using wordTrace_append hprefix tailTrace_5033289
  have hstable : (prefixWord ++ tailWord_5033289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033289).length < 2 ^ (prefixWord ++ tailWord_5033289).sum := by decide
  have hdescent : baseEnd_5033289 < baseStart_5033289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033306 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_5033306 : Nat := 118140960795 + 5033306 * 2 ^ 59
def prefixEnd_5033306 : Nat := 4983230072969 + 3 ^ 40 * 5033306 * 2
def baseEnd_5033306 : Nat := 2584505259159189400827253

theorem tailTrace_5033306 : CollatzResearch.WordTrace tailWord_5033306 prefixEnd_5033306 2584505259159189400827253 := by
  unfold tailWord_5033306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45894937875799864268011943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122386501002132971381365181 45894937875799864268011943)
  ·
    refine ⟨68842406813699796402017915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45894937875799864268011943 68842406813699796402017915)
    ·
      refine ⟨103263610220549694603026873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68842406813699796402017915 103263610220549694603026873)
      ·
        refine ⟨77447707665412270952270155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103263610220549694603026873 77447707665412270952270155)
        ·
          refine ⟨116171561498118406428405233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77447707665412270952270155 116171561498118406428405233)
          ·
            refine ⟨87128671123588804821303925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116171561498118406428405233 87128671123588804821303925)
            ·
              refine ⟨8168312917836450451997243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87128671123588804821303925 8168312917836450451997243)
              ·
                refine ⟨12252469376754675677995865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168312917836450451997243 12252469376754675677995865)
                ·
                  refine ⟨9189352032566006758496899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12252469376754675677995865 9189352032566006758496899)
                  ·
                    refine ⟨13784028048849010137745349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9189352032566006758496899 13784028048849010137745349)
                    ·
                      refine ⟨2584505259159189400827253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13784028048849010137745349 2584505259159189400827253)
                      ·
                        rfl

theorem cell23_5033306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_5033306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033306 prefixEnd_5033306 := by exact prefixLift 5033306
  have htrace : WordTrace (prefixWord ++ tailWord_5033306) baseStart_5033306 baseEnd_5033306 := by
    simpa [prefixWord, tailWord_5033306, baseEnd_5033306] using wordTrace_append hprefix tailTrace_5033306
  have hstable : (prefixWord ++ tailWord_5033306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033306).length < 2 ^ (prefixWord ++ tailWord_5033306).sum := by decide
  have hdescent : baseEnd_5033306 < baseStart_5033306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033376 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_5033376 : Nat := 118140960795 + 5033376 * 2 ^ 59
def prefixEnd_5033376 : Nat := 4983230072969 + 3 ^ 40 * 5033376 * 2
def baseEnd_5033376 : Nat := 861513734268334708983977

theorem tailTrace_5033376 : CollatzResearch.WordTrace tailWord_5033376 prefixEnd_5033376 861513734268334708983977 := by
  unfold tailWord_5033376
  simp only [CollatzResearch.WordTrace]
  refine ⟨91791152306472929513547991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122388203075297239351397321 91791152306472929513547991)
  ·
    refine ⟨137686728459709394270321987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91791152306472929513547991 137686728459709394270321987)
    ·
      refine ⟨206530092689564091405482981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137686728459709394270321987 206530092689564091405482981)
      ·
        refine ⟨38724392379293267138528059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206530092689564091405482981 38724392379293267138528059)
        ·
          refine ⟨58086588568939900707792089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38724392379293267138528059 58086588568939900707792089)
          ·
            refine ⟨43564941426704925530844067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58086588568939900707792089 43564941426704925530844067)
            ·
              refine ⟨65347412140057388296266101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43564941426704925530844067 65347412140057388296266101)
              ·
                refine ⟨6126319888130380152774947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65347412140057388296266101 6126319888130380152774947)
                ·
                  refine ⟨9189479832195570229162421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126319888130380152774947 9189479832195570229162421)
                  ·
                    refine ⟨861513734268334708983977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9189479832195570229162421 861513734268334708983977)
                    ·
                      rfl

theorem cell23_5033376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_5033376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033376 prefixEnd_5033376 := by exact prefixLift 5033376
  have htrace : WordTrace (prefixWord ++ tailWord_5033376) baseStart_5033376 baseEnd_5033376 := by
    simpa [prefixWord, tailWord_5033376, baseEnd_5033376] using wordTrace_append hprefix tailTrace_5033376
  have hstable : (prefixWord ++ tailWord_5033376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033376).length < 2 ^ (prefixWord ++ tailWord_5033376).sum := by decide
  have hdescent : baseEnd_5033376 < baseStart_5033376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033384 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5033384 : Nat := 118140960795 + 5033384 * 2 ^ 59
def prefixEnd_5033384 : Nat := 4983230072969 + 3 ^ 40 * 5033384 * 2
def baseEnd_5033384 : Nat := 861515103550080031883965

theorem tailTrace_5033384 : CollatzResearch.WordTrace tailWord_5033384 prefixEnd_5033384 861515103550080031883965 := by
  unfold tailWord_5033384
  simp only [CollatzResearch.WordTrace]
  refine ⟨91791298198458438196693603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122388397597944584262258137 91791298198458438196693603)
  ·
    refine ⟨137686947297687657295040405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91791298198458438196693603 137686947297687657295040405)
    ·
      refine ⟨6454075654579108935705019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137686947297687657295040405 6454075654579108935705019)
      ·
        refine ⟨9681113481868663403557529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454075654579108935705019 9681113481868663403557529)
        ·
          refine ⟨7260835111401497552668147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681113481868663403557529 7260835111401497552668147)
          ·
            refine ⟨10891252667102246329002221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260835111401497552668147 10891252667102246329002221)
            ·
              refine ⟨4084219750163342373375833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10891252667102246329002221 4084219750163342373375833)
              ·
                refine ⟨3063164812622506780031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084219750163342373375833 3063164812622506780031875)
                ·
                  refine ⟨4594747218933760170047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063164812622506780031875 4594747218933760170047813)
                  ·
                    refine ⟨861515103550080031883965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4594747218933760170047813 861515103550080031883965)
                    ·
                      rfl

theorem cell23_5033384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5033384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033384 prefixEnd_5033384 := by exact prefixLift 5033384
  have htrace : WordTrace (prefixWord ++ tailWord_5033384) baseStart_5033384 baseEnd_5033384 := by
    simpa [prefixWord, tailWord_5033384, baseEnd_5033384] using wordTrace_append hprefix tailTrace_5033384
  have hstable : (prefixWord ++ tailWord_5033384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033384).length < 2 ^ (prefixWord ++ tailWord_5033384).sum := by decide
  have hdescent : baseEnd_5033384 < baseStart_5033384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033406 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_5033406 : Nat := 118140960795 + 5033406 * 2 ^ 59
def prefixEnd_5033406 : Nat := 4983230072969 + 3 ^ 40 * 5033406 * 2
def baseEnd_5033406 : Nat := 861518869074879669858931

theorem tailTrace_5033406 : CollatzResearch.WordTrace tailWord_5033406 prefixEnd_5033406 861518869074879669858931 := by
  unfold tailWord_5033406
  simp only [CollatzResearch.WordTrace]
  refine ⟨22947924850354646768836009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122388932535224782767125381 22947924850354646768836009)
  ·
    refine ⟨17210943637765985076627007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22947924850354646768836009 17210943637765985076627007)
    ·
      refine ⟨25816415456648977614940511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17210943637765985076627007 25816415456648977614940511)
      ·
        refine ⟨38724623184973466422410767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25816415456648977614940511 38724623184973466422410767)
        ·
          refine ⟨58086934777460199633616151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38724623184973466422410767 58086934777460199633616151)
          ·
            refine ⟨87130402166190299450424227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58086934777460199633616151 87130402166190299450424227)
            ·
              refine ⟨130695603249285449175636341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87130402166190299450424227 130695603249285449175636341)
              ·
                refine ⟨12252712804620510860215907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130695603249285449175636341 12252712804620510860215907)
                ·
                  refine ⟨18379069206930766290323861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12252712804620510860215907 18379069206930766290323861)
                  ·
                    refine ⟨861518869074879669858931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18379069206930766290323861 861518869074879669858931)
                    ·
                      rfl

theorem cell23_5033406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_5033406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033406 prefixEnd_5033406 := by exact prefixLift 5033406
  have htrace : WordTrace (prefixWord ++ tailWord_5033406) baseStart_5033406 baseEnd_5033406 := by
    simpa [prefixWord, tailWord_5033406, baseEnd_5033406] using wordTrace_append hprefix tailTrace_5033406
  have hstable : (prefixWord ++ tailWord_5033406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033406).length < 2 ^ (prefixWord ++ tailWord_5033406).sum := by decide
  have hdescent : baseEnd_5033406 < baseStart_5033406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033419 : List Nat := [1, 1, 1, 1, 3, 3, 4, 9]
def baseStart_5033419 : Nat := 118140960795 + 5033419 * 2 ^ 59
def prefixEnd_5033419 : Nat := 4983230072969 + 3 ^ 40 * 5033419 * 2
def baseEnd_5033419 : Nat := 95724566017523979952379

theorem tailTrace_5033419 : CollatzResearch.WordTrace tailWord_5033419 prefixEnd_5033419 95724566017523979952379 := by
  unfold tailWord_5033419
  simp only [CollatzResearch.WordTrace]
  refine ⟨183583872951790077370911311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122389248634526718247274207 183583872951790077370911311)
  ·
    refine ⟨275375809427685116056366967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183583872951790077370911311 275375809427685116056366967)
    ·
      refine ⟨413063714141527674084550451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275375809427685116056366967 413063714141527674084550451)
      ·
        refine ⟨619595571212291511126825677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413063714141527674084550451 619595571212291511126825677)
        ·
          refine ⟨232348339204609316672559629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619595571212291511126825677 232348339204609316672559629)
          ·
            refine ⟨87130627201728493752209861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232348339204609316672559629 87130627201728493752209861)
            ·
              refine ⟨16336992600324092578539349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87130627201728493752209861 16336992600324092578539349)
              ·
                refine ⟨95724566017523979952379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16336992600324092578539349 95724566017523979952379)
                ·
                  rfl

theorem cell23_5033419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 9].length) (baseStart_5033419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033419 prefixEnd_5033419 := by exact prefixLift 5033419
  have htrace : WordTrace (prefixWord ++ tailWord_5033419) baseStart_5033419 baseEnd_5033419 := by
    simpa [prefixWord, tailWord_5033419, baseEnd_5033419] using wordTrace_append hprefix tailTrace_5033419
  have hstable : (prefixWord ++ tailWord_5033419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033419).length < 2 ^ (prefixWord ++ tailWord_5033419).sum := by decide
  have hdescent : baseEnd_5033419 < baseStart_5033419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033433 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_5033433 : Nat := 118140960795 + 5033433 * 2 ^ 59
def prefixEnd_5033433 : Nat := 4983230072969 + 3 ^ 40 * 5033433 * 2
def baseEnd_5033433 : Nat := 2584570471202310403939169

theorem tailTrace_5033433 : CollatzResearch.WordTrace tailWord_5033433 prefixEnd_5033433 2584570471202310403939169 := by
  unfold tailWord_5033433
  simp only [CollatzResearch.WordTrace]
  refine ⟨183584383573739357761920953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122389589049159571841280635 183584383573739357761920953)
  ·
    refine ⟨137688287680304518321440715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183584383573739357761920953 137688287680304518321440715)
    ·
      refine ⟨206532431520456777482161073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137688287680304518321440715 206532431520456777482161073)
      ·
        refine ⟨154899323640342583111620805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206532431520456777482161073 154899323640342583111620805)
        ·
          refine ⟨29043623182564234333428901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154899323640342583111620805 29043623182564234333428901)
          ·
            refine ⟨5445679346730793937517919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29043623182564234333428901 5445679346730793937517919)
            ·
              refine ⟨8168519020096190906276879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445679346730793937517919 8168519020096190906276879)
              ·
                refine ⟨12252778530144286359415319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168519020096190906276879 12252778530144286359415319)
                ·
                  refine ⟨18379167795216429539122979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12252778530144286359415319 18379167795216429539122979)
                  ·
                    refine ⟨27568751692824644308684469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18379167795216429539122979 27568751692824644308684469)
                    ·
                      refine ⟨2584570471202310403939169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27568751692824644308684469 2584570471202310403939169)
                      ·
                        rfl

theorem cell23_5033433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_5033433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033433 prefixEnd_5033433 := by exact prefixLift 5033433
  have htrace : WordTrace (prefixWord ++ tailWord_5033433) baseStart_5033433 baseEnd_5033433 := by
    simpa [prefixWord, tailWord_5033433, baseEnd_5033433] using wordTrace_append hprefix tailTrace_5033433
  have hstable : (prefixWord ++ tailWord_5033433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033433).length < 2 ^ (prefixWord ++ tailWord_5033433).sum := by decide
  have hdescent : baseEnd_5033433 < baseStart_5033433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033478 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5033478 : Nat := 118140960795 + 5033478 * 2 ^ 59
def prefixEnd_5033478 : Nat := 4983230072969 + 3 ^ 40 * 5033478 * 2
def baseEnd_5033478 : Nat := 861531192610587575958821

theorem tailTrace_5033478 : CollatzResearch.WordTrace tailWord_5033478 prefixEnd_5033478 861531192610587575958821 := by
  unfold tailWord_5033478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737063276830510326478409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122390683239050886964872725 5737063276830510326478409)
  ·
    refine ⟨4302797457622882744858807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5737063276830510326478409 4302797457622882744858807)
    ·
      refine ⟨6454196186434324117288211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302797457622882744858807 6454196186434324117288211)
      ·
        refine ⟨9681294279651486175932317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454196186434324117288211 9681294279651486175932317)
        ·
          refine ⟨3630485354869307315974619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9681294279651486175932317 3630485354869307315974619)
          ·
            refine ⟨5445728032303960973961929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630485354869307315974619 5445728032303960973961929)
            ·
              refine ⟨4084296024227970730471447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5445728032303960973961929 4084296024227970730471447)
              ·
                refine ⟨6126444036341956095707171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084296024227970730471447 6126444036341956095707171)
                ·
                  refine ⟨9189666054512934143560757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126444036341956095707171 9189666054512934143560757)
                  ·
                    refine ⟨861531192610587575958821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9189666054512934143560757 861531192610587575958821)
                    ·
                      rfl

theorem cell23_5033478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5033478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033478 prefixEnd_5033478 := by exact prefixLift 5033478
  have htrace : WordTrace (prefixWord ++ tailWord_5033478) baseStart_5033478 baseEnd_5033478 := by
    simpa [prefixWord, tailWord_5033478, baseEnd_5033478] using wordTrace_append hprefix tailTrace_5033478
  have hstable : (prefixWord ++ tailWord_5033478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033478).length < 2 ^ (prefixWord ++ tailWord_5033478).sum := by decide
  have hdescent : baseEnd_5033478 < baseStart_5033478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033484 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_5033484 : Nat := 118140960795 + 5033484 * 2 ^ 59
def prefixEnd_5033484 : Nat := 4983230072969 + 3 ^ 40 * 5033484 * 2
def baseEnd_5033484 : Nat := 2584596658715689704401435

theorem tailTrace_5033484 : CollatzResearch.WordTrace tailWord_5033484 prefixEnd_5033484 2584596658715689704401435 := by
  unfold tailWord_5033484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91793121848277296736013753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122390829131036395648018337 91793121848277296736013753)
  ·
    refine ⟨68844841386207972552010315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91793121848277296736013753 68844841386207972552010315)
    ·
      refine ⟨103267262079311958828015473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68844841386207972552010315 103267262079311958828015473)
      ·
        refine ⟨77450446559483969121011605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103267262079311958828015473 77450446559483969121011605)
        ·
          refine ⟨3630489682475811052547419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77450446559483969121011605 3630489682475811052547419)
          ·
            refine ⟨5445734523713716578821129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630489682475811052547419 5445734523713716578821129)
            ·
              refine ⟨4084300892785287434115847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5445734523713716578821129 4084300892785287434115847)
              ·
                refine ⟨6126451339177931151173771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084300892785287434115847 6126451339177931151173771)
                ·
                  refine ⟨9189677008766896726760657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126451339177931151173771 9189677008766896726760657)
                  ·
                    refine ⟨6892257756575172545070493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9189677008766896726760657 6892257756575172545070493)
                    ·
                      refine ⟨2584596658715689704401435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6892257756575172545070493 2584596658715689704401435)
                      ·
                        rfl

theorem cell23_5033484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_5033484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033484 prefixEnd_5033484 := by exact prefixLift 5033484
  have htrace : WordTrace (prefixWord ++ tailWord_5033484) baseStart_5033484 baseEnd_5033484 := by
    simpa [prefixWord, tailWord_5033484, baseEnd_5033484] using wordTrace_append hprefix tailTrace_5033484
  have hstable : (prefixWord ++ tailWord_5033484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033484).length < 2 ^ (prefixWord ++ tailWord_5033484).sum := by decide
  have hdescent : baseEnd_5033484 < baseStart_5033484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033503 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 4, 2]
def baseStart_5033503 : Nat := 118140960795 + 5033503 * 2 ^ 59
def prefixEnd_5033503 : Nat := 4983230072969 + 3 ^ 40 * 5033503 * 2
def baseEnd_5033503 : Nat := 2584606414848125130063847

theorem tailTrace_5033503 : CollatzResearch.WordTrace tailWord_5033503 prefixEnd_5033503 2584606414848125130063847 := by
  unfold tailWord_5033503
  simp only [CollatzResearch.WordTrace]
  refine ⟨183586936683485759716969163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122391291122323839811312775 183586936683485759716969163)
  ·
    refine ⟨275380405025228639575453745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183586936683485759716969163 275380405025228639575453745)
    ·
      refine ⟨206535303768921479681590309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275380405025228639575453745 206535303768921479681590309)
      ·
        refine ⟨38725369456672777440298183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206535303768921479681590309 38725369456672777440298183)
        ·
          refine ⟨58088054185009166160447275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38725369456672777440298183 58088054185009166160447275)
          ·
            refine ⟨87132081277513749240670913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58088054185009166160447275 87132081277513749240670913)
            ·
              refine ⟨65349060958135311930503185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87132081277513749240670913 65349060958135311930503185)
              ·
                refine ⟨49011795718601483947877389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65349060958135311930503185 49011795718601483947877389)
                ·
                  refine ⟨18379423394475556480454021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49011795718601483947877389 18379423394475556480454021)
                  ·
                    refine ⟨3446141886464166840085129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18379423394475556480454021 3446141886464166840085129)
                    ·
                      refine ⟨2584606414848125130063847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446141886464166840085129 2584606414848125130063847)
                      ·
                        rfl

theorem cell23_5033503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_5033503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033503 prefixEnd_5033503 := by exact prefixLift 5033503
  have htrace : WordTrace (prefixWord ++ tailWord_5033503) baseStart_5033503 baseEnd_5033503 := by
    simpa [prefixWord, tailWord_5033503, baseEnd_5033503] using wordTrace_append hprefix tailTrace_5033503
  have hstable : (prefixWord ++ tailWord_5033503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033503).length < 2 ^ (prefixWord ++ tailWord_5033503).sum := by decide
  have hdescent : baseEnd_5033503 < baseStart_5033503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033590 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5033590 : Nat := 118140960795 + 5033590 * 2 ^ 59
def prefixEnd_5033590 : Nat := 4983230072969 + 3 ^ 40 * 5033590 * 2
def baseEnd_5033590 : Nat := 861550362555022096558649

theorem tailTrace_5033590 : CollatzResearch.WordTrace tailWord_5033590 prefixEnd_5033590 861550362555022096558649 := by
  unfold tailWord_5033590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474381864635660848461639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122393406556113715716924149 11474381864635660848461639)
  ·
    refine ⟨17211572796953491272692459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11474381864635660848461639 17211572796953491272692459)
    ·
      refine ⟨25817359195430236909038689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17211572796953491272692459 25817359195430236909038689)
      ·
        refine ⟨19363019396572677681779017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25817359195430236909038689 19363019396572677681779017)
        ·
          refine ⟨14522264547429508261334263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19363019396572677681779017 14522264547429508261334263)
          ·
            refine ⟨21783396821144262392001395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14522264547429508261334263 21783396821144262392001395)
            ·
              refine ⟨32675095231716393588002093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21783396821144262392001395 32675095231716393588002093)
              ·
                refine ⟨12253160711893647595500785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32675095231716393588002093 12253160711893647595500785)
                ·
                  refine ⟨9189870533920235696625589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12253160711893647595500785 9189870533920235696625589)
                  ·
                    refine ⟨861550362555022096558649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9189870533920235696625589 861550362555022096558649)
                    ·
                      rfl

theorem cell23_5033590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5033590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033590 prefixEnd_5033590 := by exact prefixLift 5033590
  have htrace : WordTrace (prefixWord ++ tailWord_5033590) baseStart_5033590 baseEnd_5033590 := by
    simpa [prefixWord, tailWord_5033590, baseEnd_5033590] using wordTrace_append hprefix tailTrace_5033590
  have hstable : (prefixWord ++ tailWord_5033590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033590).length < 2 ^ (prefixWord ++ tailWord_5033590).sum := by decide
  have hdescent : baseEnd_5033590 < baseStart_5033590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033610 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5033610 : Nat := 118140960795 + 5033610 * 2 ^ 59
def prefixEnd_5033610 : Nat := 4983230072969 + 3 ^ 40 * 5033610 * 2
def baseEnd_5033610 : Nat := 2584661357278156211425855

theorem tailTrace_5033610 : CollatzResearch.WordTrace tailWord_5033610 prefixEnd_5033610 2584661357278156211425855 := by
  unfold tailWord_5033610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45897709823524529247778571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122393892862732077994076189 45897709823524529247778571)
  ·
    refine ⟨68846564735286793871667857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45897709823524529247778571 68846564735286793871667857)
    ·
      refine ⟨51634923551465095403750893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68846564735286793871667857 51634923551465095403750893)
      ·
        refine ⟨19363096331799410776406585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51634923551465095403750893 19363096331799410776406585)
        ·
          refine ⟨14522322248849558082304939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19363096331799410776406585 14522322248849558082304939)
          ·
            refine ⟨21783483373274337123457409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14522322248849558082304939 21783483373274337123457409)
            ·
              refine ⟨16337612529955752842593057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21783483373274337123457409 16337612529955752842593057)
              ·
                refine ⟨12253209397466814631944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16337612529955752842593057 12253209397466814631944793)
                ·
                  refine ⟨9189907048100110973958595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12253209397466814631944793 9189907048100110973958595)
                  ·
                    refine ⟨13784860572150166460937893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9189907048100110973958595 13784860572150166460937893)
                    ·
                      refine ⟨2584661357278156211425855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13784860572150166460937893 2584661357278156211425855)
                      ·
                        rfl

theorem cell23_5033610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5033610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033610 prefixEnd_5033610 := by exact prefixLift 5033610
  have htrace : WordTrace (prefixWord ++ tailWord_5033610) baseStart_5033610 baseEnd_5033610 := by
    simpa [prefixWord, tailWord_5033610, baseEnd_5033610] using wordTrace_append hprefix tailTrace_5033610
  have hstable : (prefixWord ++ tailWord_5033610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033610).length < 2 ^ (prefixWord ++ tailWord_5033610).sum := by decide
  have hdescent : baseEnd_5033610 < baseStart_5033610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033616 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 8]
def baseStart_5033616 : Nat := 118140960795 + 5033616 * 2 ^ 59
def prefixEnd_5033616 : Nat := 4983230072969 + 3 ^ 40 * 5033616 * 2
def baseEnd_5033616 : Nat := 287184937573564798661203

theorem tailTrace_5033616 : CollatzResearch.WordTrace tailWord_5033616 prefixEnd_5033616 287184937573564798661203 := by
  unfold tailWord_5033616
  simp only [CollatzResearch.WordTrace]
  refine ⟨91795529066038190007916351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122394038754717586677221801 91795529066038190007916351)
  ·
    refine ⟨137693293599057285011874527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91795529066038190007916351 137693293599057285011874527)
    ·
      refine ⟨206539940398585927517811791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137693293599057285011874527 206539940398585927517811791)
      ·
        refine ⟨309809910597878891276717687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206539940398585927517811791 309809910597878891276717687)
        ·
          refine ⟨464714865896818336915076531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309809910597878891276717687 464714865896818336915076531)
          ·
            refine ⟨697072298845227505372614797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464714865896818336915076531 697072298845227505372614797)
            ·
              refine ⟨261402112066960314514730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697072298845227505372614797 261402112066960314514730549)
              ·
                refine ⟨24506448006277529485755989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261402112066960314514730549 24506448006277529485755989)
                ·
                  refine ⟨287184937573564798661203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24506448006277529485755989 287184937573564798661203)
                  ·
                    rfl

theorem cell23_5033616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_5033616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033616 prefixEnd_5033616 := by exact prefixLift 5033616
  have htrace : WordTrace (prefixWord ++ tailWord_5033616) baseStart_5033616 baseEnd_5033616 := by
    simpa [prefixWord, tailWord_5033616, baseEnd_5033616] using wordTrace_append hprefix tailTrace_5033616
  have hstable : (prefixWord ++ tailWord_5033616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033616).length < 2 ^ (prefixWord ++ tailWord_5033616).sum := by decide
  have hdescent : baseEnd_5033616 < baseStart_5033616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033697 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_5033697 : Nat := 118140960795 + 5033697 * 2 ^ 59
def prefixEnd_5033697 : Nat := 4983230072969 + 3 ^ 40 * 5033697 * 2
def baseEnd_5033697 : Nat := 861568676698365790345985

theorem tailTrace_5033697 : CollatzResearch.WordTrace tailWord_5033697 prefixEnd_5033697 861568676698365790345985 := by
  unfold tailWord_5033697
  simp only [CollatzResearch.WordTrace]
  refine ⟨183594012444782930849531345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122396008296521953899687563 183594012444782930849531345)
  ·
    refine ⟨137695509333587198137148509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183594012444782930849531345 137695509333587198137148509)
    ·
      refine ⟨51635816000095199301430691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137695509333587198137148509 51635816000095199301430691)
      ·
        refine ⟨77453724000142798952146037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51635816000095199301430691 77453724000142798952146037)
        ·
          refine ⟨7261286625013387401763691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77453724000142798952146037 7261286625013387401763691)
          ·
            refine ⟨10891929937520081102645537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261286625013387401763691 10891929937520081102645537)
            ·
              refine ⟨8168947453140060826984153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10891929937520081102645537 8168947453140060826984153)
              ·
                refine ⟨6126710589855045620238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8168947453140060826984153 6126710589855045620238115)
                ·
                  refine ⟨9190065884782568430357173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126710589855045620238115 9190065884782568430357173)
                  ·
                    refine ⟨861568676698365790345985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9190065884782568430357173 861568676698365790345985)
                    ·
                      rfl

theorem cell23_5033697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_5033697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033697 prefixEnd_5033697 := by exact prefixLift 5033697
  have htrace : WordTrace (prefixWord ++ tailWord_5033697) baseStart_5033697 baseEnd_5033697 := by
    simpa [prefixWord, tailWord_5033697, baseEnd_5033697] using wordTrace_append hprefix tailTrace_5033697
  have hstable : (prefixWord ++ tailWord_5033697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033697).length < 2 ^ (prefixWord ++ tailWord_5033697).sum := by decide
  have hdescent : baseEnd_5033697 < baseStart_5033697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033700 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_5033700 : Nat := 118140960795 + 5033700 * 2 ^ 59
def prefixEnd_5033700 : Nat := 4983230072969 + 3 ^ 40 * 5033700 * 2
def baseEnd_5033700 : Nat := 2584707570537060859300441

theorem tailTrace_5033700 : CollatzResearch.WordTrace tailWord_5033700 prefixEnd_5033700 2584707570537060859300441 := by
  unfold tailWord_5033700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91797060931886031180945277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122396081242514708241260369 91797060931886031180945277)
  ·
    refine ⟨34423897849457261692854479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91797060931886031180945277 34423897849457261692854479)
    ·
      refine ⟨51635846774185892539281719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34423897849457261692854479 51635846774185892539281719)
      ·
        refine ⟨77453770161278838808922579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51635846774185892539281719 77453770161278838808922579)
        ·
          refine ⟨116180655241918258213383869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77453770161278838808922579 116180655241918258213383869)
          ·
            refine ⟨43567745715719346830018951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116180655241918258213383869 43567745715719346830018951)
            ·
              refine ⟨65351618573579020245028427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43567745715719346830018951 65351618573579020245028427)
              ·
                refine ⟨98027427860368530367542641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65351618573579020245028427 98027427860368530367542641)
                ·
                  refine ⟨73520570895276397775656981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98027427860368530367542641 73520570895276397775656981)
                  ·
                    refine ⟨3446276760716081145733921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73520570895276397775656981 3446276760716081145733921)
                    ·
                      refine ⟨2584707570537060859300441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446276760716081145733921 2584707570537060859300441)
                      ·
                        rfl

theorem cell23_5033700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_5033700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033700 prefixEnd_5033700 := by exact prefixLift 5033700
  have htrace : WordTrace (prefixWord ++ tailWord_5033700) baseStart_5033700 baseEnd_5033700 := by
    simpa [prefixWord, tailWord_5033700, baseEnd_5033700] using wordTrace_append hprefix tailTrace_5033700
  have hstable : (prefixWord ++ tailWord_5033700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033700).length < 2 ^ (prefixWord ++ tailWord_5033700).sum := by decide
  have hdescent : baseEnd_5033700 < baseStart_5033700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033710 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5033710 : Nat := 118140960795 + 5033710 * 2 ^ 59
def prefixEnd_5033710 : Nat := 4983230072969 + 3 ^ 40 * 5033710 * 2
def baseEnd_5033710 : Nat := 861570901781201940058465

theorem tailTrace_5033710 : CollatzResearch.WordTrace tailWord_5033710 prefixEnd_5033710 861570901781201940058465 := by
  unfold tailWord_5033710
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949310824216979258719323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122396324395823889379836389 22949310824216979258719323)
  ·
    refine ⟨34423966236325468888078985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22949310824216979258719323 34423966236325468888078985)
    ·
      refine ⟨25817974677244101666059239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34423966236325468888078985 25817974677244101666059239)
      ·
        refine ⟨38726962015866152499088859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25817974677244101666059239 38726962015866152499088859)
        ·
          refine ⟨58090443023799228748633289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38726962015866152499088859 58090443023799228748633289)
          ·
            refine ⟨43567832267849421561474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58090443023799228748633289 43567832267849421561474967)
            ·
              refine ⟨65351748401774132342212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43567832267849421561474967 65351748401774132342212451)
              ·
                refine ⟨98027622602661198513318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65351748401774132342212451 98027622602661198513318677)
                ·
                  refine ⟨4595044809499743680311813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98027622602661198513318677 4595044809499743680311813)
                  ·
                    refine ⟨861570901781201940058465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4595044809499743680311813 861570901781201940058465)
                    ·
                      rfl

theorem cell23_5033710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5033710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033710 prefixEnd_5033710 := by exact prefixLift 5033710
  have htrace : WordTrace (prefixWord ++ tailWord_5033710) baseStart_5033710 baseEnd_5033710 := by
    simpa [prefixWord, tailWord_5033710, baseEnd_5033710] using wordTrace_append hprefix tailTrace_5033710
  have hstable : (prefixWord ++ tailWord_5033710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033710).length < 2 ^ (prefixWord ++ tailWord_5033710).sum := by decide
  have hdescent : baseEnd_5033710 < baseStart_5033710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033730 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5033730 : Nat := 118140960795 + 5033730 * 2 ^ 59
def prefixEnd_5033730 : Nat := 4983230072969 + 3 ^ 40 * 5033730 * 2
def baseEnd_5033730 : Nat := 2584722974956695741925303

theorem tailTrace_5033730 : CollatzResearch.WordTrace tailWord_5033730 prefixEnd_5033730 2584722974956695741925303 := by
  unfold tailWord_5033730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898804013415844371370661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122396810702442251656988429 45898804013415844371370661)
  ·
    refine ⟨8606025752515470819631999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45898804013415844371370661 8606025752515470819631999)
    ·
      refine ⟨12909038628773206229447999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606025752515470819631999 12909038628773206229447999)
      ·
        refine ⟨19363557943159809344171999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12909038628773206229447999 19363557943159809344171999)
        ·
          refine ⟨29045336914739714016257999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19363557943159809344171999 29045336914739714016257999)
          ·
            refine ⟨43568005372109571024386999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29045336914739714016257999 43568005372109571024386999)
            ·
              refine ⟨65352008058164356536580499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43568005372109571024386999 65352008058164356536580499)
              ·
                refine ⟨98028012087246534804870749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65352008058164356536580499 98028012087246534804870749)
                ·
                  refine ⟨36760504532717450551826531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98028012087246534804870749 36760504532717450551826531)
                  ·
                    refine ⟨55140756799076175827739797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36760504532717450551826531 55140756799076175827739797)
                    ·
                      refine ⟨2584722974956695741925303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55140756799076175827739797 2584722974956695741925303)
                      ·
                        rfl

theorem cell23_5033730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5033730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033730 prefixEnd_5033730 := by exact prefixLift 5033730
  have htrace : WordTrace (prefixWord ++ tailWord_5033730) baseStart_5033730 baseEnd_5033730 := by
    simpa [prefixWord, tailWord_5033730, baseEnd_5033730] using wordTrace_append hprefix tailTrace_5033730
  have hstable : (prefixWord ++ tailWord_5033730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033730).length < 2 ^ (prefixWord ++ tailWord_5033730).sum := by decide
  have hdescent : baseEnd_5033730 < baseStart_5033730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033748 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5033748 : Nat := 118140960795 + 5033748 * 2 ^ 59
def prefixEnd_5033748 : Nat := 4983230072969 + 3 ^ 40 * 5033748 * 2
def baseEnd_5033748 : Nat := 861577405869492223833407

theorem tailTrace_5033748 : CollatzResearch.WordTrace tailWord_5033748 prefixEnd_5033748 861577405869492223833407 := by
  unfold tailWord_5033748
  simp only [CollatzResearch.WordTrace]
  refine ⟨91797936283799083279818949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122397248378398777706425265 91797936283799083279818949)
  ·
    refine ⟨17212113053212328114966053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91797936283799083279818949 17212113053212328114966053)
    ·
      refine ⟨3227271197477311521556135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17212113053212328114966053 3227271197477311521556135)
      ·
        refine ⟨4840906796215967282334203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227271197477311521556135 4840906796215967282334203)
        ·
          refine ⟨7261360194323950923501305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840906796215967282334203 7261360194323950923501305)
          ·
            refine ⟨5446020145742963192625979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7261360194323950923501305 5446020145742963192625979)
            ·
              refine ⟨8169030218614444788938969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446020145742963192625979 8169030218614444788938969)
              ·
                refine ⟨6126772663960833591704227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169030218614444788938969 6126772663960833591704227)
                ·
                  refine ⟨9190158995941250387556341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126772663960833591704227 9190158995941250387556341)
                  ·
                    refine ⟨861577405869492223833407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9190158995941250387556341 861577405869492223833407)
                    ·
                      rfl

theorem cell23_5033748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5033748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033748 prefixEnd_5033748 := by exact prefixLift 5033748
  have htrace : WordTrace (prefixWord ++ tailWord_5033748) baseStart_5033748 baseEnd_5033748 := by
    simpa [prefixWord, tailWord_5033748, baseEnd_5033748] using wordTrace_append hprefix tailTrace_5033748
  have hstable : (prefixWord ++ tailWord_5033748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033748).length < 2 ^ (prefixWord ++ tailWord_5033748).sum := by decide
  have hdescent : baseEnd_5033748 < baseStart_5033748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033754 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_5033754 : Nat := 118140960795 + 5033754 * 2 ^ 59
def prefixEnd_5033754 : Nat := 4983230072969 + 3 ^ 40 * 5033754 * 2
def baseEnd_5033754 : Nat := 2584735298492403648025193

theorem tailTrace_5033754 : CollatzResearch.WordTrace tailWord_5033754 prefixEnd_5033754 2584735298492403648025193 := by
  unfold tailWord_5033754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45899022851394107396089079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122397394270384286389570877 45899022851394107396089079)
  ·
    refine ⟨68848534277091161094133619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45899022851394107396089079 68848534277091161094133619)
    ·
      refine ⟨103272801415636741641200429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68848534277091161094133619 103272801415636741641200429)
      ·
        refine ⟨38727300530863778115450161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103272801415636741641200429 38727300530863778115450161)
        ·
          refine ⟨29045475398147833586587621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38727300530863778115450161 29045475398147833586587621)
          ·
            refine ⟨5446026637152718797485179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29045475398147833586587621 5446026637152718797485179)
            ·
              refine ⟨8169039955729078196227769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446026637152718797485179 8169039955729078196227769)
              ·
                refine ⟨6126779966796808647170827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169039955729078196227769 6126779966796808647170827)
                ·
                  refine ⟨9190169950195212970756241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126779966796808647170827 9190169950195212970756241)
                  ·
                    refine ⟨6892627462646409728067181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9190169950195212970756241 6892627462646409728067181)
                    ·
                      refine ⟨2584735298492403648025193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6892627462646409728067181 2584735298492403648025193)
                      ·
                        rfl

theorem cell23_5033754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_5033754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033754 prefixEnd_5033754 := by exact prefixLift 5033754
  have htrace : WordTrace (prefixWord ++ tailWord_5033754) baseStart_5033754 baseEnd_5033754 := by
    simpa [prefixWord, tailWord_5033754, baseEnd_5033754] using wordTrace_append hprefix tailTrace_5033754
  have hstable : (prefixWord ++ tailWord_5033754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033754).length < 2 ^ (prefixWord ++ tailWord_5033754).sum := by decide
  have hdescent : baseEnd_5033754 < baseStart_5033754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033763 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5033763 : Nat := 118140960795 + 5033763 * 2 ^ 59
def prefixEnd_5033763 : Nat := 4983230072969 + 3 ^ 40 * 5033763 * 2
def baseEnd_5033763 : Nat := 2584739919818294112812651

theorem tailTrace_5033763 : CollatzResearch.WordTrace tailWord_5033763 prefixEnd_5033763 2584739919818294112812651 := by
  unfold tailWord_5033763
  simp only [CollatzResearch.WordTrace]
  refine ⟨183596419662543824121433943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122397613108362549414289295 183596419662543824121433943)
  ·
    refine ⟨275394629493815736182150915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183596419662543824121433943 275394629493815736182150915)
    ·
      refine ⟨413091944240723604273226373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275394629493815736182150915 413091944240723604273226373)
      ·
        refine ⟨77454739545135675801229945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 413091944240723604273226373 77454739545135675801229945)
        ·
          refine ⟨58091054658851756850922459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77454739545135675801229945 58091054658851756850922459)
          ·
            refine ⟨87136581988277635276383689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58091054658851756850922459 87136581988277635276383689)
            ·
              refine ⟨65352436491208226457287767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87136581988277635276383689 65352436491208226457287767)
              ·
                refine ⟨98028654736812339685931651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65352436491208226457287767 98028654736812339685931651)
                ·
                  refine ⟨147042982105218509528897477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98028654736812339685931651 147042982105218509528897477)
                  ·
                    refine ⟨27570559144728470536668277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147042982105218509528897477 27570559144728470536668277)
                    ·
                      refine ⟨2584739919818294112812651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27570559144728470536668277 2584739919818294112812651)
                      ·
                        rfl

theorem cell23_5033763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5033763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033763 prefixEnd_5033763 := by exact prefixLift 5033763
  have htrace : WordTrace (prefixWord ++ tailWord_5033763) baseStart_5033763 baseEnd_5033763 := by
    simpa [prefixWord, tailWord_5033763, baseEnd_5033763] using wordTrace_append hprefix tailTrace_5033763
  have hstable : (prefixWord ++ tailWord_5033763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033763).length < 2 ^ (prefixWord ++ tailWord_5033763).sum := by decide
  have hdescent : baseEnd_5033763 < baseStart_5033763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033784 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_5033784 : Nat := 118140960795 + 5033784 * 2 ^ 59
def prefixEnd_5033784 : Nat := 4983230072969 + 3 ^ 40 * 5033784 * 2
def baseEnd_5033784 : Nat := 2584750702912038530650055

theorem tailTrace_5033784 : CollatzResearch.WordTrace tailWord_5033784 prefixEnd_5033784 2584750702912038530650055 := by
  unfold tailWord_5033784
  simp only [CollatzResearch.WordTrace]
  refine ⟨91798592797733872353974203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122398123730311829805298937 91798592797733872353974203)
  ·
    refine ⟨137697889196600808530961305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91798592797733872353974203 137697889196600808530961305)
    ·
      refine ⟨103273416897450606398220979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137697889196600808530961305 103273416897450606398220979)
      ·
        refine ⟨154910125346175909597331469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103273416897450606398220979 154910125346175909597331469)
        ·
          refine ⟨58091297004815966098999301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154910125346175909597331469 58091297004815966098999301)
          ·
            refine ⟨10892118188402993643562369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58091297004815966098999301 10892118188402993643562369)
            ·
              refine ⟨8169088641302245232671777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10892118188402993643562369 8169088641302245232671777)
              ·
                refine ⟨6126816480976683924503833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169088641302245232671777 6126816480976683924503833)
                ·
                  refine ⟨4595112360732512943377875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126816480976683924503833 4595112360732512943377875)
                  ·
                    refine ⟨6892668541098769415066813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595112360732512943377875 6892668541098769415066813)
                    ·
                      refine ⟨2584750702912038530650055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6892668541098769415066813 2584750702912038530650055)
                      ·
                        rfl

theorem cell23_5033784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_5033784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033784 prefixEnd_5033784 := by exact prefixLift 5033784
  have htrace : WordTrace (prefixWord ++ tailWord_5033784) baseStart_5033784 baseEnd_5033784 := by
    simpa [prefixWord, tailWord_5033784, baseEnd_5033784] using wordTrace_append hprefix tailTrace_5033784
  have hstable : (prefixWord ++ tailWord_5033784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033784).length < 2 ^ (prefixWord ++ tailWord_5033784).sum := by decide
  have hdescent : baseEnd_5033784 < baseStart_5033784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033800 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_5033800 : Nat := 118140960795 + 5033800 * 2 ^ 59
def prefixEnd_5033800 : Nat := 4983230072969 + 3 ^ 40 * 5033800 * 2
def baseEnd_5033800 : Nat := 861586306200836822683327

theorem tailTrace_5033800 : CollatzResearch.WordTrace tailWord_5033800 prefixEnd_5033800 861586306200836822683327 := by
  unfold tailWord_5033800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91798884581704889720265427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122398512775606519627020569 91798884581704889720265427)
  ·
    refine ⟨137698326872557334580398141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91798884581704889720265427 137698326872557334580398141)
    ·
      refine ⟨51636872577209000467649303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137698326872557334580398141 51636872577209000467649303)
      ·
        refine ⟨77455308865813500701473955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51636872577209000467649303 77455308865813500701473955)
        ·
          refine ⟨116182963298720251052210933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77455308865813500701473955 116182963298720251052210933)
          ·
            refine ⟨10892152809255023536144775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116182963298720251052210933 10892152809255023536144775)
            ·
              refine ⟨16338229213882535304217163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10892152809255023536144775 16338229213882535304217163)
              ·
                refine ⟨24507343820823802956325745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16338229213882535304217163 24507343820823802956325745)
                ·
                  refine ⟨18380507865617852217244309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24507343820823802956325745 18380507865617852217244309)
                  ·
                    refine ⟨861586306200836822683327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18380507865617852217244309 861586306200836822683327)
                    ·
                      rfl

theorem cell23_5033800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_5033800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033800 prefixEnd_5033800 := by exact prefixLift 5033800
  have htrace : WordTrace (prefixWord ++ tailWord_5033800) baseStart_5033800 baseEnd_5033800 := by
    simpa [prefixWord, tailWord_5033800, baseEnd_5033800] using wordTrace_append hprefix tailTrace_5033800
  have hstable : (prefixWord ++ tailWord_5033800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033800).length < 2 ^ (prefixWord ++ tailWord_5033800).sum := by decide
  have hdescent : baseEnd_5033800 < baseStart_5033800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033828 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_5033828 : Nat := 118140960795 + 5033828 * 2 ^ 59
def prefixEnd_5033828 : Nat := 4983230072969 + 3 ^ 40 * 5033828 * 2
def baseEnd_5033828 : Nat := 2584773296060836358499853

theorem tailTrace_5033828 : CollatzResearch.WordTrace tailWord_5033828 prefixEnd_5033828 2584773296060836358499853 := by
  unfold tailWord_5033828
  simp only [CollatzResearch.WordTrace]
  refine ⟨91799395203654170111275069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122399193604872226815033425 91799395203654170111275069)
  ·
    refine ⟨34424773201370313791728151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91799395203654170111275069 34424773201370313791728151)
    ·
      refine ⟨51637159802055470687592227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34424773201370313791728151 51637159802055470687592227)
      ·
        refine ⟨77455739703083206031388341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51637159802055470687592227 77455739703083206031388341)
        ·
          refine ⟨7261475597164050565442657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77455739703083206031388341 7261475597164050565442657)
          ·
            refine ⟨5446106697873037924081993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7261475597164050565442657 5446106697873037924081993)
            ·
              refine ⟨4084580023404778443061495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5446106697873037924081993 4084580023404778443061495)
              ·
                refine ⟨6126870035107167664592243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084580023404778443061495 6126870035107167664592243)
                ·
                  refine ⟨9190305052660751496888365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126870035107167664592243 9190305052660751496888365)
                  ·
                    refine ⟨3446364394747781811333137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9190305052660751496888365 3446364394747781811333137)
                    ·
                      refine ⟨2584773296060836358499853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446364394747781811333137 2584773296060836358499853)
                      ·
                        rfl

theorem cell23_5033828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_5033828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033828 prefixEnd_5033828 := by exact prefixLift 5033828
  have htrace : WordTrace (prefixWord ++ tailWord_5033828) baseStart_5033828 baseEnd_5033828 := by
    simpa [prefixWord, tailWord_5033828, baseEnd_5033828] using wordTrace_append hprefix tailTrace_5033828
  have hstable : (prefixWord ++ tailWord_5033828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033828).length < 2 ^ (prefixWord ++ tailWord_5033828).sum := by decide
  have hdescent : baseEnd_5033828 < baseStart_5033828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033854 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5033854 : Nat := 118140960795 + 5033854 * 2 ^ 59
def prefixEnd_5033854 : Nat := 4983230072969 + 3 ^ 40 * 5033854 * 2
def baseEnd_5033854 : Nat := 2584786646557853256774733

theorem tailTrace_5033854 : CollatzResearch.WordTrace tailWord_5033854 prefixEnd_5033854 2584786646557853256774733 := by
  unfold tailWord_5033854
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949967338151768332874577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122399825803476097775331077 22949967338151768332874577)
  ·
    refine ⟨17212475503613826249655933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22949967338151768332874577 17212475503613826249655933)
    ·
      refine ⟨6454678313855184843620975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17212475503613826249655933 6454678313855184843620975)
      ·
        refine ⟨9682017470782777265431463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454678313855184843620975 9682017470782777265431463)
        ·
          refine ⟨14523026206174165898147195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9682017470782777265431463 14523026206174165898147195)
          ·
            refine ⟨21784539309261248847220793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14523026206174165898147195 21784539309261248847220793)
            ·
              refine ⟨16338404481945936635415595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21784539309261248847220793 16338404481945936635415595)
              ·
                refine ⟨24507606722918904953123393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16338404481945936635415595 24507606722918904953123393)
                ·
                  refine ⟨18380705042189178714842545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24507606722918904953123393 18380705042189178714842545)
                  ·
                    refine ⟨13785528781641884036131909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18380705042189178714842545 13785528781641884036131909)
                    ·
                      refine ⟨2584786646557853256774733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13785528781641884036131909 2584786646557853256774733)
                      ·
                        rfl

theorem cell23_5033854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5033854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033854 prefixEnd_5033854 := by exact prefixLift 5033854
  have htrace : WordTrace (prefixWord ++ tailWord_5033854) baseStart_5033854 baseEnd_5033854 := by
    simpa [prefixWord, tailWord_5033854, baseEnd_5033854] using wordTrace_append hprefix tailTrace_5033854
  have hstable : (prefixWord ++ tailWord_5033854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033854).length < 2 ^ (prefixWord ++ tailWord_5033854).sum := by decide
  have hdescent : baseEnd_5033854 < baseStart_5033854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033860 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_5033860 : Nat := 118140960795 + 5033860 * 2 ^ 59
def prefixEnd_5033860 : Nat := 4983230072969 + 3 ^ 40 * 5033860 * 2
def baseEnd_5033860 : Nat := 861596575813926744433235

theorem tailTrace_5033860 : CollatzResearch.WordTrace tailWord_5033860 prefixEnd_5033860 861596575813926744433235 := by
  unfold tailWord_5033860
  simp only [CollatzResearch.WordTrace]
  refine ⟨91799978771596204843857517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122399971695461606458476689 91799978771596204843857517)
  ·
    refine ⟨34424992039348576816446569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91799978771596204843857517 34424992039348576816446569)
    ·
      refine ⟨25818744029511432612334927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34424992039348576816446569 25818744029511432612334927)
      ·
        refine ⟨38728116044267148918502391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25818744029511432612334927 38728116044267148918502391)
        ·
          refine ⟨58092174066400723377753587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38728116044267148918502391 58092174066400723377753587)
          ·
            refine ⟨87138261099601085066630381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58092174066400723377753587 87138261099601085066630381)
            ·
              refine ⟨32676847912350406899986393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87138261099601085066630381 32676847912350406899986393)
              ·
                refine ⟨24507635934262805174989795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32676847912350406899986393 24507635934262805174989795)
                ·
                  refine ⟨36761453901394207762484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24507635934262805174989795 36761453901394207762484693)
                  ·
                    refine ⟨861596575813926744433235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36761453901394207762484693 861596575813926744433235)
                    ·
                      rfl

theorem cell23_5033860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_5033860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033860 prefixEnd_5033860 := by exact prefixLift 5033860
  have htrace : WordTrace (prefixWord ++ tailWord_5033860) baseStart_5033860 baseEnd_5033860 := by
    simpa [prefixWord, tailWord_5033860, baseEnd_5033860] using wordTrace_append hprefix tailTrace_5033860
  have hstable : (prefixWord ++ tailWord_5033860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033860).length < 2 ^ (prefixWord ++ tailWord_5033860).sum := by decide
  have hdescent : baseEnd_5033860 < baseStart_5033860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033897 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 4, 2]
def baseStart_5033897 : Nat := 118140960795 + 5033897 * 2 ^ 59
def prefixEnd_5033897 : Nat := 4983230072969 + 3 ^ 40 * 5033897 * 2
def baseEnd_5033897 : Nat := 2584808726225996588537035

theorem tailTrace_5033897 : CollatzResearch.WordTrace tailWord_5033897 prefixEnd_5033897 2584808726225996588537035 := by
  unfold tailWord_5033897
  simp only [CollatzResearch.WordTrace]
  refine ⟨183601307044058365006811945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122400871362705576671207963 183601307044058365006811945)
  ·
    refine ⟨137700980283043773755108959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183601307044058365006811945 137700980283043773755108959)
    ·
      refine ⟨206551470424565660632663439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137700980283043773755108959 206551470424565660632663439)
      ·
        refine ⟨309827205636848490948995159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206551470424565660632663439 309827205636848490948995159)
        ·
          refine ⟨464740808455272736423492739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309827205636848490948995159 464740808455272736423492739)
          ·
            refine ⟨697111212682909104635239109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464740808455272736423492739 697111212682909104635239109)
            ·
              refine ⟨130708352378045457119107333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 697111212682909104635239109 130708352378045457119107333)
              ·
                refine ⟨24507816070883523209832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130708352378045457119107333 24507816070883523209832625)
                ·
                  refine ⟨18380862053162642407374469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24507816070883523209832625 18380862053162642407374469)
                  ·
                    refine ⟨3446411634967995451382713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18380862053162642407374469 3446411634967995451382713)
                    ·
                      refine ⟨2584808726225996588537035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446411634967995451382713 2584808726225996588537035)
                      ·
                        rfl

theorem cell23_5033897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 4, 2].length) (baseStart_5033897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033897 prefixEnd_5033897 := by exact prefixLift 5033897
  have htrace : WordTrace (prefixWord ++ tailWord_5033897) baseStart_5033897 baseEnd_5033897 := by
    simpa [prefixWord, tailWord_5033897, baseEnd_5033897] using wordTrace_append hprefix tailTrace_5033897
  have hstable : (prefixWord ++ tailWord_5033897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033897).length < 2 ^ (prefixWord ++ tailWord_5033897).sum := by decide
  have hdescent : baseEnd_5033897 < baseStart_5033897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033934 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_5033934 : Nat := 118140960795 + 5033934 * 2 ^ 59
def prefixEnd_5033934 : Nat := 4983230072969 + 3 ^ 40 * 5033934 * 2
def baseEnd_5033934 : Nat := 2584827725010212943774365

theorem tailTrace_5033934 : CollatzResearch.WordTrace tailWord_5033934 prefixEnd_5033934 2584827725010212943774365 := by
  unfold tailWord_5033934
  simp only [CollatzResearch.WordTrace]
  refine ⟨22950332068115540040738607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122401771029949546883939237 22950332068115540040738607)
  ·
    refine ⟨34425498102173310061107911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22950332068115540040738607 34425498102173310061107911)
    ·
      refine ⟨51638247153259965091661867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34425498102173310061107911 51638247153259965091661867)
      ·
        refine ⟨77457370729889947637492801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51638247153259965091661867 77457370729889947637492801)
        ·
          refine ⟨58093028047417460728119601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77457370729889947637492801 58093028047417460728119601)
          ·
            refine ⟨43569771035563095546089701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58093028047417460728119601 43569771035563095546089701)
            ·
              refine ⟨8169332069168080414891819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43569771035563095546089701 8169332069168080414891819)
              ·
                refine ⟨12253998103752120622337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169332069168080414891819 12253998103752120622337729)
                ·
                  refine ⟨9190498577814090466753297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12253998103752120622337729 9190498577814090466753297)
                  ·
                    refine ⟨6892873933360567850064973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9190498577814090466753297 6892873933360567850064973)
                    ·
                      refine ⟨2584827725010212943774365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6892873933360567850064973 2584827725010212943774365)
                      ·
                        rfl

theorem cell23_5033934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_5033934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033934 prefixEnd_5033934 := by exact prefixLift 5033934
  have htrace : WordTrace (prefixWord ++ tailWord_5033934) baseStart_5033934 baseEnd_5033934 := by
    simpa [prefixWord, tailWord_5033934, baseEnd_5033934] using wordTrace_append hprefix tailTrace_5033934
  have hstable : (prefixWord ++ tailWord_5033934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033934).length < 2 ^ (prefixWord ++ tailWord_5033934).sum := by decide
  have hdescent : baseEnd_5033934 < baseStart_5033934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033991 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_5033991 : Nat := 118140960795 + 5033991 * 2 ^ 59
def prefixEnd_5033991 : Nat := 4983230072969 + 3 ^ 40 * 5033991 * 2
def baseEnd_5033991 : Nat := 2584856993407519220761603

theorem tailTrace_5033991 : CollatzResearch.WordTrace tailWord_5033991 prefixEnd_5033991 2584856993407519220761603 := by
  unfold tailWord_5033991
  simp only [CollatzResearch.WordTrace]
  refine ⟨183604735505717819060733827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122403157003811879373822551 183604735505717819060733827)
  ·
    refine ⟨275407103258576728591100741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183604735505717819060733827 275407103258576728591100741)
    ·
      refine ⟨51638831860983136610831389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275407103258576728591100741 51638831860983136610831389)
      ·
        refine ⟨19364561947868676229061771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51638831860983136610831389 19364561947868676229061771)
        ·
          refine ⟨29046842921803014343592657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19364561947868676229061771 29046842921803014343592657)
          ·
            refine ⟨21785132191352260757694493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29046842921803014343592657 21785132191352260757694493)
            ·
              refine ⟨8169424571757097784135435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21785132191352260757694493 8169424571757097784135435)
              ·
                refine ⟨12254136857635646676203153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169424571757097784135435 12254136857635646676203153)
                ·
                  refine ⟨9190602643226735007152365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12254136857635646676203153 9190602643226735007152365)
                  ·
                    refine ⟨3446475991210025627682137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9190602643226735007152365 3446475991210025627682137)
                    ·
                      refine ⟨2584856993407519220761603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446475991210025627682137 2584856993407519220761603)
                      ·
                        rfl

theorem cell23_5033991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_5033991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033991 prefixEnd_5033991 := by exact prefixLift 5033991
  have htrace : WordTrace (prefixWord ++ tailWord_5033991) baseStart_5033991 baseEnd_5033991 := by
    simpa [prefixWord, tailWord_5033991, baseEnd_5033991] using wordTrace_append hprefix tailTrace_5033991
  have hstable : (prefixWord ++ tailWord_5033991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033991).length < 2 ^ (prefixWord ++ tailWord_5033991).sum := by decide
  have hdescent : baseEnd_5033991 < baseStart_5033991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5033998 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5033998 : Nat := 118140960795 + 5033998 * 2 ^ 59
def prefixEnd_5033998 : Nat := 4983230072969 + 3 ^ 40 * 5033998 * 2
def baseEnd_5033998 : Nat := 2584860587772100693374071

theorem tailTrace_5033998 : CollatzResearch.WordTrace tailWord_5033998 prefixEnd_5033998 2584860587772100693374071 := by
  unfold tailWord_5033998
  simp only [CollatzResearch.WordTrace]
  refine ⟨22950623852086557407029831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122403327211128306170825765 22950623852086557407029831)
  ·
    refine ⟨34425935778129836110544747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22950623852086557407029831 34425935778129836110544747)
    ·
      refine ⟨51638903667194754165817121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34425935778129836110544747 51638903667194754165817121)
      ·
        refine ⟨38729177750396065624362841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51638903667194754165817121 38729177750396065624362841)
        ·
          refine ⟨29046883312797049218272131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38729177750396065624362841 29046883312797049218272131)
          ·
            refine ⟨43570324969195573827408197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29046883312797049218272131 43570324969195573827408197)
            ·
              refine ⟨8169435931724170092639037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43570324969195573827408197 8169435931724170092639037)
              ·
                refine ⟨3063538474396563784739639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8169435931724170092639037 3063538474396563784739639)
                ·
                  refine ⟨4595307711594845677109459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063538474396563784739639 4595307711594845677109459)
                  ·
                    refine ⟨6892961567392268515664189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595307711594845677109459 6892961567392268515664189)
                    ·
                      refine ⟨2584860587772100693374071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6892961567392268515664189 2584860587772100693374071)
                      ·
                        rfl

theorem cell23_5033998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5033998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5033998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5033998 prefixEnd_5033998 := by exact prefixLift 5033998
  have htrace : WordTrace (prefixWord ++ tailWord_5033998) baseStart_5033998 baseEnd_5033998 := by
    simpa [prefixWord, tailWord_5033998, baseEnd_5033998] using wordTrace_append hprefix tailTrace_5033998
  have hstable : (prefixWord ++ tailWord_5033998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5033998).length < 2 ^ (prefixWord ++ tailWord_5033998).sum := by decide
  have hdescent : baseEnd_5033998 < baseStart_5033998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5033998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034021 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_5034021 : Nat := 118140960795 + 5034021 * 2 ^ 59
def prefixEnd_5034021 : Nat := 4983230072969 + 3 ^ 40 * 5034021 * 2
def baseEnd_5034021 : Nat := 2584872397827154103386465

theorem tailTrace_5034021 : CollatzResearch.WordTrace tailWord_5034021 prefixEnd_5034021 2584872397827154103386465 := by
  unfold tailWord_5034021
  simp only [CollatzResearch.WordTrace]
  refine ⟨183605829695609134184325917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122403886463739422789550611 183605829695609134184325917)
  ·
    refine ⟨68852186135853425319122219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183605829695609134184325917 68852186135853425319122219)
    ·
      refine ⟨103278279203780137978683329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68852186135853425319122219 103278279203780137978683329)
      ·
        refine ⟨77458709402835103484012497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103278279203780137978683329 77458709402835103484012497)
        ·
          refine ⟨58094032052126327613009373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77458709402835103484012497 58094032052126327613009373)
          ·
            refine ⟨21785262019547372854878515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58094032052126327613009373 21785262019547372854878515)
            ·
              refine ⟨32677893029321059282317773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21785262019547372854878515 32677893029321059282317773)
              ·
                refine ⟨12254209885995397230869165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32677893029321059282317773 12254209885995397230869165)
                ·
                  refine ⟨4595328707248273961575937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12254209885995397230869165 4595328707248273961575937)
                  ·
                    refine ⟨3446496530436205471181953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595328707248273961575937 3446496530436205471181953)
                    ·
                      refine ⟨2584872397827154103386465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446496530436205471181953 2584872397827154103386465)
                      ·
                        rfl

theorem cell23_5034021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_5034021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034021 prefixEnd_5034021 := by exact prefixLift 5034021
  have htrace : WordTrace (prefixWord ++ tailWord_5034021) baseStart_5034021 baseEnd_5034021 := by
    simpa [prefixWord, tailWord_5034021, baseEnd_5034021] using wordTrace_append hprefix tailTrace_5034021
  have hstable : (prefixWord ++ tailWord_5034021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034021).length < 2 ^ (prefixWord ++ tailWord_5034021).sum := by decide
  have hdescent : baseEnd_5034021 < baseStart_5034021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034034 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5034034 : Nat := 118140960795 + 5034034 * 2 ^ 59
def prefixEnd_5034034 : Nat := 4983230072969 + 3 ^ 40 * 5034034 * 2
def baseEnd_5034034 : Nat := 2584879073075662552523905

theorem tailTrace_5034034 : CollatzResearch.WordTrace tailWord_5034034 prefixEnd_5034034 2584879073075662552523905 := by
  unfold tailWord_5034034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45901575961140509351137289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122404202563041358269699437 45901575961140509351137289)
  ·
    refine ⟨34426181970855382013352967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45901575961140509351137289 34426181970855382013352967)
    ·
      refine ⟨51639272956283073020029451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34426181970855382013352967 51639272956283073020029451)
      ·
        refine ⟨77458909434424609530044177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51639272956283073020029451 77458909434424609530044177)
        ·
          refine ⟨58094182075818457147533133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77458909434424609530044177 58094182075818457147533133)
          ·
            refine ⟨21785318278431921430324925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58094182075818457147533133 21785318278431921430324925)
            ·
              refine ⟨8169494354411970536371847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21785318278431921430324925 8169494354411970536371847)
              ·
                refine ⟨12254241531617955804557771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169494354411970536371847 12254241531617955804557771)
                ·
                  refine ⟨18381362297426933706836657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12254241531617955804557771 18381362297426933706836657)
                  ·
                    refine ⟨13786021723070200280127493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18381362297426933706836657 13786021723070200280127493)
                    ·
                      refine ⟨2584879073075662552523905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13786021723070200280127493 2584879073075662552523905)
                      ·
                        rfl

theorem cell23_5034034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5034034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034034 prefixEnd_5034034 := by exact prefixLift 5034034
  have htrace : WordTrace (prefixWord ++ tailWord_5034034) baseStart_5034034 baseEnd_5034034 := by
    simpa [prefixWord, tailWord_5034034, baseEnd_5034034] using wordTrace_append hprefix tailTrace_5034034
  have hstable : (prefixWord ++ tailWord_5034034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034034).length < 2 ^ (prefixWord ++ tailWord_5034034).sum := by decide
  have hdescent : baseEnd_5034034 < baseStart_5034034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034038 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_5034038 : Nat := 118140960795 + 5034038 * 2 ^ 59
def prefixEnd_5034038 : Nat := 4983230072969 + 3 ^ 40 * 5034038 * 2
def baseEnd_5034038 : Nat := 2584881126998280536873887

theorem tailTrace_5034038 : CollatzResearch.WordTrace tailWord_5034038 prefixEnd_5034038 2584881126998280536873887 := by
  unfold tailWord_5034038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475403108534221630480923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122404299824365030725129845 11475403108534221630480923)
  ·
    refine ⟨17213104662801332445721385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475403108534221630480923 17213104662801332445721385)
    ·
      refine ⟨12909828497100999334291039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17213104662801332445721385 12909828497100999334291039)
      ·
        refine ⟨19364742745651499001436559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12909828497100999334291039 19364742745651499001436559)
        ·
          refine ⟨29047114118477248502154839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19364742745651499001436559 29047114118477248502154839)
          ·
            refine ⟨43570671177715872753232259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29047114118477248502154839 43570671177715872753232259)
            ·
              refine ⟨65356006766573809129848389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43570671177715872753232259 65356006766573809129848389)
              ·
                refine ⟨12254251268732589211846573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65356006766573809129848389 12254251268732589211846573)
                ·
                  refine ⟨4595344225774720954442465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12254251268732589211846573 4595344225774720954442465)
                  ·
                    refine ⟨3446508169331040715831849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595344225774720954442465 3446508169331040715831849)
                    ·
                      refine ⟨2584881126998280536873887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446508169331040715831849 2584881126998280536873887)
                      ·
                        rfl

theorem cell23_5034038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_5034038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034038 prefixEnd_5034038 := by exact prefixLift 5034038
  have htrace : WordTrace (prefixWord ++ tailWord_5034038) baseStart_5034038 baseEnd_5034038 := by
    simpa [prefixWord, tailWord_5034038, baseEnd_5034038] using wordTrace_append hprefix tailTrace_5034038
  have hstable : (prefixWord ++ tailWord_5034038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034038).length < 2 ^ (prefixWord ++ tailWord_5034038).sum := by decide
  have hdescent : baseEnd_5034038 < baseStart_5034038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034064 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2]
def baseStart_5034064 : Nat := 118140960795 + 5034064 * 2 ^ 59
def prefixEnd_5034064 : Nat := 4983230072969 + 3 ^ 40 * 5034064 * 2
def baseEnd_5034064 : Nat := 2584894477495297435148767

theorem tailTrace_5034064 : CollatzResearch.WordTrace tailWord_5034064 prefixEnd_5034064 2584894477495297435148767 := by
  unfold tailWord_5034064
  simp only [CollatzResearch.WordTrace]
  refine ⟨91803699017226676264070623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122404932022968901685427497 91803699017226676264070623)
  ·
    refine ⟨137705548525840014396105935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91803699017226676264070623 137705548525840014396105935)
    ·
      refine ⟨206558322788760021594158903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137705548525840014396105935 206558322788760021594158903)
      ·
        refine ⟨309837484183140032391238355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206558322788760021594158903 309837484183140032391238355)
        ·
          refine ⟨464756226274710048586857533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309837484183140032391238355 464756226274710048586857533)
          ·
            refine ⟨174283584853016268220071575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464756226274710048586857533 174283584853016268220071575)
            ·
              refine ⟨261425377279524402330107363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174283584853016268220071575 261425377279524402330107363)
              ·
                refine ⟨392138065919286603495161045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261425377279524402330107363 392138065919286603495161045)
                ·
                  refine ⟨9190735919983279769417837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 392138065919286603495161045 9190735919983279769417837)
                  ·
                    refine ⟨3446525969993729913531689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9190735919983279769417837 3446525969993729913531689)
                    ·
                      refine ⟨2584894477495297435148767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446525969993729913531689 2584894477495297435148767)
                      ·
                        rfl

theorem cell23_5034064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2].length) (baseStart_5034064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034064 prefixEnd_5034064 := by exact prefixLift 5034064
  have htrace : WordTrace (prefixWord ++ tailWord_5034064) baseStart_5034064 baseEnd_5034064 := by
    simpa [prefixWord, tailWord_5034064, baseEnd_5034064] using wordTrace_append hprefix tailTrace_5034064
  have hstable : (prefixWord ++ tailWord_5034064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034064).length < 2 ^ (prefixWord ++ tailWord_5034064).sum := by decide
  have hdescent : baseEnd_5034064 < baseStart_5034064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034078 : List Nat := [4, 4, 1, 1, 2, 1, 2, 8]
def baseStart_5034078 : Nat := 118140960795 + 5034078 * 2 ^ 59
def prefixEnd_5034078 : Nat := 4983230072969 + 3 ^ 40 * 5034078 * 2
def baseEnd_5034078 : Nat := 95737098749054088161989

theorem tailTrace_5034078 : CollatzResearch.WordTrace tailWord_5034078 prefixEnd_5034078 95737098749054088161989 := by
  unfold tailWord_5034078
  simp only [CollatzResearch.WordTrace]
  refine ⟨22950988582050329114893861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122405272437601755279433925 22950988582050329114893861)
  ·
    refine ⟨4303310359134436709042599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22950988582050329114893861 4303310359134436709042599)
    ·
      refine ⟨6454965538701655063563899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303310359134436709042599 6454965538701655063563899)
      ·
        refine ⟨9682448308052482595345849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454965538701655063563899 9682448308052482595345849)
        ·
          refine ⟨7261836231039361946509387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9682448308052482595345849 7261836231039361946509387)
          ·
            refine ⟨10892754346559042919764081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261836231039361946509387 10892754346559042919764081)
            ·
              refine ⟨8169565759919282189823061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10892754346559042919764081 8169565759919282189823061)
              ·
                refine ⟨95737098749054088161989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8169565759919282189823061 95737098749054088161989)
                ·
                  rfl

theorem cell23_5034078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_5034078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034078 prefixEnd_5034078 := by exact prefixLift 5034078
  have htrace : WordTrace (prefixWord ++ tailWord_5034078) baseStart_5034078 baseEnd_5034078 := by
    simpa [prefixWord, tailWord_5034078, baseEnd_5034078] using wordTrace_append hprefix tailTrace_5034078
  have hstable : (prefixWord ++ tailWord_5034078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034078).length < 2 ^ (prefixWord ++ tailWord_5034078).sum := by decide
  have hdescent : baseEnd_5034078 < baseStart_5034078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034082 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5034082 : Nat := 118140960795 + 5034082 * 2 ^ 59
def prefixEnd_5034082 : Nat := 4983230072969 + 3 ^ 40 * 5034082 * 2
def baseEnd_5034082 : Nat := 861634573382359454907895

theorem tailTrace_5034082 : CollatzResearch.WordTrace tailWord_5034082 prefixEnd_5034082 861634573382359454907895 := by
  unfold tailWord_5034082
  simp only [CollatzResearch.WordTrace]
  refine ⟨45902013637097035400574125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122405369698925427734864333 45902013637097035400574125)
  ·
    refine ⟨17213255113911388275215297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45902013637097035400574125 17213255113911388275215297)
    ·
      refine ⟨12909941335433541206411473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17213255113911388275215297 12909941335433541206411473)
      ·
        refine ⟨9682456001575155904808605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12909941335433541206411473 9682456001575155904808605)
        ·
          refine ⟨3630921000590683464303227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9682456001575155904808605 3630921000590683464303227)
          ·
            refine ⟨5446381500886025196454841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630921000590683464303227 5446381500886025196454841)
            ·
              refine ⟨4084786125664518897341131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5446381500886025196454841 4084786125664518897341131)
              ·
                refine ⟨6127179188496778346011697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084786125664518897341131 6127179188496778346011697)
                ·
                  refine ⟨4595384391372583759508773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6127179188496778346011697 4595384391372583759508773)
                  ·
                    refine ⟨861634573382359454907895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4595384391372583759508773 861634573382359454907895)
                    ·
                      rfl

theorem cell23_5034082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5034082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034082 prefixEnd_5034082 := by exact prefixLift 5034082
  have htrace : WordTrace (prefixWord ++ tailWord_5034082) baseStart_5034082 baseEnd_5034082 := by
    simpa [prefixWord, tailWord_5034082, baseEnd_5034082] using wordTrace_append hprefix tailTrace_5034082
  have hstable : (prefixWord ++ tailWord_5034082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034082).length < 2 ^ (prefixWord ++ tailWord_5034082).sum := by decide
  have hdescent : baseEnd_5034082 < baseStart_5034082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034087 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 8]
def baseStart_5034087 : Nat := 118140960795 + 5034087 * 2 ^ 59
def prefixEnd_5034087 : Nat := 4983230072969 + 3 ^ 40 * 5034087 * 2
def baseEnd_5034087 : Nat := 861635429183450281720387

theorem tailTrace_5034087 : CollatzResearch.WordTrace tailWord_5034087 prefixEnd_5034087 861635429183450281720387 := by
  unfold tailWord_5034087
  simp only [CollatzResearch.WordTrace]
  refine ⟨183608236913370027456228515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122405491275580018304152343 183608236913370027456228515)
  ·
    refine ⟨275412355370055041184342773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183608236913370027456228515 275412355370055041184342773)
    ·
      refine ⟨25819908315942660111032135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275412355370055041184342773 25819908315942660111032135)
      ·
        refine ⟨38729862473913990166548203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25819908315942660111032135 38729862473913990166548203)
        ·
          refine ⟨58094793710870985249822305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38729862473913990166548203 58094793710870985249822305)
          ·
            refine ⟨43571095283153238937366729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58094793710870985249822305 43571095283153238937366729)
            ·
              refine ⟨32678321462364929203025047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43571095283153238937366729 32678321462364929203025047)
              ·
                refine ⟨49017482193547393804537571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32678321462364929203025047 49017482193547393804537571)
                ·
                  refine ⟨73526223290321090706806357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49017482193547393804537571 73526223290321090706806357)
                  ·
                    refine ⟨861635429183450281720387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73526223290321090706806357 861635429183450281720387)
                    ·
                      rfl

theorem cell23_5034087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_5034087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034087 prefixEnd_5034087 := by exact prefixLift 5034087
  have htrace : WordTrace (prefixWord ++ tailWord_5034087) baseStart_5034087 baseEnd_5034087 := by
    simpa [prefixWord, tailWord_5034087, baseEnd_5034087] using wordTrace_append hprefix tailTrace_5034087
  have hstable : (prefixWord ++ tailWord_5034087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034087).length < 2 ^ (prefixWord ++ tailWord_5034087).sum := by decide
  have hdescent : baseEnd_5034087 < baseStart_5034087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034097 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_5034097 : Nat := 118140960795 + 5034097 * 2 ^ 59
def prefixEnd_5034097 : Nat := 4983230072969 + 3 ^ 40 * 5034097 * 2
def baseEnd_5034097 : Nat := 2584911422356895806036115

theorem tailTrace_5034097 : CollatzResearch.WordTrace tailWord_5034097 prefixEnd_5034097 2584911422356895806036115 := by
  unfold tailWord_5034097
  simp only [CollatzResearch.WordTrace]
  refine ⟨183608601643333799164092545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122405734428889199442728363 183608601643333799164092545)
  ·
    refine ⟨137706451232500349373069409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183608601643333799164092545 137706451232500349373069409)
    ·
      refine ⟨103279838424375262029802057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137706451232500349373069409 103279838424375262029802057)
      ·
        refine ⟨77459878818281446522351543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103279838424375262029802057 77459878818281446522351543)
        ·
          refine ⟨116189818227422169783527315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77459878818281446522351543 116189818227422169783527315)
          ·
            refine ⟨174284727341133254675290973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116189818227422169783527315 174284727341133254675290973)
            ·
              refine ⟨65356772752924970503234115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174284727341133254675290973 65356772752924970503234115)
              ·
                refine ⟨98035159129387455754851173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65356772752924970503234115 98035159129387455754851173)
                ·
                  refine ⟨18381592336760147954034595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98035159129387455754851173 18381592336760147954034595)
                  ·
                    refine ⟨27572388505140221931051893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18381592336760147954034595 27572388505140221931051893)
                    ·
                      refine ⟨2584911422356895806036115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27572388505140221931051893 2584911422356895806036115)
                      ·
                        rfl

theorem cell23_5034097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_5034097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034097 prefixEnd_5034097 := by exact prefixLift 5034097
  have htrace : WordTrace (prefixWord ++ tailWord_5034097) baseStart_5034097 baseEnd_5034097 := by
    simpa [prefixWord, tailWord_5034097, baseEnd_5034097] using wordTrace_append hprefix tailTrace_5034097
  have hstable : (prefixWord ++ tailWord_5034097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034097).length < 2 ^ (prefixWord ++ tailWord_5034097).sum := by decide
  have hdescent : baseEnd_5034097 < baseStart_5034097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034098 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5034098 : Nat := 118140960795 + 5034098 * 2 ^ 59
def prefixEnd_5034098 : Nat := 4983230072969 + 3 ^ 40 * 5034098 * 2
def baseEnd_5034098 : Nat := 2584911935837550302123611

theorem tailTrace_5034098 : CollatzResearch.WordTrace tailWord_5034098 prefixEnd_5034098 2584911935837550302123611 := by
  unfold tailWord_5034098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45902159529082544083719737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122405758744220117556585965 45902159529082544083719737)
  ·
    refine ⟨34426619646811908062789803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45902159529082544083719737 34426619646811908062789803)
    ·
      refine ⟨51639929470217862094184705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34426619646811908062789803 51639929470217862094184705)
      ·
        refine ⟨38729947102663396570638529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51639929470217862094184705 38729947102663396570638529)
        ·
          refine ⟨29047460326997547427978897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38729947102663396570638529 29047460326997547427978897)
          ·
            refine ⟨21785595245248160570984173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29047460326997547427978897 21785595245248160570984173)
            ·
              refine ⟨8169598216968060214119065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21785595245248160570984173 8169598216968060214119065)
              ·
                refine ⟨6127198662726045160589299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169598216968060214119065 6127198662726045160589299)
                ·
                  refine ⟨9190797994089067740883949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127198662726045160589299 9190797994089067740883949)
                  ·
                    refine ⟨3446549247783400402831481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9190797994089067740883949 3446549247783400402831481)
                    ·
                      refine ⟨2584911935837550302123611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446549247783400402831481 2584911935837550302123611)
                      ·
                        rfl

theorem cell23_5034098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5034098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034098 prefixEnd_5034098 := by exact prefixLift 5034098
  have htrace : WordTrace (prefixWord ++ tailWord_5034098) baseStart_5034098 baseEnd_5034098 := by
    simpa [prefixWord, tailWord_5034098, baseEnd_5034098] using wordTrace_append hprefix tailTrace_5034098
  have hstable : (prefixWord ++ tailWord_5034098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034098).length < 2 ^ (prefixWord ++ tailWord_5034098).sum := by decide
  have hdescent : baseEnd_5034098 < baseStart_5034098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034107 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_5034107 : Nat := 118140960795 + 5034107 * 2 ^ 59
def prefixEnd_5034107 : Nat := 4983230072969 + 3 ^ 40 * 5034107 * 2
def baseEnd_5034107 : Nat := 2584916557163440766911069

theorem tailTrace_5034107 : CollatzResearch.WordTrace tailWord_5034107 prefixEnd_5034107 2584916557163440766911069 := by
  unfold tailWord_5034107
  simp only [CollatzResearch.WordTrace]
  refine ⟨183608966373297570871956575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122405977582198380581304383 183608966373297570871956575)
  ·
    refine ⟨275413449559946356307934863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183608966373297570871956575 275413449559946356307934863)
    ·
      refine ⟨413120174339919534461902295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275413449559946356307934863 413120174339919534461902295)
      ·
        refine ⟨619680261509879301692853443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413120174339919534461902295 619680261509879301692853443)
        ·
          refine ⟨929520392264818952539280165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619680261509879301692853443 929520392264818952539280165)
          ·
            refine ⟨174285073549653553601115031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 929520392264818952539280165 174285073549653553601115031)
            ·
              refine ⟨261427610324480330401672547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174285073549653553601115031 261427610324480330401672547)
              ·
                refine ⟨392141415486720495602508821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261427610324480330401672547 392141415486720495602508821)
                ·
                  refine ⟨18381628850940023231367601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 392141415486720495602508821 18381628850940023231367601)
                  ·
                    refine ⟨13786221638205017423525701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18381628850940023231367601 13786221638205017423525701)
                    ·
                      refine ⟨2584916557163440766911069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13786221638205017423525701 2584916557163440766911069)
                      ·
                        rfl

theorem cell23_5034107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_5034107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034107 prefixEnd_5034107 := by exact prefixLift 5034107
  have htrace : WordTrace (prefixWord ++ tailWord_5034107) baseStart_5034107 baseEnd_5034107 := by
    simpa [prefixWord, tailWord_5034107, baseEnd_5034107] using wordTrace_append hprefix tailTrace_5034107
  have hstable : (prefixWord ++ tailWord_5034107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034107).length < 2 ^ (prefixWord ++ tailWord_5034107).sum := by decide
  have hdescent : baseEnd_5034107 < baseStart_5034107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034128 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2]
def baseStart_5034128 : Nat := 118140960795 + 5034128 * 2 ^ 59
def prefixEnd_5034128 : Nat := 4983230072969 + 3 ^ 40 * 5034128 * 2
def baseEnd_5034128 : Nat := 2584927340257185184748473

theorem tailTrace_5034128 : CollatzResearch.WordTrace tailWord_5034128 prefixEnd_5034128 2584927340257185184748473 := by
  unfold tailWord_5034128
  simp only [CollatzResearch.WordTrace]
  refine ⟨91804866153110745729235519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122406488204147660972314025 91804866153110745729235519)
  ·
    refine ⟨137707299229666118593853279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91804866153110745729235519 137707299229666118593853279)
    ·
      refine ⟨206560948844499177890779919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137707299229666118593853279 206560948844499177890779919)
      ·
        refine ⟨309841423266748766836169879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206560948844499177890779919 309841423266748766836169879)
        ·
          refine ⟨464762134900123150254254819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309841423266748766836169879 464762134900123150254254819)
          ·
            refine ⟨697143202350184725381382229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464762134900123150254254819 697143202350184725381382229)
            ·
              refine ⟨8169646902541227250563073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 697143202350184725381382229 8169646902541227250563073)
              ·
                refine ⟨6127235176905920437922305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169646902541227250563073 6127235176905920437922305)
                ·
                  refine ⟨4595426382679440328441729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6127235176905920437922305 4595426382679440328441729)
                  ·
                    refine ⟨3446569787009580246331297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595426382679440328441729 3446569787009580246331297)
                    ·
                      refine ⟨2584927340257185184748473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446569787009580246331297 2584927340257185184748473)
                      ·
                        rfl

theorem cell23_5034128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2].length) (baseStart_5034128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034128 prefixEnd_5034128 := by exact prefixLift 5034128
  have htrace : WordTrace (prefixWord ++ tailWord_5034128) baseStart_5034128 baseEnd_5034128 := by
    simpa [prefixWord, tailWord_5034128, baseEnd_5034128] using wordTrace_append hprefix tailTrace_5034128
  have hstable : (prefixWord ++ tailWord_5034128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034128).length < 2 ^ (prefixWord ++ tailWord_5034128).sum := by decide
  have hdescent : baseEnd_5034128 < baseStart_5034128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034144 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_5034144 : Nat := 118140960795 + 5034144 * 2 ^ 59
def prefixEnd_5034144 : Nat := 4983230072969 + 3 ^ 40 * 5034144 * 2
def baseEnd_5034144 : Nat := 2584935555947657122148399

theorem tailTrace_5034144 : CollatzResearch.WordTrace tailWord_5034144 prefixEnd_5034144 2584935555947657122148399 := by
  unfold tailWord_5034144
  simp only [CollatzResearch.WordTrace]
  refine ⟨91805157937081763095526743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122406877249442350794035657 91805157937081763095526743)
  ·
    refine ⟨137707736905622644643290115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91805157937081763095526743 137707736905622644643290115)
    ·
      refine ⟨206561605358433966964935173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137707736905622644643290115 206561605358433966964935173)
      ·
        refine ⟨38730301004706368805925345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206561605358433966964935173 38730301004706368805925345)
        ·
          refine ⟨29047725753529776604444009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38730301004706368805925345 29047725753529776604444009)
          ·
            refine ⟨21785794315147332453333007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29047725753529776604444009 21785794315147332453333007)
            ·
              refine ⟨32678691472720998679999511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21785794315147332453333007 32678691472720998679999511)
              ·
                refine ⟨49018037209081498019999267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32678691472720998679999511 49018037209081498019999267)
                ·
                  refine ⟨73527055813622247029998901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49018037209081498019999267 73527055813622247029998901)
                  ·
                    refine ⟨6893161482527085659062397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73527055813622247029998901 6893161482527085659062397)
                    ·
                      refine ⟨2584935555947657122148399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6893161482527085659062397 2584935555947657122148399)
                      ·
                        rfl

theorem cell23_5034144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_5034144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034144 prefixEnd_5034144 := by exact prefixLift 5034144
  have htrace : WordTrace (prefixWord ++ tailWord_5034144) baseStart_5034144 baseEnd_5034144 := by
    simpa [prefixWord, tailWord_5034144, baseEnd_5034144] using wordTrace_append hprefix tailTrace_5034144
  have hstable : (prefixWord ++ tailWord_5034144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034144).length < 2 ^ (prefixWord ++ tailWord_5034144).sum := by decide
  have hdescent : baseEnd_5034144 < baseStart_5034144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034151 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 7]
def baseStart_5034151 : Nat := 118140960795 + 5034151 * 2 ^ 59
def prefixEnd_5034151 : Nat := 4983230072969 + 3 ^ 40 * 5034151 * 2
def baseEnd_5034151 : Nat := 287215461145804288306763

theorem tailTrace_5034151 : CollatzResearch.WordTrace tailWord_5034151 prefixEnd_5034151 287215461145804288306763 := by
  unfold tailWord_5034151
  simp only [CollatzResearch.WordTrace]
  refine ⟨183610571185138166386558307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122407047456758777591038871 183610571185138166386558307)
  ·
    refine ⟨275415856777707249579837461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183610571185138166386558307 275415856777707249579837461)
    ·
      refine ⟨12910118286455027324054881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 275415856777707249579837461 12910118286455027324054881)
      ·
        refine ⟨9682588714841270493041161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12910118286455027324054881 9682588714841270493041161)
        ·
          refine ⟨7261941536130952869780871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9682588714841270493041161 7261941536130952869780871)
          ·
            refine ⟨10892912304196429304671307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261941536130952869780871 10892912304196429304671307)
            ·
              refine ⟨16339368456294643957006961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10892912304196429304671307 16339368456294643957006961)
              ·
                refine ⟨12254526342220982967755221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16339368456294643957006961 12254526342220982967755221)
                ·
                  refine ⟨287215461145804288306763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12254526342220982967755221 287215461145804288306763)
                  ·
                    rfl

theorem cell23_5034151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 7].length) (baseStart_5034151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034151 prefixEnd_5034151 := by exact prefixLift 5034151
  have htrace : WordTrace (prefixWord ++ tailWord_5034151) baseStart_5034151 baseEnd_5034151 := by
    simpa [prefixWord, tailWord_5034151, baseEnd_5034151] using wordTrace_append hprefix tailTrace_5034151
  have hstable : (prefixWord ++ tailWord_5034151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034151).length < 2 ^ (prefixWord ++ tailWord_5034151).sum := by decide
  have hdescent : baseEnd_5034151 < baseStart_5034151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034184 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_5034184 : Nat := 118140960795 + 5034184 * 2 ^ 59
def prefixEnd_5034184 : Nat := 4983230072969 + 3 ^ 40 * 5034184 * 2
def baseEnd_5034184 : Nat := 2584956095173836965648215

theorem tailTrace_5034184 : CollatzResearch.WordTrace tailWord_5034184 prefixEnd_5034184 2584956095173836965648215 := by
  unfold tailWord_5034184
  simp only [CollatzResearch.WordTrace]
  refine ⟨91805887397009306511254803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122407849862679075348339737 91805887397009306511254803)
  ·
    refine ⟨137708831095513959766882205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91805887397009306511254803 137708831095513959766882205)
    ·
      refine ⟨51640811660817734912580827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137708831095513959766882205 51640811660817734912580827)
      ·
        refine ⟨77461217491226602368871241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51640811660817734912580827 77461217491226602368871241)
        ·
          refine ⟨58095913118419951776653431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77461217491226602368871241 58095913118419951776653431)
          ·
            refine ⟨87143869677629927664980147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58095913118419951776653431 87143869677629927664980147)
            ·
              refine ⟨130715804516444891497470221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87143869677629927664980147 130715804516444891497470221)
              ·
                refine ⟨49018426693666834311551333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130715804516444891497470221 49018426693666834311551333)
                ·
                  refine ⟨9190955005062531433415875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49018426693666834311551333 9190955005062531433415875)
                  ·
                    refine ⟨13786432507593797150123813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9190955005062531433415875 13786432507593797150123813)
                    ·
                      refine ⟨2584956095173836965648215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13786432507593797150123813 2584956095173836965648215)
                      ·
                        rfl

theorem cell23_5034184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_5034184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034184 prefixEnd_5034184 := by exact prefixLift 5034184
  have htrace : WordTrace (prefixWord ++ tailWord_5034184) baseStart_5034184 baseEnd_5034184 := by
    simpa [prefixWord, tailWord_5034184, baseEnd_5034184] using wordTrace_append hprefix tailTrace_5034184
  have hstable : (prefixWord ++ tailWord_5034184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034184).length < 2 ^ (prefixWord ++ tailWord_5034184).sum := by decide
  have hdescent : baseEnd_5034184 < baseStart_5034184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034201 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 4, 2]
def baseStart_5034201 : Nat := 118140960795 + 5034201 * 2 ^ 59
def prefixEnd_5034201 : Nat := 4983230072969 + 3 ^ 40 * 5034201 * 2
def baseEnd_5034201 : Nat := 2584964824344963399135637

theorem tailTrace_5034201 : CollatzResearch.WordTrace tailWord_5034201 prefixEnd_5034201 2584964824344963399135637 := by
  unfold tailWord_5034201
  simp only [CollatzResearch.WordTrace]
  refine ⟨183612394834957024925878457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122408263223304683283918971 183612394834957024925878457)
  ·
    refine ⟨137709296126217768694408843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183612394834957024925878457 137709296126217768694408843)
    ·
      refine ⟨206563944189326653041613265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137709296126217768694408843 206563944189326653041613265)
      ·
        refine ⟨154922958141994989781209949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206563944189326653041613265 154922958141994989781209949)
        ·
          refine ⟨58096109303248121167953731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154922958141994989781209949 58096109303248121167953731)
          ·
            refine ⟨87144163954872181751930597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58096109303248121167953731 87144163954872181751930597)
            ·
              refine ⟨16339530741538534078486987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87144163954872181751930597 16339530741538534078486987)
              ·
                refine ⟨24509296112307801117730481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16339530741538534078486987 24509296112307801117730481)
                ·
                  refine ⟨18381972084230850838297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24509296112307801117730481 18381972084230850838297861)
                  ·
                    refine ⟨3446619765793284532180849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18381972084230850838297861 3446619765793284532180849)
                    ·
                      refine ⟨2584964824344963399135637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446619765793284532180849 2584964824344963399135637)
                      ·
                        rfl

theorem cell23_5034201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_5034201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034201 prefixEnd_5034201 := by exact prefixLift 5034201
  have htrace : WordTrace (prefixWord ++ tailWord_5034201) baseStart_5034201 baseEnd_5034201 := by
    simpa [prefixWord, tailWord_5034201, baseEnd_5034201] using wordTrace_append hprefix tailTrace_5034201
  have hstable : (prefixWord ++ tailWord_5034201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034201).length < 2 ^ (prefixWord ++ tailWord_5034201).sum := by decide
  have hdescent : baseEnd_5034201 < baseStart_5034201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034238 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_5034238 : Nat := 118140960795 + 5034238 * 2 ^ 59
def prefixEnd_5034238 : Nat := 4983230072969 + 3 ^ 40 * 5034238 * 2
def baseEnd_5034238 : Nat := 2584983823129179754372967

theorem tailTrace_5034238 : CollatzResearch.WordTrace tailWord_5034238 prefixEnd_5034238 2584983823129179754372967 := by
  unfold tailWord_5034238
  simp only [CollatzResearch.WordTrace]
  refine ⟨22951718041977872530621921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122409162890548653496650245 22951718041977872530621921)
  ·
    refine ⟨17213788531483404397966441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22951718041977872530621921 17213788531483404397966441)
    ·
      refine ⟨12910341398612553298474831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17213788531483404397966441 12910341398612553298474831)
      ·
        refine ⟨19365512097918829947712247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12910341398612553298474831 19365512097918829947712247)
        ·
          refine ⟨29048268146878244921568371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365512097918829947712247 29048268146878244921568371)
          ·
            refine ⟨43572402220317367382352557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29048268146878244921568371 43572402220317367382352557)
            ·
              refine ⟨16339650832619012768382209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43572402220317367382352557 16339650832619012768382209)
              ·
                refine ⟨12254738124464259576286657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16339650832619012768382209 12254738124464259576286657)
                ·
                  refine ⟨9191053593348194682214993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12254738124464259576286657 9191053593348194682214993)
                  ·
                    refine ⟨6893290195011146011661245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9191053593348194682214993 6893290195011146011661245)
                    ·
                      refine ⟨2584983823129179754372967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6893290195011146011661245 2584983823129179754372967)
                      ·
                        rfl

theorem cell23_5034238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_5034238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034238 prefixEnd_5034238 := by exact prefixLift 5034238
  have htrace : WordTrace (prefixWord ++ tailWord_5034238) baseStart_5034238 baseEnd_5034238 := by
    simpa [prefixWord, tailWord_5034238, baseEnd_5034238] using wordTrace_append hprefix tailTrace_5034238
  have hstable : (prefixWord ++ tailWord_5034238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034238).length < 2 ^ (prefixWord ++ tailWord_5034238).sum := by decide
  have hdescent : baseEnd_5034238 < baseStart_5034238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034261 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_5034261 : Nat := 118140960795 + 5034261 * 2 ^ 59
def prefixEnd_5034261 : Nat := 4983230072969 + 3 ^ 40 * 5034261 * 2
def baseEnd_5034261 : Nat := 2584995633184233164385361

theorem tailTrace_5034261 : CollatzResearch.WordTrace tailWord_5034261 prefixEnd_5034261 2584995633184233164385361 := by
  unfold tailWord_5034261
  simp only [CollatzResearch.WordTrace]
  refine ⟨183614583214739655173062637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122409722143159770115375091 183614583214739655173062637)
  ·
    refine ⟨68855468705527370689898489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183614583214739655173062637 68855468705527370689898489)
    ·
      refine ⟨51641601529145528017423867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68855468705527370689898489 51641601529145528017423867)
      ·
        refine ⟨77462402293718292026135801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51641601529145528017423867 77462402293718292026135801)
        ·
          refine ⟨58096801720288719019601851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77462402293718292026135801 58096801720288719019601851)
          ·
            refine ⟨87145202580433078529402777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58096801720288719019601851 87145202580433078529402777)
            ·
              refine ⟨65358901935324808897052083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87145202580433078529402777 65358901935324808897052083)
              ·
                refine ⟨98038352902987213345578125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65358901935324808897052083 98038352902987213345578125)
                ·
                  refine ⟨36764382338620205004591797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98038352902987213345578125 36764382338620205004591797)
                  ·
                    refine ⟨3446660844245644219180481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36764382338620205004591797 3446660844245644219180481)
                    ·
                      refine ⟨2584995633184233164385361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446660844245644219180481 2584995633184233164385361)
                      ·
                        rfl

theorem cell23_5034261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_5034261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034261 prefixEnd_5034261 := by exact prefixLift 5034261
  have htrace : WordTrace (prefixWord ++ tailWord_5034261) baseStart_5034261 baseEnd_5034261 := by
    simpa [prefixWord, tailWord_5034261, baseEnd_5034261] using wordTrace_append hprefix tailTrace_5034261
  have hstable : (prefixWord ++ tailWord_5034261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034261).length < 2 ^ (prefixWord ++ tailWord_5034261).sum := by decide
  have hdescent : baseEnd_5034261 < baseStart_5034261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034271 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 3, 5]
def baseStart_5034271 : Nat := 118140960795 + 5034271 * 2 ^ 59
def prefixEnd_5034271 : Nat := 4983230072969 + 3 ^ 40 * 5034271 * 2
def baseEnd_5034271 : Nat := 861666922663592708420105

theorem tailTrace_5034271 : CollatzResearch.WordTrace tailWord_5034271 prefixEnd_5034271 861666922663592708420105 := by
  unfold tailWord_5034271
  simp only [CollatzResearch.WordTrace]
  refine ⟨183614947944703426880926667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122409965296468951253951111 183614947944703426880926667)
  ·
    refine ⟨275422421917055140321390001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183614947944703426880926667 275422421917055140321390001)
    ·
      refine ⟨206566816437791355241042501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275422421917055140321390001 206566816437791355241042501)
      ·
        refine ⟨38731278082085879107695469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206566816437791355241042501 38731278082085879107695469)
        ·
          refine ⟨14524229280782204665385801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38731278082085879107695469 14524229280782204665385801)
          ·
            refine ⟨10893171960586653499039351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14524229280782204665385801 10893171960586653499039351)
            ·
              refine ⟨16339757940879980248559027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10893171960586653499039351 16339757940879980248559027)
              ·
                refine ⟨24509636911319970372838541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16339757940879980248559027 24509636911319970372838541)
                ·
                  refine ⟨9191113841744988889814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24509636911319970372838541 9191113841744988889814453)
                  ·
                    refine ⟨861666922663592708420105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9191113841744988889814453 861666922663592708420105)
                    ·
                      rfl

theorem cell23_5034271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_5034271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034271 prefixEnd_5034271 := by exact prefixLift 5034271
  have htrace : WordTrace (prefixWord ++ tailWord_5034271) baseStart_5034271 baseEnd_5034271 := by
    simpa [prefixWord, tailWord_5034271, baseEnd_5034271] using wordTrace_append hprefix tailTrace_5034271
  have hstable : (prefixWord ++ tailWord_5034271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034271).length < 2 ^ (prefixWord ++ tailWord_5034271).sum := by decide
  have hdescent : baseEnd_5034271 < baseStart_5034271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034284 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_5034284 : Nat := 118140960795 + 5034284 * 2 ^ 59
def prefixEnd_5034284 : Nat := 4983230072969 + 3 ^ 40 * 5034284 * 2
def baseEnd_5034284 : Nat := 861669147746428858132585

theorem tailTrace_5034284 : CollatzResearch.WordTrace tailWord_5034284 prefixEnd_5034284 861669147746428858132585 := by
  unfold tailWord_5034284
  simp only [CollatzResearch.WordTrace]
  refine ⟨91807711046828165050574953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122410281395770886734099937 91807711046828165050574953)
  ·
    refine ⟨68855783285121123787931215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91807711046828165050574953 68855783285121123787931215)
    ·
      refine ⟨103283674927681685681896823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68855783285121123787931215 103283674927681685681896823)
      ·
        refine ⟨154925512391522528522845235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103283674927681685681896823 154925512391522528522845235)
        ·
          refine ⟨232388268587283792784267853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154925512391522528522845235 232388268587283792784267853)
          ·
            refine ⟨87145600720231422294100445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232388268587283792784267853 87145600720231422294100445)
            ·
              refine ⟨32679600270086783360287667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87145600720231422294100445 32679600270086783360287667)
              ·
                refine ⟨49019400405130175040431501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32679600270086783360287667 49019400405130175040431501)
                ·
                  refine ⟨18382275151923815640161813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49019400405130175040431501 18382275151923815640161813)
                  ·
                    refine ⟨861669147746428858132585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18382275151923815640161813 861669147746428858132585)
                    ·
                      rfl

theorem cell23_5034284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_5034284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034284 prefixEnd_5034284 := by exact prefixLift 5034284
  have htrace : WordTrace (prefixWord ++ tailWord_5034284) baseStart_5034284 baseEnd_5034284 := by
    simpa [prefixWord, tailWord_5034284, baseEnd_5034284] using wordTrace_append hprefix tailTrace_5034284
  have hstable : (prefixWord ++ tailWord_5034284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034284).length < 2 ^ (prefixWord ++ tailWord_5034284).sum := by decide
  have hdescent : baseEnd_5034284 < baseStart_5034284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034302 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5034302 : Nat := 118140960795 + 5034302 * 2 ^ 59
def prefixEnd_5034302 : Nat := 4983230072969 + 3 ^ 40 * 5034302 * 2
def baseEnd_5034302 : Nat := 2585016685891067503972673

theorem tailTrace_5034302 : CollatzResearch.WordTrace tailWord_5034302 prefixEnd_5034302 2585016685891067503972673 := by
  unfold tailWord_5034302
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952009825948889896913145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122410719071727412783536773 22952009825948889896913145)
  ·
    refine ⟨17214007369461667422684859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22952009825948889896913145 17214007369461667422684859)
    ·
      refine ⟨25821011054192501134027289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17214007369461667422684859 25821011054192501134027289)
      ·
        refine ⟨19365758290644375850520467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25821011054192501134027289 19365758290644375850520467)
        ·
          refine ⟨29048637435966563775780701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365758290644375850520467 29048637435966563775780701)
          ·
            refine ⟨10893239038487461415917763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29048637435966563775780701 10893239038487461415917763)
            ·
              refine ⟨16339858557731192123876645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10893239038487461415917763 16339858557731192123876645)
              ·
                refine ⟨3063723479574598523226871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16339858557731192123876645 3063723479574598523226871)
                ·
                  refine ⟨4595585219361897784840307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063723479574598523226871 4595585219361897784840307)
                  ·
                    refine ⟨6893377829042846677260461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595585219361897784840307 6893377829042846677260461)
                    ·
                      refine ⟨2585016685891067503972673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6893377829042846677260461 2585016685891067503972673)
                      ·
                        rfl

theorem cell23_5034302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5034302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034302 prefixEnd_5034302 := by exact prefixLift 5034302
  have htrace : WordTrace (prefixWord ++ tailWord_5034302) baseStart_5034302 baseEnd_5034302 := by
    simpa [prefixWord, tailWord_5034302, baseEnd_5034302] using wordTrace_append hprefix tailTrace_5034302
  have hstable : (prefixWord ++ tailWord_5034302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034302).length < 2 ^ (prefixWord ++ tailWord_5034302).sum := by decide
  have hdescent : baseEnd_5034302 < baseStart_5034302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034304 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_5034304 : Nat := 118140960795 + 5034304 * 2 ^ 59
def prefixEnd_5034304 : Nat := 4983230072969 + 3 ^ 40 * 5034304 * 2
def baseEnd_5034304 : Nat := 2585017712852376496147663

theorem tailTrace_5034304 : CollatzResearch.WordTrace tailWord_5034304 prefixEnd_5034304 2585017712852376496147663 := by
  unfold tailWord_5034304
  simp only [CollatzResearch.WordTrace]
  refine ⟨91808075776791936758438983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122410767702389249011251977 91808075776791936758438983)
  ·
    refine ⟨137712113665187905137658475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91808075776791936758438983 137712113665187905137658475)
    ·
      refine ⟨206568170497781857706487713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137712113665187905137658475 206568170497781857706487713)
      ·
        refine ⟨154926127873336393279865785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206568170497781857706487713 154926127873336393279865785)
        ·
          refine ⟨116194595905002294959899339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154926127873336393279865785 116194595905002294959899339)
          ·
            refine ⟨174291893857503442439849009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116194595905002294959899339 174291893857503442439849009)
            ·
              refine ⟨130718920393127581829886757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174291893857503442439849009 130718920393127581829886757)
              ·
                refine ⟨24509797573711421593103767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130718920393127581829886757 24509797573711421593103767)
                ·
                  refine ⟨36764696360567132389655651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24509797573711421593103767 36764696360567132389655651)
                  ·
                    refine ⟨55147044540850698584483477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36764696360567132389655651 55147044540850698584483477)
                    ·
                      refine ⟨2585017712852376496147663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55147044540850698584483477 2585017712852376496147663)
                      ·
                        rfl

theorem cell23_5034304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_5034304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034304 prefixEnd_5034304 := by exact prefixLift 5034304
  have htrace : WordTrace (prefixWord ++ tailWord_5034304) baseStart_5034304 baseEnd_5034304 := by
    simpa [prefixWord, tailWord_5034304, baseEnd_5034304] using wordTrace_append hprefix tailTrace_5034304
  have hstable : (prefixWord ++ tailWord_5034304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034304).length < 2 ^ (prefixWord ++ tailWord_5034304).sum := by decide
  have hdescent : baseEnd_5034304 < baseStart_5034304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034311 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_5034311 : Nat := 118140960795 + 5034311 * 2 ^ 59
def prefixEnd_5034311 : Nat := 4983230072969 + 3 ^ 40 * 5034311 * 2
def baseEnd_5034311 : Nat := 2585021307216957968760131

theorem tailTrace_5034311 : CollatzResearch.WordTrace tailWord_5034311 prefixEnd_5034311 2585021307216957968760131 := by
  unfold tailWord_5034311
  simp only [CollatzResearch.WordTrace]
  refine ⟨183616406864558513712382787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122410937909705675808255191 183616406864558513712382787)
  ·
    refine ⟨275424610296837770568574181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183616406864558513712382787 275424610296837770568574181)
    ·
      refine ⟨51642114430657081981607659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275424610296837770568574181 51642114430657081981607659)
      ·
        refine ⟨77463171645985622972411489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51642114430657081981607659 77463171645985622972411489)
        ·
          refine ⟨58097378734489217229308617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77463171645985622972411489 58097378734489217229308617)
          ·
            refine ⟨43573034050866912921981463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58097378734489217229308617 43573034050866912921981463)
            ·
              refine ⟨65359551076300369382972195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43573034050866912921981463 65359551076300369382972195)
              ·
                refine ⟨98039326614450554074458293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65359551076300369382972195 98039326614450554074458293)
                ·
                  refine ⟨9191186870104739444480465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98039326614450554074458293 9191186870104739444480465)
                  ·
                    refine ⟨6893390152578554583360349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9191186870104739444480465 6893390152578554583360349)
                    ·
                      refine ⟨2585021307216957968760131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6893390152578554583360349 2585021307216957968760131)
                      ·
                        rfl

theorem cell23_5034311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_5034311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034311 prefixEnd_5034311 := by exact prefixLift 5034311
  have htrace : WordTrace (prefixWord ++ tailWord_5034311) baseStart_5034311 baseEnd_5034311 := by
    simpa [prefixWord, tailWord_5034311, baseEnd_5034311] using wordTrace_append hprefix tailTrace_5034311
  have hstable : (prefixWord ++ tailWord_5034311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034311).length < 2 ^ (prefixWord ++ tailWord_5034311).sum := by decide
  have hdescent : baseEnd_5034311 < baseStart_5034311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034321 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_5034321 : Nat := 118140960795 + 5034321 * 2 ^ 59
def prefixEnd_5034321 : Nat := 4983230072969 + 3 ^ 40 * 5034321 * 2
def baseEnd_5034321 : Nat := 2585026442023502929635085

theorem tailTrace_5034321 : CollatzResearch.WordTrace tailWord_5034321 prefixEnd_5034321 2585026442023502929635085 := by
  unfold tailWord_5034321
  simp only [CollatzResearch.WordTrace]
  refine ⟨183616771594522285420246817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122411181063014856946831211 183616771594522285420246817)
  ·
    refine ⟨137712578695891714065185113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183616771594522285420246817 137712578695891714065185113)
    ·
      refine ⟨103284434021918785548888835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137712578695891714065185113 103284434021918785548888835)
      ·
        refine ⟨154926651032878178323333253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103284434021918785548888835 154926651032878178323333253)
        ·
          refine ⟨29048747068664658435624985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154926651032878178323333253 29048747068664658435624985)
          ·
            refine ⟨21786560301498493826718739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29048747068664658435624985 21786560301498493826718739)
            ·
              refine ⟨32679840452247740740078109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21786560301498493826718739 32679840452247740740078109)
              ·
                refine ⟨12254940169592902777529291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32679840452247740740078109 12254940169592902777529291)
                ·
                  refine ⟨18382410254389354166293937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12254940169592902777529291 18382410254389354166293937)
                  ·
                    refine ⟨13786807690792015624720453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18382410254389354166293937 13786807690792015624720453)
                    ·
                      refine ⟨2585026442023502929635085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13786807690792015624720453 2585026442023502929635085)
                      ·
                        rfl

theorem cell23_5034321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_5034321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034321 prefixEnd_5034321 := by exact prefixLift 5034321
  have htrace : WordTrace (prefixWord ++ tailWord_5034321) baseStart_5034321 baseEnd_5034321 := by
    simpa [prefixWord, tailWord_5034321, baseEnd_5034321] using wordTrace_append hprefix tailTrace_5034321
  have hstable : (prefixWord ++ tailWord_5034321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034321).length < 2 ^ (prefixWord ++ tailWord_5034321).sum := by decide
  have hdescent : baseEnd_5034321 < baseStart_5034321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034338 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5034338 : Nat := 118140960795 + 5034338 * 2 ^ 59
def prefixEnd_5034338 : Nat := 4983230072969 + 3 ^ 40 * 5034338 * 2
def baseEnd_5034338 : Nat := 2585035171194629363122507

theorem tailTrace_5034338 : CollatzResearch.WordTrace tailWord_5034338 prefixEnd_5034338 2585035171194629363122507 := by
  unfold tailWord_5034338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45904347908865174330903917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122411594423640464882410445 45904347908865174330903917)
  ·
    refine ⟨17214130465824440374088969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45904347908865174330903917 17214130465824440374088969)
    ·
      refine ⟨12910597849368330280566727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17214130465824440374088969 12910597849368330280566727)
      ·
        refine ⟨19365896774052495420850091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12910597849368330280566727 19365896774052495420850091)
        ·
          refine ⟨29048845161078743131275137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19365896774052495420850091 29048845161078743131275137)
          ·
            refine ⟨21786633870809057348456353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29048845161078743131275137 21786633870809057348456353)
            ·
              refine ⟨16339975403106793011342265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21786633870809057348456353 16339975403106793011342265)
              ·
                refine ⟨12254981552330094758506699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16339975403106793011342265 12254981552330094758506699)
                ·
                  refine ⟨18382472328495142137760049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12254981552330094758506699 18382472328495142137760049)
                  ·
                    refine ⟨13786854246371356603320037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18382472328495142137760049 13786854246371356603320037)
                    ·
                      refine ⟨2585035171194629363122507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13786854246371356603320037 2585035171194629363122507)
                      ·
                        rfl

theorem cell23_5034338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5034338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034338 prefixEnd_5034338 := by exact prefixLift 5034338
  have htrace : WordTrace (prefixWord ++ tailWord_5034338) baseStart_5034338 baseEnd_5034338 := by
    simpa [prefixWord, tailWord_5034338, baseEnd_5034338] using wordTrace_append hprefix tailTrace_5034338
  have hstable : (prefixWord ++ tailWord_5034338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034338).length < 2 ^ (prefixWord ++ tailWord_5034338).sum := by decide
  have hdescent : baseEnd_5034338 < baseStart_5034338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034384 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_5034384 : Nat := 118140960795 + 5034384 * 2 ^ 59
def prefixEnd_5034384 : Nat := 4983230072969 + 3 ^ 40 * 5034384 * 2
def baseEnd_5034384 : Nat := 2585058791304736183147295

theorem tailTrace_5034384 : CollatzResearch.WordTrace tailWord_5034384 prefixEnd_5034384 2585058791304736183147295 := by
  unfold tailWord_5034384
  simp only [CollatzResearch.WordTrace]
  refine ⟨91809534696647023589895103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122412712928862698119860137 91809534696647023589895103)
  ·
    refine ⟨137714302044970535384842655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91809534696647023589895103 137714302044970535384842655)
    ·
      refine ⟨206571453067455803077263983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137714302044970535384842655 206571453067455803077263983)
      ·
        refine ⟨309857179601183704615895975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206571453067455803077263983 309857179601183704615895975)
        ·
          refine ⟨464785769401775556923843963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309857179601183704615895975 464785769401775556923843963)
          ·
            refine ⟨697178654102663335385765945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464785769401775556923843963 697178654102663335385765945)
            ·
              refine ⟨522883990576997501539324459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697178654102663335385765945 522883990576997501539324459)
              ·
                refine ⟨784325985865496252308986689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522883990576997501539324459 784325985865496252308986689)
                ·
                  refine ⟨588244489399122189231740017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 784325985865496252308986689 588244489399122189231740017)
                  ·
                    refine ⟨441183367049341641923805013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588244489399122189231740017 441183367049341641923805013)
                    ·
                      refine ⟨2585058791304736183147295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 441183367049341641923805013 2585058791304736183147295)
                      ·
                        rfl

theorem cell23_5034384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_5034384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034384 prefixEnd_5034384 := by exact prefixLift 5034384
  have htrace : WordTrace (prefixWord ++ tailWord_5034384) baseStart_5034384 baseEnd_5034384 := by
    simpa [prefixWord, tailWord_5034384, baseEnd_5034384] using wordTrace_append hprefix tailTrace_5034384
  have hstable : (prefixWord ++ tailWord_5034384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034384).length < 2 ^ (prefixWord ++ tailWord_5034384).sum := by decide
  have hdescent : baseEnd_5034384 < baseStart_5034384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034410 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5034410 : Nat := 118140960795 + 5034410 * 2 ^ 59
def prefixEnd_5034410 : Nat := 4983230072969 + 3 ^ 40 * 5034410 * 2
def baseEnd_5034410 : Nat := 2585072141801753081422177

theorem tailTrace_5034410 : CollatzResearch.WordTrace tailWord_5034410 prefixEnd_5034410 2585072141801753081422177 := by
  unfold tailWord_5034410
  simp only [CollatzResearch.WordTrace]
  refine ⟨45905004422799963405059171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122413345127466569080157789 45905004422799963405059171)
  ·
    refine ⟨68857506634199945107588757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45905004422799963405059171 68857506634199945107588757)
    ·
      refine ⟨3227695623478122426918223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68857506634199945107588757 3227695623478122426918223)
      ·
        refine ⟨4841543435217183640377335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227695623478122426918223 4841543435217183640377335)
        ·
          refine ⟨7262315152825775460566003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4841543435217183640377335 7262315152825775460566003)
          ·
            refine ⟨10893472729238663190849005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7262315152825775460566003 10893472729238663190849005)
            ·
              refine ⟨4085052273464498696568377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10893472729238663190849005 4085052273464498696568377)
              ·
                refine ⟨3063789205098374022426283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085052273464498696568377 3063789205098374022426283)
                ·
                  refine ⟨4595683807647561033639425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063789205098374022426283 4595683807647561033639425)
                  ·
                    refine ⟨3446762855735670775229569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595683807647561033639425 3446762855735670775229569)
                    ·
                      refine ⟨2585072141801753081422177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446762855735670775229569 2585072141801753081422177)
                      ·
                        rfl

theorem cell23_5034410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5034410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034410 prefixEnd_5034410 := by exact prefixLift 5034410
  have htrace : WordTrace (prefixWord ++ tailWord_5034410) baseStart_5034410 baseEnd_5034410 := by
    simpa [prefixWord, tailWord_5034410, baseEnd_5034410] using wordTrace_append hprefix tailTrace_5034410
  have hstable : (prefixWord ++ tailWord_5034410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034410).length < 2 ^ (prefixWord ++ tailWord_5034410).sum := by decide
  have hdescent : baseEnd_5034410 < baseStart_5034410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034436 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5034436 : Nat := 118140960795 + 5034436 * 2 ^ 59
def prefixEnd_5034436 : Nat := 4983230072969 + 3 ^ 40 * 5034436 * 2
def baseEnd_5034436 : Nat := 2585085492298769979697057

theorem tailTrace_5034436 : CollatzResearch.WordTrace tailWord_5034436 prefixEnd_5034436 2585085492298769979697057 := by
  unfold tailWord_5034436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91810482994552830030341581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122413977326070440040455441 91810482994552830030341581)
  ·
    refine ⟨34428931122957311261378093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91810482994552830030341581 34428931122957311261378093)
    ·
      refine ⟨12910849171108991723016785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34428931122957311261378093 12910849171108991723016785)
      ·
        refine ⟨9683136878331743792262589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12910849171108991723016785 9683136878331743792262589)
        ·
          refine ⟨3631176329374403922098471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9683136878331743792262589 3631176329374403922098471)
          ·
            refine ⟨5446764494061605883147707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631176329374403922098471 5446764494061605883147707)
            ·
              refine ⟨8170146741092408824721561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446764494061605883147707 8170146741092408824721561)
              ·
                refine ⟨6127610055819306618541171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8170146741092408824721561 6127610055819306618541171)
                ·
                  refine ⟨9191415083728959927811757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127610055819306618541171 9191415083728959927811757)
                  ·
                    refine ⟨3446780656398359972929409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9191415083728959927811757 3446780656398359972929409)
                    ·
                      refine ⟨2585085492298769979697057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446780656398359972929409 2585085492298769979697057)
                      ·
                        rfl

theorem cell23_5034436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5034436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034436 prefixEnd_5034436 := by exact prefixLift 5034436
  have htrace : WordTrace (prefixWord ++ tailWord_5034436) baseStart_5034436 baseEnd_5034436 := by
    simpa [prefixWord, tailWord_5034436, baseEnd_5034436] using wordTrace_append hprefix tailTrace_5034436
  have hstable : (prefixWord ++ tailWord_5034436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034436).length < 2 ^ (prefixWord ++ tailWord_5034436).sum := by decide
  have hdescent : baseEnd_5034436 < baseStart_5034436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034472 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 5]
def baseStart_5034472 : Nat := 118140960795 + 5034472 * 2 ^ 59
def prefixEnd_5034472 : Nat := 4983230072969 + 3 ^ 40 * 5034472 * 2
def baseEnd_5034472 : Nat := 287233775289147982094099

theorem tailTrace_5034472 : CollatzResearch.WordTrace tailWord_5034472 prefixEnd_5034472 287233775289147982094099 := by
  unfold tailWord_5034472
  simp only [CollatzResearch.WordTrace]
  refine ⟨91811139508487619104496835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122414852677983492139329113 91811139508487619104496835)
  ·
    refine ⟨137716709262731428656745253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91811139508487619104496835 137716709262731428656745253)
    ·
      refine ⟨25821882986762142873139735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137716709262731428656745253 25821882986762142873139735)
      ·
        refine ⟨38732824480143214309709603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25821882986762142873139735 38732824480143214309709603)
        ·
          refine ⟨58099236720214821464564405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38732824480143214309709603 58099236720214821464564405)
          ·
            refine ⟨5446803442520139512302913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58099236720214821464564405 5446803442520139512302913)
            ·
              refine ⟨4085102581890104634227185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5446803442520139512302913 4085102581890104634227185)
              ·
                refine ⟨3063826936417578475670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085102581890104634227185 3063826936417578475670389)
                ·
                  refine ⟨287233775289147982094099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3063826936417578475670389 287233775289147982094099)
                  ·
                    rfl

theorem cell23_5034472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 5].length) (baseStart_5034472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034472 prefixEnd_5034472 := by exact prefixLift 5034472
  have htrace : WordTrace (prefixWord ++ tailWord_5034472) baseStart_5034472 baseEnd_5034472 := by
    simpa [prefixWord, tailWord_5034472, baseEnd_5034472] using wordTrace_append hprefix tailTrace_5034472
  have hstable : (prefixWord ++ tailWord_5034472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034472).length < 2 ^ (prefixWord ++ tailWord_5034472).sum := by decide
  have hdescent : baseEnd_5034472 < baseStart_5034472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034478 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5034478 : Nat := 118140960795 + 5034478 * 2 ^ 59
def prefixEnd_5034478 : Nat := 4983230072969 + 3 ^ 40 * 5034478 * 2
def baseEnd_5034478 : Nat := 2585107058486258815371863

theorem tailTrace_5034478 : CollatzResearch.WordTrace tailWord_5034478 prefixEnd_5034478 2585107058486258815371863 := by
  unfold tailWord_5034478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952812231869187654214011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122414998569969000822474725 22952812231869187654214011)
  ·
    refine ⟨34429218347803781481321017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952812231869187654214011 34429218347803781481321017)
    ·
      refine ⟨25821913760852836110990763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34429218347803781481321017 25821913760852836110990763)
      ·
        refine ⟨38732870641279254166486145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25821913760852836110990763 38732870641279254166486145)
        ·
          refine ⟨29049652980959440624864609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38732870641279254166486145 29049652980959440624864609)
          ·
            refine ⟨21787239735719580468648457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29049652980959440624864609 21787239735719580468648457)
            ·
              refine ⟨16340429801789685351486343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21787239735719580468648457 16340429801789685351486343)
              ·
                refine ⟨24510644702684528027229515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16340429801789685351486343 24510644702684528027229515)
                ·
                  refine ⟨36765967054026792040844273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24510644702684528027229515 36765967054026792040844273)
                  ·
                    refine ⟨27574475290520094030633205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36765967054026792040844273 27574475290520094030633205)
                    ·
                      refine ⟨2585107058486258815371863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27574475290520094030633205 2585107058486258815371863)
                      ·
                        rfl

theorem cell23_5034478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5034478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034478 prefixEnd_5034478 := by exact prefixLift 5034478
  have htrace : WordTrace (prefixWord ++ tailWord_5034478) baseStart_5034478 baseEnd_5034478 := by
    simpa [prefixWord, tailWord_5034478, baseEnd_5034478] using wordTrace_append hprefix tailTrace_5034478
  have hstable : (prefixWord ++ tailWord_5034478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034478).length < 2 ^ (prefixWord ++ tailWord_5034478).sum := by decide
  have hdescent : baseEnd_5034478 < baseStart_5034478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034565 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_5034565 : Nat := 118140960795 + 5034565 * 2 ^ 59
def prefixEnd_5034565 : Nat := 4983230072969 + 3 ^ 40 * 5034565 * 2
def baseEnd_5034565 : Nat := 2585151731303199974983963

theorem tailTrace_5034565 : CollatzResearch.WordTrace tailWord_5034565 prefixEnd_5034565 2585151731303199974983963 := by
  unfold tailWord_5034565
  simp only [CollatzResearch.WordTrace]
  refine ⟨183625671005638315092129149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122417114003758876728086099 183625671005638315092129149)
  ·
    refine ⟨68859626627114368159548431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183625671005638315092129149 68859626627114368159548431)
    ·
      refine ⟨103289439940671552239322647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68859626627114368159548431 103289439940671552239322647)
      ·
        refine ⟨154934159911007328358983971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103289439940671552239322647 154934159911007328358983971)
        ·
          refine ⟨232401239866510992538475957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154934159911007328358983971 232401239866510992538475957)
          ·
            refine ⟨21787616237485405550482121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232401239866510992538475957 21787616237485405550482121)
            ·
              refine ⟨16340712178114054162861591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21787616237485405550482121 16340712178114054162861591)
              ·
                refine ⟨24511068267171081244292387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16340712178114054162861591 24511068267171081244292387)
                ·
                  refine ⟨36766602400756621866438581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24511068267171081244292387 36766602400756621866438581)
                  ·
                    refine ⟨3446868975070933299978617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36766602400756621866438581 3446868975070933299978617)
                    ·
                      refine ⟨2585151731303199974983963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446868975070933299978617 2585151731303199974983963)
                      ·
                        rfl

theorem cell23_5034565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_5034565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034565 prefixEnd_5034565 := by exact prefixLift 5034565
  have htrace : WordTrace (prefixWord ++ tailWord_5034565) baseStart_5034565 baseEnd_5034565 := by
    simpa [prefixWord, tailWord_5034565, baseEnd_5034565] using wordTrace_append hprefix tailTrace_5034565
  have hstable : (prefixWord ++ tailWord_5034565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034565).length < 2 ^ (prefixWord ++ tailWord_5034565).sum := by decide
  have hdescent : baseEnd_5034565 < baseStart_5034565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034566 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5034566 : Nat := 118140960795 + 5034566 * 2 ^ 59
def prefixEnd_5034566 : Nat := 4983230072969 + 3 ^ 40 * 5034566 * 2
def baseEnd_5034566 : Nat := 861717414927951490357153

theorem tailTrace_5034566 : CollatzResearch.WordTrace tailWord_5034566 prefixEnd_5034566 861717414927951490357153 := by
  unfold tailWord_5034566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5738303358707334133216111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122417138319089794841943701 5738303358707334133216111)
  ·
    refine ⟨8607455038061001199824167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5738303358707334133216111 8607455038061001199824167)
    ·
      refine ⟨12911182557091501799736251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8607455038061001199824167 12911182557091501799736251)
      ·
        refine ⟨19366773835637252699604377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12911182557091501799736251 19366773835637252699604377)
        ·
          refine ⟨14525080376727939524703283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19366773835637252699604377 14525080376727939524703283)
          ·
            refine ⟨21787620565091909287054925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14525080376727939524703283 21787620565091909287054925)
            ·
              refine ⟨8170357711909465982645597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21787620565091909287054925 8170357711909465982645597)
              ·
                refine ⟨3063884141966049743492099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8170357711909465982645597 3063884141966049743492099)
                ·
                  refine ⟨4595826212949074615238149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063884141966049743492099 4595826212949074615238149)
                  ·
                    refine ⟨861717414927951490357153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4595826212949074615238149 861717414927951490357153)
                    ·
                      rfl

theorem cell23_5034566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5034566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034566 prefixEnd_5034566 := by exact prefixLift 5034566
  have htrace : WordTrace (prefixWord ++ tailWord_5034566) baseStart_5034566 baseEnd_5034566 := by
    simpa [prefixWord, tailWord_5034566, baseEnd_5034566] using wordTrace_append hprefix tailTrace_5034566
  have hstable : (prefixWord ++ tailWord_5034566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034566).length < 2 ^ (prefixWord ++ tailWord_5034566).sum := by decide
  have hdescent : baseEnd_5034566 < baseStart_5034566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034625 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5034625 : Nat := 118140960795 + 5034625 * 2 ^ 59
def prefixEnd_5034625 : Nat := 4983230072969 + 3 ^ 40 * 5034625 * 2
def baseEnd_5034625 : Nat := 2585182540142469740233687

theorem tailTrace_5034625 : CollatzResearch.WordTrace tailWord_5034625 prefixEnd_5034625 2585182540142469740233687 := by
  unfold tailWord_5034625
  simp only [CollatzResearch.WordTrace]
  refine ⟨183627859385420945339313329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122418572923613963559542219 183627859385420945339313329)
  ·
    refine ⟨137720894539065709004484997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183627859385420945339313329 137720894539065709004484997)
    ·
      refine ⟨25822667726074820438340937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137720894539065709004484997 25822667726074820438340937)
      ·
        refine ⟨19367000794556115328755703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25822667726074820438340937 19367000794556115328755703)
        ·
          refine ⟨29050501191834172993133555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19367000794556115328755703 29050501191834172993133555)
          ·
            refine ⟨43575751787751259489700333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29050501191834172993133555 43575751787751259489700333)
            ·
              refine ⟨16340906920406722308637625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43575751787751259489700333 16340906920406722308637625)
              ·
                refine ⟨12255680190305041731478219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16340906920406722308637625 12255680190305041731478219)
                ·
                  refine ⟨18383520285457562597217329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12255680190305041731478219 18383520285457562597217329)
                  ·
                    refine ⟨13787640214093171947912997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18383520285457562597217329 13787640214093171947912997)
                    ·
                      refine ⟨2585182540142469740233687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13787640214093171947912997 2585182540142469740233687)
                      ·
                        rfl

theorem cell23_5034625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5034625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034625 prefixEnd_5034625 := by exact prefixLift 5034625
  have htrace : WordTrace (prefixWord ++ tailWord_5034625) baseStart_5034625 baseEnd_5034625 := by
    simpa [prefixWord, tailWord_5034625, baseEnd_5034625] using wordTrace_append hprefix tailTrace_5034625
  have hstable : (prefixWord ++ tailWord_5034625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034625).length < 2 ^ (prefixWord ++ tailWord_5034625).sum := by decide
  have hdescent : baseEnd_5034625 < baseStart_5034625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034648 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_5034648 : Nat := 118140960795 + 5034648 * 2 ^ 59
def prefixEnd_5034648 : Nat := 4983230072969 + 3 ^ 40 * 5034648 * 2
def baseEnd_5034648 : Nat := 861731450065841050082027

theorem tailTrace_5034648 : CollatzResearch.WordTrace tailWord_5034648 prefixEnd_5034648 861731450065841050082027 := by
  unfold tailWord_5034648
  simp only [CollatzResearch.WordTrace]
  refine ⟨91814349132168810133700299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122419132176225080178267065 91814349132168810133700299)
  ·
    refine ⟨137721523698253215200550449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91814349132168810133700299 137721523698253215200550449)
    ·
      refine ⟨103291142773689911400412837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137721523698253215200550449 103291142773689911400412837)
      ·
        refine ⟨19367089270066858387577407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103291142773689911400412837 19367089270066858387577407)
        ·
          refine ⟨29050633905100287581366111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19367089270066858387577407 29050633905100287581366111)
          ·
            refine ⟨43575950857650431372049167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29050633905100287581366111 43575950857650431372049167)
            ·
              refine ⟨65363926286475647058073751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43575950857650431372049167 65363926286475647058073751)
              ·
                refine ⟨98045889429713470587110627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65363926286475647058073751 98045889429713470587110627)
                ·
                  refine ⟨147068834144570205880665941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98045889429713470587110627 147068834144570205880665941)
                  ·
                    refine ⟨861731450065841050082027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 147068834144570205880665941 861731450065841050082027)
                    ·
                      rfl

theorem cell23_5034648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_5034648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034648 prefixEnd_5034648 := by exact prefixLift 5034648
  have htrace : WordTrace (prefixWord ++ tailWord_5034648) baseStart_5034648 baseEnd_5034648 := by
    simpa [prefixWord, tailWord_5034648, baseEnd_5034648] using wordTrace_append hprefix tailTrace_5034648
  have hstable : (prefixWord ++ tailWord_5034648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034648).length < 2 ^ (prefixWord ++ tailWord_5034648).sum := by decide
  have hdescent : baseEnd_5034648 < baseStart_5034648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034672 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2]
def baseStart_5034672 : Nat := 118140960795 + 5034672 * 2 ^ 59
def prefixEnd_5034672 : Nat := 4983230072969 + 3 ^ 40 * 5034672 * 2
def baseEnd_5034672 : Nat := 2585206673733231056345971

theorem tailTrace_5034672 : CollatzResearch.WordTrace tailWord_5034672 prefixEnd_5034672 2585206673733231056345971 := by
  unfold tailWord_5034672
  simp only [CollatzResearch.WordTrace]
  refine ⟨91814786808125336183137135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122419715744167114910849513 91814786808125336183137135)
  ·
    refine ⟨137722180212188004274705703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91814786808125336183137135 137722180212188004274705703)
    ·
      refine ⟨206583270318282006412058555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137722180212188004274705703 206583270318282006412058555)
      ·
        refine ⟨309874905477423009618087833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206583270318282006412058555 309874905477423009618087833)
        ·
          refine ⟨232406179108067257213565875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309874905477423009618087833 232406179108067257213565875)
          ·
            refine ⟨348609268662100885820348813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232406179108067257213565875 348609268662100885820348813)
            ·
              refine ⟨130728475748287832182630805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348609268662100885820348813 130728475748287832182630805)
              ·
                refine ⟨6127897300700992133560819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130728475748287832182630805 6127897300700992133560819)
                ·
                  refine ⟨9191845951051488200341229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127897300700992133560819 9191845951051488200341229)
                  ·
                    refine ⟨3446942231644308075127961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9191845951051488200341229 3446942231644308075127961)
                    ·
                      refine ⟨2585206673733231056345971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446942231644308075127961 2585206673733231056345971)
                      ·
                        rfl

theorem cell23_5034672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 3, 2].length) (baseStart_5034672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034672 prefixEnd_5034672 := by exact prefixLift 5034672
  have htrace : WordTrace (prefixWord ++ tailWord_5034672) baseStart_5034672 baseEnd_5034672 := by
    simpa [prefixWord, tailWord_5034672, baseEnd_5034672] using wordTrace_append hprefix tailTrace_5034672
  have hstable : (prefixWord ++ tailWord_5034672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034672).length < 2 ^ (prefixWord ++ tailWord_5034672).sum := by decide
  have hdescent : baseEnd_5034672 < baseStart_5034672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034719 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 4, 2]
def baseStart_5034719 : Nat := 118140960795 + 5034719 * 2 ^ 59
def prefixEnd_5034719 : Nat := 4983230072969 + 3 ^ 40 * 5034719 * 2
def baseEnd_5034719 : Nat := 2585230807323992372458255

theorem tailTrace_5034719 : CollatzResearch.WordTrace tailWord_5034719 prefixEnd_5034719 2585230807323992372458255 := by
  unfold tailWord_5034719
  simp only [CollatzResearch.WordTrace]
  refine ⟨183631287847080399393235211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122420858564720266262156807 183631287847080399393235211)
  ·
    refine ⟨275446931770620599089852817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183631287847080399393235211 275446931770620599089852817)
    ·
      refine ⟨206585198827965449317389613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275446931770620599089852817 206585198827965449317389613)
      ·
        refine ⟨77469449560487043494021105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206585198827965449317389613 77469449560487043494021105)
        ·
          refine ⟨58102087170365282620515829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77469449560487043494021105 58102087170365282620515829)
          ·
            refine ⟨5447070672221745245673359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58102087170365282620515829 5447070672221745245673359)
            ·
              refine ⟨8170606008332617868510039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447070672221745245673359 8170606008332617868510039)
              ·
                refine ⟨12255909012498926802765059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170606008332617868510039 12255909012498926802765059)
                ·
                  refine ⟨18383863518748390204147589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12255909012498926802765059 18383863518748390204147589)
                  ·
                    refine ⟨3446974409765323163277673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18383863518748390204147589 3446974409765323163277673)
                    ·
                      refine ⟨2585230807323992372458255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3446974409765323163277673 2585230807323992372458255)
                      ·
                        rfl

theorem cell23_5034719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_5034719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034719 prefixEnd_5034719 := by exact prefixLift 5034719
  have htrace : WordTrace (prefixWord ++ tailWord_5034719) baseStart_5034719 baseEnd_5034719 := by
    simpa [prefixWord, tailWord_5034719, baseEnd_5034719] using wordTrace_append hprefix tailTrace_5034719
  have hstable : (prefixWord ++ tailWord_5034719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034719).length < 2 ^ (prefixWord ++ tailWord_5034719).sum := by decide
  have hdescent : baseEnd_5034719 < baseStart_5034719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034725 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 7]
def baseStart_5034725 : Nat := 118140960795 + 5034725 * 2 ^ 59
def prefixEnd_5034725 : Nat := 4983230072969 + 3 ^ 40 * 5034725 * 2
def baseEnd_5034725 : Nat := 287248209800879927664803

theorem tailTrace_5034725 : CollatzResearch.WordTrace tailWord_5034725 prefixEnd_5034725 287248209800879927664803 := by
  unfold tailWord_5034725
  simp only [CollatzResearch.WordTrace]
  refine ⟨183631506685058662417953629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122421004456705774945302419 183631506685058662417953629)
  ·
    refine ⟨68861815006896998406732611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183631506685058662417953629 68861815006896998406732611)
    ·
      refine ⟨103292722510345497610098917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68861815006896998406732611 103292722510345497610098917)
      ·
        refine ⟨19367385470689780801893547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103292722510345497610098917 19367385470689780801893547)
        ·
          refine ⟨29051078206034671202840321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19367385470689780801893547 29051078206034671202840321)
          ·
            refine ⟨21788308654526003402130241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29051078206034671202840321 21788308654526003402130241)
            ·
              refine ⟨16341231490894502551597681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21788308654526003402130241 16341231490894502551597681)
              ·
                refine ⟨12255923618170876913698261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16341231490894502551597681 12255923618170876913698261)
                ·
                  refine ⟨287248209800879927664803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12255923618170876913698261 287248209800879927664803)
                  ·
                    rfl

theorem cell23_5034725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_5034725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034725 prefixEnd_5034725 := by exact prefixLift 5034725
  have htrace : WordTrace (prefixWord ++ tailWord_5034725) baseStart_5034725 baseEnd_5034725 := by
    simpa [prefixWord, tailWord_5034725, baseEnd_5034725] using wordTrace_append hprefix tailTrace_5034725
  have hstable : (prefixWord ++ tailWord_5034725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034725).length < 2 ^ (prefixWord ++ tailWord_5034725).sum := by decide
  have hdescent : baseEnd_5034725 < baseStart_5034725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034762 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5034762 : Nat := 118140960795 + 5034762 * 2 ^ 59
def prefixEnd_5034762 : Nat := 4983230072969 + 3 ^ 40 * 5034762 * 2
def baseEnd_5034762 : Nat := 2585252886992135704220557

theorem tailTrace_5034762 : CollatzResearch.WordTrace tailWord_5034762 prefixEnd_5034762 2585252886992135704220557 := by
  unfold tailWord_5034762
  simp only [CollatzResearch.WordTrace]
  refine ⟨45908214046481154434262635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122421904123949745158033693 45908214046481154434262635)
  ·
    refine ⟨68862321069721731651393953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45908214046481154434262635 68862321069721731651393953)
    ·
      refine ⟨51646740802291298738545465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68862321069721731651393953 51646740802291298738545465)
      ·
        refine ⟨38735055601718474053909099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51646740802291298738545465 38735055601718474053909099)
        ·
          refine ⟨58102583402577711080863649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38735055601718474053909099 58102583402577711080863649)
          ·
            refine ⟨43576937551933283310647737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58102583402577711080863649 43576937551933283310647737)
            ·
              refine ⟨32682703163949962482985803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43576937551933283310647737 32682703163949962482985803)
              ·
                refine ⟨49024054745924943724478705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32682703163949962482985803 49024054745924943724478705)
                ·
                  refine ⟨36768041059443707793359029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49024054745924943724478705 36768041059443707793359029)
                  ·
                    refine ⟨3447003849322847605627409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36768041059443707793359029 3447003849322847605627409)
                    ·
                      refine ⟨2585252886992135704220557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447003849322847605627409 2585252886992135704220557)
                      ·
                        rfl

theorem cell23_5034762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5034762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034762 prefixEnd_5034762 := by exact prefixLift 5034762
  have htrace : WordTrace (prefixWord ++ tailWord_5034762) baseStart_5034762 baseEnd_5034762 := by
    simpa [prefixWord, tailWord_5034762, baseEnd_5034762] using wordTrace_append hprefix tailTrace_5034762
  have hstable : (prefixWord ++ tailWord_5034762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034762).length < 2 ^ (prefixWord ++ tailWord_5034762).sum := by decide
  have hdescent : baseEnd_5034762 < baseStart_5034762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034819 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 1, 4]
def baseStart_5034819 : Nat := 118140960795 + 5034819 * 2 ^ 59
def prefixEnd_5034819 : Nat := 4983230072969 + 3 ^ 40 * 5034819 * 2
def baseEnd_5034819 : Nat := 861760718463147327069265

theorem tailTrace_5034819 : CollatzResearch.WordTrace tailWord_5034819 prefixEnd_5034819 861760718463147327069265 := by
  unfold tailWord_5034819
  simp only [CollatzResearch.WordTrace]
  refine ⟨183634935146718116471875511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122423290097812077647917007 183634935146718116471875511)
  ·
    refine ⟨275452402720077174707813267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183634935146718116471875511 275452402720077174707813267)
    ·
      refine ⟨413178604080115762061719901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275452402720077174707813267 413178604080115762061719901)
      ·
        refine ⟨154941976530043410773144963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413178604080115762061719901 154941976530043410773144963)
        ·
          refine ⟨232412964795065116159717445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154941976530043410773144963 232412964795065116159717445)
          ·
            refine ⟨43577430899074709279947021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232412964795065116159717445 43577430899074709279947021)
            ·
              refine ⟨16341536587153015979980133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43577430899074709279947021 16341536587153015979980133)
              ·
                refine ⟨3064038110091190496246275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16341536587153015979980133 3064038110091190496246275)
                ·
                  refine ⟨4596057165136785744369413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064038110091190496246275 4596057165136785744369413)
                  ·
                    refine ⟨861760718463147327069265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596057165136785744369413 861760718463147327069265)
                    ·
                      rfl

theorem cell23_5034819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 4].length) (baseStart_5034819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034819 prefixEnd_5034819 := by exact prefixLift 5034819
  have htrace : WordTrace (prefixWord ++ tailWord_5034819) baseStart_5034819 baseEnd_5034819 := by
    simpa [prefixWord, tailWord_5034819, baseEnd_5034819] using wordTrace_append hprefix tailTrace_5034819
  have hstable : (prefixWord ++ tailWord_5034819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034819).length < 2 ^ (prefixWord ++ tailWord_5034819).sum := by decide
  have hdescent : baseEnd_5034819 < baseStart_5034819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034875 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 6]
def baseStart_5034875 : Nat := 118140960795 + 5034875 * 2 ^ 59
def prefixEnd_5034875 : Nat := 4983230072969 + 3 ^ 40 * 5034875 * 2
def baseEnd_5034875 : Nat := 861770303435364587369179

theorem tailTrace_5034875 : CollatzResearch.WordTrace tailWord_5034875 prefixEnd_5034875 861770303435364587369179 := by
  unfold tailWord_5034875
  simp only [CollatzResearch.WordTrace]
  refine ⟨183636977634515238035914079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122424651756343492023942719 183636977634515238035914079)
  ·
    refine ⟨275455466451772857053871119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183636977634515238035914079 275455466451772857053871119)
    ·
      refine ⟨413183199677659285580806679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275455466451772857053871119 413183199677659285580806679)
      ·
        refine ⟨619774799516488928371210019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413183199677659285580806679 619774799516488928371210019)
        ·
          refine ⟨929662199274733392556815029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619774799516488928371210019 929662199274733392556815029)
          ·
            refine ⟨87155831182006255552201409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 929662199274733392556815029 87155831182006255552201409)
            ·
              refine ⟨65366873386504691664151057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87155831182006255552201409 65366873386504691664151057)
              ·
                refine ⟨49025155039878518748113293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65366873386504691664151057 49025155039878518748113293)
                ·
                  refine ⟨18384433139954444530542485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49025155039878518748113293 18384433139954444530542485)
                  ·
                    refine ⟨861770303435364587369179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18384433139954444530542485 861770303435364587369179)
                    ·
                      rfl

theorem cell23_5034875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_5034875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034875 prefixEnd_5034875 := by exact prefixLift 5034875
  have htrace : WordTrace (prefixWord ++ tailWord_5034875) baseStart_5034875 baseEnd_5034875 := by
    simpa [prefixWord, tailWord_5034875, baseEnd_5034875] using wordTrace_append hprefix tailTrace_5034875
  have hstable : (prefixWord ++ tailWord_5034875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034875).length < 2 ^ (prefixWord ++ tailWord_5034875).sum := by decide
  have hdescent : baseEnd_5034875 < baseStart_5034875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034892 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_5034892 : Nat := 118140960795 + 5034892 * 2 ^ 59
def prefixEnd_5034892 : Nat := 4983230072969 + 3 ^ 40 * 5034892 * 2
def baseEnd_5034892 : Nat := 861773213159073398531653

theorem tailTrace_5034892 : CollatzResearch.WordTrace tailWord_5034892 prefixEnd_5034892 861773213159073398531653 := by
  unfold tailWord_5034892
  simp only [CollatzResearch.WordTrace]
  refine ⟨91818798837726824969641465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122425065116969099959521953 91818798837726824969641465)
  ·
    refine ⟨68864099128295118727231099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91818798837726824969641465 68864099128295118727231099)
    ·
      refine ⟨103296148692442678090846649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68864099128295118727231099 103296148692442678090846649)
      ·
        refine ⟨77472111519332008568134987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103296148692442678090846649 77472111519332008568134987)
        ·
          refine ⟨116208167278998012852202481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77472111519332008568134987 116208167278998012852202481)
          ·
            refine ⟨87156125459248509639151861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116208167278998012852202481 87156125459248509639151861)
            ·
              refine ⟨8170886761804547778670487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87156125459248509639151861 8170886761804547778670487)
              ·
                refine ⟨12256330142706821668005731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170886761804547778670487 12256330142706821668005731)
                ·
                  refine ⟨18384495214060232502008597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12256330142706821668005731 18384495214060232502008597)
                  ·
                    refine ⟨861773213159073398531653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18384495214060232502008597 861773213159073398531653)
                    ·
                      rfl

theorem cell23_5034892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_5034892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034892 prefixEnd_5034892 := by exact prefixLift 5034892
  have htrace : WordTrace (prefixWord ++ tailWord_5034892) baseStart_5034892 baseEnd_5034892 := by
    simpa [prefixWord, tailWord_5034892, baseEnd_5034892] using wordTrace_append hprefix tailTrace_5034892
  have hstable : (prefixWord ++ tailWord_5034892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034892).length < 2 ^ (prefixWord ++ tailWord_5034892).sum := by decide
  have hdescent : baseEnd_5034892 < baseStart_5034892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034899 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 5, 2, 2]
def baseStart_5034899 : Nat := 118140960795 + 5034899 * 2 ^ 59
def prefixEnd_5034899 : Nat := 4983230072969 + 3 ^ 40 * 5034899 * 2
def baseEnd_5034899 : Nat := 2585323233841801668207427

theorem tailTrace_5034899 : CollatzResearch.WordTrace tailWord_5034899 prefixEnd_5034899 2585323233841801668207427 := by
  unfold tailWord_5034899
  simp only [CollatzResearch.WordTrace]
  refine ⟨183637852986428290134787751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122425235324285526756525167 183637852986428290134787751)
  ·
    refine ⟨275456779479642435202181627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183637852986428290134787751 275456779479642435202181627)
    ·
      refine ⟨413185169219463652803272441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275456779479642435202181627 413185169219463652803272441)
      ·
        refine ⟨309888876914597739602454331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413185169219463652803272441 309888876914597739602454331)
        ·
          refine ⟨464833315371896609403681497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309888876914597739602454331 464833315371896609403681497)
          ·
            refine ⟨348624986528922457052761123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464833315371896609403681497 348624986528922457052761123)
            ·
              refine ⟨522937479793383685579141685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348624986528922457052761123 522937479793383685579141685)
              ·
                refine ⟨49025388730629720523044533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522937479793383685579141685 49025388730629720523044533)
                ·
                  refine ⟨4596130193496536299035425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49025388730629720523044533 4596130193496536299035425)
                  ·
                    refine ⟨3447097645122402224276569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4596130193496536299035425 3447097645122402224276569)
                    ·
                      refine ⟨2585323233841801668207427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447097645122402224276569 2585323233841801668207427)
                      ·
                        rfl

theorem cell23_5034899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 2, 2].length) (baseStart_5034899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034899 prefixEnd_5034899 := by exact prefixLift 5034899
  have htrace : WordTrace (prefixWord ++ tailWord_5034899) baseStart_5034899 baseEnd_5034899 := by
    simpa [prefixWord, tailWord_5034899, baseEnd_5034899] using wordTrace_append hprefix tailTrace_5034899
  have hstable : (prefixWord ++ tailWord_5034899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034899).length < 2 ^ (prefixWord ++ tailWord_5034899).sum := by decide
  have hdescent : baseEnd_5034899 < baseStart_5034899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034912 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5034912 : Nat := 118140960795 + 5034912 * 2 ^ 59
def prefixEnd_5034912 : Nat := 4983230072969 + 3 ^ 40 * 5034912 * 2
def baseEnd_5034912 : Nat := 2585329909090310117344867

theorem tailTrace_5034912 : CollatzResearch.WordTrace tailWord_5034912 prefixEnd_5034912 2585329909090310117344867 := by
  unfold tailWord_5034912
  simp only [CollatzResearch.WordTrace]
  refine ⟨91819163567690596677505495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122425551423587462236673993 91819163567690596677505495)
  ·
    refine ⟨137728745351535895016258243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91819163567690596677505495 137728745351535895016258243)
    ·
      refine ⟨206593118027303842524387365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137728745351535895016258243 206593118027303842524387365)
      ·
        refine ⟨38736209630119470473322631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206593118027303842524387365 38736209630119470473322631)
        ·
          refine ⟨58104314445179205709983947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38736209630119470473322631 58104314445179205709983947)
          ·
            refine ⟨87156471667768808564975921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58104314445179205709983947 87156471667768808564975921)
            ·
              refine ⟨65367353750826606423731941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87156471667768808564975921 65367353750826606423731941)
              ·
                refine ⟨12256378828279988704449739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65367353750826606423731941 12256378828279988704449739)
                ·
                  refine ⟨18384568242419983056674609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12256378828279988704449739 18384568242419983056674609)
                  ·
                    refine ⟨13788426181814987292505957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18384568242419983056674609 13788426181814987292505957)
                    ·
                      refine ⟨2585329909090310117344867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13788426181814987292505957 2585329909090310117344867)
                      ·
                        rfl

theorem cell23_5034912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5034912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034912 prefixEnd_5034912 := by exact prefixLift 5034912
  have htrace : WordTrace (prefixWord ++ tailWord_5034912) baseStart_5034912 baseEnd_5034912 := by
    simpa [prefixWord, tailWord_5034912, baseEnd_5034912] using wordTrace_append hprefix tailTrace_5034912
  have hstable : (prefixWord ++ tailWord_5034912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034912).length < 2 ^ (prefixWord ++ tailWord_5034912).sum := by decide
  have hdescent : baseEnd_5034912 < baseStart_5034912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034942 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5034942 : Nat := 118140960795 + 5034942 * 2 ^ 59
def prefixEnd_5034942 : Nat := 4983230072969 + 3 ^ 40 * 5034942 * 2
def baseEnd_5034942 : Nat := 2585345313509944999969729

theorem tailTrace_5034942 : CollatzResearch.WordTrace tailWord_5034942 prefixEnd_5034942 2585345313509944999969729 := by
  unfold tailWord_5034942
  simp only [CollatzResearch.WordTrace]
  refine ⟨22954927665659063559825385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122426280883515005652402053 22954927665659063559825385)
  ·
    refine ⟨17216195749244297669869039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22954927665659063559825385 17216195749244297669869039)
    ·
      refine ⟨25824293623866446504803559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17216195749244297669869039 25824293623866446504803559)
      ·
        refine ⟨38736440435799669757205339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25824293623866446504803559 38736440435799669757205339)
        ·
          refine ⟨58104660653699504635808009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38736440435799669757205339 58104660653699504635808009)
          ·
            refine ⟨43578495490274628476856007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58104660653699504635808009 43578495490274628476856007)
            ·
              refine ⟨65367743235411942715284011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43578495490274628476856007 65367743235411942715284011)
              ·
                refine ⟨98051614853117914072926017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65367743235411942715284011 98051614853117914072926017)
                ·
                  refine ⟨73538711139838435554694513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98051614853117914072926017 73538711139838435554694513)
                  ·
                    refine ⟨55154033354878826666020885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73538711139838435554694513 55154033354878826666020885)
                    ·
                      refine ⟨2585345313509944999969729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55154033354878826666020885 2585345313509944999969729)
                      ·
                        rfl

theorem cell23_5034942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5034942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034942 prefixEnd_5034942 := by exact prefixLift 5034942
  have htrace : WordTrace (prefixWord ++ tailWord_5034942) baseStart_5034942 baseEnd_5034942 := by
    simpa [prefixWord, tailWord_5034942, baseEnd_5034942] using wordTrace_append hprefix tailTrace_5034942
  have hstable : (prefixWord ++ tailWord_5034942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034942).length < 2 ^ (prefixWord ++ tailWord_5034942).sum := by decide
  have hdescent : baseEnd_5034942 < baseStart_5034942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034966 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5034966 : Nat := 118140960795 + 5034966 * 2 ^ 59
def prefixEnd_5034966 : Nat := 4983230072969 + 3 ^ 40 * 5034966 * 2
def baseEnd_5034966 : Nat := 2585357637045652906069619

theorem tailTrace_5034966 : CollatzResearch.WordTrace tailWord_5034966 prefixEnd_5034966 2585357637045652906069619 := by
  unfold tailWord_5034966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477518542324097536092297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122426864451457040384984501 11477518542324097536092297)
  ·
    refine ⟨8608138906743073152069223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11477518542324097536092297 8608138906743073152069223)
    ·
      refine ⟨12912208360114609728103835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8608138906743073152069223 12912208360114609728103835)
      ·
        refine ⟨19368312540171914592155753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12912208360114609728103835 19368312540171914592155753)
        ·
          refine ⟨14526234405128935944116815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19368312540171914592155753 14526234405128935944116815)
          ·
            refine ⟨21789351607693403916175223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14526234405128935944116815 21789351607693403916175223)
            ·
              refine ⟨32684027411540105874262835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21789351607693403916175223 32684027411540105874262835)
              ·
                refine ⟨49026041117310158811394253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32684027411540105874262835 49026041117310158811394253)
                ·
                  refine ⟨18384765418991309554272845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49026041117310158811394253 18384765418991309554272845)
                  ·
                    refine ⟨6894287032121741082852317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18384765418991309554272845 6894287032121741082852317)
                    ·
                      refine ⟨2585357637045652906069619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6894287032121741082852317 2585357637045652906069619)
                      ·
                        rfl

theorem cell23_5034966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5034966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034966 prefixEnd_5034966 := by exact prefixLift 5034966
  have htrace : WordTrace (prefixWord ++ tailWord_5034966) baseStart_5034966 baseEnd_5034966 := by
    simpa [prefixWord, tailWord_5034966, baseEnd_5034966] using wordTrace_append hprefix tailTrace_5034966
  have hstable : (prefixWord ++ tailWord_5034966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034966).length < 2 ^ (prefixWord ++ tailWord_5034966).sum := by decide
  have hdescent : baseEnd_5034966 < baseStart_5034966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5034983 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5034983 : Nat := 118140960795 + 5034983 * 2 ^ 59
def prefixEnd_5034983 : Nat := 4983230072969 + 3 ^ 40 * 5034983 * 2
def baseEnd_5034983 : Nat := 2585366366216779339557041

theorem tailTrace_5034983 : CollatzResearch.WordTrace tailWord_5034983 prefixEnd_5034983 2585366366216779339557041 := by
  unfold tailWord_5034983
  simp only [CollatzResearch.WordTrace]
  refine ⟨183640916718123972480845603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122427277812082648320563735 183640916718123972480845603)
  ·
    refine ⟨275461375077185958721268405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183640916718123972480845603 275461375077185958721268405)
    ·
      refine ⟨25824503913486183630118913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275461375077185958721268405 25824503913486183630118913)
      ·
        refine ⟨19368377935114637722589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25824503913486183630118913 19368377935114637722589185)
        ·
          refine ⟨14526283451335978291941889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19368377935114637722589185 14526283451335978291941889)
          ·
            refine ⟨10894712588501983718956417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14526283451335978291941889 10894712588501983718956417)
            ·
              refine ⟨8171034441376487789217313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10894712588501983718956417 8171034441376487789217313)
              ·
                refine ⟨6128275831032365841912985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8171034441376487789217313 6128275831032365841912985)
                ·
                  refine ⟨4596206873274274381434739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6128275831032365841912985 4596206873274274381434739)
                  ·
                    refine ⟨6894310309911411572152109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4596206873274274381434739 6894310309911411572152109)
                    ·
                      refine ⟨2585366366216779339557041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6894310309911411572152109 2585366366216779339557041)
                      ·
                        rfl

theorem cell23_5034983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5034983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5034983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5034983 prefixEnd_5034983 := by exact prefixLift 5034983
  have htrace : WordTrace (prefixWord ++ tailWord_5034983) baseStart_5034983 baseEnd_5034983 := by
    simpa [prefixWord, tailWord_5034983, baseEnd_5034983] using wordTrace_append hprefix tailTrace_5034983
  have hstable : (prefixWord ++ tailWord_5034983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5034983).length < 2 ^ (prefixWord ++ tailWord_5034983).sum := by decide
  have hdescent : baseEnd_5034983 < baseStart_5034983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5034983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035039 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_5035039 : Nat := 118140960795 + 5035039 * 2 ^ 59
def prefixEnd_5035039 : Nat := 4983230072969 + 3 ^ 40 * 5035039 * 2
def baseEnd_5035039 : Nat := 2585395121133431120456783

theorem tailTrace_5035039 : CollatzResearch.WordTrace tailWord_5035039 prefixEnd_5035039 2585395121133431120456783 := by
  unfold tailWord_5035039
  simp only [CollatzResearch.WordTrace]
  refine ⟨183642959205921094044884171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122428639470614062696589447 183642959205921094044884171)
  ·
    refine ⟨275464438808881641067326257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183642959205921094044884171 275464438808881641067326257)
    ·
      refine ⟨206598329106661230800494693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275464438808881641067326257 206598329106661230800494693)
      ·
        refine ⟨38737186707498980775092755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206598329106661230800494693 38737186707498980775092755)
        ·
          refine ⟨58105780061248471162639133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38737186707498980775092755 58105780061248471162639133)
          ·
            refine ⟨21789667522968176685989675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58105780061248471162639133 21789667522968176685989675)
            ·
              refine ⟨32684501284452265028984513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21789667522968176685989675 32684501284452265028984513)
              ·
                refine ⟨24513375963339198771738385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32684501284452265028984513 24513375963339198771738385)
                ·
                  refine ⟨18385031972504399078803789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24513375963339198771738385 18385031972504399078803789)
                  ·
                    refine ⟨6894386989689149654551421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18385031972504399078803789 6894386989689149654551421)
                    ·
                      refine ⟨2585395121133431120456783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6894386989689149654551421 2585395121133431120456783)
                      ·
                        rfl

theorem cell23_5035039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_5035039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035039 prefixEnd_5035039 := by exact prefixLift 5035039
  have htrace : WordTrace (prefixWord ++ tailWord_5035039) baseStart_5035039 baseEnd_5035039 := by
    simpa [prefixWord, tailWord_5035039, baseEnd_5035039] using wordTrace_append hprefix tailTrace_5035039
  have hstable : (prefixWord ++ tailWord_5035039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035039).length < 2 ^ (prefixWord ++ tailWord_5035039).sum := by decide
  have hdescent : baseEnd_5035039 < baseStart_5035039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035040 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5035040 : Nat := 118140960795 + 5035040 * 2 ^ 59
def prefixEnd_5035040 : Nat := 4983230072969 + 3 ^ 40 * 5035040 * 2
def baseEnd_5035040 : Nat := 2585395634614085616544279

theorem tailTrace_5035040 : CollatzResearch.WordTrace tailWord_5035040 prefixEnd_5035040 2585395634614085616544279 := by
  unfold tailWord_5035040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91821497839458735607835287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122428663785944980810447049 91821497839458735607835287)
  ·
    refine ⟨137732246759188103411752931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91821497839458735607835287 137732246759188103411752931)
    ·
      refine ⟨206598370138782155117629397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137732246759188103411752931 206598370138782155117629397)
      ·
        refine ⟨4842149300127706760569439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 206598370138782155117629397 4842149300127706760569439)
        ·
          refine ⟨7263223950191560140854159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4842149300127706760569439 7263223950191560140854159)
          ·
            refine ⟨10894835925287340211281239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7263223950191560140854159 10894835925287340211281239)
            ·
              refine ⟨16342253887931010316921859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10894835925287340211281239 16342253887931010316921859)
              ·
                refine ⟨24513380831896515475382789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16342253887931010316921859 24513380831896515475382789)
                ·
                  refine ⟨4596258905980596651634273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24513380831896515475382789 4596258905980596651634273)
                  ·
                    refine ⟨3447194179485447488725705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4596258905980596651634273 3447194179485447488725705)
                    ·
                      refine ⟨2585395634614085616544279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447194179485447488725705 2585395634614085616544279)
                      ·
                        rfl

theorem cell23_5035040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5035040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035040 prefixEnd_5035040 := by exact prefixLift 5035040
  have htrace : WordTrace (prefixWord ++ tailWord_5035040) baseStart_5035040 baseEnd_5035040 := by
    simpa [prefixWord, tailWord_5035040, baseEnd_5035040] using wordTrace_append hprefix tailTrace_5035040
  have hstable : (prefixWord ++ tailWord_5035040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035040).length < 2 ^ (prefixWord ++ tailWord_5035040).sum := by decide
  have hdescent : baseEnd_5035040 < baseStart_5035040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035052 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_5035052 : Nat := 118140960795 + 5035052 * 2 ^ 59
def prefixEnd_5035052 : Nat := 4983230072969 + 3 ^ 40 * 5035052 * 2
def baseEnd_5035052 : Nat := 2585401796381939569594223

theorem tailTrace_5035052 : CollatzResearch.WordTrace tailWord_5035052 prefixEnd_5035052 2585401796381939569594223 := by
  unfold tailWord_5035052
  simp only [CollatzResearch.WordTrace]
  refine ⟨91821716677436998632553705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122428955569915998176738273 91821716677436998632553705)
  ·
    refine ⟨68866287508077748974415279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91821716677436998632553705 68866287508077748974415279)
    ·
      refine ⟨103299431262116623461622919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68866287508077748974415279 103299431262116623461622919)
      ·
        refine ⟨154949146893174935192434379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103299431262116623461622919 154949146893174935192434379)
        ·
          refine ⟨232423720339762402788651569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154949146893174935192434379 232423720339762402788651569)
          ·
            refine ⟨174317790254821802091488677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232423720339762402788651569 174317790254821802091488677)
            ·
              refine ⟨32684585672779087892154127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174317790254821802091488677 32684585672779087892154127)
              ·
                refine ⟨49026878509168631838231191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32684585672779087892154127 49026878509168631838231191)
                ·
                  refine ⟨73540317763752947757346787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49026878509168631838231191 73540317763752947757346787)
                  ·
                    refine ⟨110310476645629421636020181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73540317763752947757346787 110310476645629421636020181)
                    ·
                      refine ⟨2585401796381939569594223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110310476645629421636020181 2585401796381939569594223)
                      ·
                        rfl

theorem cell23_5035052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_5035052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035052 prefixEnd_5035052 := by exact prefixLift 5035052
  have htrace : WordTrace (prefixWord ++ tailWord_5035052) baseStart_5035052 baseEnd_5035052 := by
    simpa [prefixWord, tailWord_5035052, baseEnd_5035052] using wordTrace_append hprefix tailTrace_5035052
  have hstable : (prefixWord ++ tailWord_5035052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035052).length < 2 ^ (prefixWord ++ tailWord_5035052).sum := by decide
  have hdescent : baseEnd_5035052 < baseStart_5035052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035072 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_5035072 : Nat := 118140960795 + 5035072 * 2 ^ 59
def prefixEnd_5035072 : Nat := 4983230072969 + 3 ^ 40 * 5035072 * 2
def baseEnd_5035072 : Nat := 861804021998343163781377

theorem tailTrace_5035072 : CollatzResearch.WordTrace tailWord_5035072 prefixEnd_5035072 861804021998343163781377 := by
  unfold tailWord_5035072
  simp only [CollatzResearch.WordTrace]
  refine ⟨91822081407400770340417735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122429441876534360453890313 91822081407400770340417735)
  ·
    refine ⟨137733122111101155510626603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91822081407400770340417735 137733122111101155510626603)
    ·
      refine ⟨206599683166651733265939905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137733122111101155510626603 206599683166651733265939905)
      ·
        refine ⟨154949762374988799949454929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206599683166651733265939905 154949762374988799949454929)
        ·
          refine ⟨116212321781241599962091197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154949762374988799949454929 116212321781241599962091197)
          ·
            refine ⟨43579620667965599985784199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116212321781241599962091197 43579620667965599985784199)
            ·
              refine ⟨65369431001948399978676299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43579620667965599985784199 65369431001948399978676299)
              ·
                refine ⟨98054146502922599968014449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65369431001948399978676299 98054146502922599968014449)
                ·
                  refine ⟨73540609877191949976010837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98054146502922599968014449 73540609877191949976010837)
                  ·
                    refine ⟨861804021998343163781377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73540609877191949976010837 861804021998343163781377)
                    ·
                      rfl

theorem cell23_5035072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_5035072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035072 prefixEnd_5035072 := by exact prefixLift 5035072
  have htrace : WordTrace (prefixWord ++ tailWord_5035072) baseStart_5035072 baseEnd_5035072 := by
    simpa [prefixWord, tailWord_5035072, baseEnd_5035072] using wordTrace_append hprefix tailTrace_5035072
  have hstable : (prefixWord ++ tailWord_5035072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035072).length < 2 ^ (prefixWord ++ tailWord_5035072).sum := by decide
  have hdescent : baseEnd_5035072 < baseStart_5035072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035079 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_5035079 : Nat := 118140960795 + 5035079 * 2 ^ 59
def prefixEnd_5035079 : Nat := 4983230072969 + 3 ^ 40 * 5035079 * 2
def baseEnd_5035079 : Nat := 2585415660359610963956599

theorem tailTrace_5035079 : CollatzResearch.WordTrace tailWord_5035079 prefixEnd_5035079 2585415660359610963956599 := by
  unfold tailWord_5035079
  simp only [CollatzResearch.WordTrace]
  refine ⟨183644418125776180876340291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122429612083850787250893527 183644418125776180876340291)
  ·
    refine ⟨275466627188664271314510437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183644418125776180876340291 275466627188664271314510437)
    ·
      refine ⟨51649992597874550871470707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275466627188664271314510437 51649992597874550871470707)
      ·
        refine ⟨77474988896811826307206061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51649992597874550871470707 77474988896811826307206061)
        ·
          refine ⟨29053120836304434865202273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77474988896811826307206061 29053120836304434865202273)
          ·
            refine ⟨21789840627228326148901705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29053120836304434865202273 21789840627228326148901705)
            ·
              refine ⟨16342380470421244611676279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21789840627228326148901705 16342380470421244611676279)
              ·
                refine ⟨24513570705631866917514419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16342380470421244611676279 24513570705631866917514419)
                ·
                  refine ⟨36770356058447800376271629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24513570705631866917514419 36770356058447800376271629)
                  ·
                    refine ⟨13788883521917925141101861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36770356058447800376271629 13788883521917925141101861)
                    ·
                      refine ⟨2585415660359610963956599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13788883521917925141101861 2585415660359610963956599)
                      ·
                        rfl

theorem cell23_5035079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_5035079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035079 prefixEnd_5035079 := by exact prefixLift 5035079
  have htrace : WordTrace (prefixWord ++ tailWord_5035079) baseStart_5035079 baseEnd_5035079 := by
    simpa [prefixWord, tailWord_5035079, baseEnd_5035079] using wordTrace_append hprefix tailTrace_5035079
  have hstable : (prefixWord ++ tailWord_5035079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035079).length < 2 ^ (prefixWord ++ tailWord_5035079).sum := by decide
  have hdescent : baseEnd_5035079 < baseStart_5035079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035089 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_5035089 : Nat := 118140960795 + 5035089 * 2 ^ 59
def prefixEnd_5035089 : Nat := 4983230072969 + 3 ^ 40 * 5035089 * 2
def baseEnd_5035089 : Nat := 861806931722051974943851

theorem tailTrace_5035089 : CollatzResearch.WordTrace tailWord_5035089 prefixEnd_5035089 861806931722051974943851 := by
  unfold tailWord_5035089
  simp only [CollatzResearch.WordTrace]
  refine ⟨183644782855739952584204321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122429855237159968389469547 183644782855739952584204321)
  ·
    refine ⟨137733587141804964438153241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183644782855739952584204321 137733587141804964438153241)
    ·
      refine ⟨103300190356353723328614931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137733587141804964438153241 103300190356353723328614931)
      ·
        refine ⟨154950285534530584992922397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103300190356353723328614931 154950285534530584992922397)
        ·
          refine ⟨58106357075448969372345899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154950285534530584992922397 58106357075448969372345899)
          ·
            refine ⟨87159535613173454058518849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58106357075448969372345899 87159535613173454058518849)
            ·
              refine ⟨65369651709880090543889137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87159535613173454058518849 65369651709880090543889137)
              ·
                refine ⟨49027238782410067907916853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65369651709880090543889137 49027238782410067907916853)
                ·
                  refine ⟨4596303635850943866367205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49027238782410067907916853 4596303635850943866367205)
                  ·
                    refine ⟨861806931722051974943851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596303635850943866367205 861806931722051974943851)
                    ·
                      rfl

theorem cell23_5035089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_5035089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035089 prefixEnd_5035089 := by exact prefixLift 5035089
  have htrace : WordTrace (prefixWord ++ tailWord_5035089) baseStart_5035089 baseEnd_5035089 := by
    simpa [prefixWord, tailWord_5035089, baseEnd_5035089] using wordTrace_append hprefix tailTrace_5035089
  have hstable : (prefixWord ++ tailWord_5035089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035089).length < 2 ^ (prefixWord ++ tailWord_5035089).sum := by decide
  have hdescent : baseEnd_5035089 < baseStart_5035089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035119 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 6]
def baseStart_5035119 : Nat := 118140960795 + 5035119 * 2 ^ 59
def prefixEnd_5035119 : Nat := 4983230072969 + 3 ^ 40 * 5035119 * 2
def baseEnd_5035119 : Nat := 287270688842865645272935

theorem tailTrace_5035119 : CollatzResearch.WordTrace tailWord_5035119 prefixEnd_5035119 287270688842865645272935 := by
  unfold tailWord_5035119
  simp only [CollatzResearch.WordTrace]
  refine ⟨183645877045631267707796411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122430584697087511805197607 183645877045631267707796411)
  ·
    refine ⟨275468815568446901561694617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183645877045631267707796411 275468815568446901561694617)
    ·
      refine ⟨206601611676335176171270963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275468815568446901561694617 206601611676335176171270963)
      ·
        refine ⟨309902417514502764256906445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206601611676335176171270963 309902417514502764256906445)
        ·
          refine ⟨116213406567938536596339917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309902417514502764256906445 116213406567938536596339917)
          ·
            refine ⟨43580027462976951223627469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116213406567938536596339917 43580027462976951223627469)
            ·
              refine ⟨16342510298616356708860301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43580027462976951223627469 16342510298616356708860301)
              ·
                refine ⟨6128441361981133765822613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16342510298616356708860301 6128441361981133765822613)
                ·
                  refine ⟨287270688842865645272935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6128441361981133765822613 287270688842865645272935)
                  ·
                    rfl

theorem cell23_5035119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 6].length) (baseStart_5035119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035119 prefixEnd_5035119 := by exact prefixLift 5035119
  have htrace : WordTrace (prefixWord ++ tailWord_5035119) baseStart_5035119 baseEnd_5035119 := by
    simpa [prefixWord, tailWord_5035119, baseEnd_5035119] using wordTrace_append hprefix tailTrace_5035119
  have hstable : (prefixWord ++ tailWord_5035119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035119).length < 2 ^ (prefixWord ++ tailWord_5035119).sum := by decide
  have hdescent : baseEnd_5035119 < baseStart_5035119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035186 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5035186 : Nat := 118140960795 + 5035186 * 2 ^ 59
def prefixEnd_5035186 : Nat := 4983230072969 + 3 ^ 40 * 5035186 * 2
def baseEnd_5035186 : Nat := 2585470602789642045318607

theorem tailTrace_5035186 : CollatzResearch.WordTrace tailWord_5035186 prefixEnd_5035186 2585470602789642045318607 := by
  unfold tailWord_5035186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45912080184097134537621353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122432213824259025433656941 45912080184097134537621353)
  ·
    refine ⟨34434060138072850903216015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45912080184097134537621353 34434060138072850903216015)
    ·
      refine ⟨51651090207109276354824023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34434060138072850903216015 51651090207109276354824023)
      ·
        refine ⟨77476635310663914532236035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51651090207109276354824023 77476635310663914532236035)
        ·
          refine ⟨116214952965995871798354053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77476635310663914532236035 116214952965995871798354053)
          ·
            refine ⟨21790303681124225962191385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116214952965995871798354053 21790303681124225962191385)
            ·
              refine ⟨16342727760843169471643539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21790303681124225962191385 16342727760843169471643539)
              ·
                refine ⟨24514091641264754207465309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16342727760843169471643539 24514091641264754207465309)
                ·
                  refine ⟨9192784365474282827799491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24514091641264754207465309 9192784365474282827799491)
                  ·
                    refine ⟨13789176548211424241699237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9192784365474282827799491 13789176548211424241699237)
                    ·
                      refine ⟨2585470602789642045318607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13789176548211424241699237 2585470602789642045318607)
                      ·
                        rfl

theorem cell23_5035186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5035186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035186 prefixEnd_5035186 := by exact prefixLift 5035186
  have htrace : WordTrace (prefixWord ++ tailWord_5035186) baseStart_5035186 baseEnd_5035186 := by
    simpa [prefixWord, tailWord_5035186, baseEnd_5035186] using wordTrace_append hprefix tailTrace_5035186
  have hstable : (prefixWord ++ tailWord_5035186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035186).length < 2 ^ (prefixWord ++ tailWord_5035186).sum := by decide
  have hdescent : baseEnd_5035186 < baseStart_5035186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035196 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_5035196 : Nat := 118140960795 + 5035196 * 2 ^ 59
def prefixEnd_5035196 : Nat := 4983230072969 + 3 ^ 40 * 5035196 * 2
def baseEnd_5035196 : Nat := 861825245865395668731187

theorem tailTrace_5035196 : CollatzResearch.WordTrace tailWord_5035196 prefixEnd_5035196 861825245865395668731187 := by
  unfold tailWord_5035196
  simp only [CollatzResearch.WordTrace]
  refine ⟨91824342733176154929174721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122432456977568206572232961 91824342733176154929174721)
  ·
    refine ⟨68868257049882116196881041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91824342733176154929174721 68868257049882116196881041)
    ·
      refine ⟨51651192787411587147660781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68868257049882116196881041 51651192787411587147660781)
      ·
        refine ⟨19369197295279345180372793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51651192787411587147660781 19369197295279345180372793)
        ·
          refine ⟨14526897971459508885279595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19369197295279345180372793 14526897971459508885279595)
          ·
            refine ⟨21790346957189263327919393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14526897971459508885279595 21790346957189263327919393)
            ·
              refine ⟨16342760217891947495939545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21790346957189263327919393 16342760217891947495939545)
              ·
                refine ⟨12257070163418960621954659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16342760217891947495939545 12257070163418960621954659)
                ·
                  refine ⟨18385605245128440932931989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12257070163418960621954659 18385605245128440932931989)
                  ·
                    refine ⟨861825245865395668731187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18385605245128440932931989 861825245865395668731187)
                    ·
                      rfl

theorem cell23_5035196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_5035196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035196 prefixEnd_5035196 := by exact prefixLift 5035196
  have htrace : WordTrace (prefixWord ++ tailWord_5035196) baseStart_5035196 baseEnd_5035196 := by
    simpa [prefixWord, tailWord_5035196, baseEnd_5035196] using wordTrace_append hprefix tailTrace_5035196
  have hstable : (prefixWord ++ tailWord_5035196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035196).length < 2 ^ (prefixWord ++ tailWord_5035196).sum := by decide
  have hdescent : baseEnd_5035196 < baseStart_5035196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035200 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_5035200 : Nat := 118140960795 + 5035200 * 2 ^ 59
def prefixEnd_5035200 : Nat := 4983230072969 + 3 ^ 40 * 5035200 * 2
def baseEnd_5035200 : Nat := 861825930506268330181181

theorem tailTrace_5035200 : CollatzResearch.WordTrace tailWord_5035200 prefixEnd_5035200 861825930506268330181181 := by
  unfold tailWord_5035200
  simp only [CollatzResearch.WordTrace]
  refine ⟨91824415679168909270747527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122432554238891879027663369 91824415679168909270747527)
  ·
    refine ⟨137736623518753363906121291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91824415679168909270747527 137736623518753363906121291)
    ·
      refine ⟨206604935278130045859181937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137736623518753363906121291 206604935278130045859181937)
      ·
        refine ⟨154953701458597534394386453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206604935278130045859181937 154953701458597534394386453)
        ·
          refine ⟨7263454755871759424736865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154953701458597534394386453 7263454755871759424736865)
          ·
            refine ⟨5447591066903819568552649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7263454755871759424736865 5447591066903819568552649)
            ·
              refine ⟨4085693300177864676414487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5447591066903819568552649 4085693300177864676414487)
              ·
                refine ⟨6128539950266797014621731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4085693300177864676414487 6128539950266797014621731)
                ·
                  refine ⟨9192809925400195521932597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6128539950266797014621731 9192809925400195521932597)
                  ·
                    refine ⟨861825930506268330181181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9192809925400195521932597 861825930506268330181181)
                    ·
                      rfl

theorem cell23_5035200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_5035200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035200 prefixEnd_5035200 := by exact prefixLift 5035200
  have htrace : WordTrace (prefixWord ++ tailWord_5035200) baseStart_5035200 baseEnd_5035200 := by
    simpa [prefixWord, tailWord_5035200, baseEnd_5035200] using wordTrace_append hprefix tailTrace_5035200
  have hstable : (prefixWord ++ tailWord_5035200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035200).length < 2 ^ (prefixWord ++ tailWord_5035200).sum := by decide
  have hdescent : baseEnd_5035200 < baseStart_5035200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035233 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_5035233 : Nat := 118140960795 + 5035233 * 2 ^ 59
def prefixEnd_5035233 : Nat := 4983230072969 + 3 ^ 40 * 5035233 * 2
def baseEnd_5035233 : Nat := 2585494736380403361430891

theorem tailTrace_5035233 : CollatzResearch.WordTrace tailWord_5035233 prefixEnd_5035233 2585494736380403361430891 := by
  unfold tailWord_5035233
  simp only [CollatzResearch.WordTrace]
  refine ⟨183650034967218265177446353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122433356644812176784964235 183650034967218265177446353)
  ·
    refine ⟨137737526225413698883084765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183650034967218265177446353 137737526225413698883084765)
    ·
      refine ⟨51651572334530137081156787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137737526225413698883084765 51651572334530137081156787)
      ·
        refine ⟨77477358501795205621735181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51651572334530137081156787 77477358501795205621735181)
        ·
          refine ⟨29054009438173202108150693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77477358501795205621735181 29054009438173202108150693)
          ·
            refine ⟨5447626769657475395278255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29054009438173202108150693 5447626769657475395278255)
            ·
              refine ⟨8171440154486213092917383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5447626769657475395278255 8171440154486213092917383)
              ·
                refine ⟨12257160231729319639376075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8171440154486213092917383 12257160231729319639376075)
                ·
                  refine ⟨18385740347593979459064113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12257160231729319639376075 18385740347593979459064113)
                  ·
                    refine ⟨13789305260695484594298085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18385740347593979459064113 13789305260695484594298085)
                    ·
                      refine ⟨2585494736380403361430891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13789305260695484594298085 2585494736380403361430891)
                      ·
                        rfl

theorem cell23_5035233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_5035233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035233 prefixEnd_5035233 := by exact prefixLift 5035233
  have htrace : WordTrace (prefixWord ++ tailWord_5035233) baseStart_5035233 baseEnd_5035233 := by
    simpa [prefixWord, tailWord_5035233, baseEnd_5035233] using wordTrace_append hprefix tailTrace_5035233
  have hstable : (prefixWord ++ tailWord_5035233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035233).length < 2 ^ (prefixWord ++ tailWord_5035233).sum := by decide
  have hdescent : baseEnd_5035233 < baseStart_5035233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035289 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_5035289 : Nat := 118140960795 + 5035289 * 2 ^ 59
def prefixEnd_5035289 : Nat := 4983230072969 + 3 ^ 40 * 5035289 * 2
def baseEnd_5035289 : Nat := 2585523491297055142330633

theorem tailTrace_5035289 : CollatzResearch.WordTrace tailWord_5035289 prefixEnd_5035289 2585523491297055142330633 := by
  unfold tailWord_5035289
  simp only [CollatzResearch.WordTrace]
  refine ⟨183652077455015386741484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122434718303343591160989947 183652077455015386741484921)
  ·
    refine ⟨137739058091261540056113691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183652077455015386741484921 137739058091261540056113691)
    ·
      refine ⟨206608587136892310084170537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137739058091261540056113691 206608587136892310084170537)
      ·
        refine ⟨154956440352669232563127903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206608587136892310084170537 154956440352669232563127903)
        ·
          refine ⟨232434660529003848844691855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154956440352669232563127903 232434660529003848844691855)
          ·
            refine ⟨348651990793505773267037783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232434660529003848844691855 348651990793505773267037783)
            ·
              refine ⟨522977986190258659900556675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348651990793505773267037783 522977986190258659900556675)
              ·
                refine ⟨784466979285387989850835013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522977986190258659900556675 784466979285387989850835013)
                ·
                  refine ⟨147087558616010248097031565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784466979285387989850835013 147087558616010248097031565)
                  ·
                    refine ⟨55157834481003843036386837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147087558616010248097031565 55157834481003843036386837)
                    ·
                      refine ⟨2585523491297055142330633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55157834481003843036386837 2585523491297055142330633)
                      ·
                        rfl

theorem cell23_5035289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_5035289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035289 prefixEnd_5035289 := by exact prefixLift 5035289
  have htrace : WordTrace (prefixWord ++ tailWord_5035289) baseStart_5035289 baseEnd_5035289 := by
    simpa [prefixWord, tailWord_5035289, baseEnd_5035289] using wordTrace_append hprefix tailTrace_5035289
  have hstable : (prefixWord ++ tailWord_5035289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035289).length < 2 ^ (prefixWord ++ tailWord_5035289).sum := by decide
  have hdescent : baseEnd_5035289 < baseStart_5035289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035327 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 2, 2, 2]
def baseStart_5035327 : Nat := 118140960795 + 5035327 * 2 ^ 59
def prefixEnd_5035327 : Nat := 4983230072969 + 3 ^ 40 * 5035327 * 2
def baseEnd_5035327 : Nat := 2585543003561925993655459

theorem tailTrace_5035327 : CollatzResearch.WordTrace tailWord_5035327 prefixEnd_5035327 2585543003561925993655459 := by
  unfold tailWord_5035327
  simp only [CollatzResearch.WordTrace]
  refine ⟨183653463428877719231368235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122435642285918479487578823 183653463428877719231368235)
  ·
    refine ⟨275480195143316578847052353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183653463428877719231368235 275480195143316578847052353)
    ·
      refine ⟨206610146357487434135289265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275480195143316578847052353 206610146357487434135289265)
      ·
        refine ⟨154957609768115575601466949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206610146357487434135289265 154957609768115575601466949)
        ·
          refine ⟨29054551831521670425275053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154957609768115575601466949 29054551831521670425275053)
          ·
            refine ⟨10895456936820626409478145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29054551831521670425275053 10895456936820626409478145)
            ·
              refine ⟨8171592702615469807108609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10895456936820626409478145 8171592702615469807108609)
              ·
                refine ⟨6128694526961602355331457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8171592702615469807108609 6128694526961602355331457)
                ·
                  refine ⟨4596520895221201766498593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6128694526961602355331457 4596520895221201766498593)
                  ·
                    refine ⟨3447390671415901324873945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4596520895221201766498593 3447390671415901324873945)
                    ·
                      refine ⟨2585543003561925993655459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447390671415901324873945 2585543003561925993655459)
                      ·
                        rfl

theorem cell23_5035327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_5035327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035327 prefixEnd_5035327 := by exact prefixLift 5035327
  have htrace : WordTrace (prefixWord ++ tailWord_5035327) baseStart_5035327 baseEnd_5035327 := by
    simpa [prefixWord, tailWord_5035327, baseEnd_5035327] using wordTrace_append hprefix tailTrace_5035327
  have hstable : (prefixWord ++ tailWord_5035327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035327).length < 2 ^ (prefixWord ++ tailWord_5035327).sum := by decide
  have hdescent : baseEnd_5035327 < baseStart_5035327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035346 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5035346 : Nat := 118140960795 + 5035346 * 2 ^ 59
def prefixEnd_5035346 : Nat := 4983230072969 + 3 ^ 40 * 5035346 * 2
def baseEnd_5035346 : Nat := 861850919898120473105957

theorem tailTrace_5035346 : CollatzResearch.WordTrace tailWord_5035346 prefixEnd_5035346 861850919898120473105957 := by
  unfold tailWord_5035346
  simp only [CollatzResearch.WordTrace]
  refine ⟨45913539103952221369077473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122436104277205923650873261 45913539103952221369077473)
  ·
    refine ⟨34435154327964166026808105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45913539103952221369077473 34435154327964166026808105)
    ·
      refine ⟨25826365745973124520106079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34435154327964166026808105 25826365745973124520106079)
      ·
        refine ⟨38739548618959686780159119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25826365745973124520106079 38739548618959686780159119)
        ·
          refine ⟨58109322928439530170238679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38739548618959686780159119 58109322928439530170238679)
          ·
            refine ⟨87163984392659295255358019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58109322928439530170238679 87163984392659295255358019)
            ·
              refine ⟨130745976588988942883037029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87163984392659295255358019 130745976588988942883037029)
              ·
                refine ⟨24514870610435426790569443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130745976588988942883037029 24514870610435426790569443)
                ·
                  refine ⟨36772305915653140185854165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24514870610435426790569443 36772305915653140185854165)
                  ·
                    refine ⟨861850919898120473105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36772305915653140185854165 861850919898120473105957)
                    ·
                      rfl

theorem cell23_5035346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5035346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035346 prefixEnd_5035346 := by exact prefixLift 5035346
  have htrace : WordTrace (prefixWord ++ tailWord_5035346) baseStart_5035346 baseEnd_5035346 := by
    simpa [prefixWord, tailWord_5035346, baseEnd_5035346] using wordTrace_append hprefix tailTrace_5035346
  have hstable : (prefixWord ++ tailWord_5035346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035346).length < 2 ^ (prefixWord ++ tailWord_5035346).sum := by decide
  have hdescent : baseEnd_5035346 < baseStart_5035346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035363 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 2, 5]
def baseStart_5035363 : Nat := 118140960795 + 5035363 * 2 ^ 59
def prefixEnd_5035363 : Nat := 4983230072969 + 3 ^ 40 * 5035363 * 2
def baseEnd_5035363 : Nat := 861853829621829284268431

theorem tailTrace_5035363 : CollatzResearch.WordTrace tailWord_5035363 prefixEnd_5035363 861853829621829284268431 := by
  unfold tailWord_5035363
  simp only [CollatzResearch.WordTrace]
  refine ⟨183654776456747297379678743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122436517637831531586452495 183654776456747297379678743)
  ·
    refine ⟨275482164685120946069518115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183654776456747297379678743 275482164685120946069518115)
    ·
      refine ⟨413223247027681419104277173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275482164685120946069518115 413223247027681419104277173)
      ·
        refine ⟨38739679408845133041025985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 413223247027681419104277173 38739679408845133041025985)
        ·
          refine ⟨29054759556633849780769489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38739679408845133041025985 29054759556633849780769489)
          ·
            refine ⟨21791069667475387335577117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29054759556633849780769489 21791069667475387335577117)
            ·
              refine ⟨8171651125303270250841419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21791069667475387335577117 8171651125303270250841419)
              ·
                refine ⟨12257476687954905376262129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8171651125303270250841419 12257476687954905376262129)
                ·
                  refine ⟨9193107515966179032196597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12257476687954905376262129 9193107515966179032196597)
                  ·
                    refine ⟨861853829621829284268431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9193107515966179032196597 861853829621829284268431)
                    ·
                      rfl

theorem cell23_5035363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].length) (baseStart_5035363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035363 prefixEnd_5035363 := by exact prefixLift 5035363
  have htrace : WordTrace (prefixWord ++ tailWord_5035363) baseStart_5035363 baseEnd_5035363 := by
    simpa [prefixWord, tailWord_5035363, baseEnd_5035363] using wordTrace_append hprefix tailTrace_5035363
  have hstable : (prefixWord ++ tailWord_5035363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035363).length < 2 ^ (prefixWord ++ tailWord_5035363).sum := by decide
  have hdescent : baseEnd_5035363 < baseStart_5035363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035383 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_5035383 : Nat := 118140960795 + 5035383 * 2 ^ 59
def prefixEnd_5035383 : Nat := 4983230072969 + 3 ^ 40 * 5035383 * 2
def baseEnd_5035383 : Nat := 2585571758478577774555201

theorem tailTrace_5035383 : CollatzResearch.WordTrace tailWord_5035383 prefixEnd_5035383 2585571758478577774555201 := by
  unfold tailWord_5035383
  simp only [CollatzResearch.WordTrace]
  refine ⟨183655505916674840795406803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122437003944449893863604535 183655505916674840795406803)
  ·
    refine ⟨275483258875012261193110205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183655505916674840795406803 275483258875012261193110205)
    ·
      refine ⟨103306222078129597947416327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275483258875012261193110205 103306222078129597947416327)
      ·
        refine ⟨154959333117194396921124491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103306222078129597947416327 154959333117194396921124491)
        ·
          refine ⟨232438999675791595381686737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154959333117194396921124491 232438999675791595381686737)
          ·
            refine ⟨174329249756843696536265053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232438999675791595381686737 174329249756843696536265053)
            ·
              refine ⟨65373468658816386201099395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174329249756843696536265053 65373468658816386201099395)
              ·
                refine ⟨98060202988224579301649093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65373468658816386201099395 98060202988224579301649093)
                ·
                  refine ⟨18386288060292108619059205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98060202988224579301649093 18386288060292108619059205)
                  ·
                    refine ⟨3447429011304770366073601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18386288060292108619059205 3447429011304770366073601)
                    ·
                      refine ⟨2585571758478577774555201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447429011304770366073601 2585571758478577774555201)
                      ·
                        rfl

theorem cell23_5035383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_5035383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035383 prefixEnd_5035383 := by exact prefixLift 5035383
  have htrace : WordTrace (prefixWord ++ tailWord_5035383) baseStart_5035383 baseEnd_5035383 := by
    simpa [prefixWord, tailWord_5035383, baseEnd_5035383] using wordTrace_append hprefix tailTrace_5035383
  have hstable : (prefixWord ++ tailWord_5035383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035383).length < 2 ^ (prefixWord ++ tailWord_5035383).sum := by decide
  have hdescent : baseEnd_5035383 < baseStart_5035383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035400 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_5035400 : Nat := 118140960795 + 5035400 * 2 ^ 59
def prefixEnd_5035400 : Nat := 4983230072969 + 3 ^ 40 * 5035400 * 2
def baseEnd_5035400 : Nat := 2585580487649704208042623

theorem tailTrace_5035400 : CollatzResearch.WordTrace tailWord_5035400 prefixEnd_5035400 2585580487649704208042623 := by
  unfold tailWord_5035400
  simp only [CollatzResearch.WordTrace]
  refine ⟨91828062978806626349387827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122437417305075501799183769 91828062978806626349387827)
  ·
    refine ⟨137742094468209939524081741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91828062978806626349387827 137742094468209939524081741)
    ·
      refine ⟨51653285425578727321530653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137742094468209939524081741 51653285425578727321530653)
      ·
        refine ⟨19369982034592022745573995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51653285425578727321530653 19369982034592022745573995)
        ·
          refine ⟨29054973051888034118360993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19369982034592022745573995 29054973051888034118360993)
          ·
            refine ⟨21791229788916025588770745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29054973051888034118360993 21791229788916025588770745)
            ·
              refine ⟨16343422341687019191578059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21791229788916025588770745 16343422341687019191578059)
              ·
                refine ⟨24515133512530528787367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16343422341687019191578059 24515133512530528787367089)
                ·
                  refine ⟨18386350134397896590525317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24515133512530528787367089 18386350134397896590525317)
                  ·
                    refine ⟨3447440650199605610723497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18386350134397896590525317 3447440650199605610723497)
                    ·
                      refine ⟨2585580487649704208042623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447440650199605610723497 2585580487649704208042623)
                      ·
                        rfl

theorem cell23_5035400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_5035400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035400 prefixEnd_5035400 := by exact prefixLift 5035400
  have htrace : WordTrace (prefixWord ++ tailWord_5035400) baseStart_5035400 baseEnd_5035400 := by
    simpa [prefixWord, tailWord_5035400, baseEnd_5035400] using wordTrace_append hprefix tailTrace_5035400
  have hstable : (prefixWord ++ tailWord_5035400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035400).length < 2 ^ (prefixWord ++ tailWord_5035400).sum := by decide
  have hdescent : baseEnd_5035400 < baseStart_5035400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035437 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5035437 : Nat := 118140960795 + 5035437 * 2 ^ 59
def prefixEnd_5035437 : Nat := 4983230072969 + 3 ^ 40 * 5035437 * 2
def baseEnd_5035437 : Nat := 2585599486433920563279953

theorem tailTrace_5035437 : CollatzResearch.WordTrace tailWord_5035437 prefixEnd_5035437 2585599486433920563279953 := by
  unfold tailWord_5035437
  simp only [CollatzResearch.WordTrace]
  refine ⟨183657475458479208017872565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122438316972319472011915043 183657475458479208017872565)
  ·
    refine ⟨17217888324232425751675553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183657475458479208017872565 17217888324232425751675553)
    ·
      refine ⟨12913416243174319313756665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17217888324232425751675553 12913416243174319313756665)
      ·
        refine ⟨9685062182380739485317499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12913416243174319313756665 9685062182380739485317499)
        ·
          refine ⟨14527593273571109227976249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9685062182380739485317499 14527593273571109227976249)
          ·
            refine ⟨10895694955178331920982187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14527593273571109227976249 10895694955178331920982187)
            ·
              refine ⟨16343542432767497881473281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10895694955178331920982187 16343542432767497881473281)
              ·
                refine ⟨12257656824575623411104961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16343542432767497881473281 12257656824575623411104961)
                ·
                  refine ⟨9193242618431717558328721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12257656824575623411104961 9193242618431717558328721)
                  ·
                    refine ⟨6894931963823788168746541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9193242618431717558328721 6894931963823788168746541)
                    ·
                      refine ⟨2585599486433920563279953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6894931963823788168746541 2585599486433920563279953)
                      ·
                        rfl

theorem cell23_5035437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5035437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035437 prefixEnd_5035437 := by exact prefixLift 5035437
  have htrace : WordTrace (prefixWord ++ tailWord_5035437) baseStart_5035437 baseEnd_5035437 := by
    simpa [prefixWord, tailWord_5035437, baseEnd_5035437] using wordTrace_append hprefix tailTrace_5035437
  have hstable : (prefixWord ++ tailWord_5035437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035437).length < 2 ^ (prefixWord ++ tailWord_5035437).sum := by decide
  have hdescent : baseEnd_5035437 < baseStart_5035437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035453 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_5035453 : Nat := 118140960795 + 5035453 * 2 ^ 59
def prefixEnd_5035453 : Nat := 4983230072969 + 3 ^ 40 * 5035453 * 2
def baseEnd_5035453 : Nat := 861869234041464166893293

theorem tailTrace_5035453 : CollatzResearch.WordTrace tailWord_5035453 prefixEnd_5035453 861869234041464166893293 := by
  unfold tailWord_5035453
  simp only [CollatzResearch.WordTrace]
  refine ⟨183658059026421242750455013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122438706017614161833636675 183658059026421242750455013)
  ·
    refine ⟨34435886067453983015710315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183658059026421242750455013 34435886067453983015710315)
    ·
      refine ⟨51653829101180974523565473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34435886067453983015710315 51653829101180974523565473)
      ·
        refine ⟨38740371825885730892674105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51653829101180974523565473 38740371825885730892674105)
        ·
          refine ⟨29055278869414298169505579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38740371825885730892674105 29055278869414298169505579)
          ·
            refine ⟨43582918304121447254258369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29055278869414298169505579 43582918304121447254258369)
            ·
              refine ⟨32687188728091085440693777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43582918304121447254258369 32687188728091085440693777)
              ·
                refine ⟨24515391546068314080520333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32687188728091085440693777 24515391546068314080520333)
                ·
                  refine ⟨9193271829775617780195125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24515391546068314080520333 9193271829775617780195125)
                  ·
                    refine ⟨861869234041464166893293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9193271829775617780195125 861869234041464166893293)
                    ·
                      rfl

theorem cell23_5035453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_5035453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035453 prefixEnd_5035453 := by exact prefixLift 5035453
  have htrace : WordTrace (prefixWord ++ tailWord_5035453) baseStart_5035453 baseEnd_5035453 := by
    simpa [prefixWord, tailWord_5035453, baseEnd_5035453] using wordTrace_append hprefix tailTrace_5035453
  have hstable : (prefixWord ++ tailWord_5035453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035453).length < 2 ^ (prefixWord ++ tailWord_5035453).sum := by decide
  have hdescent : baseEnd_5035453 < baseStart_5035453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035470 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5035470 : Nat := 118140960795 + 5035470 * 2 ^ 59
def prefixEnd_5035470 : Nat := 4983230072969 + 3 ^ 40 * 5035470 * 2
def baseEnd_5035470 : Nat := 861872143765172978055767

theorem tailTrace_5035470 : CollatzResearch.WordTrace tailWord_5035470 prefixEnd_5035470 861872143765172978055767 := by
  unfold tailWord_5035470
  simp only [CollatzResearch.WordTrace]
  refine ⟨22957334883419956831727983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122439119378239769769215909 22957334883419956831727983)
  ·
    refine ⟨34436002325129935247591975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22957334883419956831727983 34436002325129935247591975)
    ·
      refine ⟨51654003487694902871387963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34436002325129935247591975 51654003487694902871387963)
      ·
        refine ⟨77481005231542354307081945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51654003487694902871387963 77481005231542354307081945)
        ·
          refine ⟨58110753923656765730311459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77481005231542354307081945 58110753923656765730311459)
          ·
            refine ⟨87166130885485148595467189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58110753923656765730311459 87166130885485148595467189)
            ·
              refine ⟨8171824770514232680825049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87166130885485148595467189 8171824770514232680825049)
              ·
                refine ⟨6128868577885674510618787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8171824770514232680825049 6128868577885674510618787)
                ·
                  refine ⟨9193302866828511765928181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6128868577885674510618787 9193302866828511765928181)
                  ·
                    refine ⟨861872143765172978055767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9193302866828511765928181 861872143765172978055767)
                    ·
                      rfl

theorem cell23_5035470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5035470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035470 prefixEnd_5035470 := by exact prefixLift 5035470
  have htrace : WordTrace (prefixWord ++ tailWord_5035470) baseStart_5035470 baseEnd_5035470 := by
    simpa [prefixWord, tailWord_5035470, baseEnd_5035470] using wordTrace_append hprefix tailTrace_5035470
  have hstable : (prefixWord ++ tailWord_5035470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035470).length < 2 ^ (prefixWord ++ tailWord_5035470).sum := by decide
  have hdescent : baseEnd_5035470 < baseStart_5035470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035477 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_5035477 : Nat := 118140960795 + 5035477 * 2 ^ 59
def prefixEnd_5035477 : Nat := 4983230072969 + 3 ^ 40 * 5035477 * 2
def baseEnd_5035477 : Nat := 2585620025660100406779769

theorem tailTrace_5035477 : CollatzResearch.WordTrace tailWord_5035477 prefixEnd_5035477 2585620025660100406779769 := by
  unfold tailWord_5035477
  simp only [CollatzResearch.WordTrace]
  refine ⟨183658934378334294849328685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122439289585556196566219123 183658934378334294849328685)
  ·
    refine ⟨68872100391875360568498257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183658934378334294849328685 68872100391875360568498257)
    ·
      refine ⟨51654075293906520426373693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68872100391875360568498257 51654075293906520426373693)
      ·
        refine ⟨19370278235214945159890135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51654075293906520426373693 19370278235214945159890135)
        ·
          refine ⟨29055417352822417739835203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19370278235214945159890135 29055417352822417739835203)
          ·
            refine ⟨43583126029233626609752805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29055417352822417739835203 43583126029233626609752805)
            ·
              refine ⟨8171836130481304989328651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43583126029233626609752805 8171836130481304989328651)
              ·
                refine ⟨12257754195721957483992977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8171836130481304989328651 12257754195721957483992977)
                ·
                  refine ⟨9193315646791468112994733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12257754195721957483992977 9193315646791468112994733)
                  ·
                    refine ⟨3447493367546800542373025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9193315646791468112994733 3447493367546800542373025)
                    ·
                      refine ⟨2585620025660100406779769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447493367546800542373025 2585620025660100406779769)
                      ·
                        rfl

theorem cell23_5035477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_5035477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035477 prefixEnd_5035477 := by exact prefixLift 5035477
  have htrace : WordTrace (prefixWord ++ tailWord_5035477) baseStart_5035477 baseEnd_5035477 := by
    simpa [prefixWord, tailWord_5035477, baseEnd_5035477] using wordTrace_append hprefix tailTrace_5035477
  have hstable : (prefixWord ++ tailWord_5035477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035477).length < 2 ^ (prefixWord ++ tailWord_5035477).sum := by decide
  have hdescent : baseEnd_5035477 < baseStart_5035477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035501 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5035501 : Nat := 118140960795 + 5035501 * 2 ^ 59
def prefixEnd_5035501 : Nat := 4983230072969 + 3 ^ 40 * 5035501 * 2
def baseEnd_5035501 : Nat := 2585632349195808312879659

theorem tailTrace_5035501 : CollatzResearch.WordTrace tailWord_5035501 prefixEnd_5035501 2585632349195808312879659 := by
  unfold tailWord_5035501
  simp only [CollatzResearch.WordTrace]
  refine ⟨183659809730247346948202357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122439873153498231298801571 183659809730247346948202357)
  ·
    refine ⟨17218107162210688776393971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183659809730247346948202357 17218107162210688776393971)
    ·
      refine ⟨25827160743316033164590957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17218107162210688776393971 25827160743316033164590957)
      ·
        refine ⟨9685185278743512436721609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25827160743316033164590957 9685185278743512436721609)
        ·
          refine ⟨7263888959057634327541207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9685185278743512436721609 7263888959057634327541207)
          ·
            refine ⟨10895833438586451491311811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7263888959057634327541207 10895833438586451491311811)
            ·
              refine ⟨16343750157879677236967717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10895833438586451491311811 16343750157879677236967717)
              ·
                refine ⟨3064453154602439481931447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16343750157879677236967717 3064453154602439481931447)
                ·
                  refine ⟨4596679731903659222897171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064453154602439481931447 4596679731903659222897171)
                  ·
                    refine ⟨6895019597855488834345757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4596679731903659222897171 6895019597855488834345757)
                    ·
                      refine ⟨2585632349195808312879659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6895019597855488834345757 2585632349195808312879659)
                      ·
                        rfl

theorem cell23_5035501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5035501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035501 prefixEnd_5035501 := by exact prefixLift 5035501
  have htrace : WordTrace (prefixWord ++ tailWord_5035501) baseStart_5035501 baseEnd_5035501 := by
    simpa [prefixWord, tailWord_5035501, baseEnd_5035501] using wordTrace_append hprefix tailTrace_5035501
  have hstable : (prefixWord ++ tailWord_5035501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035501).length < 2 ^ (prefixWord ++ tailWord_5035501).sum := by decide
  have hdescent : baseEnd_5035501 < baseStart_5035501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035530 : List Nat := [3, 1, 2, 2, 2, 3, 3, 7]
def baseStart_5035530 : Nat := 118140960795 + 5035530 * 2 ^ 59
def prefixEnd_5035530 : Nat := 4983230072969 + 3 ^ 40 * 5035530 * 2
def baseEnd_5035530 : Nat := 95764712597584766645075

theorem tailTrace_5035530 : CollatzResearch.WordTrace tailWord_5035530 prefixEnd_5035530 95764712597584766645075 := by
  unfold tailWord_5035530
  simp only [CollatzResearch.WordTrace]
  refine ⟨45915216861785571225252011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122440578298094856600672029 45915216861785571225252011)
  ·
    refine ⟨68872825292678356837878017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45915216861785571225252011 68872825292678356837878017)
    ·
      refine ⟨51654618969508767628408513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68872825292678356837878017 51654618969508767628408513)
      ·
        refine ⟨38740964227131575721306385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51654618969508767628408513 38740964227131575721306385)
        ·
          refine ⟨29055723170348681790979789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38740964227131575721306385 29055723170348681790979789)
          ·
            refine ⟨10895896188880755671617421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29055723170348681790979789 10895896188880755671617421)
            ·
              refine ⟨4085961070830283376856533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10895896188880755671617421 4085961070830283376856533)
              ·
                refine ⟨95764712597584766645075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4085961070830283376856533 95764712597584766645075)
                ·
                  rfl

theorem cell23_5035530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_5035530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035530 prefixEnd_5035530 := by exact prefixLift 5035530
  have htrace : WordTrace (prefixWord ++ tailWord_5035530) baseStart_5035530 baseEnd_5035530 := by
    simpa [prefixWord, tailWord_5035530, baseEnd_5035530] using wordTrace_append hprefix tailTrace_5035530
  have hstable : (prefixWord ++ tailWord_5035530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035530).length < 2 ^ (prefixWord ++ tailWord_5035530).sum := by decide
  have hdescent : baseEnd_5035530 < baseStart_5035530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035541 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_5035541 : Nat := 118140960795 + 5035541 * 2 ^ 59
def prefixEnd_5035541 : Nat := 4983230072969 + 3 ^ 40 * 5035541 * 2
def baseEnd_5035541 : Nat := 2585652888421988156379475

theorem tailTrace_5035541 : CollatzResearch.WordTrace tailWord_5035541 prefixEnd_5035541 2585652888421988156379475 := by
  unfold tailWord_5035541
  simp only [CollatzResearch.WordTrace]
  refine ⟨183661268650102433779658477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122440845766734955853105651 183661268650102433779658477)
  ·
    refine ⟨68872975743788412667371929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183661268650102433779658477 68872975743788412667371929)
    ·
      refine ⟨51654731807841309500528947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68872975743788412667371929 51654731807841309500528947)
      ·
        refine ⟨77482097711761964250793421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51654731807841309500528947 77482097711761964250793421)
        ·
          refine ⟨29055786641910736594047533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77482097711761964250793421 29055786641910736594047533)
          ·
            refine ⟨10895919990716526222767825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29055786641910736594047533 10895919990716526222767825)
            ·
              refine ⟨8171939993037394667075869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10895919990716526222767825 8171939993037394667075869)
              ·
                refine ⟨3064477497389023000153451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171939993037394667075869 3064477497389023000153451)
                ·
                  refine ⟨4596716246083534500230177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064477497389023000153451 4596716246083534500230177)
                  ·
                    refine ⟨3447537184562650875172633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4596716246083534500230177 3447537184562650875172633)
                    ·
                      refine ⟨2585652888421988156379475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447537184562650875172633 2585652888421988156379475)
                      ·
                        rfl

theorem cell23_5035541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_5035541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035541 prefixEnd_5035541 := by exact prefixLift 5035541
  have htrace : WordTrace (prefixWord ++ tailWord_5035541) baseStart_5035541 baseEnd_5035541 := by
    simpa [prefixWord, tailWord_5035541, baseEnd_5035541] using wordTrace_append hprefix tailTrace_5035541
  have hstable : (prefixWord ++ tailWord_5035541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035541).length < 2 ^ (prefixWord ++ tailWord_5035541).sum := by decide
  have hdescent : baseEnd_5035541 < baseStart_5035541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035593 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_5035593 : Nat := 118140960795 + 5035593 * 2 ^ 59
def prefixEnd_5035593 : Nat := 4983230072969 + 3 ^ 40 * 5035593 * 2
def baseEnd_5035593 : Nat := 2585679589416021952929235

theorem tailTrace_5035593 : CollatzResearch.WordTrace tailWord_5035593 prefixEnd_5035593 2585679589416021952929235 := by
  unfold tailWord_5035593
  simp only [CollatzResearch.WordTrace]
  refine ⟨183663165245914046660551433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122442110163942697773700955 183663165245914046660551433)
  ·
    refine ⟨137747373934435534995413575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183663165245914046660551433 137747373934435534995413575)
    ·
      refine ⟨206621060901653302493120363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137747373934435534995413575 206621060901653302493120363)
      ·
        refine ⟨309931591352479953739680545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206621060901653302493120363 309931591352479953739680545)
        ·
          refine ⟨232448693514359965304760409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309931591352479953739680545 232448693514359965304760409)
          ·
            refine ⟨174336520135769973978570307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232448693514359965304760409 174336520135769973978570307)
            ·
              refine ⟨261504780203654960967855461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174336520135769973978570307 261504780203654960967855461)
              ·
                refine ⟨49032146288185305181472899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261504780203654960967855461 49032146288185305181472899)
                ·
                  refine ⟨73548219432277957772209349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49032146288185305181472899 73548219432277957772209349)
                  ·
                    refine ⟨13790291143552117082289253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73548219432277957772209349 13790291143552117082289253)
                    ·
                      refine ⟨2585679589416021952929235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13790291143552117082289253 2585679589416021952929235)
                      ·
                        rfl

theorem cell23_5035593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_5035593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035593 prefixEnd_5035593 := by exact prefixLift 5035593
  have htrace : WordTrace (prefixWord ++ tailWord_5035593) baseStart_5035593 baseEnd_5035593 := by
    simpa [prefixWord, tailWord_5035593, baseEnd_5035593] using wordTrace_append hprefix tailTrace_5035593
  have hstable : (prefixWord ++ tailWord_5035593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035593).length < 2 ^ (prefixWord ++ tailWord_5035593).sum := by decide
  have hdescent : baseEnd_5035593 < baseStart_5035593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035620 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 7]
def baseStart_5035620 : Nat := 118140960795 + 5035620 * 2 ^ 59
def prefixEnd_5035620 : Nat := 4983230072969 + 3 ^ 40 * 5035620 * 2
def baseEnd_5035620 : Nat := 287299272599299260810179

theorem tailTrace_5035620 : CollatzResearch.WordTrace tailWord_5035620 prefixEnd_5035620 287299272599299260810179 := by
  unfold tailWord_5035620
  simp only [CollatzResearch.WordTrace]
  refine ⟨91832075008408115135892157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122442766677877486847856209 91832075008408115135892157)
  ·
    refine ⟨34437028128153043175959559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91832075008408115135892157 34437028128153043175959559)
    ·
      refine ⟨51655542192229564763939339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34437028128153043175959559 51655542192229564763939339)
      ·
        refine ⟨77483313288344347145909009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51655542192229564763939339 77483313288344347145909009)
        ·
          refine ⟨58112484966258260359431757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77483313288344347145909009 58112484966258260359431757)
          ·
            refine ⟨21792181862346847634786909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58112484966258260359431757 21792181862346847634786909)
            ·
              refine ⟨8172068198380067863045091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21792181862346847634786909 8172068198380067863045091)
              ·
                refine ⟨12258102297570101794567637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172068198380067863045091 12258102297570101794567637)
                ·
                  refine ⟨287299272599299260810179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12258102297570101794567637 287299272599299260810179)
                  ·
                    rfl

theorem cell23_5035620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_5035620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035620 prefixEnd_5035620 := by exact prefixLift 5035620
  have htrace : WordTrace (prefixWord ++ tailWord_5035620) baseStart_5035620 baseEnd_5035620 := by
    simpa [prefixWord, tailWord_5035620, baseEnd_5035620] using wordTrace_append hprefix tailTrace_5035620
  have hstable : (prefixWord ++ tailWord_5035620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035620).length < 2 ^ (prefixWord ++ tailWord_5035620).sum := by decide
  have hdescent : baseEnd_5035620 < baseStart_5035620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035633 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_5035633 : Nat := 118140960795 + 5035633 * 2 ^ 59
def prefixEnd_5035633 : Nat := 4983230072969 + 3 ^ 40 * 5035633 * 2
def baseEnd_5035633 : Nat := 861900042880733932143017

theorem tailTrace_5035633 : CollatzResearch.WordTrace tailWord_5035633 prefixEnd_5035633 861900042880733932143017 := by
  unfold tailWord_5035633
  simp only [CollatzResearch.WordTrace]
  refine ⟨183664624165769133492007553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122443082777179422328005035 183664624165769133492007553)
  ·
    refine ⟨137748468124326850119005665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183664624165769133492007553 137748468124326850119005665)
    ·
      refine ⟨103311351093245137589254249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137748468124326850119005665 103311351093245137589254249)
      ·
        refine ⟨77483513319933853191940687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103311351093245137589254249 77483513319933853191940687)
        ·
          refine ⟨116225269979900779787911031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77483513319933853191940687 116225269979900779787911031)
          ·
            refine ⟨174337904969851169681866547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116225269979900779787911031 174337904969851169681866547)
            ·
              refine ⟨261506857454776754522799821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174337904969851169681866547 261506857454776754522799821)
              ·
                refine ⟨98065071545541282946049933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261506857454776754522799821 98065071545541282946049933)
                ·
                  refine ⟨36774401829577981104768725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98065071545541282946049933 36774401829577981104768725)
                  ·
                    refine ⟨861900042880733932143017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36774401829577981104768725 861900042880733932143017)
                    ·
                      rfl

theorem cell23_5035633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_5035633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035633 prefixEnd_5035633 := by exact prefixLift 5035633
  have htrace : WordTrace (prefixWord ++ tailWord_5035633) baseStart_5035633 baseEnd_5035633 := by
    simpa [prefixWord, tailWord_5035633, baseEnd_5035633] using wordTrace_append hprefix tailTrace_5035633
  have hstable : (prefixWord ++ tailWord_5035633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035633).length < 2 ^ (prefixWord ++ tailWord_5035633).sum := by decide
  have hdescent : baseEnd_5035633 < baseStart_5035633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035643 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_5035643 : Nat := 118140960795 + 5035643 * 2 ^ 59
def prefixEnd_5035643 : Nat := 4983230072969 + 3 ^ 40 * 5035643 * 2
def baseEnd_5035643 : Nat := 2585705263448746757304005

theorem tailTrace_5035643 : CollatzResearch.WordTrace tailWord_5035643 prefixEnd_5035643 2585705263448746757304005 := by
  unfold tailWord_5035643
  simp only [CollatzResearch.WordTrace]
  refine ⟨183664988895732905199871583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122443325930488603466581055 183664988895732905199871583)
  ·
    refine ⟨275497483343599357799807375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183664988895732905199871583 275497483343599357799807375)
    ·
      refine ⟨413246225015399036699711063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275497483343599357799807375 413246225015399036699711063)
      ·
        refine ⟨619869337523098555049566595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413246225015399036699711063 619869337523098555049566595)
        ·
          refine ⟨929804006284647832574349893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619869337523098555049566595 929804006284647832574349893)
          ·
            refine ⟨174338251178371468607690605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 929804006284647832574349893 174338251178371468607690605)
            ·
              refine ⟨65376844191889300727883977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174338251178371468607690605 65376844191889300727883977)
              ·
                refine ⟨49032633143916975545912983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65376844191889300727883977 49032633143916975545912983)
                ·
                  refine ⟨73548949715875463318869475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49032633143916975545912983 73548949715875463318869475)
                  ·
                    refine ⟨110323424573813194978304213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73548949715875463318869475 110323424573813194978304213)
                    ·
                      refine ⟨2585705263448746757304005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110323424573813194978304213 2585705263448746757304005)
                      ·
                        rfl

theorem cell23_5035643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_5035643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035643 prefixEnd_5035643 := by exact prefixLift 5035643
  have htrace : WordTrace (prefixWord ++ tailWord_5035643) baseStart_5035643 baseEnd_5035643 := by
    simpa [prefixWord, tailWord_5035643, baseEnd_5035643] using wordTrace_append hprefix tailTrace_5035643
  have hstable : (prefixWord ++ tailWord_5035643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035643).length < 2 ^ (prefixWord ++ tailWord_5035643).sum := by decide
  have hdescent : baseEnd_5035643 < baseStart_5035643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035701 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_5035701 : Nat := 118140960795 + 5035701 * 2 ^ 59
def prefixEnd_5035701 : Nat := 4983230072969 + 3 ^ 40 * 5035701 * 2
def baseEnd_5035701 : Nat := 861911681775569176792913

theorem tailTrace_5035701 : CollatzResearch.WordTrace tailWord_5035701 prefixEnd_5035701 861911681775569176792913 := by
  unfold tailWord_5035701
  simp only [CollatzResearch.WordTrace]
  refine ⟨183667104329522781105482957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122444736219681854070321971 183667104329522781105482957)
  ·
    refine ⟨68875164123571042914556109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183667104329522781105482957 68875164123571042914556109)
    ·
      refine ⟨25828186546339141092958541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68875164123571042914556109 25828186546339141092958541)
      ·
        refine ⟨9685569954877177909859453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25828186546339141092958541 9685569954877177909859453)
        ·
          refine ⟨3632088733078941716197295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9685569954877177909859453 3632088733078941716197295)
          ·
            refine ⟨5448133099618412574295943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632088733078941716197295 5448133099618412574295943)
            ·
              refine ⟨8172199649427618861443915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448133099618412574295943 8172199649427618861443915)
              ·
                refine ⟨12258299474141428292165873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172199649427618861443915 12258299474141428292165873)
                ·
                  refine ⟨9193724605606071219124405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12258299474141428292165873 9193724605606071219124405)
                  ·
                    refine ⟨861911681775569176792913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9193724605606071219124405 861911681775569176792913)
                    ·
                      rfl

theorem cell23_5035701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_5035701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035701 prefixEnd_5035701 := by exact prefixLift 5035701
  have htrace : WordTrace (prefixWord ++ tailWord_5035701) baseStart_5035701 baseEnd_5035701 := by
    simpa [prefixWord, tailWord_5035701, baseEnd_5035701] using wordTrace_append hprefix tailTrace_5035701
  have hstable : (prefixWord ++ tailWord_5035701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035701).length < 2 ^ (prefixWord ++ tailWord_5035701).sum := by decide
  have hdescent : baseEnd_5035701 < baseStart_5035701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035754 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_5035754 : Nat := 118140960795 + 5035754 * 2 ^ 59
def prefixEnd_5035754 : Nat := 4983230072969 + 3 ^ 40 * 5035754 * 2
def baseEnd_5035754 : Nat := 2585762259801395823015995

theorem tailTrace_5035754 : CollatzResearch.WordTrace tailWord_5035754 prefixEnd_5035754 2585762259801395823015995 := by
  unfold tailWord_5035754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917259349582692789290579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122446024932220514104774877 45917259349582692789290579)
  ·
    refine ⟨68875889024374039183935869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45917259349582692789290579 68875889024374039183935869)
    ·
      refine ⟨25828458384140264693975951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68875889024374039183935869 25828458384140264693975951)
      ·
        refine ⟨38742687576210397040963927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25828458384140264693975951 38742687576210397040963927)
        ·
          refine ⟨58114031364315595561445891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38742687576210397040963927 58114031364315595561445891)
          ·
            refine ⟨87171047046473393342168837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58114031364315595561445891 87171047046473393342168837)
            ·
              refine ⟨16344571321213761251656657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87171047046473393342168837 16344571321213761251656657)
              ·
                refine ⟨12258428490910320938742493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16344571321213761251656657 12258428490910320938742493)
                ·
                  refine ⟨4596910684091370352028435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12258428490910320938742493 4596910684091370352028435)
                  ·
                    refine ⟨6895366026137055528042653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4596910684091370352028435 6895366026137055528042653)
                    ·
                      refine ⟨2585762259801395823015995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6895366026137055528042653 2585762259801395823015995)
                      ·
                        rfl

theorem cell23_5035754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_5035754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035754 prefixEnd_5035754 := by exact prefixLift 5035754
  have htrace : WordTrace (prefixWord ++ tailWord_5035754) baseStart_5035754 baseEnd_5035754 := by
    simpa [prefixWord, tailWord_5035754, baseEnd_5035754] using wordTrace_append hprefix tailTrace_5035754
  have hstable : (prefixWord ++ tailWord_5035754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035754).length < 2 ^ (prefixWord ++ tailWord_5035754).sum := by decide
  have hdescent : baseEnd_5035754 < baseStart_5035754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035770 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_5035770 : Nat := 118140960795 + 5035770 * 2 ^ 59
def prefixEnd_5035770 : Nat := 4983230072969 + 3 ^ 40 * 5035770 * 2
def baseEnd_5035770 : Nat := 861923491830622586805307

theorem tailTrace_5035770 : CollatzResearch.WordTrace tailWord_5035770 prefixEnd_5035770 861923491830622586805307 := by
  unfold tailWord_5035770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45917405241568201472436191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122446413977515203926496509 45917405241568201472436191)
  ·
    refine ⟨68876107862352302208654287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45917405241568201472436191 68876107862352302208654287)
    ·
      refine ⟨103314161793528453312981431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68876107862352302208654287 103314161793528453312981431)
      ·
        refine ⟨154971242690292679969472147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103314161793528453312981431 154971242690292679969472147)
        ·
          refine ⟨232456864035439019954208221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154971242690292679969472147 232456864035439019954208221)
          ·
            refine ⟨87171324013289632482828083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232456864035439019954208221 87171324013289632482828083)
            ·
              refine ⟨130756986019934448724242125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87171324013289632482828083 130756986019934448724242125)
              ·
                refine ⟨49033869757475418271590797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130756986019934448724242125 49033869757475418271590797)
                ·
                  refine ⟨18387701159053281851846549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49033869757475418271590797 18387701159053281851846549)
                  ·
                    refine ⟨861923491830622586805307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18387701159053281851846549 861923491830622586805307)
                    ·
                      rfl

theorem cell23_5035770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_5035770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035770 prefixEnd_5035770 := by exact prefixLift 5035770
  have htrace : WordTrace (prefixWord ++ tailWord_5035770) baseStart_5035770 baseEnd_5035770 := by
    simpa [prefixWord, tailWord_5035770, baseEnd_5035770] using wordTrace_append hprefix tailTrace_5035770
  have hstable : (prefixWord ++ tailWord_5035770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035770).length < 2 ^ (prefixWord ++ tailWord_5035770).sum := by decide
  have hdescent : baseEnd_5035770 < baseStart_5035770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035787 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 4, 4]
def baseStart_5035787 : Nat := 118140960795 + 5035787 * 2 ^ 59
def prefixEnd_5035787 : Nat := 4983230072969 + 3 ^ 40 * 5035787 * 2
def baseEnd_5035787 : Nat := 861926401554331397967781

theorem tailTrace_5035787 : CollatzResearch.WordTrace tailWord_5035787 prefixEnd_5035787 861926401554331397967781 := by
  unfold tailWord_5035787
  simp only [CollatzResearch.WordTrace]
  refine ⟨183670241007211217793113615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122446827338140811862075743 183670241007211217793113615)
  ·
    refine ⟨275505361510816826689670423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183670241007211217793113615 275505361510816826689670423)
    ·
      refine ⟨413258042266225240034505635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275505361510816826689670423 413258042266225240034505635)
      ·
        refine ⟨619887063399337860051758453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413258042266225240034505635 619887063399337860051758453)
        ·
          refine ⟨58114412193687924379852355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 619887063399337860051758453 58114412193687924379852355)
          ·
            refine ⟨87171618290531886569778533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58114412193687924379852355 87171618290531886569778533)
            ·
              refine ⟨16344678429474728731833475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87171618290531886569778533 16344678429474728731833475)
              ·
                refine ⟨24517017644212093097750213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16344678429474728731833475 24517017644212093097750213)
                ·
                  refine ⟨4596940808289767455828165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24517017644212093097750213 4596940808289767455828165)
                  ·
                    refine ⟨861926401554331397967781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596940808289767455828165 861926401554331397967781)
                    ·
                      rfl

theorem cell23_5035787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 4].length) (baseStart_5035787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035787 prefixEnd_5035787 := by exact prefixLift 5035787
  have htrace : WordTrace (prefixWord ++ tailWord_5035787) baseStart_5035787 baseEnd_5035787 := by
    simpa [prefixWord, tailWord_5035787, baseEnd_5035787] using wordTrace_append hprefix tailTrace_5035787
  have hstable : (prefixWord ++ tailWord_5035787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035787).length < 2 ^ (prefixWord ++ tailWord_5035787).sum := by decide
  have hdescent : baseEnd_5035787 < baseStart_5035787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035797 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_5035797 : Nat := 118140960795 + 5035797 * 2 ^ 59
def prefixEnd_5035797 : Nat := 4983230072969 + 3 ^ 40 * 5035797 * 2
def baseEnd_5035797 : Nat := 2585784339469539154778297

theorem tailTrace_5035797 : CollatzResearch.WordTrace tailWord_5035797 prefixEnd_5035797 2585784339469539154778297 := by
  unfold tailWord_5035797
  simp only [CollatzResearch.WordTrace]
  refine ⟨183670605737174989500977645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122447070491449993000651763 183670605737174989500977645)
  ·
    refine ⟨68876477151440621062866617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183670605737174989500977645 68876477151440621062866617)
    ·
      refine ⟨51657357863580465797149963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68876477151440621062866617 51657357863580465797149963)
      ·
        refine ⟨77486036795370698695724945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51657357863580465797149963 77486036795370698695724945)
        ·
          refine ⟨58114527596528024021793709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77486036795370698695724945 58114527596528024021793709)
          ·
            refine ⟨21792947848698009008172641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58114527596528024021793709 21792947848698009008172641)
            ·
              refine ⟨16344710886523506756129481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21792947848698009008172641 16344710886523506756129481)
              ·
                refine ⟨12258533164892630067097111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16344710886523506756129481 12258533164892630067097111)
                ·
                  refine ⟨18387799747338945100645667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12258533164892630067097111 18387799747338945100645667)
                  ·
                    refine ⟨27581699621008417650968501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18387799747338945100645667 27581699621008417650968501)
                    ·
                      refine ⟨2585784339469539154778297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27581699621008417650968501 2585784339469539154778297)
                      ·
                        rfl

theorem cell23_5035797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_5035797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035797 prefixEnd_5035797 := by exact prefixLift 5035797
  have htrace : WordTrace (prefixWord ++ tailWord_5035797) baseStart_5035797 baseEnd_5035797 := by
    simpa [prefixWord, tailWord_5035797, baseEnd_5035797] using wordTrace_append hprefix tailTrace_5035797
  have hstable : (prefixWord ++ tailWord_5035797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035797).length < 2 ^ (prefixWord ++ tailWord_5035797).sum := by decide
  have hdescent : baseEnd_5035797 < baseStart_5035797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035800 : List Nat := [2, 1, 2, 3, 1, 1, 3, 10]
def baseStart_5035800 : Nat := 118140960795 + 5035800 * 2 ^ 59
def prefixEnd_5035800 : Nat := 4983230072969 + 3 ^ 40 * 5035800 * 2
def baseEnd_5035800 : Nat := 95769847404129727520029

theorem tailTrace_5035800 : CollatzResearch.WordTrace tailWord_5035800 prefixEnd_5035800 95769847404129727520029 := by
  unfold tailWord_5035800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835357578082060506668427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122447143437442747342224569 91835357578082060506668427)
  ·
    refine ⟨137753036367123090760002641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91835357578082060506668427 137753036367123090760002641)
    ·
      refine ⟨103314777275342318070001981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137753036367123090760002641 103314777275342318070001981)
      ·
        refine ⟨38743041478253369276250743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103314777275342318070001981 38743041478253369276250743)
        ·
          refine ⟨58114562217380053914376115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38743041478253369276250743 58114562217380053914376115)
          ·
            refine ⟨87171843326070080871564173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58114562217380053914376115 87171843326070080871564173)
            ·
              refine ⟨32689441247276280326836565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87171843326070080871564173 32689441247276280326836565)
              ·
                refine ⟨95769847404129727520029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32689441247276280326836565 95769847404129727520029)
                ·
                  rfl

theorem cell23_5035800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 10].length) (baseStart_5035800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035800 prefixEnd_5035800 := by exact prefixLift 5035800
  have htrace : WordTrace (prefixWord ++ tailWord_5035800) baseStart_5035800 baseEnd_5035800 := by
    simpa [prefixWord, tailWord_5035800, baseEnd_5035800] using wordTrace_append hprefix tailTrace_5035800
  have hstable : (prefixWord ++ tailWord_5035800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035800).length < 2 ^ (prefixWord ++ tailWord_5035800).sum := by decide
  have hdescent : baseEnd_5035800 < baseStart_5035800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035804 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_5035804 : Nat := 118140960795 + 5035804 * 2 ^ 59
def prefixEnd_5035804 : Nat := 4983230072969 + 3 ^ 40 * 5035804 * 2
def baseEnd_5035804 : Nat := 861929311278040209130255

theorem tailTrace_5035804 : CollatzResearch.WordTrace tailWord_5035804 prefixEnd_5035804 861929311278040209130255 := by
  unfold tailWord_5035804
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835430524074814848241233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122447240698766419797654977 91835430524074814848241233)
  ·
    refine ⟨68876572893056111136180925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91835430524074814848241233 68876572893056111136180925)
    ·
      refine ⟨25828714834896041676067847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68876572893056111136180925 25828714834896041676067847)
      ·
        refine ⟨38743072252344062514101771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25828714834896041676067847 38743072252344062514101771)
        ·
          refine ⟨58114608378516093771152657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38743072252344062514101771 58114608378516093771152657)
          ·
            refine ⟨43585956283887070328364493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58114608378516093771152657 43585956283887070328364493)
            ·
              refine ⟨16344733606457651373136685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43585956283887070328364493 16344733606457651373136685)
              ·
                refine ⟨6129275102421619264926257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16344733606457651373136685 6129275102421619264926257)
                ·
                  refine ⟨4596956326816214448694693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6129275102421619264926257 4596956326816214448694693)
                  ·
                    refine ⟨861929311278040209130255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4596956326816214448694693 861929311278040209130255)
                    ·
                      rfl

theorem cell23_5035804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_5035804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035804 prefixEnd_5035804 := by exact prefixLift 5035804
  have htrace : WordTrace (prefixWord ++ tailWord_5035804) baseStart_5035804 baseEnd_5035804 := by
    simpa [prefixWord, tailWord_5035804, baseEnd_5035804] using wordTrace_append hprefix tailTrace_5035804
  have hstable : (prefixWord ++ tailWord_5035804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035804).length < 2 ^ (prefixWord ++ tailWord_5035804).sum := by decide
  have hdescent : baseEnd_5035804 < baseStart_5035804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035807 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5035807 : Nat := 118140960795 + 5035807 * 2 ^ 59
def prefixEnd_5035807 : Nat := 4983230072969 + 3 ^ 40 * 5035807 * 2
def baseEnd_5035807 : Nat := 2585789474276084115653251

theorem tailTrace_5035807 : CollatzResearch.WordTrace tailWord_5035807 prefixEnd_5035807 2585789474276084115653251 := by
  unfold tailWord_5035807
  simp only [CollatzResearch.WordTrace]
  refine ⟨183670970467138761208841675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122447313644759174139227783 183670970467138761208841675)
  ·
    refine ⟨275506455700708141813262513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183670970467138761208841675 275506455700708141813262513)
    ·
      refine ⟨206629841775531106359946885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275506455700708141813262513 206629841775531106359946885)
      ·
        refine ⟨38743095332912082442490041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206629841775531106359946885 38743095332912082442490041)
        ·
          refine ⟨29057321499684061831867531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38743095332912082442490041 29057321499684061831867531)
          ·
            refine ⟨43585982249526092747801297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29057321499684061831867531 43585982249526092747801297)
            ·
              refine ⟨32689486687144569560850973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43585982249526092747801297 32689486687144569560850973)
              ·
                refine ⟨12258557507679213585319115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32689486687144569560850973 12258557507679213585319115)
                ·
                  refine ⟨18387836261518820377978673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12258557507679213585319115 18387836261518820377978673)
                  ·
                    refine ⟨13790877196139115283484005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18387836261518820377978673 13790877196139115283484005)
                    ·
                      refine ⟨2585789474276084115653251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13790877196139115283484005 2585789474276084115653251)
                      ·
                        rfl

theorem cell23_5035807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5035807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035807 prefixEnd_5035807 := by exact prefixLift 5035807
  have htrace : WordTrace (prefixWord ++ tailWord_5035807) baseStart_5035807 baseEnd_5035807 := by
    simpa [prefixWord, tailWord_5035807, baseEnd_5035807] using wordTrace_append hprefix tailTrace_5035807
  have hstable : (prefixWord ++ tailWord_5035807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035807).length < 2 ^ (prefixWord ++ tailWord_5035807).sum := by decide
  have hdescent : baseEnd_5035807 < baseStart_5035807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035828 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5035828 : Nat := 118140960795 + 5035828 * 2 ^ 59
def prefixEnd_5035828 : Nat := 4983230072969 + 3 ^ 40 * 5035828 * 2
def baseEnd_5035828 : Nat := 2585800257369828533490655

theorem tailTrace_5035828 : CollatzResearch.WordTrace tailWord_5035828 prefixEnd_5035828 2585800257369828533490655 := by
  unfold tailWord_5035828
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835868200031340897678069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122447824266708454530237425 91835868200031340897678069)
  ·
    refine ⟨8609612643752938209157319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91835868200031340897678069 8609612643752938209157319)
    ·
      refine ⟨12914418965629407313735979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8609612643752938209157319 12914418965629407313735979)
      ·
        refine ⟨19371628448444110970603969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914418965629407313735979 19371628448444110970603969)
        ·
          refine ⟨14528721336333083227952977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19371628448444110970603969 14528721336333083227952977)
          ·
            refine ⟨10896541002249812420964733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14528721336333083227952977 10896541002249812420964733)
            ·
              refine ⟨4086202875843679657861775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10896541002249812420964733 4086202875843679657861775)
              ·
                refine ⟨6129304313765519486792663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086202875843679657861775 6129304313765519486792663)
                ·
                  refine ⟨9193956470648279230188995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129304313765519486792663 9193956470648279230188995)
                  ·
                    refine ⟨13790934705972418845283493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9193956470648279230188995 13790934705972418845283493)
                    ·
                      refine ⟨2585800257369828533490655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13790934705972418845283493 2585800257369828533490655)
                      ·
                        rfl

theorem cell23_5035828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5035828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035828 prefixEnd_5035828 := by exact prefixLift 5035828
  have htrace : WordTrace (prefixWord ++ tailWord_5035828) baseStart_5035828 baseEnd_5035828 := by
    simpa [prefixWord, tailWord_5035828, baseEnd_5035828] using wordTrace_append hprefix tailTrace_5035828
  have hstable : (prefixWord ++ tailWord_5035828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035828).length < 2 ^ (prefixWord ++ tailWord_5035828).sum := by decide
  have hdescent : baseEnd_5035828 < baseStart_5035828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035840 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_5035840 : Nat := 118140960795 + 5035840 * 2 ^ 59
def prefixEnd_5035840 : Nat := 4983230072969 + 3 ^ 40 * 5035840 * 2
def baseEnd_5035840 : Nat := 2585806419137682486540599

theorem tailTrace_5035840 : CollatzResearch.WordTrace tailWord_5035840 prefixEnd_5035840 2585806419137682486540599 := by
  unfold tailWord_5035840
  simp only [CollatzResearch.WordTrace]
  refine ⟨91836087038009603922396487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122448116050679471896528649 91836087038009603922396487)
  ·
    refine ⟨137754130557014405883594731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91836087038009603922396487 137754130557014405883594731)
    ·
      refine ⟨206631195835521608825392097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137754130557014405883594731 206631195835521608825392097)
      ·
        refine ⟨154973396876641206619044073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206631195835521608825392097 154973396876641206619044073)
        ·
          refine ⟨116230047657480904964283055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154973396876641206619044073 116230047657480904964283055)
          ·
            refine ⟨174345071486221357446424583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116230047657480904964283055 174345071486221357446424583)
            ·
              refine ⟨261517607229332036169636875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174345071486221357446424583 261517607229332036169636875)
              ·
                refine ⟨392276410843998054254455313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261517607229332036169636875 392276410843998054254455313)
                ·
                  refine ⟨294207308132998540690841485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392276410843998054254455313 294207308132998540690841485)
                  ·
                    refine ⟨110327740549874452759065557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294207308132998540690841485 110327740549874452759065557)
                    ·
                      refine ⟨2585806419137682486540599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110327740549874452759065557 2585806419137682486540599)
                      ·
                        rfl

theorem cell23_5035840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_5035840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035840 prefixEnd_5035840 := by exact prefixLift 5035840
  have htrace : WordTrace (prefixWord ++ tailWord_5035840) baseStart_5035840 baseEnd_5035840 := by
    simpa [prefixWord, tailWord_5035840, baseEnd_5035840] using wordTrace_append hprefix tailTrace_5035840
  have hstable : (prefixWord ++ tailWord_5035840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035840).length < 2 ^ (prefixWord ++ tailWord_5035840).sum := by decide
  have hdescent : baseEnd_5035840 < baseStart_5035840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035861 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_5035861 : Nat := 118140960795 + 5035861 * 2 ^ 59
def prefixEnd_5035861 : Nat := 4983230072969 + 3 ^ 40 * 5035861 * 2
def baseEnd_5035861 : Nat := 2585817202231426904378003

theorem tailTrace_5035861 : CollatzResearch.WordTrace tailWord_5035861 prefixEnd_5035861 2585817202231426904378003 := by
  unfold tailWord_5035861
  simp only [CollatzResearch.WordTrace]
  refine ⟨183672940008943128431307437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122448626672628752287538291 183672940008943128431307437)
  ·
    refine ⟨68877352503353673161740289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183672940008943128431307437 68877352503353673161740289)
    ·
      refine ⟨51658014377515254871305217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68877352503353673161740289 51658014377515254871305217)
      ·
        refine ⟨38743510783136441153478913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51658014377515254871305217 38743510783136441153478913)
        ·
          refine ⟨29057633087352330865109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38743510783136441153478913 29057633087352330865109185)
          ·
            refine ⟨21793224815514248148831889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29057633087352330865109185 21793224815514248148831889)
            ·
              refine ⟨16344918611635686111623917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21793224815514248148831889 16344918611635686111623917)
              ·
                refine ⟨6129344479363382291858969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16344918611635686111623917 6129344479363382291858969)
                ·
                  refine ⟨4597008359522536718894227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6129344479363382291858969 4597008359522536718894227)
                  ·
                    refine ⟨6895512539283805078341341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597008359522536718894227 6895512539283805078341341)
                    ·
                      refine ⟨2585817202231426904378003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6895512539283805078341341 2585817202231426904378003)
                      ·
                        rfl

theorem cell23_5035861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_5035861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035861 prefixEnd_5035861 := by exact prefixLift 5035861
  have htrace : WordTrace (prefixWord ++ tailWord_5035861) baseStart_5035861 baseEnd_5035861 := by
    simpa [prefixWord, tailWord_5035861, baseEnd_5035861] using wordTrace_append hprefix tailTrace_5035861
  have hstable : (prefixWord ++ tailWord_5035861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035861).length < 2 ^ (prefixWord ++ tailWord_5035861).sum := by decide
  have hdescent : baseEnd_5035861 < baseStart_5035861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035882 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5035882 : Nat := 118140960795 + 5035882 * 2 ^ 59
def prefixEnd_5035882 : Nat := 4983230072969 + 3 ^ 40 * 5035882 * 2
def baseEnd_5035882 : Nat := 2585827985325171322215407

theorem tailTrace_5035882 : CollatzResearch.WordTrace tailWord_5035882 prefixEnd_5035882 2585827985325171322215407 := by
  unfold tailWord_5035882
  simp only [CollatzResearch.WordTrace]
  refine ⟨45918426485466762254455475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122449137294578032678547933 45918426485466762254455475)
  ·
    refine ⟨68877639728200143381683213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45918426485466762254455475 68877639728200143381683213)
    ·
      refine ⟨25829114898075053768131205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68877639728200143381683213 25829114898075053768131205)
      ·
        refine ⟨4842959043389072581524601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25829114898075053768131205 4842959043389072581524601)
        ·
          refine ⟨3632219282541804436143451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4842959043389072581524601 3632219282541804436143451)
          ·
            refine ⟨5448328923812706654215177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632219282541804436143451 5448328923812706654215177)
            ·
              refine ⟨4086246692859529990661383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5448328923812706654215177 4086246692859529990661383)
              ·
                refine ⟨6129370039289294985992075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086246692859529990661383 6129370039289294985992075)
                ·
                  refine ⟨9194055058933942478988113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129370039289294985992075 9194055058933942478988113)
                  ·
                    refine ⟨6895541294200456859241085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9194055058933942478988113 6895541294200456859241085)
                    ·
                      refine ⟨2585827985325171322215407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6895541294200456859241085 2585827985325171322215407)
                      ·
                        rfl

theorem cell23_5035882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5035882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035882 prefixEnd_5035882 := by exact prefixLift 5035882
  have htrace : WordTrace (prefixWord ++ tailWord_5035882) baseStart_5035882 baseEnd_5035882 := by
    simpa [prefixWord, tailWord_5035882, baseEnd_5035882] using wordTrace_append hprefix tailTrace_5035882
  have hstable : (prefixWord ++ tailWord_5035882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035882).length < 2 ^ (prefixWord ++ tailWord_5035882).sum := by decide
  have hdescent : baseEnd_5035882 < baseStart_5035882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035897 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_5035897 : Nat := 118140960795 + 5035897 * 2 ^ 59
def prefixEnd_5035897 : Nat := 4983230072969 + 3 ^ 40 * 5035897 * 2
def baseEnd_5035897 : Nat := 2585835687534988763527837

theorem tailTrace_5035897 : CollatzResearch.WordTrace tailWord_5035897 prefixEnd_5035897 2585835687534988763527837 := by
  unfold tailWord_5035897
  simp only [CollatzResearch.WordTrace]
  refine ⟨183674253036812706579617945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122449502024541804386411963 183674253036812706579617945)
  ·
    refine ⟨137755689777609529934713459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183674253036812706579617945 137755689777609529934713459)
    ·
      refine ⟨206633534666414294902070189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137755689777609529934713459 206633534666414294902070189)
      ·
        refine ⟨77487575499905360588276321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206633534666414294902070189 77487575499905360588276321)
        ·
          refine ⟨58115681624929020441207241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77487575499905360588276321 58115681624929020441207241)
          ·
            refine ⟨43586761218696765330905431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58115681624929020441207241 43586761218696765330905431)
            ·
              refine ⟨65380141828045147996358147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43586761218696765330905431 65380141828045147996358147)
              ·
                refine ⟨98070212742067721994537221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65380141828045147996358147 98070212742067721994537221)
                ·
                  refine ⟨18388164889137697873975729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98070212742067721994537221 18388164889137697873975729)
                  ·
                    refine ⟨13791123666853273405481797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18388164889137697873975729 13791123666853273405481797)
                    ·
                      refine ⟨2585835687534988763527837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13791123666853273405481797 2585835687534988763527837)
                      ·
                        rfl

theorem cell23_5035897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_5035897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035897 prefixEnd_5035897 := by exact prefixLift 5035897
  have htrace : WordTrace (prefixWord ++ tailWord_5035897) baseStart_5035897 baseEnd_5035897 := by
    simpa [prefixWord, tailWord_5035897, baseEnd_5035897] using wordTrace_append hprefix tailTrace_5035897
  have hstable : (prefixWord ++ tailWord_5035897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035897).length < 2 ^ (prefixWord ++ tailWord_5035897).sum := by decide
  have hdescent : baseEnd_5035897 < baseStart_5035897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035907 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 7]
def baseStart_5035907 : Nat := 118140960795 + 5035907 * 2 ^ 59
def prefixEnd_5035907 : Nat := 4983230072969 + 3 ^ 40 * 5035907 * 2
def baseEnd_5035907 : Nat := 287315646926837080489199

theorem tailTrace_5035907 : CollatzResearch.WordTrace tailWord_5035907 prefixEnd_5035907 287315646926837080489199 := by
  unfold tailWord_5035907
  simp only [CollatzResearch.WordTrace]
  refine ⟨183674617766776478287481975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122449745177850985524987983 183674617766776478287481975)
  ·
    refine ⟨275511926650164717431222963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183674617766776478287481975 275511926650164717431222963)
    ·
      refine ⟨413267889975247076146834445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275511926650164717431222963 413267889975247076146834445)
      ·
        refine ⟨154975458740717653555062917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413267889975247076146834445 154975458740717653555062917)
        ·
          refine ⟨29057898513884560041574297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154975458740717653555062917 29057898513884560041574297)
          ·
            refine ⟨21793423885413420031180723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29057898513884560041574297 21793423885413420031180723)
            ·
              refine ⟨32690135828120130046771085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21793423885413420031180723 32690135828120130046771085)
              ·
                refine ⟨12258800935545048767539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32690135828120130046771085 12258800935545048767539157)
                ·
                  refine ⟨287315646926837080489199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12258800935545048767539157 287315646926837080489199)
                  ·
                    rfl

theorem cell23_5035907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 7].length) (baseStart_5035907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035907 prefixEnd_5035907 := by exact prefixLift 5035907
  have htrace : WordTrace (prefixWord ++ tailWord_5035907) baseStart_5035907 baseEnd_5035907 := by
    simpa [prefixWord, tailWord_5035907, baseEnd_5035907] using wordTrace_append hprefix tailTrace_5035907
  have hstable : (prefixWord ++ tailWord_5035907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035907).length < 2 ^ (prefixWord ++ tailWord_5035907).sum := by decide
  have hdescent : baseEnd_5035907 < baseStart_5035907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035924 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 7]
def baseStart_5035924 : Nat := 118140960795 + 5035924 * 2 ^ 59
def prefixEnd_5035924 : Nat := 4983230072969 + 3 ^ 40 * 5035924 * 2
def baseEnd_5035924 : Nat := 287316616834740017543357

theorem tailTrace_5035924 : CollatzResearch.WordTrace tailWord_5035924 prefixEnd_5035924 287316616834740017543357 := by
  unfold tailWord_5035924
  simp only [CollatzResearch.WordTrace]
  refine ⟨91837618903857445095425413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122450158538476593460567217 91837618903857445095425413)
  ·
    refine ⟨17219553544473270955392265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91837618903857445095425413 17219553544473270955392265)
    ·
      refine ⟨12914665158354953216544199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17219553544473270955392265 12914665158354953216544199)
      ·
        refine ⟨19371997737532429824816299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914665158354953216544199 19371997737532429824816299)
        ·
          refine ⟨29057996606298644737224449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19371997737532429824816299 29057996606298644737224449)
          ·
            refine ⟨21793497454723983552918337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29057996606298644737224449 21793497454723983552918337)
            ·
              refine ⟨16345123091042987664688753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21793497454723983552918337 16345123091042987664688753)
              ·
                refine ⟨12258842318282240748516565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16345123091042987664688753 12258842318282240748516565)
                ·
                  refine ⟨287316616834740017543357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12258842318282240748516565 287316616834740017543357)
                  ·
                    rfl

theorem cell23_5035924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_5035924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035924 prefixEnd_5035924 := by exact prefixLift 5035924
  have htrace : WordTrace (prefixWord ++ tailWord_5035924) baseStart_5035924 baseEnd_5035924 := by
    simpa [prefixWord, tailWord_5035924, baseEnd_5035924] using wordTrace_append hprefix tailTrace_5035924
  have hstable : (prefixWord ++ tailWord_5035924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035924).length < 2 ^ (prefixWord ++ tailWord_5035924).sum := by decide
  have hdescent : baseEnd_5035924 < baseStart_5035924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5035984 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_5035984 : Nat := 118140960795 + 5035984 * 2 ^ 59
def prefixEnd_5035984 : Nat := 4983230072969 + 3 ^ 40 * 5035984 * 2
def baseEnd_5035984 : Nat := 861960120117309974379979

theorem tailTrace_5035984 : CollatzResearch.WordTrace tailWord_5035984 prefixEnd_5035984 861960120117309974379979 := by
  unfold tailWord_5035984
  simp only [CollatzResearch.WordTrace]
  refine ⟨91838713093748760219017503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122451617458331680292023337 91838713093748760219017503)
  ·
    refine ⟨137758069640623140328526255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91838713093748760219017503 137758069640623140328526255)
    ·
      refine ⟨206637104460934710492789383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137758069640623140328526255 206637104460934710492789383)
      ·
        refine ⟨309955656691402065739184075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206637104460934710492789383 309955656691402065739184075)
        ·
          refine ⟨464933485037103098608776113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309955656691402065739184075 464933485037103098608776113)
          ·
            refine ⟨348700113777827323956582085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464933485037103098608776113 348700113777827323956582085)
            ·
              refine ⟨65381271333342623241859141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348700113777827323956582085 65381271333342623241859141)
              ·
                refine ⟨12258988375001741857848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65381271333342623241859141 12258988375001741857848589)
                ·
                  refine ⟨4597120640625653196693221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12258988375001741857848589 4597120640625653196693221)
                  ·
                    refine ⟨861960120117309974379979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597120640625653196693221 861960120117309974379979)
                    ·
                      rfl

theorem cell23_5035984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_5035984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5035984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5035984 prefixEnd_5035984 := by exact prefixLift 5035984
  have htrace : WordTrace (prefixWord ++ tailWord_5035984) baseStart_5035984 baseEnd_5035984 := by
    simpa [prefixWord, tailWord_5035984, baseEnd_5035984] using wordTrace_append hprefix tailTrace_5035984
  have hstable : (prefixWord ++ tailWord_5035984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5035984).length < 2 ^ (prefixWord ++ tailWord_5035984).sum := by decide
  have hdescent : baseEnd_5035984 < baseStart_5035984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5035984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036044 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_5036044 : Nat := 118140960795 + 5036044 * 2 ^ 59
def prefixEnd_5036044 : Nat := 4983230072969 + 3 ^ 40 * 5036044 * 2
def baseEnd_5036044 : Nat := 861970389730399896129887

theorem tailTrace_5036044 : CollatzResearch.WordTrace tailWord_5036044 prefixEnd_5036044 861970389730399896129887 := by
  unfold tailWord_5036044
  simp only [CollatzResearch.WordTrace]
  refine ⟨91839807283640075342609593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122453076378186767123479457 91839807283640075342609593)
  ·
    refine ⟨68879855462730056506957195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91839807283640075342609593 68879855462730056506957195)
    ·
      refine ⟨103319783194095084760435793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68879855462730056506957195 103319783194095084760435793)
      ·
        refine ⟨77489837395571313570326845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103319783194095084760435793 77489837395571313570326845)
        ·
          refine ⟨29058689023339242588872567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77489837395571313570326845 29058689023339242588872567)
          ·
            refine ⟨43588033535008863883308851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29058689023339242588872567 43588033535008863883308851)
            ·
              refine ⟨65382050302513295824963277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43588033535008863883308851 65382050302513295824963277)
              ·
                refine ⟨24518268863442485934361229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65382050302513295824963277 24518268863442485934361229)
                ·
                  refine ⟨9194350823790932225385461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24518268863442485934361229 9194350823790932225385461)
                  ·
                    refine ⟨861970389730399896129887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9194350823790932225385461 861970389730399896129887)
                    ·
                      rfl

theorem cell23_5036044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_5036044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036044 prefixEnd_5036044 := by exact prefixLift 5036044
  have htrace : WordTrace (prefixWord ++ tailWord_5036044) baseStart_5036044 baseEnd_5036044 := by
    simpa [prefixWord, tailWord_5036044, baseEnd_5036044] using wordTrace_append hprefix tailTrace_5036044
  have hstable : (prefixWord ++ tailWord_5036044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036044).length < 2 ^ (prefixWord ++ tailWord_5036044).sum := by decide
  have hdescent : baseEnd_5036044 < baseStart_5036044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036126 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5036126 : Nat := 118140960795 + 5036126 * 2 ^ 59
def prefixEnd_5036126 : Nat := 4983230072969 + 3 ^ 40 * 5036126 * 2
def baseEnd_5036126 : Nat := 2585953274604868367564285

theorem tailTrace_5036126 : CollatzResearch.WordTrace tailWord_5036126 prefixEnd_5036126 2585953274604868367564285 := by
  unfold tailWord_5036126
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960325669122884836213029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122455070235322052459802821 22960325669122884836213029)
  ·
    refine ⟨4305061062960540906789943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22960325669122884836213029 4305061062960540906789943)
    ·
      refine ⟨6457591594440811360184915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305061062960540906789943 6457591594440811360184915)
      ·
        refine ⟨9686387391661217040277373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457591594440811360184915 9686387391661217040277373)
        ·
          refine ⟨3632395271872956390104015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9686387391661217040277373 3632395271872956390104015)
          ·
            refine ⟨5448592907809434585156023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632395271872956390104015 5448592907809434585156023)
            ·
              refine ⟨8172889361714151877734035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448592907809434585156023 8172889361714151877734035)
              ·
                refine ⟨12259334042571227816601053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8172889361714151877734035 12259334042571227816601053)
                ·
                  refine ⟨4597250265964210431225395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12259334042571227816601053 4597250265964210431225395)
                  ·
                    refine ⟨6895875398946315646838093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597250265964210431225395 6895875398946315646838093)
                    ·
                      refine ⟨2585953274604868367564285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6895875398946315646838093 2585953274604868367564285)
                      ·
                        rfl

theorem cell23_5036126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5036126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036126 prefixEnd_5036126 := by exact prefixLift 5036126
  have htrace : WordTrace (prefixWord ++ tailWord_5036126) baseStart_5036126 baseEnd_5036126 := by
    simpa [prefixWord, tailWord_5036126, baseEnd_5036126] using wordTrace_append hprefix tailTrace_5036126
  have hstable : (prefixWord ++ tailWord_5036126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036126).length < 2 ^ (prefixWord ++ tailWord_5036126).sum := by decide
  have hdescent : baseEnd_5036126 < baseStart_5036126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036188 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5036188 : Nat := 118140960795 + 5036188 * 2 ^ 59
def prefixEnd_5036188 : Nat := 4983230072969 + 3 ^ 40 * 5036188 * 2
def baseEnd_5036188 : Nat := 2585985110405447124988999

theorem tailTrace_5036188 : CollatzResearch.WordTrace tailWord_5036188 prefixEnd_5036188 2585985110405447124988999 := by
  unfold tailWord_5036188
  simp only [CollatzResearch.WordTrace]
  refine ⟨91842433339379231639230609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122456577785838975518974145 91842433339379231639230609)
  ·
    refine ⟨68881825004534423729422957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91842433339379231639230609 68881825004534423729422957)
    ·
      refine ⟨25830684376700408898533609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68881825004534423729422957 25830684376700408898533609)
      ·
        refine ⟨19373013282525306673900207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25830684376700408898533609 19373013282525306673900207)
        ·
          refine ⟨29059519923787960010850311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19373013282525306673900207 29059519923787960010850311)
          ·
            refine ⟨43589279885681940016275467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29059519923787960010850311 43589279885681940016275467)
            ·
              refine ⟨65383919828522910024413201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43589279885681940016275467 65383919828522910024413201)
              ·
                refine ⟨49037939871392182518309901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65383919828522910024413201 49037939871392182518309901)
                ·
                  refine ⟨18389227451772068444366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49037939871392182518309901 18389227451772068444366213)
                  ·
                    refine ⟨3447980147207262833318665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18389227451772068444366213 3447980147207262833318665)
                    ·
                      refine ⟨2585985110405447124988999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447980147207262833318665 2585985110405447124988999)
                      ·
                        rfl

theorem cell23_5036188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5036188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036188 prefixEnd_5036188 := by exact prefixLift 5036188
  have htrace : WordTrace (prefixWord ++ tailWord_5036188) baseStart_5036188 baseEnd_5036188 := by
    simpa [prefixWord, tailWord_5036188, baseEnd_5036188] using wordTrace_append hprefix tailTrace_5036188
  have hstable : (prefixWord ++ tailWord_5036188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036188).length < 2 ^ (prefixWord ++ tailWord_5036188).sum := by decide
  have hdescent : baseEnd_5036188 < baseStart_5036188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036204 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_5036204 : Nat := 118140960795 + 5036204 * 2 ^ 59
def prefixEnd_5036204 : Nat := 4983230072969 + 3 ^ 40 * 5036204 * 2
def baseEnd_5036204 : Nat := 2585993326095919062388925

theorem tailTrace_5036204 : CollatzResearch.WordTrace tailWord_5036204 prefixEnd_5036204 2585993326095919062388925 := by
  unfold tailWord_5036204
  simp only [CollatzResearch.WordTrace]
  refine ⟨91842725123350249005521833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122456966831133665340695777 91842725123350249005521833)
  ·
    refine ⟨68882043842512686754141375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91842725123350249005521833 68882043842512686754141375)
    ·
      refine ⟨103323065763769030131212063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68882043842512686754141375 103323065763769030131212063)
      ·
        refine ⟨154984598645653545196818095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103323065763769030131212063 154984598645653545196818095)
        ·
          refine ⟨232476897968480317795227143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154984598645653545196818095 232476897968480317795227143)
          ·
            refine ⟨348715346952720476692840715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232476897968480317795227143 348715346952720476692840715)
            ·
              refine ⟨523073020429080715039261073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348715346952720476692840715 523073020429080715039261073)
              ·
                refine ⟨392304765321810536279445805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523073020429080715039261073 392304765321810536279445805)
                ·
                  refine ⟨147114286995678951104792177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392304765321810536279445805 147114286995678951104792177)
                  ·
                    refine ⟨110335715246759213328594133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147114286995678951104792177 110335715246759213328594133)
                    ·
                      refine ⟨2585993326095919062388925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110335715246759213328594133 2585993326095919062388925)
                      ·
                        rfl

theorem cell23_5036204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_5036204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036204 prefixEnd_5036204 := by exact prefixLift 5036204
  have htrace : WordTrace (prefixWord ++ tailWord_5036204) baseStart_5036204 baseEnd_5036204 := by
    simpa [prefixWord, tailWord_5036204, baseEnd_5036204] using wordTrace_append hprefix tailTrace_5036204
  have hstable : (prefixWord ++ tailWord_5036204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036204).length < 2 ^ (prefixWord ++ tailWord_5036204).sum := by decide
  have hdescent : baseEnd_5036204 < baseStart_5036204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036205 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5036205 : Nat := 118140960795 + 5036205 * 2 ^ 59
def prefixEnd_5036205 : Nat := 4983230072969 + 3 ^ 40 * 5036205 * 2
def baseEnd_5036205 : Nat := 2585993839576573558476421

theorem tailTrace_5036205 : CollatzResearch.WordTrace tailWord_5036205 prefixEnd_5036205 2585993839576573558476421 := by
  unfold tailWord_5036205
  simp only [CollatzResearch.WordTrace]
  refine ⟨183685486719696875181830069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122456991146464583454553379 183685486719696875181830069)
  ·
    refine ⟨17220514379971582048296569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183685486719696875181830069 17220514379971582048296569)
    ·
      refine ⟨12915385784978686536222427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17220514379971582048296569 12915385784978686536222427)
      ·
        refine ⟨19373078677468029804333641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12915385784978686536222427 19373078677468029804333641)
        ·
          refine ⟨14529809008101022353250231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19373078677468029804333641 14529809008101022353250231)
          ·
            refine ⟨21794713512151533529875347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14529809008101022353250231 21794713512151533529875347)
            ·
              refine ⟨32692070268227300294813021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21794713512151533529875347 32692070268227300294813021)
              ·
                refine ⟨12259526350585237610554883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32692070268227300294813021 12259526350585237610554883)
                ·
                  refine ⟨18389289525877856415832325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12259526350585237610554883 18389289525877856415832325)
                  ·
                    refine ⟨3447991786102098077968561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18389289525877856415832325 3447991786102098077968561)
                    ·
                      refine ⟨2585993839576573558476421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3447991786102098077968561 2585993839576573558476421)
                      ·
                        rfl

theorem cell23_5036205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5036205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036205 prefixEnd_5036205 := by exact prefixLift 5036205
  have htrace : WordTrace (prefixWord ++ tailWord_5036205) baseStart_5036205 baseEnd_5036205 := by
    simpa [prefixWord, tailWord_5036205, baseEnd_5036205] using wordTrace_append hprefix tailTrace_5036205
  have hstable : (prefixWord ++ tailWord_5036205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036205).length < 2 ^ (prefixWord ++ tailWord_5036205).sum := by decide
  have hdescent : baseEnd_5036205 < baseStart_5036205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036221 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_5036221 : Nat := 118140960795 + 5036221 * 2 ^ 59
def prefixEnd_5036221 : Nat := 4983230072969 + 3 ^ 40 * 5036221 * 2
def baseEnd_5036221 : Nat := 2586002055267045495876347

theorem tailTrace_5036221 : CollatzResearch.WordTrace tailWord_5036221 prefixEnd_5036221 2586002055267045495876347 := by
  unfold tailWord_5036221
  simp only [CollatzResearch.WordTrace]
  refine ⟨183686070287638909914412517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122457380191759273276275011 183686070287638909914412517)
  ·
    refine ⟨34441138178932295608952347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183686070287638909914412517 34441138178932295608952347)
    ·
      refine ⟨51661707268398443413428521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34441138178932295608952347 51661707268398443413428521)
      ·
        refine ⟨38746280451298832560071391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51661707268398443413428521 38746280451298832560071391)
        ·
          refine ⟨58119420676948248840107087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38746280451298832560071391 58119420676948248840107087)
          ·
            refine ⟨87179131015422373260160631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58119420676948248840107087 87179131015422373260160631)
            ·
              refine ⟨130768696523133559890240947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87179131015422373260160631 130768696523133559890240947)
              ·
                refine ⟨196153044784700339835361421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130768696523133559890240947 196153044784700339835361421)
                ·
                  refine ⟨73557391794262627438260533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196153044784700339835361421 73557391794262627438260533)
                  ·
                    refine ⟨6896005480712121322336925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73557391794262627438260533 6896005480712121322336925)
                    ·
                      refine ⟨2586002055267045495876347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896005480712121322336925 2586002055267045495876347)
                      ·
                        rfl

theorem cell23_5036221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_5036221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036221 prefixEnd_5036221 := by exact prefixLift 5036221
  have htrace : WordTrace (prefixWord ++ tailWord_5036221) baseStart_5036221 baseEnd_5036221 := by
    simpa [prefixWord, tailWord_5036221, baseEnd_5036221] using wordTrace_append hprefix tailTrace_5036221
  have hstable : (prefixWord ++ tailWord_5036221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036221).length < 2 ^ (prefixWord ++ tailWord_5036221).sum := by decide
  have hdescent : baseEnd_5036221 < baseStart_5036221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036226 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5036226 : Nat := 118140960795 + 5036226 * 2 ^ 59
def prefixEnd_5036226 : Nat := 4983230072969 + 3 ^ 40 * 5036226 * 2
def baseEnd_5036226 : Nat := 2586004622670317976313825

theorem tailTrace_5036226 : CollatzResearch.WordTrace tailWord_5036226 prefixEnd_5036226 2586004622670317976313825 := by
  unfold tailWord_5036226
  simp only [CollatzResearch.WordTrace]
  refine ⟨45921563163155198942086133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122457501768413863845563021 45921563163155198942086133)
  ·
    refine ⟨4305146546545799900820575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45921563163155198942086133 4305146546545799900820575)
    ·
      refine ⟨6457719819818699851230863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4305146546545799900820575 6457719819818699851230863)
      ·
        refine ⟨9686579729728049776846295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6457719819818699851230863 9686579729728049776846295)
        ·
          refine ⟨14529869594592074665269443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9686579729728049776846295 14529869594592074665269443)
          ·
            refine ⟨21794804391888111997904165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14529869594592074665269443 21794804391888111997904165)
            ·
              refine ⟨4086525823479020999607031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21794804391888111997904165 4086525823479020999607031)
              ·
                refine ⟨6129788735218531499410547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086525823479020999607031 6129788735218531499410547)
                ·
                  refine ⟨9194683102827797249115821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129788735218531499410547 9194683102827797249115821)
                  ·
                    refine ⟨3448006163560423968418433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9194683102827797249115821 3448006163560423968418433)
                    ·
                      refine ⟨2586004622670317976313825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448006163560423968418433 2586004622670317976313825)
                      ·
                        rfl

theorem cell23_5036226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5036226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036226 prefixEnd_5036226 := by exact prefixLift 5036226
  have htrace : WordTrace (prefixWord ++ tailWord_5036226) baseStart_5036226 baseEnd_5036226 := by
    simpa [prefixWord, tailWord_5036226, baseEnd_5036226] using wordTrace_append hprefix tailTrace_5036226
  have hstable : (prefixWord ++ tailWord_5036226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036226).length < 2 ^ (prefixWord ++ tailWord_5036226).sum := by decide
  have hdescent : baseEnd_5036226 < baseStart_5036226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036238 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_5036238 : Nat := 118140960795 + 5036238 * 2 ^ 59
def prefixEnd_5036238 : Nat := 4983230072969 + 3 ^ 40 * 5036238 * 2
def baseEnd_5036238 : Nat := 2586010784438171929363769

theorem tailTrace_5036238 : CollatzResearch.WordTrace tailWord_5036238 prefixEnd_5036238 2586010784438171929363769 := by
  unfold tailWord_5036238
  simp only [CollatzResearch.WordTrace]
  refine ⟨22960836291072165227222671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122457793552384881211854245 22960836291072165227222671)
  ·
    refine ⟨34441254436608247840834007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22960836291072165227222671 34441254436608247840834007)
    ·
      refine ⟨51661881654912371761251011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34441254436608247840834007 51661881654912371761251011)
      ·
        refine ⟨77492822482368557641876517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51661881654912371761251011 77492822482368557641876517)
        ·
          refine ⟨14529904215444104557851847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77492822482368557641876517 14529904215444104557851847)
          ·
            refine ⟨21794856323166156836777771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14529904215444104557851847 21794856323166156836777771)
            ·
              refine ⟨32692284484749235255166657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21794856323166156836777771 32692284484749235255166657)
              ·
                refine ⟨24519213363561926441374993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32692284484749235255166657 24519213363561926441374993)
                ·
                  refine ⟨18389410022671444831031245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24519213363561926441374993 18389410022671444831031245)
                  ·
                    refine ⟨6896028758501791811636717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18389410022671444831031245 6896028758501791811636717)
                    ·
                      refine ⟨2586010784438171929363769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896028758501791811636717 2586010784438171929363769)
                      ·
                        rfl

theorem cell23_5036238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_5036238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036238 prefixEnd_5036238 := by exact prefixLift 5036238
  have htrace : WordTrace (prefixWord ++ tailWord_5036238) baseStart_5036238 baseEnd_5036238 := by
    simpa [prefixWord, tailWord_5036238, baseEnd_5036238] using wordTrace_append hprefix tailTrace_5036238
  have hstable : (prefixWord ++ tailWord_5036238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036238).length < 2 ^ (prefixWord ++ tailWord_5036238).sum := by decide
  have hdescent : baseEnd_5036238 < baseStart_5036238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036241 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_5036241 : Nat := 118140960795 + 5036241 * 2 ^ 59
def prefixEnd_5036241 : Nat := 4983230072969 + 3 ^ 40 * 5036241 * 2
def baseEnd_5036241 : Nat := 862004108293378472542085

theorem tailTrace_5036241 : CollatzResearch.WordTrace tailWord_5036241 prefixEnd_5036241 862004108293378472542085 := by
  unfold tailWord_5036241
  simp only [CollatzResearch.WordTrace]
  refine ⟨183686799747566453330140577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122457866498377635553427051 183686799747566453330140577)
  ·
    refine ⟨137765099810674839997605433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183686799747566453330140577 137765099810674839997605433)
    ·
      refine ⟨103323824858006129998204075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137765099810674839997605433 103323824858006129998204075)
      ·
        refine ⟨154985737287009194997306113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103323824858006129998204075 154985737287009194997306113)
        ·
          refine ⟨116239302965256896247979585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154985737287009194997306113 116239302965256896247979585)
          ·
            refine ⟨87179477223942672185984689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116239302965256896247979585 87179477223942672185984689)
            ·
              refine ⟨65384607917957004139488517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87179477223942672185984689 65384607917957004139488517)
              ·
                refine ⟨12259613984616938276154097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65384607917957004139488517 12259613984616938276154097)
                ·
                  refine ⟨9194710488462703707115573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12259613984616938276154097 9194710488462703707115573)
                  ·
                    refine ⟨862004108293378472542085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9194710488462703707115573 862004108293378472542085)
                    ·
                      rfl

theorem cell23_5036241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_5036241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036241 prefixEnd_5036241 := by exact prefixLift 5036241
  have htrace : WordTrace (prefixWord ++ tailWord_5036241) baseStart_5036241 baseEnd_5036241 := by
    simpa [prefixWord, tailWord_5036241, baseEnd_5036241] using wordTrace_append hprefix tailTrace_5036241
  have hstable : (prefixWord ++ tailWord_5036241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036241).length < 2 ^ (prefixWord ++ tailWord_5036241).sum := by decide
  have hdescent : baseEnd_5036241 < baseStart_5036241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036278 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5036278 : Nat := 118140960795 + 5036278 * 2 ^ 59
def prefixEnd_5036278 : Nat := 4983230072969 + 3 ^ 40 * 5036278 * 2
def baseEnd_5036278 : Nat := 2586031323664351772863585

theorem tailTrace_5036278 : CollatzResearch.WordTrace tailWord_5036278 prefixEnd_5036278 2586031323664351772863585 := by
  unfold tailWord_5036278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11480509328027025540577343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122458766165621605766158325 11480509328027025540577343)
  ·
    refine ⟨17220763992040538310866015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11480509328027025540577343 17220763992040538310866015)
    ·
      refine ⟨25831145988060807466299023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17220763992040538310866015 25831145988060807466299023)
      ·
        refine ⟨38746718982091211199448535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25831145988060807466299023 38746718982091211199448535)
        ·
          refine ⟨58120078473136816799172803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38746718982091211199448535 58120078473136816799172803)
          ·
            refine ⟨87180117709705225198759205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58120078473136816799172803 87180117709705225198759205)
            ·
              refine ⟨16346272070569729724767351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87180117709705225198759205 16346272070569729724767351)
              ·
                refine ⟨24519408105854594587151027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16346272070569729724767351 24519408105854594587151027)
                ·
                  refine ⟨36779112158781891880726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24519408105854594587151027 36779112158781891880726541)
                  ·
                    refine ⟨13792167059543209455272453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36779112158781891880726541 13792167059543209455272453)
                    ·
                      refine ⟨2586031323664351772863585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13792167059543209455272453 2586031323664351772863585)
                      ·
                        rfl

theorem cell23_5036278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5036278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036278 prefixEnd_5036278 := by exact prefixLift 5036278
  have htrace : WordTrace (prefixWord ++ tailWord_5036278) baseStart_5036278 baseEnd_5036278 := by
    simpa [prefixWord, tailWord_5036278, baseEnd_5036278] using wordTrace_append hprefix tailTrace_5036278
  have hstable : (prefixWord ++ tailWord_5036278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036278).length < 2 ^ (prefixWord ++ tailWord_5036278).sum := by decide
  have hdescent : baseEnd_5036278 < baseStart_5036278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036298 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5036298 : Nat := 118140960795 + 5036298 * 2 ^ 59
def prefixEnd_5036298 : Nat := 4983230072969 + 3 ^ 40 * 5036298 * 2
def baseEnd_5036298 : Nat := 2586041593277441694613493

theorem tailTrace_5036298 : CollatzResearch.WordTrace tailWord_5036298 prefixEnd_5036298 2586041593277441694613493 := by
  unfold tailWord_5036298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45922219677089988016241387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122459252472239968043310365 45922219677089988016241387)
  ·
    refine ⟨68883329515634982024362081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45922219677089988016241387 68883329515634982024362081)
    ·
      refine ⟨51662497136726236518271561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68883329515634982024362081 51662497136726236518271561)
      ·
        refine ⟨38746872852544677388703671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51662497136726236518271561 38746872852544677388703671)
        ·
          refine ⟨58120309278817016083055507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38746872852544677388703671 58120309278817016083055507)
          ·
            refine ⟨87180463918225524124583261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58120309278817016083055507 87180463918225524124583261)
            ·
              refine ⟨32692673969334571546718723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87180463918225524124583261 32692673969334571546718723)
              ·
                refine ⟨49039010954001857320078085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32692673969334571546718723 49039010954001857320078085)
                ·
                  refine ⟨9194814553875348247514641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49039010954001857320078085 9194814553875348247514641)
                  ·
                    refine ⟨6896110915406511185635981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9194814553875348247514641 6896110915406511185635981)
                    ·
                      refine ⟨2586041593277441694613493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896110915406511185635981 2586041593277441694613493)
                      ·
                        rfl

theorem cell23_5036298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5036298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036298 prefixEnd_5036298 := by exact prefixLift 5036298
  have htrace : WordTrace (prefixWord ++ tailWord_5036298) baseStart_5036298 baseEnd_5036298 := by
    simpa [prefixWord, tailWord_5036298, baseEnd_5036298] using wordTrace_append hprefix tailTrace_5036298
  have hstable : (prefixWord ++ tailWord_5036298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036298).length < 2 ^ (prefixWord ++ tailWord_5036298).sum := by decide
  have hdescent : baseEnd_5036298 < baseStart_5036298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036305 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_5036305 : Nat := 118140960795 + 5036305 * 2 ^ 59
def prefixEnd_5036305 : Nat := 4983230072969 + 3 ^ 40 * 5036305 * 2
def baseEnd_5036305 : Nat := 862015062547341055741987

theorem tailTrace_5036305 : CollatzResearch.WordTrace tailWord_5036305 prefixEnd_5036305 862015062547341055741987 := by
  unfold tailWord_5036305
  simp only [CollatzResearch.WordTrace]
  refine ⟨183689134019334592260470369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122459422679556394840313579 183689134019334592260470369)
  ·
    refine ⟨137766850514500944195352777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183689134019334592260470369 137766850514500944195352777)
    ·
      refine ⟨103325137885875708146514583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137766850514500944195352777 103325137885875708146514583)
      ·
        refine ⟨154987706828813562219771875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103325137885875708146514583 154987706828813562219771875)
        ·
          refine ⟨232481560243220343329657813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154987706828813562219771875 232481560243220343329657813)
          ·
            refine ⟨5448786568200476796788855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 232481560243220343329657813 5448786568200476796788855)
            ·
              refine ⟨8173179852300715195183283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448786568200476796788855 8173179852300715195183283)
              ·
                refine ⟨12259769778451072792774925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173179852300715195183283 12259769778451072792774925)
                ·
                  refine ⟨4597413666919152297290597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12259769778451072792774925 4597413666919152297290597)
                  ·
                    refine ⟨862015062547341055741987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597413666919152297290597 862015062547341055741987)
                    ·
                      rfl

theorem cell23_5036305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_5036305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036305 prefixEnd_5036305 := by exact prefixLift 5036305
  have htrace : WordTrace (prefixWord ++ tailWord_5036305) baseStart_5036305 baseEnd_5036305 := by
    simpa [prefixWord, tailWord_5036305, baseEnd_5036305] using wordTrace_append hprefix tailTrace_5036305
  have hstable : (prefixWord ++ tailWord_5036305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036305).length < 2 ^ (prefixWord ++ tailWord_5036305).sum := by decide
  have hdescent : baseEnd_5036305 < baseStart_5036305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036321 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5036321 : Nat := 118140960795 + 5036321 * 2 ^ 59
def prefixEnd_5036321 : Nat := 4983230072969 + 3 ^ 40 * 5036321 * 2
def baseEnd_5036321 : Nat := 2586053403332495104625887

theorem tailTrace_5036321 : CollatzResearch.WordTrace tailWord_5036321 prefixEnd_5036321 2586053403332495104625887 := by
  unfold tailWord_5036321
  simp only [CollatzResearch.WordTrace]
  refine ⟨183689717587276626993052817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122459811724851084662035211 183689717587276626993052817)
  ·
    refine ⟨137767288190457470244789613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183689717587276626993052817 137767288190457470244789613)
    ·
      refine ⟨51662733071421551341796105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137767288190457470244789613 51662733071421551341796105)
      ·
        refine ⟨38747049803566163506347079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51662733071421551341796105 38747049803566163506347079)
        ·
          refine ⟨58120574705349245259520619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38747049803566163506347079 58120574705349245259520619)
          ·
            refine ⟨87180862058023867889280929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58120574705349245259520619 87180862058023867889280929)
            ·
              refine ⟨65385646543517900916960697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87180862058023867889280929 65385646543517900916960697)
              ·
                refine ⟨49039234907638425687720523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65385646543517900916960697 49039234907638425687720523)
                ·
                  refine ⟨73558852361457638531580785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49039234907638425687720523 73558852361457638531580785)
                  ·
                    refine ⟨55169139271093228898685589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73558852361457638531580785 55169139271093228898685589)
                    ·
                      refine ⟨2586053403332495104625887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55169139271093228898685589 2586053403332495104625887)
                      ·
                        rfl

theorem cell23_5036321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5036321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036321 prefixEnd_5036321 := by exact prefixLift 5036321
  have htrace : WordTrace (prefixWord ++ tailWord_5036321) baseStart_5036321 baseEnd_5036321 := by
    simpa [prefixWord, tailWord_5036321, baseEnd_5036321] using wordTrace_append hprefix tailTrace_5036321
  have hstable : (prefixWord ++ tailWord_5036321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036321).length < 2 ^ (prefixWord ++ tailWord_5036321).sum := by decide
  have hdescent : baseEnd_5036321 < baseStart_5036321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036355 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 2, 3, 2]
def baseStart_5036355 : Nat := 118140960795 + 5036355 * 2 ^ 59
def prefixEnd_5036355 : Nat := 4983230072969 + 3 ^ 40 * 5036355 * 2
def baseEnd_5036355 : Nat := 2586070861674747971600731

theorem tailTrace_5036355 : CollatzResearch.WordTrace tailWord_5036355 prefixEnd_5036355 2586070861674747971600731 := by
  unfold tailWord_5036355
  simp only [CollatzResearch.WordTrace]
  refine ⟨183690957669153450799790519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122460638446102300533193679 183690957669153450799790519)
  ·
    refine ⟨275536436503730176199685779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183690957669153450799790519 275536436503730176199685779)
    ·
      refine ⟨413304654755595264299528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275536436503730176199685779 413304654755595264299528669)
      ·
        refine ⟨154989245533348224112323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413304654755595264299528669 154989245533348224112323251)
        ·
          refine ⟨232483868300022336168484877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154989245533348224112323251 232483868300022336168484877)
          ·
            refine ⟨87181450612508376063181829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232483868300022336168484877 87181450612508376063181829)
            ·
              refine ⟨16346521989845320511846593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87181450612508376063181829 16346521989845320511846593)
              ·
                refine ⟨12259891492383990383884945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16346521989845320511846593 12259891492383990383884945)
                ·
                  refine ⟨9194918619287992787913709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12259891492383990383884945 9194918619287992787913709)
                  ·
                    refine ⟨3448094482232997295467641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9194918619287992787913709 3448094482232997295467641)
                    ·
                      refine ⟨2586070861674747971600731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448094482232997295467641 2586070861674747971600731)
                      ·
                        rfl

theorem cell23_5036355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_5036355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036355 prefixEnd_5036355 := by exact prefixLift 5036355
  have htrace : WordTrace (prefixWord ++ tailWord_5036355) baseStart_5036355 baseEnd_5036355 := by
    simpa [prefixWord, tailWord_5036355, baseEnd_5036355] using wordTrace_append hprefix tailTrace_5036355
  have hstable : (prefixWord ++ tailWord_5036355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036355).length < 2 ^ (prefixWord ++ tailWord_5036355).sum := by decide
  have hdescent : baseEnd_5036355 < baseStart_5036355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036361 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_5036361 : Nat := 118140960795 + 5036361 * 2 ^ 59
def prefixEnd_5036361 : Nat := 4983230072969 + 3 ^ 40 * 5036361 * 2
def baseEnd_5036361 : Nat := 862024647519558316041901

theorem tailTrace_5036361 : CollatzResearch.WordTrace tailWord_5036361 prefixEnd_5036361 862024647519558316041901 := by
  unfold tailWord_5036361
  simp only [CollatzResearch.WordTrace]
  refine ⟨183691176507131713824508937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122460784338087809216339291 183691176507131713824508937)
  ·
    refine ⟨137768382380348785368381703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183691176507131713824508937 137768382380348785368381703)
    ·
      refine ⟨206652573570523178052572555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137768382380348785368381703 206652573570523178052572555)
      ·
        refine ⟨309978860355784767078858833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206652573570523178052572555 309978860355784767078858833)
        ·
          refine ⟨232484145266838575309144125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309978860355784767078858833 232484145266838575309144125)
          ·
            refine ⟨87181554475064465740929047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232484145266838575309144125 87181554475064465740929047)
            ·
              refine ⟨130772331712596698611393571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87181554475064465740929047 130772331712596698611393571)
              ·
                refine ⟨196158497568895047917090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130772331712596698611393571 196158497568895047917090357)
                ·
                  refine ⟨18389859147083910742227221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196158497568895047917090357 18389859147083910742227221)
                  ·
                    refine ⟨862024647519558316041901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18389859147083910742227221 862024647519558316041901)
                    ·
                      rfl

theorem cell23_5036361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_5036361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036361 prefixEnd_5036361 := by exact prefixLift 5036361
  have htrace : WordTrace (prefixWord ++ tailWord_5036361) baseStart_5036361 baseEnd_5036361 := by
    simpa [prefixWord, tailWord_5036361, baseEnd_5036361] using wordTrace_append hprefix tailTrace_5036361
  have hstable : (prefixWord ++ tailWord_5036361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036361).length < 2 ^ (prefixWord ++ tailWord_5036361).sum := by decide
  have hdescent : baseEnd_5036361 < baseStart_5036361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036368 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_5036368 : Nat := 118140960795 + 5036368 * 2 ^ 59
def prefixEnd_5036368 : Nat := 4983230072969 + 3 ^ 40 * 5036368 * 2
def baseEnd_5036368 : Nat := 2586077536923256420738171

theorem tailTrace_5036368 : CollatzResearch.WordTrace tailWord_5036368 prefixEnd_5036368 2586077536923256420738171 := by
  unfold tailWord_5036368
  simp only [CollatzResearch.WordTrace]
  refine ⟨91845715909053177010006879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122460954545404236013342505 91845715909053177010006879)
  ·
    refine ⟨137768573863579765515010319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91845715909053177010006879 137768573863579765515010319)
    ·
      refine ⟨206652860795369648272515479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137768573863579765515010319 206652860795369648272515479)
      ·
        refine ⟨309979291193054472408773219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206652860795369648272515479 309979291193054472408773219)
        ·
          refine ⟨464968936789581708613159829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309979291193054472408773219 464968936789581708613159829)
          ·
            refine ⟨21795418912011642591241867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 464968936789581708613159829 21795418912011642591241867)
            ·
              refine ⟨32693128368017463886862801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21795418912011642591241867 32693128368017463886862801)
              ·
                refine ⟨24519846276013097915147101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32693128368017463886862801 24519846276013097915147101)
                ·
                  refine ⟨9194942353504911718180163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24519846276013097915147101 9194942353504911718180163)
                  ·
                    refine ⟨13792413530257367577270245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9194942353504911718180163 13792413530257367577270245)
                    ·
                      refine ⟨2586077536923256420738171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13792413530257367577270245 2586077536923256420738171)
                      ·
                        rfl

theorem cell23_5036368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_5036368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036368 prefixEnd_5036368 := by exact prefixLift 5036368
  have htrace : WordTrace (prefixWord ++ tailWord_5036368) baseStart_5036368 baseEnd_5036368 := by
    simpa [prefixWord, tailWord_5036368, baseEnd_5036368] using wordTrace_append hprefix tailTrace_5036368
  have hstable : (prefixWord ++ tailWord_5036368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036368).length < 2 ^ (prefixWord ++ tailWord_5036368).sum := by decide
  have hdescent : baseEnd_5036368 < baseStart_5036368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036378 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_5036378 : Nat := 118140960795 + 5036378 * 2 ^ 59
def prefixEnd_5036378 : Nat := 4983230072969 + 3 ^ 40 * 5036378 * 2
def baseEnd_5036378 : Nat := 862027557243267127204375

theorem tailTrace_5036378 : CollatzResearch.WordTrace tailWord_5036378 prefixEnd_5036378 862027557243267127204375 := by
  unfold tailWord_5036378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45922949137017531431969447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122461197698713417151918525 45922949137017531431969447)
  ·
    refine ⟨68884423705526297147954171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45922949137017531431969447 68884423705526297147954171)
    ·
      refine ⟨103326635558289445721931257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68884423705526297147954171 103326635558289445721931257)
      ·
        refine ⟨77494976668717084291448443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103326635558289445721931257 77494976668717084291448443)
        ·
          refine ⟨116242465003075626437172665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77494976668717084291448443 116242465003075626437172665)
          ·
            refine ⟨87181848752306719827879499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116242465003075626437172665 87181848752306719827879499)
            ·
              refine ⟨130772773128460079741819249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87181848752306719827879499 130772773128460079741819249)
              ·
                refine ⟨98079579846345059806364437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130772773128460079741819249 98079579846345059806364437)
                ·
                  refine ⟨4597480305297424678423333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98079579846345059806364437 4597480305297424678423333)
                  ·
                    refine ⟨862027557243267127204375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597480305297424678423333 862027557243267127204375)
                    ·
                      rfl

theorem cell23_5036378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_5036378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036378 prefixEnd_5036378 := by exact prefixLift 5036378
  have htrace : WordTrace (prefixWord ++ tailWord_5036378) baseStart_5036378 baseEnd_5036378 := by
    simpa [prefixWord, tailWord_5036378, baseEnd_5036378] using wordTrace_append hprefix tailTrace_5036378
  have hstable : (prefixWord ++ tailWord_5036378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036378).length < 2 ^ (prefixWord ++ tailWord_5036378).sum := by decide
  have hdescent : baseEnd_5036378 < baseStart_5036378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036402 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5036402 : Nat := 118140960795 + 5036402 * 2 ^ 59
def prefixEnd_5036402 : Nat := 4983230072969 + 3 ^ 40 * 5036402 * 2
def baseEnd_5036402 : Nat := 2586094995265509287713015

theorem tailTrace_5036402 : CollatzResearch.WordTrace tailWord_5036402 prefixEnd_5036402 2586094995265509287713015 := by
  unfold tailWord_5036402
  simp only [CollatzResearch.WordTrace]
  refine ⟨45923167974995794456687865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122461781266655451884500973 45923167974995794456687865)
  ·
    refine ⟨34442375981246845842515899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45923167974995794456687865 34442375981246845842515899)
    ·
      refine ⟨51663563971870268763773849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34442375981246845842515899 51663563971870268763773849)
      ·
        refine ⟨38747672978902701572830387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51663563971870268763773849 38747672978902701572830387)
        ·
          refine ⟨58121509468354052359245581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38747672978902701572830387 58121509468354052359245581)
          ·
            refine ⟨21795566050632769634717093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58121509468354052359245581 21795566050632769634717093)
            ·
              refine ⟨4086668634493644306509455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21795566050632769634717093 4086668634493644306509455)
              ·
                refine ⟨6130002951740466459764183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086668634493644306509455 6130002951740466459764183)
                ·
                  refine ⟨9195004427610699689646275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6130002951740466459764183 9195004427610699689646275)
                  ·
                    refine ⟨13792506641416049534469413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9195004427610699689646275 13792506641416049534469413)
                    ·
                      refine ⟨2586094995265509287713015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13792506641416049534469413 2586094995265509287713015)
                      ·
                        rfl

theorem cell23_5036402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5036402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036402 prefixEnd_5036402 := by exact prefixLift 5036402
  have htrace : WordTrace (prefixWord ++ tailWord_5036402) baseStart_5036402 baseEnd_5036402 := by
    simpa [prefixWord, tailWord_5036402, baseEnd_5036402] using wordTrace_append hprefix tailTrace_5036402
  have hstable : (prefixWord ++ tailWord_5036402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036402).length < 2 ^ (prefixWord ++ tailWord_5036402).sum := by decide
  have hdescent : baseEnd_5036402 < baseStart_5036402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036419 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 3, 2, 2]
def baseStart_5036419 : Nat := 118140960795 + 5036419 * 2 ^ 59
def prefixEnd_5036419 : Nat := 4983230072969 + 3 ^ 40 * 5036419 * 2
def baseEnd_5036419 : Nat := 2586103724436635721200437

theorem tailTrace_5036419 : CollatzResearch.WordTrace tailWord_5036419 prefixEnd_5036419 2586103724436635721200437 := by
  unfold tailWord_5036419
  simp only [CollatzResearch.WordTrace]
  refine ⟨183693291940921589730120311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122462194627281059820080207 183693291940921589730120311)
  ·
    refine ⟨275539937911382384595180467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183693291940921589730120311 275539937911382384595180467)
    ·
      refine ⟨413309906867073576892770701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275539937911382384595180467 413309906867073576892770701)
      ·
        refine ⟨154991215075152591334789013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413309906867073576892770701 154991215075152591334789013)
        ·
          refine ⟨7265213206647777718818235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154991215075152591334789013 7265213206647777718818235)
          ·
            refine ⟨10897819809971666578227353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7265213206647777718818235 10897819809971666578227353)
            ·
              refine ⟨8173364857478749933670515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10897819809971666578227353 8173364857478749933670515)
              ·
                refine ⟨12260047286218124900505773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173364857478749933670515 12260047286218124900505773)
                ·
                  refine ⟨4597517732331796837689665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12260047286218124900505773 4597517732331796837689665)
                  ·
                    refine ⟨3448138299248847628267249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4597517732331796837689665 3448138299248847628267249)
                    ·
                      refine ⟨2586103724436635721200437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448138299248847628267249 2586103724436635721200437)
                      ·
                        rfl

theorem cell23_5036419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_5036419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036419 prefixEnd_5036419 := by exact prefixLift 5036419
  have htrace : WordTrace (prefixWord ++ tailWord_5036419) baseStart_5036419 baseEnd_5036419 := by
    simpa [prefixWord, tailWord_5036419, baseEnd_5036419] using wordTrace_append hprefix tailTrace_5036419
  have hstable : (prefixWord ++ tailWord_5036419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036419).length < 2 ^ (prefixWord ++ tailWord_5036419).sum := by decide
  have hdescent : baseEnd_5036419 < baseStart_5036419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036448 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5036448 : Nat := 118140960795 + 5036448 * 2 ^ 59
def prefixEnd_5036448 : Nat := 4983230072969 + 3 ^ 40 * 5036448 * 2
def baseEnd_5036448 : Nat := 2586118615375616107737803

theorem tailTrace_5036448 : CollatzResearch.WordTrace tailWord_5036448 prefixEnd_5036448 2586118615375616107737803 := by
  unfold tailWord_5036448
  simp only [CollatzResearch.WordTrace]
  refine ⟨91847174828908263841462999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122462899771877685121950665 91847174828908263841462999)
  ·
    refine ⟨137770762243362395762194499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91847174828908263841462999 137770762243362395762194499)
    ·
      refine ⟨206656143365043593643291749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137770762243362395762194499 206656143365043593643291749)
      ·
        refine ⟨38748026880945673808117203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206656143365043593643291749 38748026880945673808117203)
        ·
          refine ⟨58122040321418510712175805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38748026880945673808117203 58122040321418510712175805)
          ·
            refine ⟨21795765120531941517065927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58122040321418510712175805 21795765120531941517065927)
            ·
              refine ⟨32693647680797912275598891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21795765120531941517065927 32693647680797912275598891)
              ·
                refine ⟨49040471521196868413398337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32693647680797912275598891 49040471521196868413398337)
                ·
                  refine ⟨36780353640897651310048753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49040471521196868413398337 36780353640897651310048753)
                  ·
                    refine ⟨27585265230673238482536565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36780353640897651310048753 27585265230673238482536565)
                    ·
                      refine ⟨2586118615375616107737803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27585265230673238482536565 2586118615375616107737803)
                      ·
                        rfl

theorem cell23_5036448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5036448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036448 prefixEnd_5036448 := by exact prefixLift 5036448
  have htrace : WordTrace (prefixWord ++ tailWord_5036448) baseStart_5036448 baseEnd_5036448 := by
    simpa [prefixWord, tailWord_5036448, baseEnd_5036448] using wordTrace_append hprefix tailTrace_5036448
  have hstable : (prefixWord ++ tailWord_5036448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036448).length < 2 ^ (prefixWord ++ tailWord_5036448).sum := by decide
  have hdescent : baseEnd_5036448 < baseStart_5036448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036526 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5036526 : Nat := 118140960795 + 5036526 * 2 ^ 59
def prefixEnd_5036526 : Nat := 4983230072969 + 3 ^ 40 * 5036526 * 2
def baseEnd_5036526 : Nat := 2586158666866666802562445

theorem tailTrace_5036526 : CollatzResearch.WordTrace tailWord_5036526 prefixEnd_5036526 2586158666866666802562445 := by
  unfold tailWord_5036526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22962149318941743375533179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122464796367689298002843621 22962149318941743375533179)
  ·
    refine ⟨34443223978412615063299769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22962149318941743375533179 34443223978412615063299769)
    ·
      refine ⟨25832417983809461297474827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34443223978412615063299769 25832417983809461297474827)
      ·
        refine ⟨38748626975714191946212241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25832417983809461297474827 38748626975714191946212241)
        ·
          refine ⟨29061470231785643959659181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38748626975714191946212241 29061470231785643959659181)
          ·
            refine ⟨10898051336919616484872193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29061470231785643959659181 10898051336919616484872193)
            ·
              refine ⟨8173538502689712363654145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10898051336919616484872193 8173538502689712363654145)
              ·
                refine ⟨6130153877017284272740609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8173538502689712363654145 6130153877017284272740609)
                ·
                  refine ⟨4597615407762963204555457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130153877017284272740609 4597615407762963204555457)
                  ·
                    refine ⟨3448211555822222403416593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4597615407762963204555457 3448211555822222403416593)
                    ·
                      refine ⟨2586158666866666802562445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448211555822222403416593 2586158666866666802562445)
                      ·
                        rfl

theorem cell23_5036526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5036526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036526 prefixEnd_5036526 := by exact prefixLift 5036526
  have htrace : WordTrace (prefixWord ++ tailWord_5036526) baseStart_5036526 baseEnd_5036526 := by
    simpa [prefixWord, tailWord_5036526, baseEnd_5036526] using wordTrace_append hprefix tailTrace_5036526
  have hstable : (prefixWord ++ tailWord_5036526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036526).length < 2 ^ (prefixWord ++ tailWord_5036526).sum := by decide
  have hdescent : baseEnd_5036526 < baseStart_5036526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036538 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_5036538 : Nat := 118140960795 + 5036538 * 2 ^ 59
def prefixEnd_5036538 : Nat := 4983230072969 + 3 ^ 40 * 5036538 * 2
def baseEnd_5036538 : Nat := 2586164828634520755612389

theorem tailTrace_5036538 : CollatzResearch.WordTrace tailWord_5036538 prefixEnd_5036538 2586164828634520755612389 := by
  unfold tailWord_5036538
  simp only [CollatzResearch.WordTrace]
  refine ⟨45924408056872618263425567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122465088151660315369134845 45924408056872618263425567)
  ·
    refine ⟨68886612085308927395138351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45924408056872618263425567 68886612085308927395138351)
    ·
      refine ⟨103329918127963391092707527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68886612085308927395138351 103329918127963391092707527)
      ·
        refine ⟨154994877191945086639061291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103329918127963391092707527 154994877191945086639061291)
        ·
          refine ⟨232492315787917629958591937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154994877191945086639061291 232492315787917629958591937)
          ·
            refine ⟨174369236840938222468943953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232492315787917629958591937 174369236840938222468943953)
            ·
              refine ⟨130776927630703666851707965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174369236840938222468943953 130776927630703666851707965)
              ·
                refine ⟨49041347861513875069390487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130776927630703666851707965 49041347861513875069390487)
                ·
                  refine ⟨73562021792270812604085731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49041347861513875069390487 73562021792270812604085731)
                  ·
                    refine ⟨110343032688406218906128597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73562021792270812604085731 110343032688406218906128597)
                    ·
                      refine ⟨2586164828634520755612389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110343032688406218906128597 2586164828634520755612389)
                      ·
                        rfl

theorem cell23_5036538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_5036538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036538 prefixEnd_5036538 := by exact prefixLift 5036538
  have htrace : WordTrace (prefixWord ++ tailWord_5036538) baseStart_5036538 baseEnd_5036538 := by
    simpa [prefixWord, tailWord_5036538, baseEnd_5036538] using wordTrace_append hprefix tailTrace_5036538
  have hstable : (prefixWord ++ tailWord_5036538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036538).length < 2 ^ (prefixWord ++ tailWord_5036538).sum := by decide
  have hdescent : baseEnd_5036538 < baseStart_5036538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036565 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_5036565 : Nat := 118140960795 + 5036565 * 2 ^ 59
def prefixEnd_5036565 : Nat := 4983230072969 + 3 ^ 40 * 5036565 * 2
def baseEnd_5036565 : Nat := 2586178692612192149974765

theorem tailTrace_5036565 : CollatzResearch.WordTrace tailWord_5036565 prefixEnd_5036565 2586178692612192149974765 := by
  unfold tailWord_5036565
  simp only [CollatzResearch.WordTrace]
  refine ⟨183698616998392656664935149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122465744665595104443290099 183698616998392656664935149)
  ·
    refine ⟨68886981374397246249350681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183698616998392656664935149 68886981374397246249350681)
    ·
      refine ⟨51665236030797934687013011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68886981374397246249350681 51665236030797934687013011)
      ·
        refine ⟨77497854046196902030519517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51665236030797934687013011 77497854046196902030519517)
        ·
          refine ⟨29061695267323838261444819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77497854046196902030519517 29061695267323838261444819)
          ·
            refine ⟨43592542900985757392167229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29061695267323838261444819 43592542900985757392167229)
            ·
              refine ⟨16347203587869659022062711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43592542900985757392167229 16347203587869659022062711)
              ·
                refine ⟨24520805381804488533094067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16347203587869659022062711 24520805381804488533094067)
                ·
                  refine ⟨36781208072706732799641101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24520805381804488533094067 36781208072706732799641101)
                  ·
                    refine ⟨13792953027265024799865413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36781208072706732799641101 13792953027265024799865413)
                    ·
                      refine ⟨2586178692612192149974765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13792953027265024799865413 2586178692612192149974765)
                      ·
                        rfl

theorem cell23_5036565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_5036565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036565 prefixEnd_5036565 := by exact prefixLift 5036565
  have htrace : WordTrace (prefixWord ++ tailWord_5036565) baseStart_5036565 baseEnd_5036565 := by
    simpa [prefixWord, tailWord_5036565, baseEnd_5036565] using wordTrace_append hprefix tailTrace_5036565
  have hstable : (prefixWord ++ tailWord_5036565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036565).length < 2 ^ (prefixWord ++ tailWord_5036565).sum := by decide
  have hdescent : baseEnd_5036565 < baseStart_5036565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036575 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 7, 4]
def baseStart_5036575 : Nat := 118140960795 + 5036575 * 2 ^ 59
def prefixEnd_5036575 : Nat := 4983230072969 + 3 ^ 40 * 5036575 * 2
def baseEnd_5036575 : Nat := 862061275806245703616573

theorem tailTrace_5036575 : CollatzResearch.WordTrace tailWord_5036575 prefixEnd_5036575 862061275806245703616573 := by
  unfold tailWord_5036575
  simp only [CollatzResearch.WordTrace]
  refine ⟨183698981728356428372799179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122465987818904285581866119 183698981728356428372799179)
  ·
    refine ⟨275548472592534642559198769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183698981728356428372799179 275548472592534642559198769)
    ·
      refine ⟨206661354444400981919399077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275548472592534642559198769 206661354444400981919399077)
      ·
        refine ⟨38749003958325184109887327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206661354444400981919399077 38749003958325184109887327)
        ·
          refine ⟨58123505937487776164830991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38749003958325184109887327 58123505937487776164830991)
          ·
            refine ⟨87185258906231664247246487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58123505937487776164830991 87185258906231664247246487)
            ·
              refine ⟨130777888359347496370869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87185258906231664247246487 130777888359347496370869731)
              ·
                refine ⟨196166832539021244556304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130777888359347496370869731 196166832539021244556304597)
                ·
                  refine ⟨4597660137633310419288389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 196166832539021244556304597 4597660137633310419288389)
                  ·
                    refine ⟨862061275806245703616573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4597660137633310419288389 862061275806245703616573)
                    ·
                      rfl

theorem cell23_5036575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_5036575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036575 prefixEnd_5036575 := by exact prefixLift 5036575
  have htrace : WordTrace (prefixWord ++ tailWord_5036575) baseStart_5036575 baseEnd_5036575 := by
    simpa [prefixWord, tailWord_5036575, baseEnd_5036575] using wordTrace_append hprefix tailTrace_5036575
  have hstable : (prefixWord ++ tailWord_5036575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036575).length < 2 ^ (prefixWord ++ tailWord_5036575).sum := by decide
  have hdescent : baseEnd_5036575 < baseStart_5036575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036632 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_5036632 : Nat := 118140960795 + 5036632 * 2 ^ 59
def prefixEnd_5036632 : Nat := 4983230072969 + 3 ^ 40 * 5036632 * 2
def baseEnd_5036632 : Nat := 2586213095816043387836957

theorem tailTrace_5036632 : CollatzResearch.WordTrace tailWord_5036632 prefixEnd_5036632 2586213095816043387836957 := by
  unfold tailWord_5036632
  simp only [CollatzResearch.WordTrace]
  refine ⟨91850530344574963553812075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122467373792766618071749433 91850530344574963553812075)
  ·
    refine ⟨137775795516862445330718113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91850530344574963553812075 137775795516862445330718113)
    ·
      refine ⟨103331846637646833998038585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137775795516862445330718113 103331846637646833998038585)
      ·
        refine ⟨77498884978235125498528939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103331846637646833998038585 77498884978235125498528939)
        ·
          refine ⟨116248327467352688247793409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77498884978235125498528939 116248327467352688247793409)
          ·
            refine ⟨87186245600514516185845057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116248327467352688247793409 87186245600514516185845057)
            ·
              refine ⟨65389684200385887139383793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87186245600514516185845057 65389684200385887139383793)
              ·
                refine ⟨49042263150289415354537845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65389684200385887139383793 49042263150289415354537845)
                ·
                  refine ⟨4597712170339632689487923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49042263150289415354537845 4597712170339632689487923)
                  ·
                    refine ⟨6896568255509449034231885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597712170339632689487923 6896568255509449034231885)
                    ·
                      refine ⟨2586213095816043387836957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896568255509449034231885 2586213095816043387836957)
                      ·
                        rfl

theorem cell23_5036632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_5036632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036632 prefixEnd_5036632 := by exact prefixLift 5036632
  have htrace : WordTrace (prefixWord ++ tailWord_5036632) baseStart_5036632 baseEnd_5036632 := by
    simpa [prefixWord, tailWord_5036632, baseEnd_5036632] using wordTrace_append hprefix tailTrace_5036632
  have hstable : (prefixWord ++ tailWord_5036632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036632).length < 2 ^ (prefixWord ++ tailWord_5036632).sum := by decide
  have hdescent : baseEnd_5036632 < baseStart_5036632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036656 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 6]
def baseStart_5036656 : Nat := 118140960795 + 5036656 * 2 ^ 59
def prefixEnd_5036656 : Nat := 4983230072969 + 3 ^ 40 * 5036656 * 2
def baseEnd_5036656 : Nat := 287358379927972365992983

theorem tailTrace_5036656 : CollatzResearch.WordTrace tailWord_5036656 prefixEnd_5036656 287358379927972365992983 := by
  unfold tailWord_5036656
  simp only [CollatzResearch.WordTrace]
  refine ⟨91850968020531489603248911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122467957360708652804331881 91850968020531489603248911)
  ·
    refine ⟨137776452030797234404873367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91850968020531489603248911 137776452030797234404873367)
    ·
      refine ⟨206664678046195851607310051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137776452030797234404873367 206664678046195851607310051)
      ·
        refine ⟨309997017069293777410965077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206664678046195851607310051 309997017069293777410965077)
        ·
          refine ⟨3632777543780786454034747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 309997017069293777410965077 3632777543780786454034747)
          ·
            refine ⟨5449166315671179681052121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3632777543780786454034747 5449166315671179681052121)
            ·
              refine ⟨4086874736753384760789091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449166315671179681052121 4086874736753384760789091)
              ·
                refine ⟨6130312105130077141183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086874736753384760789091 6130312105130077141183637)
                ·
                  refine ⟨287358379927972365992983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6130312105130077141183637 287358379927972365992983)
                  ·
                    rfl

theorem cell23_5036656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_5036656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036656 prefixEnd_5036656 := by exact prefixLift 5036656
  have htrace : WordTrace (prefixWord ++ tailWord_5036656) baseStart_5036656 baseEnd_5036656 := by
    simpa [prefixWord, tailWord_5036656, baseEnd_5036656] using wordTrace_append hprefix tailTrace_5036656
  have hstable : (prefixWord ++ tailWord_5036656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036656).length < 2 ^ (prefixWord ++ tailWord_5036656).sum := by decide
  have hdescent : baseEnd_5036656 < baseStart_5036656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036672 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_5036672 : Nat := 118140960795 + 5036672 * 2 ^ 59
def prefixEnd_5036672 : Nat := 4983230072969 + 3 ^ 40 * 5036672 * 2
def baseEnd_5036672 : Nat := 2586233635042223231336773

theorem tailTrace_5036672 : CollatzResearch.WordTrace tailWord_5036672 prefixEnd_5036672 2586233635042223231336773 := by
  unfold tailWord_5036672
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851259804502506969540135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122468346406003342626053513 91851259804502506969540135)
  ·
    refine ⟨137776889706753760454310203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91851259804502506969540135 137776889706753760454310203)
    ·
      refine ⟨206665334560130640681465305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137776889706753760454310203 206665334560130640681465305)
      ·
        refine ⟨154999000920097980511098979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206665334560130640681465305 154999000920097980511098979)
        ·
          refine ⟨232498501380146970766648469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154999000920097980511098979 232498501380146970766648469)
          ·
            refine ⟨10898367252194389254686647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 232498501380146970766648469 10898367252194389254686647)
            ·
              refine ⟨16347550878291583882029971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10898367252194389254686647 16347550878291583882029971)
              ·
                refine ⟨24521326317437375823044957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16347550878291583882029971 24521326317437375823044957)
                ·
                  refine ⟨9195497369039015933641859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24521326317437375823044957 9195497369039015933641859)
                  ·
                    refine ⟨13793246053558523900462789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9195497369039015933641859 13793246053558523900462789)
                    ·
                      refine ⟨2586233635042223231336773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13793246053558523900462789 2586233635042223231336773)
                      ·
                        rfl

theorem cell23_5036672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_5036672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036672 prefixEnd_5036672 := by exact prefixLift 5036672
  have htrace : WordTrace (prefixWord ++ tailWord_5036672) baseStart_5036672 baseEnd_5036672 := by
    simpa [prefixWord, tailWord_5036672, baseEnd_5036672] using wordTrace_append hprefix tailTrace_5036672
  have hstable : (prefixWord ++ tailWord_5036672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036672).length < 2 ^ (prefixWord ++ tailWord_5036672).sum := by decide
  have hdescent : baseEnd_5036672 < baseStart_5036672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036675 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5036675 : Nat := 118140960795 + 5036675 * 2 ^ 59
def prefixEnd_5036675 : Nat := 4983230072969 + 3 ^ 40 * 5036675 * 2
def baseEnd_5036675 : Nat := 2586235175484186719599259

theorem tailTrace_5036675 : CollatzResearch.WordTrace tailWord_5036675 prefixEnd_5036675 2586235175484186719599259 := by
  unfold tailWord_5036675
  simp only [CollatzResearch.WordTrace]
  refine ⟨183702629027994145451439479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122468419351996096967626319 183702629027994145451439479)
  ·
    refine ⟨275553943541991218177159219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183702629027994145451439479 275553943541991218177159219)
    ·
      refine ⟨413330915312986827265738829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275553943541991218177159219 413330915312986827265738829)
      ·
        refine ⟨154999093242370060224652061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413330915312986827265738829 154999093242370060224652061)
        ·
          refine ⟨58124659965888772584244523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154999093242370060224652061 58124659965888772584244523)
          ·
            refine ⟨87186989948833158876366785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58124659965888772584244523 87186989948833158876366785)
            ·
              refine ⟨65390242461624869157275089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87186989948833158876366785 65390242461624869157275089)
              ·
                refine ⟨49042681846218651867956317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65390242461624869157275089 49042681846218651867956317)
                ·
                  refine ⟨18391005692331994450483619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49042681846218651867956317 18391005692331994450483619)
                  ·
                    refine ⟨27586508538497991675725429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18391005692331994450483619 27586508538497991675725429)
                    ·
                      refine ⟨2586235175484186719599259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27586508538497991675725429 2586235175484186719599259)
                      ·
                        rfl

theorem cell23_5036675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5036675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036675 prefixEnd_5036675 := by exact prefixLift 5036675
  have htrace : WordTrace (prefixWord ++ tailWord_5036675) baseStart_5036675 baseEnd_5036675 := by
    simpa [prefixWord, tailWord_5036675, baseEnd_5036675] using wordTrace_append hprefix tailTrace_5036675
  have hstable : (prefixWord ++ tailWord_5036675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036675).length < 2 ^ (prefixWord ++ tailWord_5036675).sum := by decide
  have hdescent : baseEnd_5036675 < baseStart_5036675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036676 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_5036676 : Nat := 118140960795 + 5036676 * 2 ^ 59
def prefixEnd_5036676 : Nat := 4983230072969 + 3 ^ 40 * 5036676 * 2
def baseEnd_5036676 : Nat := 2586235688964841215686755

theorem tailTrace_5036676 : CollatzResearch.WordTrace tailWord_5036676 prefixEnd_5036676 2586235688964841215686755 := by
  unfold tailWord_5036676
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851332750495261311112941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122468443667327015081483921 91851332750495261311112941)
  ·
    refine ⟨34444249781435722991667353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91851332750495261311112941 34444249781435722991667353)
    ·
      refine ⟨25833187336076792243750515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34444249781435722991667353 25833187336076792243750515)
      ·
        refine ⟨38749781004115188365625773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25833187336076792243750515 38749781004115188365625773)
        ·
          refine ⟨14531167876543195637109665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38749781004115188365625773 14531167876543195637109665)
          ·
            refine ⟨10898375907407396727832249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14531167876543195637109665 10898375907407396727832249)
            ·
              refine ⟨8173781930555547545874187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10898375907407396727832249 8173781930555547545874187)
              ·
                refine ⟨12260672895833321318811281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8173781930555547545874187 12260672895833321318811281)
                ·
                  refine ⟨9195504671874990989108461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12260672895833321318811281 9195504671874990989108461)
                  ·
                    refine ⟨3448314251953121620915673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9195504671874990989108461 3448314251953121620915673)
                    ·
                      refine ⟨2586235688964841215686755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448314251953121620915673 2586235688964841215686755)
                      ·
                        rfl

theorem cell23_5036676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_5036676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036676 prefixEnd_5036676 := by exact prefixLift 5036676
  have htrace : WordTrace (prefixWord ++ tailWord_5036676) baseStart_5036676 baseEnd_5036676 := by
    simpa [prefixWord, tailWord_5036676, baseEnd_5036676] using wordTrace_append hprefix tailTrace_5036676
  have hstable : (prefixWord ++ tailWord_5036676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036676).length < 2 ^ (prefixWord ++ tailWord_5036676).sum := by decide
  have hdescent : baseEnd_5036676 < baseStart_5036676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036700 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5036700 : Nat := 118140960795 + 5036700 * 2 ^ 59
def prefixEnd_5036700 : Nat := 4983230072969 + 3 ^ 40 * 5036700 * 2
def baseEnd_5036700 : Nat := 2586248012500549121786645

theorem tailTrace_5036700 : CollatzResearch.WordTrace tailWord_5036700 prefixEnd_5036700 2586248012500549121786645 := by
  unfold tailWord_5036700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91851770426451787360549777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122469027235269049814066369 91851770426451787360549777)
  ·
    refine ⟨68888827819838840520412333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91851770426451787360549777 68888827819838840520412333)
    ·
      refine ⟨25833310432439565195154625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68888827819838840520412333 25833310432439565195154625)
      ·
        refine ⟨19374982824329673896365969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25833310432439565195154625 19374982824329673896365969)
        ·
          refine ⟨14531237118247255422274477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19374982824329673896365969 14531237118247255422274477)
          ·
            refine ⟨5449213919342720783352929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14531237118247255422274477 5449213919342720783352929)
            ·
              refine ⟨4086910439507040587514697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5449213919342720783352929 4086910439507040587514697)
              ·
                refine ⟨3065182829630280440636023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4086910439507040587514697 3065182829630280440636023)
                ·
                  refine ⟨4597774244445420660954035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065182829630280440636023 4597774244445420660954035)
                  ·
                    refine ⟨6896661366668130991431053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597774244445420660954035 6896661366668130991431053)
                    ·
                      refine ⟨2586248012500549121786645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896661366668130991431053 2586248012500549121786645)
                      ·
                        rfl

theorem cell23_5036700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5036700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036700 prefixEnd_5036700 := by exact prefixLift 5036700
  have htrace : WordTrace (prefixWord ++ tailWord_5036700) baseStart_5036700 baseEnd_5036700 := by
    simpa [prefixWord, tailWord_5036700, baseEnd_5036700] using wordTrace_append hprefix tailTrace_5036700
  have hstable : (prefixWord ++ tailWord_5036700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036700).length < 2 ^ (prefixWord ++ tailWord_5036700).sum := by decide
  have hdescent : baseEnd_5036700 < baseStart_5036700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036740 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5036740 : Nat := 118140960795 + 5036740 * 2 ^ 59
def prefixEnd_5036740 : Nat := 4983230072969 + 3 ^ 40 * 5036740 * 2
def baseEnd_5036740 : Nat := 2586268551726728965286461

theorem tailTrace_5036740 : CollatzResearch.WordTrace tailWord_5036740 prefixEnd_5036740 2586268551726728965286461 := by
  unfold tailWord_5036740
  simp only [CollatzResearch.WordTrace]
  refine ⟨91852499886379330776277837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122469999848505774368370449 91852499886379330776277837)
  ·
    refine ⟨34444687457392249041104189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91852499886379330776277837 34444687457392249041104189)
    ·
      refine ⟨12916757796522093390414071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34444687457392249041104189 12916757796522093390414071)
      ·
        refine ⟨19375136694783140085621107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12916757796522093390414071 19375136694783140085621107)
        ·
          refine ⟨29062705042174710128431661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19375136694783140085621107 29062705042174710128431661)
          ·
            refine ⟨10898514390815516298161873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29062705042174710128431661 10898514390815516298161873)
            ·
              refine ⟨8173885793111637223621405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10898514390815516298161873 8173885793111637223621405)
              ·
                refine ⟨3065207172416863958858027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8173885793111637223621405 3065207172416863958858027)
                ·
                  refine ⟨4597810758625295938287041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3065207172416863958858027 4597810758625295938287041)
                  ·
                    refine ⟨3448358068968971953715281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4597810758625295938287041 3448358068968971953715281)
                    ·
                      refine ⟨2586268551726728965286461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448358068968971953715281 2586268551726728965286461)
                      ·
                        rfl

theorem cell23_5036740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5036740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036740 prefixEnd_5036740 := by exact prefixLift 5036740
  have htrace : WordTrace (prefixWord ++ tailWord_5036740) baseStart_5036740 baseEnd_5036740 := by
    simpa [prefixWord, tailWord_5036740, baseEnd_5036740] using wordTrace_append hprefix tailTrace_5036740
  have hstable : (prefixWord ++ tailWord_5036740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036740).length < 2 ^ (prefixWord ++ tailWord_5036740).sum := by decide
  have hdescent : baseEnd_5036740 < baseStart_5036740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036772 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_5036772 : Nat := 118140960795 + 5036772 * 2 ^ 59
def prefixEnd_5036772 : Nat := 4983230072969 + 3 ^ 40 * 5036772 * 2
def baseEnd_5036772 : Nat := 862094994369224280028771

theorem tailTrace_5036772 : CollatzResearch.WordTrace tailWord_5036772 prefixEnd_5036772 862094994369224280028771 := by
  unfold tailWord_5036772
  simp only [CollatzResearch.WordTrace]
  refine ⟨91853083454321365508860285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122470777939095154011813713 91853083454321365508860285)
  ·
    refine ⟨34444906295370512065822607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91853083454321365508860285 34444906295370512065822607)
    ·
      refine ⟨51667359443055768098733911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34444906295370512065822607 51667359443055768098733911)
      ·
        refine ⟨77501039164583652148100867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51667359443055768098733911 77501039164583652148100867)
        ·
          refine ⟨116251558746875478222151301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77501039164583652148100867 116251558746875478222151301)
          ·
            refine ⟨21797167265039152166653369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116251558746875478222151301 21797167265039152166653369)
            ·
              refine ⟨16347875448779364124990027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21797167265039152166653369 16347875448779364124990027)
              ·
                refine ⟨24521813173169046187485041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16347875448779364124990027 24521813173169046187485041)
                ·
                  refine ⟨18391359879876784640613781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24521813173169046187485041 18391359879876784640613781)
                  ·
                    refine ⟨862094994369224280028771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18391359879876784640613781 862094994369224280028771)
                    ·
                      rfl

theorem cell23_5036772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_5036772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036772 prefixEnd_5036772 := by exact prefixLift 5036772
  have htrace : WordTrace (prefixWord ++ tailWord_5036772) baseStart_5036772 baseEnd_5036772 := by
    simpa [prefixWord, tailWord_5036772, baseEnd_5036772] using wordTrace_append hprefix tailTrace_5036772
  have hstable : (prefixWord ++ tailWord_5036772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036772).length < 2 ^ (prefixWord ++ tailWord_5036772).sum := by decide
  have hdescent : baseEnd_5036772 < baseStart_5036772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036773 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5036773 : Nat := 118140960795 + 5036773 * 2 ^ 59
def prefixEnd_5036773 : Nat := 4983230072969 + 3 ^ 40 * 5036773 * 2
def baseEnd_5036773 : Nat := 2586285496588327336173809

theorem tailTrace_5036773 : CollatzResearch.WordTrace tailWord_5036773 prefixEnd_5036773 2586285496588327336173809 := by
  unfold tailWord_5036773
  simp only [CollatzResearch.WordTrace]
  refine ⟨183706203381639108188506973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122470802254426072125671315 183706203381639108188506973)
  ·
    refine ⟨68889826268114665570690115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183706203381639108188506973 68889826268114665570690115)
    ·
      refine ⟨103334739402171998356035173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68889826268114665570690115 103334739402171998356035173)
      ·
        refine ⟨19375263637907249691756595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103334739402171998356035173 19375263637907249691756595)
        ·
          refine ⟨29062895456860874537634893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19375263637907249691756595 29062895456860874537634893)
          ·
            refine ⟨10898585796322827951613085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29062895456860874537634893 10898585796322827951613085)
            ·
              refine ⟨4086969673621060481854907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10898585796322827951613085 4086969673621060481854907)
              ·
                refine ⟨6130454510431590722782361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086969673621060481854907 6130454510431590722782361)
                ·
                  refine ⟨4597840882823693042086771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6130454510431590722782361 4597840882823693042086771)
                  ·
                    refine ⟨6896761324235539563130157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4597840882823693042086771 6896761324235539563130157)
                    ·
                      refine ⟨2586285496588327336173809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6896761324235539563130157 2586285496588327336173809)
                      ·
                        rfl

theorem cell23_5036773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5036773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036773 prefixEnd_5036773 := by exact prefixLift 5036773
  have htrace : WordTrace (prefixWord ++ tailWord_5036773) baseStart_5036773 baseEnd_5036773 := by
    simpa [prefixWord, tailWord_5036773, baseEnd_5036773] using wordTrace_append hprefix tailTrace_5036773
  have hstable : (prefixWord ++ tailWord_5036773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036773).length < 2 ^ (prefixWord ++ tailWord_5036773).sum := by decide
  have hdescent : baseEnd_5036773 < baseStart_5036773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036796 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_5036796 : Nat := 118140960795 + 5036796 * 2 ^ 59
def prefixEnd_5036796 : Nat := 4983230072969 + 3 ^ 40 * 5036796 * 2
def baseEnd_5036796 : Nat := 2586297306643380746186203

theorem tailTrace_5036796 : CollatzResearch.WordTrace tailWord_5036796 prefixEnd_5036796 2586297306643380746186203 := by
  unfold tailWord_5036796
  simp only [CollatzResearch.WordTrace]
  refine ⟨91853521130277891558297121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122471361507037188744396161 91853521130277891558297121)
  ·
    refine ⟨68890140847708418668722841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91853521130277891558297121 68890140847708418668722841)
    ·
      refine ⟨51667605635781314001542131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68890140847708418668722841 51667605635781314001542131)
      ·
        refine ⟨77501408453671971002313197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51667605635781314001542131 77501408453671971002313197)
        ·
          refine ⟨29063028170126989125867449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77501408453671971002313197 29063028170126989125867449)
          ·
            refine ⟨21797271127595241844400587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29063028170126989125867449 21797271127595241844400587)
            ·
              refine ⟨32695906691392862766600881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21797271127595241844400587 32695906691392862766600881)
              ·
                refine ⟨24521930018544647074950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32695906691392862766600881 24521930018544647074950661)
                ·
                  refine ⟨4597861878477121326553249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24521930018544647074950661 4597861878477121326553249)
                  ·
                    refine ⟨3448396408857840994914937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4597861878477121326553249 3448396408857840994914937)
                    ·
                      refine ⟨2586297306643380746186203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3448396408857840994914937 2586297306643380746186203)
                      ·
                        rfl

theorem cell23_5036796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_5036796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036796 prefixEnd_5036796 := by exact prefixLift 5036796
  have htrace : WordTrace (prefixWord ++ tailWord_5036796) baseStart_5036796 baseEnd_5036796 := by
    simpa [prefixWord, tailWord_5036796, baseEnd_5036796] using wordTrace_append hprefix tailTrace_5036796
  have hstable : (prefixWord ++ tailWord_5036796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036796).length < 2 ^ (prefixWord ++ tailWord_5036796).sum := by decide
  have hdescent : baseEnd_5036796 < baseStart_5036796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036849 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_5036849 : Nat := 118140960795 + 5036849 * 2 ^ 59
def prefixEnd_5036849 : Nat := 4983230072969 + 3 ^ 40 * 5036849 * 2
def baseEnd_5036849 : Nat := 862108173706023012941153

theorem tailTrace_5036849 : CollatzResearch.WordTrace tailWord_5036849 prefixEnd_5036849 862108173706023012941153 := by
  unfold tailWord_5036849
  simp only [CollatzResearch.WordTrace]
  refine ⟨183708975329363773168273601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122472650219575848778849067 183708975329363773168273601)
  ·
    refine ⟨137781731497022829876205201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183708975329363773168273601 137781731497022829876205201)
    ·
      refine ⟨103336298622767122407153901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137781731497022829876205201 103336298622767122407153901)
      ·
        refine ⟨38751111983537670902682713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103336298622767122407153901 38751111983537670902682713)
        ·
          refine ⟨29063333987653253177012035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38751111983537670902682713 29063333987653253177012035)
          ·
            refine ⟨43595000981479879765518053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29063333987653253177012035 43595000981479879765518053)
            ·
              refine ⟨8174062684027477456034635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43595000981479879765518053 8174062684027477456034635)
              ·
                refine ⟨12261094026041216184051953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8174062684027477456034635 12261094026041216184051953)
                ·
                  refine ⟨9195820519530912138038965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12261094026041216184051953 9195820519530912138038965)
                  ·
                    refine ⟨862108173706023012941153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9195820519530912138038965 862108173706023012941153)
                    ·
                      rfl

theorem cell23_5036849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_5036849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036849 prefixEnd_5036849 := by exact prefixLift 5036849
  have htrace : WordTrace (prefixWord ++ tailWord_5036849) baseStart_5036849 baseEnd_5036849 := by
    simpa [prefixWord, tailWord_5036849, baseEnd_5036849] using wordTrace_append hprefix tailTrace_5036849
  have hstable : (prefixWord ++ tailWord_5036849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036849).length < 2 ^ (prefixWord ++ tailWord_5036849).sum := by decide
  have hdescent : baseEnd_5036849 < baseStart_5036849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5036870 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5036870 : Nat := 118140960795 + 5036870 * 2 ^ 59
def prefixEnd_5036870 : Nat := 4983230072969 + 3 ^ 40 * 5036870 * 2
def baseEnd_5036870 : Nat := 287370589356868161851207

theorem tailTrace_5036870 : CollatzResearch.WordTrace tailWord_5036870 prefixEnd_5036870 287370589356868161851207 := by
  unfold tailWord_5036870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5740929414446490429837127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122473160841525129169858709 5740929414446490429837127)
  ·
    refine ⟨8611394121669735644755691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5740929414446490429837127 8611394121669735644755691)
    ·
      refine ⟨12917091182504603467133537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8611394121669735644755691 12917091182504603467133537)
      ·
        refine ⟨9687818386878452600350153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12917091182504603467133537 9687818386878452600350153)
        ·
          refine ⟨7265863790158839450262615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9687818386878452600350153 7265863790158839450262615)
          ·
            refine ⟨10898795685238259175393923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7265863790158839450262615 10898795685238259175393923)
            ·
              refine ⟨16348193527857388763090885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10898795685238259175393923 16348193527857388763090885)
              ·
                refine ⟨3065286286473260393079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16348193527857388763090885 3065286286473260393079541)
                ·
                  refine ⟨287370589356868161851207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3065286286473260393079541 287370589356868161851207)
                  ·
                    rfl

theorem cell23_5036870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5036870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5036870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5036870 prefixEnd_5036870 := by exact prefixLift 5036870
  have htrace : WordTrace (prefixWord ++ tailWord_5036870) baseStart_5036870 baseEnd_5036870 := by
    simpa [prefixWord, tailWord_5036870, baseEnd_5036870] using wordTrace_append hprefix tailTrace_5036870
  have hstable : (prefixWord ++ tailWord_5036870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5036870).length < 2 ^ (prefixWord ++ tailWord_5036870).sum := by decide
  have hdescent : baseEnd_5036870 < baseStart_5036870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5036870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
