import V185TrunkScan23Chunk1272

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7541837 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7541837 : Nat := 118140960795 + 7541837 * 2 ^ 59
def prefixEnd_7541837 : Nat := 4983230072969 + 3 ^ 40 * 7541837 * 2
def baseEnd_7541837 : Nat := 3872587398862914261753229

theorem tailTrace_7541837 : CollatzResearch.WordTrace tailWord_7541837 prefixEnd_7541837 3872587398862914261753229 := by
  unfold tailWord_7541837
  simp only [CollatzResearch.WordTrace]
  refine ⟨275073393578220067058351765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183382262385480044705567843 275073393578220067058351765)
  ·
    refine ⟨12894065323979065643360239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275073393578220067058351765 12894065323979065643360239)
    ·
      refine ⟨19341097985968598465040359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12894065323979065643360239 19341097985968598465040359)
      ·
        refine ⟨29011646978952897697560539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19341097985968598465040359 29011646978952897697560539)
        ·
          refine ⟨43517470468429346546340809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29011646978952897697560539 43517470468429346546340809)
          ·
            refine ⟨32638102851322009909755607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43517470468429346546340809 32638102851322009909755607)
            ·
              refine ⟨48957154276983014864633411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32638102851322009909755607 48957154276983014864633411)
              ·
                refine ⟨73435731415474522296950117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48957154276983014864633411 73435731415474522296950117)
                ·
                  refine ⟨13769199640401472930678147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73435731415474522296950117 13769199640401472930678147)
                  ·
                    refine ⟨20653799460602209396017221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13769199640401472930678147 20653799460602209396017221)
                    ·
                      refine ⟨3872587398862914261753229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653799460602209396017221 3872587398862914261753229)
                      ·
                        rfl

theorem cell23_7541837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7541837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541837 prefixEnd_7541837 := by exact prefixLift 7541837
  have htrace : WordTrace (prefixWord ++ tailWord_7541837) baseStart_7541837 baseEnd_7541837 := by
    simpa [prefixWord, tailWord_7541837, baseEnd_7541837] using wordTrace_append hprefix tailTrace_7541837
  have hstable : (prefixWord ++ tailWord_7541837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541837).length < 2 ^ (prefixWord ++ tailWord_7541837).sum := by decide
  have hdescent : baseEnd_7541837 < baseStart_7541837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541883 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_7541883 : Nat := 118140960795 + 7541883 * 2 ^ 59
def prefixEnd_7541883 : Nat := 4983230072969 + 3 ^ 40 * 7541883 * 2
def baseEnd_7541883 : Nat := 3872611018973021081778017

theorem tailTrace_7541883 : CollatzResearch.WordTrace tailWord_7541883 prefixEnd_7541883 3872611018973021081778017 := by
  unfold tailWord_7541883
  simp only [CollatzResearch.WordTrace]
  refine ⟨275075071336053416914526303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183383380890702277943017535 275075071336053416914526303)
  ·
    refine ⟨412612607004080125371789455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275075071336053416914526303 412612607004080125371789455)
    ·
      refine ⟨618918910506120188057684183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412612607004080125371789455 618918910506120188057684183)
      ·
        refine ⟨928378365759180282086526275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618918910506120188057684183 928378365759180282086526275)
        ·
          refine ⟨1392567548638770423129789413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928378365759180282086526275 1392567548638770423129789413)
          ·
            refine ⟨261106415369769454336835515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1392567548638770423129789413 261106415369769454336835515)
            ·
              refine ⟨391659623054654181505253273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261106415369769454336835515 391659623054654181505253273)
              ·
                refine ⟨293744717290990636128939955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391659623054654181505253273 293744717290990636128939955)
                ·
                  refine ⟨440617075936485954193409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293744717290990636128939955 440617075936485954193409933)
                  ·
                    refine ⟨165231403476182232822528725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 440617075936485954193409933 165231403476182232822528725)
                    ·
                      refine ⟨3872611018973021081778017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165231403476182232822528725 3872611018973021081778017)
                      ·
                        rfl

theorem cell23_7541883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_7541883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541883 prefixEnd_7541883 := by exact prefixLift 7541883
  have htrace : WordTrace (prefixWord ++ tailWord_7541883) baseStart_7541883 baseEnd_7541883 := by
    simpa [prefixWord, tailWord_7541883, baseEnd_7541883] using wordTrace_append hprefix tailTrace_7541883
  have hstable : (prefixWord ++ tailWord_7541883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541883).length < 2 ^ (prefixWord ++ tailWord_7541883).sum := by decide
  have hdescent : baseEnd_7541883 < baseStart_7541883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541937 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_7541937 : Nat := 118140960795 + 7541937 * 2 ^ 59
def prefixEnd_7541937 : Nat := 4983230072969 + 3 ^ 40 * 7541937 * 2
def baseEnd_7541937 : Nat := 1290879582309454623500923

theorem tailTrace_7541937 : CollatzResearch.WordTrace tailWord_7541937 prefixEnd_7541937 1290879582309454623500923 := by
  unfold tailWord_7541937
  simp only [CollatzResearch.WordTrace]
  refine ⟨275077040877857784136992065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183384693918571856091328043 275077040877857784136992065)
  ·
    refine ⟨206307780658393338102744049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275077040877857784136992065 206307780658393338102744049)
    ·
      refine ⟨154730835493795003577058037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206307780658393338102744049 154730835493795003577058037)
      ·
        refine ⟨14506015827543281585349191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154730835493795003577058037 14506015827543281585349191)
        ·
          refine ⟨21759023741314922378023787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14506015827543281585349191 21759023741314922378023787)
          ·
            refine ⟨32638535611972383567035681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21759023741314922378023787 32638535611972383567035681)
            ·
              refine ⟨24478901708979287675276761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32638535611972383567035681 24478901708979287675276761)
              ·
                refine ⟨18359176281734465756457571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24478901708979287675276761 18359176281734465756457571)
                ·
                  refine ⟨27538764422601698634686357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18359176281734465756457571 27538764422601698634686357)
                  ·
                    refine ⟨1290879582309454623500923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27538764422601698634686357 1290879582309454623500923)
                    ·
                      rfl

theorem cell23_7541937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_7541937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541937 prefixEnd_7541937 := by exact prefixLift 7541937
  have htrace : WordTrace (prefixWord ++ tailWord_7541937) baseStart_7541937 baseEnd_7541937 := by
    simpa [prefixWord, tailWord_7541937, baseEnd_7541937] using wordTrace_append hprefix tailTrace_7541937
  have hstable : (prefixWord ++ tailWord_7541937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541937).length < 2 ^ (prefixWord ++ tailWord_7541937).sum := by decide
  have hdescent : baseEnd_7541937 < baseStart_7541937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541994 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_7541994 : Nat := 118140960795 + 7541994 * 2 ^ 59
def prefixEnd_7541994 : Nat := 4983230072969 + 3 ^ 40 * 7541994 * 2
def baseEnd_7541994 : Nat := 3872668015325670147490007

theorem tailTrace_7541994 : CollatzResearch.WordTrace tailWord_7541994 prefixEnd_7541994 3872668015325670147490007 := by
  unfold tailWord_7541994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68769779959662820717954259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183386079892434188581211357 68769779959662820717954259)
  ·
    refine ⟨103154669939494231076931389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68769779959662820717954259 103154669939494231076931389)
    ·
      refine ⟨38683001227310336653849271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103154669939494231076931389 38683001227310336653849271)
      ·
        refine ⟨58024501840965504980773907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38683001227310336653849271 58024501840965504980773907)
        ·
          refine ⟨87036752761448257471160861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58024501840965504980773907 87036752761448257471160861)
          ·
            refine ⟨32638782285543096551685323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87036752761448257471160861 32638782285543096551685323)
            ·
              refine ⟨48958173428314644827527985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32638782285543096551685323 48958173428314644827527985)
              ·
                refine ⟨36718630071235983620645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48958173428314644827527985 36718630071235983620645989)
                ·
                  refine ⟨6884743138356746928871123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36718630071235983620645989 6884743138356746928871123)
                  ·
                    refine ⟨10327114707535120393306685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6884743138356746928871123 10327114707535120393306685)
                    ·
                      refine ⟨3872668015325670147490007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10327114707535120393306685 3872668015325670147490007)
                      ·
                        rfl

theorem cell23_7541994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_7541994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541994 prefixEnd_7541994 := by exact prefixLift 7541994
  have htrace : WordTrace (prefixWord ++ tailWord_7541994) baseStart_7541994 baseEnd_7541994 := by
    simpa [prefixWord, tailWord_7541994, baseEnd_7541994] using wordTrace_append hprefix tailTrace_7541994
  have hstable : (prefixWord ++ tailWord_7541994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541994).length < 2 ^ (prefixWord ++ tailWord_7541994).sum := by decide
  have hdescent : baseEnd_7541994 < baseStart_7541994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542000 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_7542000 : Nat := 118140960795 + 7542000 * 2 ^ 59
def prefixEnd_7542000 : Nat := 4983230072969 + 3 ^ 40 * 7542000 * 2
def baseEnd_7542000 : Nat := 3872671096209597124014979

theorem tailTrace_7542000 : CollatzResearch.WordTrace tailWord_7542000 prefixEnd_7542000 3872671096209597124014979 := by
  unfold tailWord_7542000
  simp only [CollatzResearch.WordTrace]
  refine ⟨137539669338314772948267727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183386225784419697264356969 137539669338314772948267727)
  ·
    refine ⟨206309504007472159422401591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137539669338314772948267727 206309504007472159422401591)
    ·
      refine ⟨309464256011208239133602387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206309504007472159422401591 309464256011208239133602387)
      ·
        refine ⟨464196384016812358700403581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309464256011208239133602387 464196384016812358700403581)
        ·
          refine ⟨174073644006304634512651343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464196384016812358700403581 174073644006304634512651343)
          ·
            refine ⟨261110466009456951768977015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174073644006304634512651343 261110466009456951768977015)
            ·
              refine ⟨391665699014185427653465523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261110466009456951768977015 391665699014185427653465523)
              ·
                refine ⟨587498548521278141480198285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391665699014185427653465523 587498548521278141480198285)
                ·
                  refine ⟨220311955695479303055074357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587498548521278141480198285 220311955695479303055074357)
                  ·
                    refine ⟨20654245846451184661413221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220311955695479303055074357 20654245846451184661413221)
                    ·
                      refine ⟨3872671096209597124014979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20654245846451184661413221 3872671096209597124014979)
                      ·
                        rfl

theorem cell23_7542000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_7542000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542000 prefixEnd_7542000 := by exact prefixLift 7542000
  have htrace : WordTrace (prefixWord ++ tailWord_7542000) baseStart_7542000 baseEnd_7542000 := by
    simpa [prefixWord, tailWord_7542000, baseEnd_7542000] using wordTrace_append hprefix tailTrace_7542000
  have hstable : (prefixWord ++ tailWord_7542000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542000).length < 2 ^ (prefixWord ++ tailWord_7542000).sum := by decide
  have hdescent : baseEnd_7542000 < baseStart_7542000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542028 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_7542028 : Nat := 118140960795 + 7542028 * 2 ^ 59
def prefixEnd_7542028 : Nat := 4983230072969 + 3 ^ 40 * 7542028 * 2
def baseEnd_7542028 : Nat := 3872685473667923014464851

theorem tailTrace_7542028 : CollatzResearch.WordTrace tailWord_7542028 prefixEnd_7542028 3872685473667923014464851 := by
  unfold tailWord_7542028
  simp only [CollatzResearch.WordTrace]
  refine ⟨137540179960264053339277369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183386906613685404452369825 137540179960264053339277369)
  ·
    refine ⟨103155134970198040004458027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137540179960264053339277369 103155134970198040004458027)
    ·
      refine ⟨154732702455297060006687041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103155134970198040004458027 154732702455297060006687041)
      ·
        refine ⟨116049526841472795005015281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154732702455297060006687041 116049526841472795005015281)
        ·
          refine ⟨87037145131104596253761461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116049526841472795005015281 87037145131104596253761461)
          ·
            refine ⟨8159732356041055898790137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87037145131104596253761461 8159732356041055898790137)
            ·
              refine ⟨6119799267030791924092603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8159732356041055898790137 6119799267030791924092603)
              ·
                refine ⟨9179698900546187886138905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119799267030791924092603 9179698900546187886138905)
                ·
                  refine ⟨6884774175409640914604179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179698900546187886138905 6884774175409640914604179)
                  ·
                    refine ⟨10327161263114461371906269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6884774175409640914604179 10327161263114461371906269)
                    ·
                      refine ⟨3872685473667923014464851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10327161263114461371906269 3872685473667923014464851)
                      ·
                        rfl

theorem cell23_7542028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_7542028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542028 prefixEnd_7542028 := by exact prefixLift 7542028
  have htrace : WordTrace (prefixWord ++ tailWord_7542028) baseStart_7542028 baseEnd_7542028 := by
    simpa [prefixWord, tailWord_7542028, baseEnd_7542028] using wordTrace_append hprefix tailTrace_7542028
  have hstable : (prefixWord ++ tailWord_7542028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542028).length < 2 ^ (prefixWord ++ tailWord_7542028).sum := by decide
  have hdescent : baseEnd_7542028 < baseStart_7542028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542074 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_7542074 : Nat := 118140960795 + 7542074 * 2 ^ 59
def prefixEnd_7542074 : Nat := 4983230072969 + 3 ^ 40 * 7542074 * 2
def baseEnd_7542074 : Nat := 430301010419781092721071

theorem tailTrace_7542074 : CollatzResearch.WordTrace tailWord_7542074 prefixEnd_7542074 430301010419781092721071 := by
  unfold tailWord_7542074
  simp only [CollatzResearch.WordTrace]
  refine ⟨68770509419590364133682319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183388025118907637689819517 68770509419590364133682319)
  ·
    refine ⟨103155764129385546200523479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68770509419590364133682319 103155764129385546200523479)
    ·
      refine ⟨154733646194078319300785219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103155764129385546200523479 154733646194078319300785219)
      ·
        refine ⟨232100469291117478951177829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154733646194078319300785219 232100469291117478951177829)
        ·
          refine ⟨43518837992084527303345843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232100469291117478951177829 43518837992084527303345843)
          ·
            refine ⟨65278256988126790955018765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43518837992084527303345843 65278256988126790955018765)
            ·
              refine ⟨24479346370547546608132037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65278256988126790955018765 24479346370547546608132037)
              ·
                refine ⟨4589877444477664989024757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24479346370547546608132037 4589877444477664989024757)
                ·
                  refine ⟨430301010419781092721071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4589877444477664989024757 430301010419781092721071)
                  ·
                    rfl

theorem cell23_7542074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_7542074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542074 prefixEnd_7542074 := by exact prefixLift 7542074
  have htrace : WordTrace (prefixWord ++ tailWord_7542074) baseStart_7542074 baseEnd_7542074 := by
    simpa [prefixWord, tailWord_7542074, baseEnd_7542074] using wordTrace_append hprefix tailTrace_7542074
  have hstable : (prefixWord ++ tailWord_7542074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542074).length < 2 ^ (prefixWord ++ tailWord_7542074).sum := by decide
  have hdescent : baseEnd_7542074 < baseStart_7542074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542094 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_7542094 : Nat := 118140960795 + 7542094 * 2 ^ 59
def prefixEnd_7542094 : Nat := 4983230072969 + 3 ^ 40 * 7542094 * 2
def baseEnd_7542094 : Nat := 3872719363391119756239547

theorem tailTrace_7542094 : CollatzResearch.WordTrace tailWord_7542094 prefixEnd_7542094 3872719363391119756239547 := by
  unfold tailWord_7542094
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385345892286124993807167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183388511425525999966971557 34385345892286124993807167)
  ·
    refine ⟨51578018838429187490710751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34385345892286124993807167 51578018838429187490710751)
    ·
      refine ⟨77367028257643781236066127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51578018838429187490710751 77367028257643781236066127)
      ·
        refine ⟨116050542386465671854099191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77367028257643781236066127 116050542386465671854099191)
        ·
          refine ⟨174075813579698507781148787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116050542386465671854099191 174075813579698507781148787)
          ·
            refine ⟨261113720369547761671723181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174075813579698507781148787 261113720369547761671723181)
            ·
              refine ⟨97917645138580410626896193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261113720369547761671723181 97917645138580410626896193)
              ·
                refine ⟨73438233853935307970172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97917645138580410626896193 73438233853935307970172145)
                ·
                  refine ⟨55078675390451480977629109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73438233853935307970172145 55078675390451480977629109)
                  ·
                    refine ⟨5163625817854826341652729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55078675390451480977629109 5163625817854826341652729)
                    ·
                      refine ⟨3872719363391119756239547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163625817854826341652729 3872719363391119756239547)
                      ·
                        rfl

theorem cell23_7542094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_7542094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542094 prefixEnd_7542094 := by exact prefixLift 7542094
  have htrace : WordTrace (prefixWord ++ tailWord_7542094) baseStart_7542094 baseEnd_7542094 := by
    simpa [prefixWord, tailWord_7542094, baseEnd_7542094] using wordTrace_append hprefix tailTrace_7542094
  have hstable : (prefixWord ++ tailWord_7542094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542094).length < 2 ^ (prefixWord ++ tailWord_7542094).sum := by decide
  have hdescent : baseEnd_7542094 < baseStart_7542094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542164 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 8]
def baseStart_7542164 : Nat := 118140960795 + 7542164 * 2 ^ 59
def prefixEnd_7542164 : Nat := 4983230072969 + 3 ^ 40 * 7542164 * 2
def baseEnd_7542164 : Nat := 430306145226326053596025

theorem tailTrace_7542164 : CollatzResearch.WordTrace tailWord_7542164 prefixEnd_7542164 430306145226326053596025 := by
  unfold tailWord_7542164
  simp only [CollatzResearch.WordTrace]
  refine ⟨137542660124017700952752773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183390213498690267937003697 137542660124017700952752773)
  ·
    refine ⟨25789248773253318928641145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137542660124017700952752773 25789248773253318928641145)
    ·
      refine ⟨19341936579939989196480859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25789248773253318928641145 19341936579939989196480859)
      ·
        refine ⟨29012904869909983794721289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19341936579939989196480859 29012904869909983794721289)
        ·
          refine ⟨21759678652432487846040967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29012904869909983794721289 21759678652432487846040967)
          ·
            refine ⟨32639517978648731769061451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21759678652432487846040967 32639517978648731769061451)
            ·
              refine ⟨48959276967973097653592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32639517978648731769061451 48959276967973097653592177)
              ·
                refine ⟨36719457725979823240194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48959276967973097653592177 36719457725979823240194133)
                ·
                  refine ⟨430306145226326053596025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36719457725979823240194133 430306145226326053596025)
                  ·
                    rfl

theorem cell23_7542164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_7542164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542164 prefixEnd_7542164 := by exact prefixLift 7542164
  have htrace : WordTrace (prefixWord ++ tailWord_7542164) baseStart_7542164 baseEnd_7542164 := by
    simpa [prefixWord, tailWord_7542164, baseEnd_7542164] using wordTrace_append hprefix tailTrace_7542164
  have hstable : (prefixWord ++ tailWord_7542164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542164).length < 2 ^ (prefixWord ++ tailWord_7542164).sum := by decide
  have hdescent : baseEnd_7542164 < baseStart_7542164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542207 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 6]
def baseStart_7542207 : Nat := 118140960795 + 7542207 * 2 ^ 59
def prefixEnd_7542207 : Nat := 4983230072969 + 3 ^ 40 * 7542207 * 2
def baseEnd_7542207 : Nat := 1290925795568359271375509

theorem tailTrace_7542207 : CollatzResearch.WordTrace tailWord_7542207 prefixEnd_7542207 1290925795568359271375509 := by
  unfold tailWord_7542207
  simp only [CollatzResearch.WordTrace]
  refine ⟨275086888586879620249320875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183391259057919746832880583 275086888586879620249320875)
  ·
    refine ⟨412630332880319430373981313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275086888586879620249320875 412630332880319430373981313)
    ·
      refine ⟨309472749660239572780485985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412630332880319430373981313 309472749660239572780485985)
      ·
        refine ⟨232104562245179679585364489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309472749660239572780485985 232104562245179679585364489)
        ·
          refine ⟨174078421683884759689023367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232104562245179679585364489 174078421683884759689023367)
          ·
            refine ⟨261117632525827139533535051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174078421683884759689023367 261117632525827139533535051)
            ·
              refine ⟨391676448788740709300302577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261117632525827139533535051 391676448788740709300302577)
              ·
                refine ⟨293757336591555531975226933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391676448788740709300302577 293757336591555531975226933)
                ·
                  refine ⟨27539750305458331122677525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293757336591555531975226933 27539750305458331122677525)
                  ·
                    refine ⟨1290925795568359271375509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27539750305458331122677525 1290925795568359271375509)
                    ·
                      rfl

theorem cell23_7542207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_7542207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542207 prefixEnd_7542207 := by exact prefixLift 7542207
  have htrace : WordTrace (prefixWord ++ tailWord_7542207) baseStart_7542207 baseEnd_7542207 := by
    simpa [prefixWord, tailWord_7542207, baseEnd_7542207] using wordTrace_append hprefix tailTrace_7542207
  have hstable : (prefixWord ++ tailWord_7542207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542207).length < 2 ^ (prefixWord ++ tailWord_7542207).sum := by decide
  have hdescent : baseEnd_7542207 < baseStart_7542207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542218 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_7542218 : Nat := 118140960795 + 7542218 * 2 ^ 59
def prefixEnd_7542218 : Nat := 4983230072969 + 3 ^ 40 * 7542218 * 2
def baseEnd_7542218 : Nat := 3872783034992277271088977

theorem tailTrace_7542218 : CollatzResearch.WordTrace tailWord_7542218 prefixEnd_7542218 3872783034992277271088977 := by
  unfold tailWord_7542218
  simp only [CollatzResearch.WordTrace]
  refine ⟨68771822447459942281992827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183391526526559846085314205 68771822447459942281992827)
  ·
    refine ⟨103157733671189913422989241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68771822447459942281992827 103157733671189913422989241)
    ·
      refine ⟨77368300253392435067241931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103157733671189913422989241 77368300253392435067241931)
      ·
        refine ⟨116052450380088652600862897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77368300253392435067241931 116052450380088652600862897)
        ·
          refine ⟨87039337785066489450647173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116052450380088652600862897 87039337785066489450647173)
          ·
            refine ⟨16319875834699966771996345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87039337785066489450647173 16319875834699966771996345)
            ·
              refine ⟨12239906876024975078997259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16319875834699966771996345 12239906876024975078997259)
              ·
                refine ⟨18359860314037462618495889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12239906876024975078997259 18359860314037462618495889)
                ·
                  refine ⟨13769895235528096963871917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18359860314037462618495889 13769895235528096963871917)
                  ·
                    refine ⟨5163710713323036361451969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13769895235528096963871917 5163710713323036361451969)
                    ·
                      refine ⟨3872783034992277271088977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163710713323036361451969 3872783034992277271088977)
                      ·
                        rfl

theorem cell23_7542218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_7542218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542218 prefixEnd_7542218 := by exact prefixLift 7542218
  have htrace : WordTrace (prefixWord ++ tailWord_7542218) baseStart_7542218 baseEnd_7542218 := by
    simpa [prefixWord, tailWord_7542218, baseEnd_7542218] using wordTrace_append hprefix tailTrace_7542218
  have hstable : (prefixWord ++ tailWord_7542218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542218).length < 2 ^ (prefixWord ++ tailWord_7542218).sum := by decide
  have hdescent : baseEnd_7542218 < baseStart_7542218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542241 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_7542241 : Nat := 118140960795 + 7542241 * 2 ^ 59
def prefixEnd_7542241 : Nat := 4983230072969 + 3 ^ 40 * 7542241 * 2
def baseEnd_7542241 : Nat := 1290931615015776893700457

theorem tailTrace_7542241 : CollatzResearch.WordTrace tailWord_7542241 prefixEnd_7542241 1290931615015776893700457 := by
  unfold tailWord_7542241
  simp only [CollatzResearch.WordTrace]
  refine ⟨275088128668756444056058577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183392085779170962704039051 275088128668756444056058577)
  ·
    refine ⟨206316096501567333042043933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275088128668756444056058577 206316096501567333042043933)
    ·
      refine ⟨77368536188087749890766475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206316096501567333042043933 77368536188087749890766475)
      ·
        refine ⟨116052804282131624836149713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77368536188087749890766475 116052804282131624836149713)
        ·
          refine ⟨87039603211598718627112285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116052804282131624836149713 87039603211598718627112285)
          ·
            refine ⟨32639851204349519485167107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87039603211598718627112285 32639851204349519485167107)
            ·
              refine ⟨48959776806524279227750661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32639851204349519485167107 48959776806524279227750661)
              ·
                refine ⟨9179958151223302355203249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48959776806524279227750661 9179958151223302355203249)
                ·
                  refine ⟨6884968613417476766402437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179958151223302355203249 6884968613417476766402437)
                  ·
                    refine ⟨1290931615015776893700457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884968613417476766402437 1290931615015776893700457)
                    ·
                      rfl

theorem cell23_7542241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_7542241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542241 prefixEnd_7542241 := by exact prefixLift 7542241
  have htrace : WordTrace (prefixWord ++ tailWord_7542241) baseStart_7542241 baseEnd_7542241 := by
    simpa [prefixWord, tailWord_7542241, baseEnd_7542241] using wordTrace_append hprefix tailTrace_7542241
  have hstable : (prefixWord ++ tailWord_7542241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542241).length < 2 ^ (prefixWord ++ tailWord_7542241).sum := by decide
  have hdescent : baseEnd_7542241 < baseStart_7542241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542248 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_7542248 : Nat := 118140960795 + 7542248 * 2 ^ 59
def prefixEnd_7542248 : Nat := 4983230072969 + 3 ^ 40 * 7542248 * 2
def baseEnd_7542248 : Nat := 3872798439411912153713839

theorem tailTrace_7542248 : CollatzResearch.WordTrace tailWord_7542248 prefixEnd_7542248 3872798439411912153713839 := by
  unfold tailWord_7542248
  simp only [CollatzResearch.WordTrace]
  refine ⟨137544191989865542125781699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183392255986487389501042265 137544191989865542125781699)
  ·
    refine ⟨206316287984798313188672549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137544191989865542125781699 206316287984798313188672549)
    ·
      refine ⟨38684303997149683722876103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206316287984798313188672549 38684303997149683722876103)
      ·
        refine ⟨58026455995724525584314155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38684303997149683722876103 58026455995724525584314155)
        ·
          refine ⟨87039683993586788376471233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58026455995724525584314155 87039683993586788376471233)
          ·
            refine ⟨65279762995190091282353425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87039683993586788376471233 65279762995190091282353425)
            ·
              refine ⟨48959822246392568461765069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65279762995190091282353425 48959822246392568461765069)
              ·
                refine ⟨18359933342397213173161901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48959822246392568461765069 18359933342397213173161901)
                ·
                  refine ⟨6884975003398954939935713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18359933342397213173161901 6884975003398954939935713)
                  ·
                    refine ⟨5163731252549216204951785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6884975003398954939935713 5163731252549216204951785)
                    ·
                      refine ⟨3872798439411912153713839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163731252549216204951785 3872798439411912153713839)
                      ·
                        rfl

theorem cell23_7542248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_7542248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542248 prefixEnd_7542248 := by exact prefixLift 7542248
  have htrace : WordTrace (prefixWord ++ tailWord_7542248) baseStart_7542248 baseEnd_7542248 := by
    simpa [prefixWord, tailWord_7542248, baseEnd_7542248] using wordTrace_append hprefix tailTrace_7542248
  have hstable : (prefixWord ++ tailWord_7542248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542248).length < 2 ^ (prefixWord ++ tailWord_7542248).sum := by decide
  have hdescent : baseEnd_7542248 < baseStart_7542248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542258 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_7542258 : Nat := 118140960795 + 7542258 * 2 ^ 59
def prefixEnd_7542258 : Nat := 4983230072969 + 3 ^ 40 * 7542258 * 2
def baseEnd_7542258 : Nat := 1290934524739485704862931

theorem tailTrace_7542258 : CollatzResearch.WordTrace tailWord_7542258 prefixEnd_7542258 1290934524739485704862931 := by
  unfold tailWord_7542258
  simp only [CollatzResearch.WordTrace]
  refine ⟨68772187177423713989856857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183392499139796570639618285 68772187177423713989856857)
  ·
    refine ⟨51579140383067785492392643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68772187177423713989856857 51579140383067785492392643)
    ·
      refine ⟨77368710574601678238588965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51579140383067785492392643 77368710574601678238588965)
      ·
        refine ⟨14506633232737814669735431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77368710574601678238588965 14506633232737814669735431)
        ·
          refine ⟨21759949849106722004603147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14506633232737814669735431 21759949849106722004603147)
          ·
            refine ⟨32639924773660083006904721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21759949849106722004603147 32639924773660083006904721)
            ·
              refine ⟨24479943580245062255178541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32639924773660083006904721 24479943580245062255178541)
              ·
                refine ⟨9179978842591898345691953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24479943580245062255178541 9179978842591898345691953)
                ·
                  refine ⟨6884984131943923759268965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179978842591898345691953 6884984131943923759268965)
                  ·
                    refine ⟨1290934524739485704862931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884984131943923759268965 1290934524739485704862931)
                    ·
                      rfl

theorem cell23_7542258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_7542258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542258 prefixEnd_7542258 := by exact prefixLift 7542258
  have htrace : WordTrace (prefixWord ++ tailWord_7542258) baseStart_7542258 baseEnd_7542258 := by
    simpa [prefixWord, tailWord_7542258, baseEnd_7542258] using wordTrace_append hprefix tailTrace_7542258
  have hstable : (prefixWord ++ tailWord_7542258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542258).length < 2 ^ (prefixWord ++ tailWord_7542258).sum := by decide
  have hdescent : baseEnd_7542258 < baseStart_7542258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542281 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_7542281 : Nat := 118140960795 + 7542281 * 2 ^ 59
def prefixEnd_7542281 : Nat := 4983230072969 + 3 ^ 40 * 7542281 * 2
def baseEnd_7542281 : Nat := 3872815384273510524601187

theorem tailTrace_7542281 : CollatzResearch.WordTrace tailWord_7542281 prefixEnd_7542281 3872815384273510524601187 := by
  unfold tailWord_7542281
  simp only [CollatzResearch.WordTrace]
  refine ⟨275089587588611530887514697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183393058392407687258343131 275089587588611530887514697)
  ·
    refine ⟨206317190691458648165636023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275089587588611530887514697 206317190691458648165636023)
    ·
      refine ⟨309475786037187972248454035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206317190691458648165636023 309475786037187972248454035)
      ·
        refine ⟨464213679055781958372681053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309475786037187972248454035 464213679055781958372681053)
        ·
          refine ⟨174080129645918234389755395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464213679055781958372681053 174080129645918234389755395)
          ·
            refine ⟨261120194468877351584633093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174080129645918234389755395 261120194468877351584633093)
            ·
              refine ⟨48960036462914503422118705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261120194468877351584633093 48960036462914503422118705)
              ·
                refine ⟨36720027347185877566589029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48960036462914503422118705 36720027347185877566589029)
                ·
                  refine ⟨6885005127597352043735443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36720027347185877566589029 6885005127597352043735443)
                  ·
                    refine ⟨10327507691396028065603165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6885005127597352043735443 10327507691396028065603165)
                    ·
                      refine ⟨3872815384273510524601187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10327507691396028065603165 3872815384273510524601187)
                      ·
                        rfl

theorem cell23_7542281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_7542281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542281 prefixEnd_7542281 := by exact prefixLift 7542281
  have htrace : WordTrace (prefixWord ++ tailWord_7542281) baseStart_7542281 baseEnd_7542281 := by
    simpa [prefixWord, tailWord_7542281, baseEnd_7542281] using wordTrace_append hprefix tailTrace_7542281
  have hstable : (prefixWord ++ tailWord_7542281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542281).length < 2 ^ (prefixWord ++ tailWord_7542281).sum := by decide
  have hdescent : baseEnd_7542281 < baseStart_7542281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542282 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_7542282 : Nat := 118140960795 + 7542282 * 2 ^ 59
def prefixEnd_7542282 : Nat := 4983230072969 + 3 ^ 40 * 7542282 * 2
def baseEnd_7542282 : Nat := 3872815897754165020688683

theorem tailTrace_7542282 : CollatzResearch.WordTrace tailWord_7542282 prefixEnd_7542282 3872815897754165020688683 := by
  unfold tailWord_7542282
  simp only [CollatzResearch.WordTrace]
  refine ⟨68772406015401977014575275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183393082707738605372200733 68772406015401977014575275)
  ·
    refine ⟨103158609023102965521862913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68772406015401977014575275 103158609023102965521862913)
    ·
      refine ⟨77368956767327224141397185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103158609023102965521862913 77368956767327224141397185)
      ·
        refine ⟨58026717575495418106047889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77368956767327224141397185 58026717575495418106047889)
        ·
          refine ⟨43520038181621563579535917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58026717575495418106047889 43520038181621563579535917)
          ·
            refine ⟨16320014318108086342325969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43520038181621563579535917 16320014318108086342325969)
            ·
              refine ⟨12240010738581064756744477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16320014318108086342325969 12240010738581064756744477)
              ·
                refine ⟨4590004026967899283779179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12240010738581064756744477 4590004026967899283779179)
                ·
                  refine ⟨6885006040451848925668769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590004026967899283779179 6885006040451848925668769)
                  ·
                    refine ⟨5163754530338886694251577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885006040451848925668769 5163754530338886694251577)
                    ·
                      refine ⟨3872815897754165020688683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163754530338886694251577 3872815897754165020688683)
                      ·
                        rfl

theorem cell23_7542282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_7542282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542282 prefixEnd_7542282 := by exact prefixLift 7542282
  have htrace : WordTrace (prefixWord ++ tailWord_7542282) baseStart_7542282 baseEnd_7542282 := by
    simpa [prefixWord, tailWord_7542282, baseEnd_7542282] using wordTrace_append hprefix tailTrace_7542282
  have hstable : (prefixWord ++ tailWord_7542282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542282).length < 2 ^ (prefixWord ++ tailWord_7542282).sum := by decide
  have hdescent : baseEnd_7542282 < baseStart_7542282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542292 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7542292 : Nat := 118140960795 + 7542292 * 2 ^ 59
def prefixEnd_7542292 : Nat := 4983230072969 + 3 ^ 40 * 7542292 * 2
def baseEnd_7542292 : Nat := 1290940344186903327187879

theorem tailTrace_7542292 : CollatzResearch.WordTrace tailWord_7542292 prefixEnd_7542292 1290940344186903327187879 := by
  unfold tailWord_7542292
  simp only [CollatzResearch.WordTrace]
  refine ⟨137544994395785839883082565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183393325861047786510776753 137544994395785839883082565)
  ·
    refine ⟨25789686449209844978077981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137544994395785839883082565 25789686449209844978077981)
    ·
      refine ⟨9671132418453691866779243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25789686449209844978077981 9671132418453691866779243)
      ·
        refine ⟨14506698627680537800168865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671132418453691866779243 14506698627680537800168865)
        ·
          refine ⟨10880023970760403350126649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14506698627680537800168865 10880023970760403350126649)
          ·
            refine ⟨8160017978070302512594987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10880023970760403350126649 8160017978070302512594987)
            ·
              refine ⟨12240026967105453768892481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160017978070302512594987 12240026967105453768892481)
              ·
                refine ⟨9180020225329090326669361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12240026967105453768892481 9180020225329090326669361)
                ·
                  refine ⟨6885015168996817745002021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180020225329090326669361 6885015168996817745002021)
                  ·
                    refine ⟨1290940344186903327187879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885015168996817745002021 1290940344186903327187879)
                    ·
                      rfl

theorem cell23_7542292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7542292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542292 prefixEnd_7542292 := by exact prefixLift 7542292
  have htrace : WordTrace (prefixWord ++ tailWord_7542292) baseStart_7542292 baseEnd_7542292 := by
    simpa [prefixWord, tailWord_7542292, baseEnd_7542292] using wordTrace_append hprefix tailTrace_7542292
  have hstable : (prefixWord ++ tailWord_7542292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542292).length < 2 ^ (prefixWord ++ tailWord_7542292).sum := by decide
  have hdescent : baseEnd_7542292 < baseStart_7542292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542302 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7542302 : Nat := 118140960795 + 7542302 * 2 ^ 59
def prefixEnd_7542302 : Nat := 4983230072969 + 3 ^ 40 * 7542302 * 2
def baseEnd_7542302 : Nat := 3872826167367254942438591

theorem tailTrace_7542302 : CollatzResearch.WordTrace tailWord_7542302 prefixEnd_7542302 3872826167367254942438591 := by
  unfold tailWord_7542302
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386294190191931434253645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183393569014356967649352773 34386294190191931434253645)
  ·
    refine ⟨12894860321321974287845117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34386294190191931434253645 12894860321321974287845117)
    ·
      refine ⟨4835572620495740357941919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12894860321321974287845117 4835572620495740357941919)
      ·
        refine ⟨7253358930743610536912879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835572620495740357941919 7253358930743610536912879)
        ·
          refine ⟨10880038396115415805369319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253358930743610536912879 10880038396115415805369319)
          ·
            refine ⟨16320057594173123708053979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880038396115415805369319 16320057594173123708053979)
            ·
              refine ⟨24480086391259685562080969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16320057594173123708053979 24480086391259685562080969)
              ·
                refine ⟨18360064793444764171560727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24480086391259685562080969 18360064793444764171560727)
                ·
                  refine ⟨27540097190167146257341091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18360064793444764171560727 27540097190167146257341091)
                  ·
                    refine ⟨41310145785250719386011637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27540097190167146257341091 41310145785250719386011637)
                    ·
                      refine ⟨3872826167367254942438591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41310145785250719386011637 3872826167367254942438591)
                      ·
                        rfl

theorem cell23_7542302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7542302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542302 prefixEnd_7542302 := by exact prefixLift 7542302
  have htrace : WordTrace (prefixWord ++ tailWord_7542302) baseStart_7542302 baseEnd_7542302 := by
    simpa [prefixWord, tailWord_7542302, baseEnd_7542302] using wordTrace_append hprefix tailTrace_7542302
  have hstable : (prefixWord ++ tailWord_7542302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542302).length < 2 ^ (prefixWord ++ tailWord_7542302).sum := by decide
  have hdescent : baseEnd_7542302 < baseStart_7542302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542325 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7542325 : Nat := 118140960795 + 7542325 * 2 ^ 59
def prefixEnd_7542325 : Nat := 4983230072969 + 3 ^ 40 * 7542325 * 2
def baseEnd_7542325 : Nat := 3872837977422308352450985

theorem tailTrace_7542325 : CollatzResearch.WordTrace tailWord_7542325 prefixEnd_7542325 3872837977422308352450985 := by
  unfold tailWord_7542325
  simp only [CollatzResearch.WordTrace]
  refine ⟨275091192400452126402116429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183394128266968084268077619 275091192400452126402116429)
  ·
    refine ⟨103159197150169547400793661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275091192400452126402116429 103159197150169547400793661)
    ·
      refine ⟨38684698931313580275297623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103159197150169547400793661 38684698931313580275297623)
      ·
        refine ⟨58027048396970370412946435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38684698931313580275297623 58027048396970370412946435)
        ·
          refine ⟨87040572595455555619419653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58027048396970370412946435 87040572595455555619419653)
          ·
            refine ⟨16320107361647916678641185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87040572595455555619419653 16320107361647916678641185)
            ·
              refine ⟨12240080521235937508980889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16320107361647916678641185 12240080521235937508980889)
              ·
                refine ⟨9180060390926953131735667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12240080521235937508980889 9180060390926953131735667)
                ·
                  refine ⟨13770090586390429697603501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180060390926953131735667 13770090586390429697603501)
                  ·
                    refine ⟨5163783969896411136601313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13770090586390429697603501 5163783969896411136601313)
                    ·
                      refine ⟨3872837977422308352450985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163783969896411136601313 3872837977422308352450985)
                      ·
                        rfl

theorem cell23_7542325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7542325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542325 prefixEnd_7542325 := by exact prefixLift 7542325
  have htrace : WordTrace (prefixWord ++ tailWord_7542325) baseStart_7542325 baseEnd_7542325 := by
    simpa [prefixWord, tailWord_7542325, baseEnd_7542325] using wordTrace_append hprefix tailTrace_7542325
  have hstable : (prefixWord ++ tailWord_7542325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542325).length < 2 ^ (prefixWord ++ tailWord_7542325).sum := by decide
  have hdescent : baseEnd_7542325 < baseStart_7542325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542361 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 5]
def baseStart_7542361 : Nat := 118140960795 + 7542361 * 2 ^ 59
def prefixEnd_7542361 : Nat := 4983230072969 + 3 ^ 40 * 7542361 * 2
def baseEnd_7542361 : Nat := 430317384747318912400091

theorem tailTrace_7542361 : CollatzResearch.WordTrace tailWord_7542361 prefixEnd_7542361 430317384747318912400091 := by
  unfold tailWord_7542361
  simp only [CollatzResearch.WordTrace]
  refine ⟨275092505428321704550426937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183395003618881136366951291 275092505428321704550426937)
  ·
    refine ⟨206319379071241278412820203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275092505428321704550426937 206319379071241278412820203)
    ·
      refine ⟨309479068606861917619230305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206319379071241278412820203 309479068606861917619230305)
      ·
        refine ⟨232109301455146438214422729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309479068606861917619230305 232109301455146438214422729)
        ·
          refine ⟨174081976091359828660817047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232109301455146438214422729 174081976091359828660817047)
          ·
            refine ⟨261122964137039742991225571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174081976091359828660817047 261122964137039742991225571)
            ·
              refine ⟨391684446205559614486838357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261122964137039742991225571 391684446205559614486838357)
              ·
                refine ⟨4590052103971401732267637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 391684446205559614486838357 4590052103971401732267637)
                ·
                  refine ⟨430317384747318912400091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590052103971401732267637 430317384747318912400091)
                  ·
                    rfl

theorem cell23_7542361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 5].length) (baseStart_7542361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542361 prefixEnd_7542361 := by exact prefixLift 7542361
  have htrace : WordTrace (prefixWord ++ tailWord_7542361) baseStart_7542361 baseEnd_7542361 := by
    simpa [prefixWord, tailWord_7542361, baseEnd_7542361] using wordTrace_append hprefix tailTrace_7542361
  have hstable : (prefixWord ++ tailWord_7542361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542361).length < 2 ^ (prefixWord ++ tailWord_7542361).sum := by decide
  have hdescent : baseEnd_7542361 < baseStart_7542361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542372 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_7542372 : Nat := 118140960795 + 7542372 * 2 ^ 59
def prefixEnd_7542372 : Nat := 4983230072969 + 3 ^ 40 * 7542372 * 2
def baseEnd_7542372 : Nat := 3872862111013069668563269

theorem tailTrace_7542372 : CollatzResearch.WordTrace tailWord_7542372 prefixEnd_7542372 3872862111013069668563269 := by
  unfold tailWord_7542372
  simp only [CollatzResearch.WordTrace]
  refine ⟨137546453315640926714538685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183395271087521235619384913 137546453315640926714538685)
  ·
    refine ⟨51579919993365347517952007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137546453315640926714538685 51579919993365347517952007)
    ·
      refine ⟨77369879990048021276928011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51579919993365347517952007 77369879990048021276928011)
      ·
        refine ⟨116054819985072031915392017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77369879990048021276928011 116054819985072031915392017)
        ·
          refine ⟨87041114988804023936544013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116054819985072031915392017 87041114988804023936544013)
          ·
            refine ⟨32640418120801508976204005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87041114988804023936544013 32640418120801508976204005)
            ·
              refine ⟨6120078397650282933038251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32640418120801508976204005 6120078397650282933038251)
              ·
                refine ⟨9180117596475424399557377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120078397650282933038251 9180117596475424399557377)
                ·
                  refine ⟨6885088197356568299668033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180117596475424399557377 6885088197356568299668033)
                  ·
                    refine ⟨5163816148017426224751025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885088197356568299668033 5163816148017426224751025)
                    ·
                      refine ⟨3872862111013069668563269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163816148017426224751025 3872862111013069668563269)
                      ·
                        rfl

theorem cell23_7542372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_7542372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542372 prefixEnd_7542372 := by exact prefixLift 7542372
  have htrace : WordTrace (prefixWord ++ tailWord_7542372) baseStart_7542372 baseEnd_7542372 := by
    simpa [prefixWord, tailWord_7542372, baseEnd_7542372] using wordTrace_append hprefix tailTrace_7542372
  have hstable : (prefixWord ++ tailWord_7542372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542372).length < 2 ^ (prefixWord ++ tailWord_7542372).sum := by decide
  have hdescent : baseEnd_7542372 < baseStart_7542372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542401 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7542401 : Nat := 118140960795 + 7542401 * 2 ^ 59
def prefixEnd_7542401 : Nat := 4983230072969 + 3 ^ 40 * 7542401 * 2
def baseEnd_7542401 : Nat := 3872877001952050055100635

theorem tailTrace_7542401 : CollatzResearch.WordTrace tailWord_7542401 prefixEnd_7542401 3872877001952050055100635 := by
  unfold tailWord_7542401
  simp only [CollatzResearch.WordTrace]
  refine ⟨275093964348176791381883057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183395976232117860921255371 275093964348176791381883057)
  ·
    refine ⟨206320473261132593536412293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275093964348176791381883057 206320473261132593536412293)
    ·
      refine ⟨38685088736462361288077305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206320473261132593536412293 38685088736462361288077305)
      ·
        refine ⟨29013816552346770966057979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38685088736462361288077305 29013816552346770966057979)
        ·
          refine ⟨43520724828520156449086969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29013816552346770966057979 43520724828520156449086969)
          ·
            refine ⟨32640543621390117336815227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43520724828520156449086969 32640543621390117336815227)
            ·
              refine ⟨48960815432085176005222841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32640543621390117336815227 48960815432085176005222841)
              ·
                refine ⟨36720611574063882003917131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48960815432085176005222841 36720611574063882003917131)
                ·
                  refine ⟨55080917361095823005875697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36720611574063882003917131 55080917361095823005875697)
                  ·
                    refine ⟨41310688020821867254406773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55080917361095823005875697 41310688020821867254406773)
                    ·
                      refine ⟨3872877001952050055100635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41310688020821867254406773 3872877001952050055100635)
                      ·
                        rfl

theorem cell23_7542401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7542401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542401 prefixEnd_7542401 := by exact prefixLift 7542401
  have htrace : WordTrace (prefixWord ++ tailWord_7542401) baseStart_7542401 baseEnd_7542401 := by
    simpa [prefixWord, tailWord_7542401, baseEnd_7542401] using wordTrace_append hprefix tailTrace_7542401
  have hstable : (prefixWord ++ tailWord_7542401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542401).length < 2 ^ (prefixWord ++ tailWord_7542401).sum := by decide
  have hdescent : baseEnd_7542401 < baseStart_7542401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542411 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4]
def baseStart_7542411 : Nat := 118140960795 + 7542411 * 2 ^ 59
def prefixEnd_7542411 : Nat := 4983230072969 + 3 ^ 40 * 7542411 * 2
def baseEnd_7542411 : Nat := 3872882136758595015975589

theorem tailTrace_7542411 : CollatzResearch.WordTrace tailWord_7542411 prefixEnd_7542411 3872882136758595015975589 := by
  unfold tailWord_7542411
  simp only [CollatzResearch.WordTrace]
  refine ⟨275094329078140563089747087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183396219385427042059831391 275094329078140563089747087)
  ·
    refine ⟨412641493617210844634620631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275094329078140563089747087 412641493617210844634620631)
    ·
      refine ⟨618962240425816266951930947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412641493617210844634620631 618962240425816266951930947)
      ·
        refine ⟨928443360638724400427896421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618962240425816266951930947 928443360638724400427896421)
        ·
          refine ⟨174083130119760825080230579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928443360638724400427896421 174083130119760825080230579)
          ·
            refine ⟨261124695179641237620345869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174083130119760825080230579 261124695179641237620345869)
            ·
              refine ⟨97921760692365464107629701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261124695179641237620345869 97921760692365464107629701)
              ·
                refine ⟨18360330129818524520180569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97921760692365464107629701 18360330129818524520180569)
                ·
                  refine ⟨13770247597363893390135427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18360330129818524520180569 13770247597363893390135427)
                  ·
                    refine ⟨20655371396045840085203141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13770247597363893390135427 20655371396045840085203141)
                    ·
                      refine ⟨3872882136758595015975589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20655371396045840085203141 3872882136758595015975589)
                      ·
                        rfl

theorem cell23_7542411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_7542411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542411 prefixEnd_7542411 := by exact prefixLift 7542411
  have htrace : WordTrace (prefixWord ++ tailWord_7542411) baseStart_7542411 baseEnd_7542411 := by
    simpa [prefixWord, tailWord_7542411, baseEnd_7542411] using wordTrace_append hprefix tailTrace_7542411
  have hstable : (prefixWord ++ tailWord_7542411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542411).length < 2 ^ (prefixWord ++ tailWord_7542411).sum := by decide
  have hdescent : baseEnd_7542411 < baseStart_7542411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542421 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7542421 : Nat := 118140960795 + 7542421 * 2 ^ 59
def prefixEnd_7542421 : Nat := 4983230072969 + 3 ^ 40 * 7542421 * 2
def baseEnd_7542421 : Nat := 1290962423855046658950181

theorem tailTrace_7542421 : CollatzResearch.WordTrace tailWord_7542421 prefixEnd_7542421 1290962423855046658950181 := by
  unfold tailWord_7542421
  simp only [CollatzResearch.WordTrace]
  refine ⟨275094693808104334797611117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183396462538736223198407411 275094693808104334797611117)
  ·
    refine ⟨103160510178039125549104169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275094693808104334797611117 103160510178039125549104169)
    ·
      refine ⟨77370382633529344161828127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103160510178039125549104169 77370382633529344161828127)
      ·
        refine ⟨116055573950294016242742191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77370382633529344161828127 116055573950294016242742191)
        ·
          refine ⟨174083360925441024364113287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116055573950294016242742191 174083360925441024364113287)
          ·
            refine ⟨261125041388161536546169931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174083360925441024364113287 261125041388161536546169931)
            ·
              refine ⟨391687562082242304819254897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261125041388161536546169931 391687562082242304819254897)
              ·
                refine ⟨293765671561681728614441173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391687562082242304819254897 293765671561681728614441173)
                ·
                  refine ⟨6885132927226915514400965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293765671561681728614441173 6885132927226915514400965)
                  ·
                    refine ⟨1290962423855046658950181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885132927226915514400965 1290962423855046658950181)
                    ·
                      rfl

theorem cell23_7542421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7542421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542421 prefixEnd_7542421 := by exact prefixLift 7542421
  have htrace : WordTrace (prefixWord ++ tailWord_7542421) baseStart_7542421 baseEnd_7542421 := by
    simpa [prefixWord, tailWord_7542421, baseEnd_7542421] using wordTrace_append hprefix tailTrace_7542421
  have hstable : (prefixWord ++ tailWord_7542421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542421).length < 2 ^ (prefixWord ++ tailWord_7542421).sum := by decide
  have hdescent : baseEnd_7542421 < baseStart_7542421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542448 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_7542448 : Nat := 118140960795 + 7542448 * 2 ^ 59
def prefixEnd_7542448 : Nat := 4983230072969 + 3 ^ 40 * 7542448 * 2
def baseEnd_7542448 : Nat := 3872901135542811371212919

theorem tailTrace_7542448 : CollatzResearch.WordTrace tailWord_7542448 prefixEnd_7542448 3872901135542811371212919 := by
  unfold tailWord_7542448
  simp only [CollatzResearch.WordTrace]
  refine ⟨137547839289503259204421999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183397119052671012272562665 137547839289503259204421999)
  ·
    refine ⟨206321758934254888806632999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137547839289503259204421999 206321758934254888806632999)
    ·
      refine ⟨309482638401382333209949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206321758934254888806632999 309482638401382333209949499)
      ·
        refine ⟨464223957602073499814924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309482638401382333209949499 464223957602073499814924249)
        ·
          refine ⟨348167968201555124861193187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464223957602073499814924249 348167968201555124861193187)
          ·
            refine ⟨522251952302332687291789781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348167968201555124861193187 522251952302332687291789781)
            ·
              refine ⟨12240280132085922358401323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 522251952302332687291789781 12240280132085922358401323)
              ·
                refine ⟨18360420198128883537601985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240280132085922358401323 18360420198128883537601985)
                ·
                  refine ⟨13770315148596662653201489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18360420198128883537601985 13770315148596662653201489)
                  ·
                    refine ⟨10327736361447496989901117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13770315148596662653201489 10327736361447496989901117)
                    ·
                      refine ⟨3872901135542811371212919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10327736361447496989901117 3872901135542811371212919)
                      ·
                        rfl

theorem cell23_7542448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_7542448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542448 prefixEnd_7542448 := by exact prefixLift 7542448
  have htrace : WordTrace (prefixWord ++ tailWord_7542448) baseStart_7542448 baseEnd_7542448 := by
    simpa [prefixWord, tailWord_7542448, baseEnd_7542448] using wordTrace_append hprefix tailTrace_7542448
  have hstable : (prefixWord ++ tailWord_7542448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542448).length < 2 ^ (prefixWord ++ tailWord_7542448).sum := by decide
  have hdescent : baseEnd_7542448 < baseStart_7542448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542455 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 1, 4]
def baseStart_7542455 : Nat := 118140960795 + 7542455 * 2 ^ 59
def prefixEnd_7542455 : Nat := 4983230072969 + 3 ^ 40 * 7542455 * 2
def baseEnd_7542455 : Nat := 1290968243302464281275129

theorem tailTrace_7542455 : CollatzResearch.WordTrace tailWord_7542455 prefixEnd_7542455 1290968243302464281275129 := by
  unfold tailWord_7542455
  simp only [CollatzResearch.WordTrace]
  refine ⟨275095933889981158604348819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183397289259987439069565879 275095933889981158604348819)
  ·
    refine ⟨412643900834971737906523229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275095933889981158604348819 412643900834971737906523229)
    ·
      refine ⟨154741462813114401714946211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412643900834971737906523229 154741462813114401714946211)
      ·
        refine ⟨232112194219671602572419317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154741462813114401714946211 232112194219671602572419317)
        ·
          refine ⟨21760518208094212741164311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232112194219671602572419317 21760518208094212741164311)
          ·
            refine ⟨32640777312141319111746467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21760518208094212741164311 32640777312141319111746467)
            ·
              refine ⟨48961165968211978667619701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32640777312141319111746467 48961165968211978667619701)
              ·
                refine ⟨4590109309519873000089347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48961165968211978667619701 4590109309519873000089347)
                ·
                  refine ⟨6885163964279809500134021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590109309519873000089347 6885163964279809500134021)
                  ·
                    refine ⟨1290968243302464281275129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885163964279809500134021 1290968243302464281275129)
                    ·
                      rfl

theorem cell23_7542455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_7542455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542455 prefixEnd_7542455 := by exact prefixLift 7542455
  have htrace : WordTrace (prefixWord ++ tailWord_7542455) baseStart_7542455 baseEnd_7542455 := by
    simpa [prefixWord, tailWord_7542455, baseEnd_7542455] using wordTrace_append hprefix tailTrace_7542455
  have hstable : (prefixWord ++ tailWord_7542455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542455).length < 2 ^ (prefixWord ++ tailWord_7542455).sum := by decide
  have hdescent : baseEnd_7542455 < baseStart_7542455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542488 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_7542488 : Nat := 118140960795 + 7542488 * 2 ^ 59
def prefixEnd_7542488 : Nat := 4983230072969 + 3 ^ 40 * 7542488 * 2
def baseEnd_7542488 : Nat := 3872921674768991214712735

theorem tailTrace_7542488 : CollatzResearch.WordTrace tailWord_7542488 prefixEnd_7542488 3872921674768991214712735 := by
  unfold tailWord_7542488
  simp only [CollatzResearch.WordTrace]
  refine ⟨137548568749430802620150059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183398091665907736826866745 137548568749430802620150059)
  ·
    refine ⟨206322853124146203930225089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137548568749430802620150059 206322853124146203930225089)
    ·
      refine ⟨154742139843109652947668817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206322853124146203930225089 154742139843109652947668817)
      ·
        refine ⟨116056604882332239710751613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154742139843109652947668817 116056604882332239710751613)
        ·
          refine ⟨43521226830874589891531855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116056604882332239710751613 43521226830874589891531855)
          ·
            refine ⟨65281840246311884837297783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43521226830874589891531855 65281840246311884837297783)
            ·
              refine ⟨97922760369467827255946675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65281840246311884837297783 97922760369467827255946675)
              ·
                refine ⟨146884140554201740883920013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97922760369467827255946675 146884140554201740883920013)
                ·
                  refine ⟨55081552707825652831470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146884140554201740883920013 55081552707825652831470005)
                  ·
                    refine ⟨5163895566358654952950313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55081552707825652831470005 5163895566358654952950313)
                    ·
                      refine ⟨3872921674768991214712735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163895566358654952950313 3872921674768991214712735)
                      ·
                        rfl

theorem cell23_7542488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_7542488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542488 prefixEnd_7542488 := by exact prefixLift 7542488
  have htrace : WordTrace (prefixWord ++ tailWord_7542488) baseStart_7542488 baseEnd_7542488 := by
    simpa [prefixWord, tailWord_7542488, baseEnd_7542488] using wordTrace_append hprefix tailTrace_7542488
  have hstable : (prefixWord ++ tailWord_7542488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542488).length < 2 ^ (prefixWord ++ tailWord_7542488).sum := by decide
  have hdescent : baseEnd_7542488 < baseStart_7542488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542511 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 6]
def baseStart_7542511 : Nat := 118140960795 + 7542511 * 2 ^ 59
def prefixEnd_7542511 : Nat := 4983230072969 + 3 ^ 40 * 7542511 * 2
def baseEnd_7542511 : Nat := 1290977828274681541575043

theorem tailTrace_7542511 : CollatzResearch.WordTrace tailWord_7542511 prefixEnd_7542511 1290977828274681541575043 := by
  unfold tailWord_7542511
  simp only [CollatzResearch.WordTrace]
  refine ⟨275097976377778280168387387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183398650918518853445591591 275097976377778280168387387)
  ·
    refine ⟨412646964566667420252581081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275097976377778280168387387 412646964566667420252581081)
    ·
      refine ⟨309485223425000565189435811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412646964566667420252581081 309485223425000565189435811)
      ·
        refine ⟨464227835137500847784153717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309485223425000565189435811 464227835137500847784153717)
        ·
          refine ⟨43521359544140704479764411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464227835137500847784153717 43521359544140704479764411)
          ·
            refine ⟨65282039316211056719646617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43521359544140704479764411 65282039316211056719646617)
            ·
              refine ⟨48961529487158292539734963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65282039316211056719646617 48961529487158292539734963)
              ·
                refine ⟨73442294230737438809602445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48961529487158292539734963 73442294230737438809602445)
                ·
                  refine ⟨27540860336526539553600917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73442294230737438809602445 27540860336526539553600917)
                  ·
                    refine ⟨1290977828274681541575043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27540860336526539553600917 1290977828274681541575043)
                    ·
                      rfl

theorem cell23_7542511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_7542511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542511 prefixEnd_7542511 := by exact prefixLift 7542511
  have htrace : WordTrace (prefixWord ++ tailWord_7542511) baseStart_7542511 baseEnd_7542511 := by
    simpa [prefixWord, tailWord_7542511, baseEnd_7542511] using wordTrace_append hprefix tailTrace_7542511
  have hstable : (prefixWord ++ tailWord_7542511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542511).length < 2 ^ (prefixWord ++ tailWord_7542511).sum := by decide
  have hdescent : baseEnd_7542511 < baseStart_7542511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542531 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_7542531 : Nat := 118140960795 + 7542531 * 2 ^ 59
def prefixEnd_7542531 : Nat := 4983230072969 + 3 ^ 40 * 7542531 * 2
def baseEnd_7542531 : Nat := 3872943754437134546475037

theorem tailTrace_7542531 : CollatzResearch.WordTrace tailWord_7542531 prefixEnd_7542531 3872943754437134546475037 := by
  unfold tailWord_7542531
  simp only [CollatzResearch.WordTrace]
  refine ⟨275098705837705823584115447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183399137225137215722743631 275098705837705823584115447)
  ·
    refine ⟨412648058756558735376173171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275098705837705823584115447 412648058756558735376173171)
    ·
      refine ⟨618972088134838103064259757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412648058756558735376173171 618972088134838103064259757)
      ·
        refine ⟨232114533050564288649097409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618972088134838103064259757 232114533050564288649097409)
        ·
          refine ⟨174085899787923216486823057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232114533050564288649097409 174085899787923216486823057)
          ·
            refine ⟨130564424840942412365117293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174085899787923216486823057 130564424840942412365117293)
            ·
              refine ⟨48961659315353404636918985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130564424840942412365117293 48961659315353404636918985)
              ·
                refine ⟨36721244486515053477689239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48961659315353404636918985 36721244486515053477689239)
                ·
                  refine ⟨55081866729772580216533859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36721244486515053477689239 55081866729772580216533859)
                  ·
                    refine ⟨82622800094658870324800789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55081866729772580216533859 82622800094658870324800789)
                    ·
                      refine ⟨3872943754437134546475037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82622800094658870324800789 3872943754437134546475037)
                      ·
                        rfl

theorem cell23_7542531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_7542531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542531 prefixEnd_7542531 := by exact prefixLift 7542531
  have htrace : WordTrace (prefixWord ++ tailWord_7542531) baseStart_7542531 baseEnd_7542531 := by
    simpa [prefixWord, tailWord_7542531, baseEnd_7542531] using wordTrace_append hprefix tailTrace_7542531
  have hstable : (prefixWord ++ tailWord_7542531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542531).length < 2 ^ (prefixWord ++ tailWord_7542531).sum := by decide
  have hdescent : baseEnd_7542531 < baseStart_7542531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542538 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_7542538 : Nat := 118140960795 + 7542538 * 2 ^ 59
def prefixEnd_7542538 : Nat := 4983230072969 + 3 ^ 40 * 7542538 * 2
def baseEnd_7542538 : Nat := 3872947348801716019087505

theorem tailTrace_7542538 : CollatzResearch.WordTrace tailWord_7542538 prefixEnd_7542538 3872947348801716019087505 := by
  unfold tailWord_7542538
  simp only [CollatzResearch.WordTrace]
  refine ⟨68774740287170115944905067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183399307432453642519746845 68774740287170115944905067)
  ·
    refine ⟨103162110430755173917357601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68774740287170115944905067 103162110430755173917357601)
    ·
      refine ⟨77371582823066380438018201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103162110430755173917357601 77371582823066380438018201)
      ·
        refine ⟨58028687117299785328513651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77371582823066380438018201 58028687117299785328513651)
        ·
          refine ⟨87043030675949677992770477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58028687117299785328513651 87043030675949677992770477)
          ·
            refine ⟨32641136503481129247288929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87043030675949677992770477 32641136503481129247288929)
            ·
              refine ⟨24480852377610846935466697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32641136503481129247288929 24480852377610846935466697)
              ·
                refine ⟨18360639283208135201600023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24480852377610846935466697 18360639283208135201600023)
                ·
                  refine ⟨27540958924812202802400035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18360639283208135201600023 27540958924812202802400035)
                  ·
                    refine ⟨41311438387218304203600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27540958924812202802400035 41311438387218304203600053)
                    ·
                      refine ⟨3872947348801716019087505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41311438387218304203600053 3872947348801716019087505)
                      ·
                        rfl

theorem cell23_7542538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_7542538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542538 prefixEnd_7542538 := by exact prefixLift 7542538
  have htrace : WordTrace (prefixWord ++ tailWord_7542538) baseStart_7542538 baseEnd_7542538 := by
    simpa [prefixWord, tailWord_7542538, baseEnd_7542538] using wordTrace_append hprefix tailTrace_7542538
  have hstable : (prefixWord ++ tailWord_7542538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542538).length < 2 ^ (prefixWord ++ tailWord_7542538).sum := by decide
  have hdescent : baseEnd_7542538 < baseStart_7542538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542572 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_7542572 : Nat := 118140960795 + 7542572 * 2 ^ 59
def prefixEnd_7542572 : Nat := 4983230072969 + 3 ^ 40 * 7542572 * 2
def baseEnd_7542572 : Nat := 3872964807143968886062349

theorem tailTrace_7542572 : CollatzResearch.WordTrace tailWord_7542572 prefixEnd_7542572 3872964807143968886062349 := by
  unfold tailWord_7542572
  simp only [CollatzResearch.WordTrace]
  refine ⟨137550100615278643793178985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183400134153704858390905313 137550100615278643793178985)
  ·
    refine ⟨103162575461458982844884239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137550100615278643793178985 103162575461458982844884239)
    ·
      refine ⟨154743863192188474267326359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103162575461458982844884239 154743863192188474267326359)
      ·
        refine ⟨232115794788282711400989539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154743863192188474267326359 232115794788282711400989539)
        ·
          refine ⟨348173692182424067101484309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232115794788282711400989539 348173692182424067101484309)
          ·
            refine ⟨16320641821051128145382077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348173692182424067101484309 16320641821051128145382077)
            ·
              refine ⟨6120240682894173054518279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16320641821051128145382077 6120240682894173054518279)
              ·
                refine ⟨9180361024341259581777419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120240682894173054518279 9180361024341259581777419)
                ·
                  refine ⟨13770541536511889372666129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180361024341259581777419 13770541536511889372666129)
                  ·
                    refine ⟨10327906152383917029499597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13770541536511889372666129 10327906152383917029499597)
                    ·
                      refine ⟨3872964807143968886062349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10327906152383917029499597 3872964807143968886062349)
                      ·
                        rfl

theorem cell23_7542572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_7542572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542572 prefixEnd_7542572 := by exact prefixLift 7542572
  have htrace : WordTrace (prefixWord ++ tailWord_7542572) baseStart_7542572 baseEnd_7542572 := by
    simpa [prefixWord, tailWord_7542572, baseEnd_7542572] using wordTrace_append hprefix tailTrace_7542572
  have hstable : (prefixWord ++ tailWord_7542572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542572).length < 2 ^ (prefixWord ++ tailWord_7542572).sum := by decide
  have hdescent : baseEnd_7542572 < baseStart_7542572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542586 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2]
def baseStart_7542586 : Nat := 118140960795 + 7542586 * 2 ^ 59
def prefixEnd_7542586 : Nat := 4983230072969 + 3 ^ 40 * 7542586 * 2
def baseEnd_7542586 : Nat := 3872971995873131831287285

theorem tailTrace_7542586 : CollatzResearch.WordTrace tailWord_7542586 prefixEnd_7542586 3872971995873131831287285 := by
  unfold tailWord_7542586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68775177963126641994341903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183400474568337711984911741 68775177963126641994341903)
  ·
    refine ⟨103162766944689962991512855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68775177963126641994341903 103162766944689962991512855)
    ·
      refine ⟨154744150417034944487269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103162766944689962991512855 154744150417034944487269283)
      ·
        refine ⟨232116225625552416730903925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154744150417034944487269283 232116225625552416730903925)
        ·
          refine ⟨21760896152395539068522243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232116225625552416730903925 21760896152395539068522243)
          ·
            refine ⟨32641344228593308602783365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21760896152395539068522243 32641344228593308602783365)
            ·
              refine ⟨6120252042861245363021881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32641344228593308602783365 6120252042861245363021881)
              ·
                refine ⟨4590189032145934022266411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120252042861245363021881 4590189032145934022266411)
                ·
                  refine ⟨6885283548218901033399617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590189032145934022266411 6885283548218901033399617)
                  ·
                    refine ⟨5163962661164175775049713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885283548218901033399617 5163962661164175775049713)
                    ·
                      refine ⟨3872971995873131831287285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163962661164175775049713 3872971995873131831287285)
                      ·
                        rfl

theorem cell23_7542586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_7542586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542586 prefixEnd_7542586 := by exact prefixLift 7542586
  have htrace : WordTrace (prefixWord ++ tailWord_7542586) baseStart_7542586 baseEnd_7542586 := by
    simpa [prefixWord, tailWord_7542586, baseEnd_7542586] using wordTrace_append hprefix tailTrace_7542586
  have hstable : (prefixWord ++ tailWord_7542586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542586).length < 2 ^ (prefixWord ++ tailWord_7542586).sum := by decide
  have hdescent : baseEnd_7542586 < baseStart_7542586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542595 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 3, 3, 2]
def baseStart_7542595 : Nat := 118140960795 + 7542595 * 2 ^ 59
def prefixEnd_7542595 : Nat := 4983230072969 + 3 ^ 40 * 7542595 * 2
def baseEnd_7542595 : Nat := 3872976617199022296074743

theorem tailTrace_7542595 : CollatzResearch.WordTrace tailWord_7542595 prefixEnd_7542595 3872976617199022296074743 := by
  unfold tailWord_7542595
  simp only [CollatzResearch.WordTrace]
  refine ⟨275101040109473962514445239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183400693406315975009630159 275101040109473962514445239)
  ·
    refine ⟨412651560164210943771667859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275101040109473962514445239 412651560164210943771667859)
    ·
      refine ⟨618977340246316415657501789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412651560164210943771667859 618977340246316415657501789)
      ·
        refine ⟨232116502592368655871563171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618977340246316415657501789 232116502592368655871563171)
        ·
          refine ⟨348174753888552983807344757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232116502592368655871563171 348174753888552983807344757)
          ·
            refine ⟨32641383177051842231938571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348174753888552983807344757 32641383177051842231938571)
            ·
              refine ⟨48962074765577763347907857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32641383177051842231938571 48962074765577763347907857)
              ·
                refine ⟨36721556074183322510930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48962074765577763347907857 36721556074183322510930893)
                ·
                  refine ⟨13770583527818745941599085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36721556074183322510930893 13770583527818745941599085)
                  ·
                    refine ⟨5163968822932029728099657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13770583527818745941599085 5163968822932029728099657)
                    ·
                      refine ⟨3872976617199022296074743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163968822932029728099657 3872976617199022296074743)
                      ·
                        rfl

theorem cell23_7542595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_7542595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542595 prefixEnd_7542595 := by exact prefixLift 7542595
  have htrace : WordTrace (prefixWord ++ tailWord_7542595) baseStart_7542595 baseEnd_7542595 := by
    simpa [prefixWord, tailWord_7542595, baseEnd_7542595] using wordTrace_append hprefix tailTrace_7542595
  have hstable : (prefixWord ++ tailWord_7542595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542595).length < 2 ^ (prefixWord ++ tailWord_7542595).sum := by decide
  have hdescent : baseEnd_7542595 < baseStart_7542595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542612 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_7542612 : Nat := 118140960795 + 7542612 * 2 ^ 59
def prefixEnd_7542612 : Nat := 4983230072969 + 3 ^ 40 * 7542612 * 2
def baseEnd_7542612 : Nat := 3872985346370148729562165

theorem tailTrace_7542612 : CollatzResearch.WordTrace tailWord_7542612 prefixEnd_7542612 3872985346370148729562165 := by
  unfold tailWord_7542612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137550830075206187208907045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183401106766941582945209393 137550830075206187208907045)
  ·
    refine ⟨25790780639101160101670071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137550830075206187208907045 25790780639101160101670071)
    ·
      refine ⟨38686170958651740152505107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25790780639101160101670071 38686170958651740152505107)
      ·
        refine ⟨58029256437977610228757661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38686170958651740152505107 58029256437977610228757661)
        ·
          refine ⟨21760971164241603835784123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58029256437977610228757661 21760971164241603835784123)
          ·
            refine ⟨32641456746362405753676185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21760971164241603835784123 32641456746362405753676185)
            ·
              refine ⟨24481092559771804315257139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32641456746362405753676185 24481092559771804315257139)
              ·
                refine ⟨36721638839657706472885709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24481092559771804315257139 36721638839657706472885709)
                ·
                  refine ⟨13770614564871639927332141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36721638839657706472885709 13770614564871639927332141)
                  ·
                    refine ⟨5163980461826864972749553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13770614564871639927332141 5163980461826864972749553)
                    ·
                      refine ⟨3872985346370148729562165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163980461826864972749553 3872985346370148729562165)
                      ·
                        rfl

theorem cell23_7542612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_7542612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542612 prefixEnd_7542612 := by exact prefixLift 7542612
  have htrace : WordTrace (prefixWord ++ tailWord_7542612) baseStart_7542612 baseEnd_7542612 := by
    simpa [prefixWord, tailWord_7542612, baseEnd_7542612] using wordTrace_append hprefix tailTrace_7542612
  have hstable : (prefixWord ++ tailWord_7542612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542612).length < 2 ^ (prefixWord ++ tailWord_7542612).sum := by decide
  have hdescent : baseEnd_7542612 < baseStart_7542612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542625 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_7542625 : Nat := 118140960795 + 7542625 * 2 ^ 59
def prefixEnd_7542625 : Nat := 4983230072969 + 3 ^ 40 * 7542625 * 2
def baseEnd_7542625 : Nat := 3872992021618657178699605

theorem tailTrace_7542625 : CollatzResearch.WordTrace tailWord_7542625 prefixEnd_7542625 3872992021618657178699605 := by
  unfold tailWord_7542625
  simp only [CollatzResearch.WordTrace]
  refine ⟨275102134299365277638037329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183401422866243518425358219 275102134299365277638037329)
  ·
    refine ⟨206326600724523958228527997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275102134299365277638037329 206326600724523958228527997)
    ·
      refine ⟨77372475271696484335697999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206326600724523958228527997 77372475271696484335697999)
      ·
        refine ⟨116058712907544726503546999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77372475271696484335697999 116058712907544726503546999)
        ·
          refine ⟨174088069361317089755320499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116058712907544726503546999 174088069361317089755320499)
          ·
            refine ⟨261132104041975634632980749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174088069361317089755320499 261132104041975634632980749)
            ·
              refine ⟨97924539015740862987367781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261132104041975634632980749 97924539015740862987367781)
              ·
                refine ⟨18360851065451411810131459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97924539015740862987367781 18360851065451411810131459)
                ·
                  refine ⟨27541276598177117715197189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18360851065451411810131459 27541276598177117715197189)
                  ·
                    refine ⟨5163989362158209571599473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27541276598177117715197189 5163989362158209571599473)
                    ·
                      refine ⟨3872992021618657178699605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163989362158209571599473 3872992021618657178699605)
                      ·
                        rfl

theorem cell23_7542625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_7542625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542625 prefixEnd_7542625 := by exact prefixLift 7542625
  have htrace : WordTrace (prefixWord ++ tailWord_7542625) baseStart_7542625 baseEnd_7542625 := by
    simpa [prefixWord, tailWord_7542625, baseEnd_7542625] using wordTrace_append hprefix tailTrace_7542625
  have hstable : (prefixWord ++ tailWord_7542625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542625).length < 2 ^ (prefixWord ++ tailWord_7542625).sum := by decide
  have hdescent : baseEnd_7542625 < baseStart_7542625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542682 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_7542682 : Nat := 118140960795 + 7542682 * 2 ^ 59
def prefixEnd_7542682 : Nat := 4983230072969 + 3 ^ 40 * 7542682 * 2
def baseEnd_7542682 : Nat := 430335698890662606187427

theorem tailTrace_7542682 : CollatzResearch.WordTrace tailWord_7542682 prefixEnd_7542682 430335698890662606187427 := by
  unfold tailWord_7542682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68776053315039694093215575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183402808840105850915241533 68776053315039694093215575)
  ·
    refine ⟨103164079972559541139823363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68776053315039694093215575 103164079972559541139823363)
    ·
      refine ⟨154746119958839311709735045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103164079972559541139823363 154746119958839311709735045)
      ·
        refine ⟨29014897492282370945575321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154746119958839311709735045 29014897492282370945575321)
        ·
          refine ⟨21761173119211778209181491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29014897492282370945575321 21761173119211778209181491)
          ·
            refine ⟨32641759678817667313772237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21761173119211778209181491 32641759678817667313772237)
            ·
              refine ⟨12240659879556625242664589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32641759678817667313772237 12240659879556625242664589)
              ·
                refine ⟨4590247454833734465999221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12240659879556625242664589 4590247454833734465999221)
                ·
                  refine ⟨430335698890662606187427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590247454833734465999221 430335698890662606187427)
                  ·
                    rfl

theorem cell23_7542682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_7542682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542682 prefixEnd_7542682 := by exact prefixLift 7542682
  have htrace : WordTrace (prefixWord ++ tailWord_7542682) baseStart_7542682 baseEnd_7542682 := by
    simpa [prefixWord, tailWord_7542682, baseEnd_7542682] using wordTrace_append hprefix tailTrace_7542682
  have hstable : (prefixWord ++ tailWord_7542682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542682).length < 2 ^ (prefixWord ++ tailWord_7542682).sum := by decide
  have hdescent : baseEnd_7542682 < baseStart_7542682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542688 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_7542688 : Nat := 118140960795 + 7542688 * 2 ^ 59
def prefixEnd_7542688 : Nat := 4983230072969 + 3 ^ 40 * 7542688 * 2
def baseEnd_7542688 : Nat := 3873024370899890432211815

theorem tailTrace_7542688 : CollatzResearch.WordTrace tailWord_7542688 prefixEnd_7542688 3873024370899890432211815 := by
  unfold tailWord_7542688
  simp only [CollatzResearch.WordTrace]
  refine ⟨137552216049068519698790359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183402954732091359598387145 137552216049068519698790359)
  ·
    refine ⟨206328324073602779548185539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137552216049068519698790359 206328324073602779548185539)
    ·
      refine ⟨309492486110404169322278309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206328324073602779548185539 309492486110404169322278309)
      ·
        refine ⟨58029841145700781747927183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309492486110404169322278309 58029841145700781747927183)
        ·
          refine ⟨87044761718551172621890775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58029841145700781747927183 87044761718551172621890775)
          ·
            refine ⟨130567142577826758932836163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87044761718551172621890775 130567142577826758932836163)
            ·
              refine ⟨195850713866740138399254245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130567142577826758932836163 195850713866740138399254245)
              ·
                refine ⟨36722008850013775949860171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195850713866740138399254245 36722008850013775949860171)
                ·
                  refine ⟨55083013275020663924790257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36722008850013775949860171 55083013275020663924790257)
                  ·
                    refine ⟨41312259956265497943592693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55083013275020663924790257 41312259956265497943592693)
                    ·
                      refine ⟨3873024370899890432211815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41312259956265497943592693 3873024370899890432211815)
                      ·
                        rfl

theorem cell23_7542688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_7542688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542688 prefixEnd_7542688 := by exact prefixLift 7542688
  have htrace : WordTrace (prefixWord ++ tailWord_7542688) baseStart_7542688 baseEnd_7542688 := by
    simpa [prefixWord, tailWord_7542688, baseEnd_7542688] using wordTrace_append hprefix tailTrace_7542688
  have hstable : (prefixWord ++ tailWord_7542688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542688).length < 2 ^ (prefixWord ++ tailWord_7542688).sum := by decide
  have hdescent : baseEnd_7542688 < baseStart_7542688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542695 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7542695 : Nat := 118140960795 + 7542695 * 2 ^ 59
def prefixEnd_7542695 : Nat := 4983230072969 + 3 ^ 40 * 7542695 * 2
def baseEnd_7542695 : Nat := 1291009321754823968274761

theorem tailTrace_7542695 : CollatzResearch.WordTrace tailWord_7542695 prefixEnd_7542695 1291009321754823968274761 := by
  unfold tailWord_7542695
  simp only [CollatzResearch.WordTrace]
  refine ⟨275104687409111679593085539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183403124939407786395390359 275104687409111679593085539)
  ·
    refine ⟨412657031113667519389628309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275104687409111679593085539 412657031113667519389628309)
    ·
      refine ⟨19343298333453164971388827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 412657031113667519389628309 19343298333453164971388827)
      ·
        refine ⟨29014947500179747457083241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19343298333453164971388827 29014947500179747457083241)
        ·
          refine ⟨21761210625134810592812431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29014947500179747457083241 21761210625134810592812431)
          ·
            refine ⟨32641815937702215889218647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21761210625134810592812431 32641815937702215889218647)
            ·
              refine ⟨48962723906553323833827971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32641815937702215889218647 48962723906553323833827971)
              ·
                refine ⟨73444085859829985750741957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48962723906553323833827971 73444085859829985750741957)
                ·
                  refine ⟨13770766098718122328264117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73444085859829985750741957 13770766098718122328264117)
                  ·
                    refine ⟨1291009321754823968274761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13770766098718122328264117 1291009321754823968274761)
                    ·
                      rfl

theorem cell23_7542695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7542695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542695 prefixEnd_7542695 := by exact prefixLift 7542695
  have htrace : WordTrace (prefixWord ++ tailWord_7542695) baseStart_7542695 baseEnd_7542695 := by
    simpa [prefixWord, tailWord_7542695, baseEnd_7542695] using wordTrace_append hprefix tailTrace_7542695
  have hstable : (prefixWord ++ tailWord_7542695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542695).length < 2 ^ (prefixWord ++ tailWord_7542695).sum := by decide
  have hdescent : baseEnd_7542695 < baseStart_7542695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542705 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7542705 : Nat := 118140960795 + 7542705 * 2 ^ 59
def prefixEnd_7542705 : Nat := 4983230072969 + 3 ^ 40 * 7542705 * 2
def baseEnd_7542705 : Nat := 3873033100071016865699237

theorem tailTrace_7542705 : CollatzResearch.WordTrace tailWord_7542705 prefixEnd_7542705 3873033100071016865699237 := by
  unfold tailWord_7542705
  simp only [CollatzResearch.WordTrace]
  refine ⟨275105052139075451300949569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183403368092716967533966379 275105052139075451300949569)
  ·
    refine ⟨206328789104306588475712177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275105052139075451300949569 206328789104306588475712177)
    ·
      refine ⟨154746591828229941356784133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206328789104306588475712177 154746591828229941356784133)
      ·
        refine ⟨29014985967793114004397025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154746591828229941356784133 29014985967793114004397025)
        ·
          refine ⟨21761239475844835503297769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29014985967793114004397025 21761239475844835503297769)
          ·
            refine ⟨16320929606883626627473327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21761239475844835503297769 16320929606883626627473327)
            ·
              refine ⟨24481394410325439941209991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16320929606883626627473327 24481394410325439941209991)
              ·
                refine ⟨36722091615488159911814987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24481394410325439941209991 36722091615488159911814987)
                ·
                  refine ⟨55083137423232239867722481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36722091615488159911814987 55083137423232239867722481)
                  ·
                    refine ⟨41312353067424179900791861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55083137423232239867722481 41312353067424179900791861)
                    ·
                      refine ⟨3873033100071016865699237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41312353067424179900791861 3873033100071016865699237)
                      ·
                        rfl

theorem cell23_7542705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7542705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542705 prefixEnd_7542705 := by exact prefixLift 7542705
  have htrace : WordTrace (prefixWord ++ tailWord_7542705) baseStart_7542705 baseEnd_7542705 := by
    simpa [prefixWord, tailWord_7542705, baseEnd_7542705] using wordTrace_append hprefix tailTrace_7542705
  have hstable : (prefixWord ++ tailWord_7542705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542705).length < 2 ^ (prefixWord ++ tailWord_7542705).sum := by decide
  have hdescent : baseEnd_7542705 < baseStart_7542705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542732 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7542732 : Nat := 118140960795 + 7542732 * 2 ^ 59
def prefixEnd_7542732 : Nat := 4983230072969 + 3 ^ 40 * 7542732 * 2
def baseEnd_7542732 : Nat := 3873046964048688260061613

theorem tailTrace_7542732 : CollatzResearch.WordTrace tailWord_7542732 prefixEnd_7542732 3873046964048688260061613 := by
  unfold tailWord_7542732
  simp only [CollatzResearch.WordTrace]
  refine ⟨137553018454988817456091225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183404024606651756608121633 137553018454988817456091225)
  ·
    refine ⟨103164763841241613092068419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137553018454988817456091225 103164763841241613092068419)
    ·
      refine ⟨154747145761862419638102629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103164763841241613092068419 154747145761862419638102629)
      ·
        refine ⟨29015089830349203682144243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154747145761862419638102629 29015089830349203682144243)
        ·
          refine ⟨43522634745523805523216365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015089830349203682144243 43522634745523805523216365)
          ·
            refine ⟨16320988029571427071206137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43522634745523805523216365 16320988029571427071206137)
            ·
              refine ⟨12240741022178570303404603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16320988029571427071206137 12240741022178570303404603)
              ·
                refine ⟨18361111533267855455106905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240741022178570303404603 18361111533267855455106905)
                ·
                  refine ⟨13770833649950891591330179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18361111533267855455106905 13770833649950891591330179)
                  ·
                    refine ⟨20656250474926337386995269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13770833649950891591330179 20656250474926337386995269)
                    ·
                      refine ⟨3873046964048688260061613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20656250474926337386995269 3873046964048688260061613)
                      ·
                        rfl

theorem cell23_7542732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7542732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542732 prefixEnd_7542732 := by exact prefixLift 7542732
  have htrace : WordTrace (prefixWord ++ tailWord_7542732) baseStart_7542732 baseEnd_7542732 := by
    simpa [prefixWord, tailWord_7542732, baseEnd_7542732] using wordTrace_append hprefix tailTrace_7542732
  have hstable : (prefixWord ++ tailWord_7542732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542732).length < 2 ^ (prefixWord ++ tailWord_7542732).sum := by decide
  have hdescent : baseEnd_7542732 < baseStart_7542732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542755 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 6]
def baseStart_7542755 : Nat := 118140960795 + 7542755 * 2 ^ 59
def prefixEnd_7542755 : Nat := 4983230072969 + 3 ^ 40 * 7542755 * 2
def baseEnd_7542755 : Nat := 430339863789304630008223

theorem tailTrace_7542755 : CollatzResearch.WordTrace tailWord_7542755 prefixEnd_7542755 430339863789304630008223 := by
  unfold tailWord_7542755
  simp only [CollatzResearch.WordTrace]
  refine ⟨275106875788894309840269719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183404583859262873226846479 275106875788894309840269719)
  ·
    refine ⟨412660313683341464760404579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275106875788894309840269719 412660313683341464760404579)
    ·
      refine ⟨618990470525012197140606869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412660313683341464760404579 618990470525012197140606869)
      ·
        refine ⟨29015178305859946740965947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 618990470525012197140606869 29015178305859946740965947)
        ·
          refine ⟨43522767458789920111448921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015178305859946740965947 43522767458789920111448921)
          ·
            refine ⟨32642075594092440083586691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43522767458789920111448921 32642075594092440083586691)
            ·
              refine ⟨48963113391138660125380037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32642075594092440083586691 48963113391138660125380037)
              ·
                refine ⟨9180583760838498773508757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48963113391138660125380037 9180583760838498773508757)
                ·
                  refine ⟨430339863789304630008223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9180583760838498773508757 430339863789304630008223)
                  ·
                    rfl

theorem cell23_7542755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 6].length) (baseStart_7542755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542755 prefixEnd_7542755 := by exact prefixLift 7542755
  have htrace : WordTrace (prefixWord ++ tailWord_7542755) baseStart_7542755 baseEnd_7542755 := by
    simpa [prefixWord, tailWord_7542755, baseEnd_7542755] using wordTrace_append hprefix tailTrace_7542755
  have hstable : (prefixWord ++ tailWord_7542755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542755).length < 2 ^ (prefixWord ++ tailWord_7542755).sum := by decide
  have hdescent : baseEnd_7542755 < baseStart_7542755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542785 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7542785 : Nat := 118140960795 + 7542785 * 2 ^ 59
def prefixEnd_7542785 : Nat := 4983230072969 + 3 ^ 40 * 7542785 * 2
def baseEnd_7542785 : Nat := 1291024726174458850899623

theorem tailTrace_7542785 : CollatzResearch.WordTrace tailWord_7542785 prefixEnd_7542785 1291024726174458850899623 := by
  unfold tailWord_7542785
  simp only [CollatzResearch.WordTrace]
  refine ⟨275107969978785624963861809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183405313319190416642574539 275107969978785624963861809)
  ·
    refine ⟨206330977484089218722896357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275107969978785624963861809 206330977484089218722896357)
    ·
      refine ⟨38687058278266728510543067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206330977484089218722896357 38687058278266728510543067)
      ·
        refine ⟨58030587417400092765814601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38687058278266728510543067 58030587417400092765814601)
        ·
          refine ⟨43522940563050069574360951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58030587417400092765814601 43522940563050069574360951)
          ·
            refine ⟨65284410844575104361541427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43522940563050069574360951 65284410844575104361541427)
            ·
              refine ⟨97926616266862656542312141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65284410844575104361541427 97926616266862656542312141)
              ·
                refine ⟨36722481100073496203367053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97926616266862656542312141 36722481100073496203367053)
                ·
                  refine ⟨13770930412527561076262645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36722481100073496203367053 13770930412527561076262645)
                  ·
                    refine ⟨1291024726174458850899623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13770930412527561076262645 1291024726174458850899623)
                    ·
                      rfl

theorem cell23_7542785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7542785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542785 prefixEnd_7542785 := by exact prefixLift 7542785
  have htrace : WordTrace (prefixWord ++ tailWord_7542785) baseStart_7542785 baseEnd_7542785 := by
    simpa [prefixWord, tailWord_7542785, baseEnd_7542785] using wordTrace_append hprefix tailTrace_7542785
  have hstable : (prefixWord ++ tailWord_7542785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542785).length < 2 ^ (prefixWord ++ tailWord_7542785).sum := by decide
  have hdescent : baseEnd_7542785 < baseStart_7542785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542792 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_7542792 : Nat := 118140960795 + 7542792 * 2 ^ 59
def prefixEnd_7542792 : Nat := 4983230072969 + 3 ^ 40 * 7542792 * 2
def baseEnd_7542792 : Nat := 3873077772887958025311337

theorem tailTrace_7542792 : CollatzResearch.WordTrace tailWord_7542792 prefixEnd_7542792 3873077772887958025311337 := by
  unfold tailWord_7542792
  simp only [CollatzResearch.WordTrace]
  refine ⟨137554112644880132579683315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183405483526506843439577753 137554112644880132579683315)
  ·
    refine ⟨206331168967320198869524973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137554112644880132579683315 206331168967320198869524973)
    ·
      refine ⟨77374188362745074576071865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206331168967320198869524973 77374188362745074576071865)
      ·
        refine ⟨58030641272058805932053899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77374188362745074576071865 58030641272058805932053899)
        ·
          refine ⟨87045961908088208898080849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58030641272058805932053899 87045961908088208898080849)
          ·
            refine ⟨65284471431066156673560637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87045961908088208898080849 65284471431066156673560637)
            ·
              refine ⟨24481676786649808752585239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65284471431066156673560637 24481676786649808752585239)
              ·
                refine ⟨36722515179974713128877859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24481676786649808752585239 36722515179974713128877859)
                ·
                  refine ⟨55083772769962069693316789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36722515179974713128877859 55083772769962069693316789)
                  ·
                    refine ⟨5164103697183944033748449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55083772769962069693316789 5164103697183944033748449)
                    ·
                      refine ⟨3873077772887958025311337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164103697183944033748449 3873077772887958025311337)
                      ·
                        rfl

theorem cell23_7542792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_7542792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542792 prefixEnd_7542792 := by exact prefixLift 7542792
  have htrace : WordTrace (prefixWord ++ tailWord_7542792) baseStart_7542792 baseEnd_7542792 := by
    simpa [prefixWord, tailWord_7542792, baseEnd_7542792] using wordTrace_append hprefix tailTrace_7542792
  have hstable : (prefixWord ++ tailWord_7542792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542792).length < 2 ^ (prefixWord ++ tailWord_7542792).sum := by decide
  have hdescent : baseEnd_7542792 < baseStart_7542792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542832 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_7542832 : Nat := 118140960795 + 7542832 * 2 ^ 59
def prefixEnd_7542832 : Nat := 4983230072969 + 3 ^ 40 * 7542832 * 2
def baseEnd_7542832 : Nat := 1291032770704712622937051

theorem tailTrace_7542832 : CollatzResearch.WordTrace tailWord_7542832 prefixEnd_7542832 1291032770704712622937051 := by
  unfold tailWord_7542832
  simp only [CollatzResearch.WordTrace]
  refine ⟨137554842104807675995411375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183406456139743567993881833 137554842104807675995411375)
  ·
    refine ⟨206332263157211513993117063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137554842104807675995411375 206332263157211513993117063)
    ·
      refine ⟨309498394735817270989675595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206332263157211513993117063 309498394735817270989675595)
      ·
        refine ⟨464247592103725906484513393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309498394735817270989675595 464247592103725906484513393)
        ·
          refine ⟨348185694077794429863385045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464247592103725906484513393 348185694077794429863385045)
          ·
            refine ⟨8160602204948306949923087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 348185694077794429863385045 8160602204948306949923087)
            ·
              refine ⟨12240903307422460424884631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160602204948306949923087 12240903307422460424884631)
              ·
                refine ⟨18361354961133690637326947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240903307422460424884631 18361354961133690637326947)
                ·
                  refine ⟨27542032441700535955990421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18361354961133690637326947 27542032441700535955990421)
                  ·
                    refine ⟨1291032770704712622937051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27542032441700535955990421 1291032770704712622937051)
                    ·
                      rfl

theorem cell23_7542832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_7542832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542832 prefixEnd_7542832 := by exact prefixLift 7542832
  have htrace : WordTrace (prefixWord ++ tailWord_7542832) baseStart_7542832 baseEnd_7542832 := by
    simpa [prefixWord, tailWord_7542832, baseEnd_7542832] using wordTrace_append hprefix tailTrace_7542832
  have hstable : (prefixWord ++ tailWord_7542832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542832).length < 2 ^ (prefixWord ++ tailWord_7542832).sum := by decide
  have hdescent : baseEnd_7542832 < baseStart_7542832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542836 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_7542836 : Nat := 118140960795 + 7542836 * 2 ^ 59
def prefixEnd_7542836 : Nat := 4983230072969 + 3 ^ 40 * 7542836 * 2
def baseEnd_7542836 : Nat := 1291033455345585284387045

theorem tailTrace_7542836 : CollatzResearch.WordTrace tailWord_7542836 prefixEnd_7542836 1291033455345585284387045 := by
  unfold tailWord_7542836
  simp only [CollatzResearch.WordTrace]
  refine ⟨137554915050800430336984181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183406553401067240449312241 137554915050800430336984181)
  ·
    refine ⟨12895773286012540344092267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137554915050800430336984181 12895773286012540344092267)
    ·
      refine ⟨19343659929018810516138401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895773286012540344092267 19343659929018810516138401)
      ·
        refine ⟨14507744946764107887103801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19343659929018810516138401 14507744946764107887103801)
        ·
          refine ⟨10880808710073080915327851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14507744946764107887103801 10880808710073080915327851)
          ·
            refine ⟨16321213065109621372991777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880808710073080915327851 16321213065109621372991777)
            ·
              refine ⟨12240909798832216029743833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16321213065109621372991777 12240909798832216029743833)
              ·
                refine ⟨9180682349124162022307875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12240909798832216029743833 9180682349124162022307875)
                ·
                  refine ⟨13771023523686243033461813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9180682349124162022307875 13771023523686243033461813)
                  ·
                    refine ⟨1291033455345585284387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13771023523686243033461813 1291033455345585284387045)
                    ·
                      rfl

theorem cell23_7542836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_7542836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542836 prefixEnd_7542836 := by exact prefixLift 7542836
  have htrace : WordTrace (prefixWord ++ tailWord_7542836) baseStart_7542836 baseEnd_7542836 := by
    simpa [prefixWord, tailWord_7542836, baseEnd_7542836] using wordTrace_append hprefix tailTrace_7542836
  have hstable : (prefixWord ++ tailWord_7542836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542836).length < 2 ^ (prefixWord ++ tailWord_7542836).sum := by decide
  have hdescent : baseEnd_7542836 < baseStart_7542836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542839 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_7542839 : Nat := 118140960795 + 7542839 * 2 ^ 59
def prefixEnd_7542839 : Nat := 4983230072969 + 3 ^ 40 * 7542839 * 2
def baseEnd_7542839 : Nat := 3873101906478719341423621

theorem tailTrace_7542839 : CollatzResearch.WordTrace tailWord_7542839 prefixEnd_7542839 3873101906478719341423621 := by
  unfold tailWord_7542839
  simp only [CollatzResearch.WordTrace]
  refine ⟨275109939520589992186327571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183406626347059994790885047 275109939520589992186327571)
  ·
    refine ⟨412664909280884988279491357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275109939520589992186327571 412664909280884988279491357)
    ·
      refine ⟨154749340980331870604809259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412664909280884988279491357 154749340980331870604809259)
      ·
        refine ⟨232124011470497805907213889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154749340980331870604809259 232124011470497805907213889)
        ·
          refine ⟨174093008602873354430410417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232124011470497805907213889 174093008602873354430410417)
          ·
            refine ⟨130569756452155015822807813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174093008602873354430410417 130569756452155015822807813)
            ·
              refine ⟨24481829334779065466776465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130569756452155015822807813 24481829334779065466776465)
              ·
                refine ⟨18361372001084299100082349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24481829334779065466776465 18361372001084299100082349)
                ·
                  refine ⟨6885514500406612162530881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18361372001084299100082349 6885514500406612162530881)
                  ·
                    refine ⟨5164135875304959121898161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885514500406612162530881 5164135875304959121898161)
                    ·
                      refine ⟨3873101906478719341423621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164135875304959121898161 3873101906478719341423621)
                      ·
                        rfl

theorem cell23_7542839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_7542839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542839 prefixEnd_7542839 := by exact prefixLift 7542839
  have htrace : WordTrace (prefixWord ++ tailWord_7542839) baseStart_7542839 baseEnd_7542839 := by
    simpa [prefixWord, tailWord_7542839, baseEnd_7542839] using wordTrace_append hprefix tailTrace_7542839
  have hstable : (prefixWord ++ tailWord_7542839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542839).length < 2 ^ (prefixWord ++ tailWord_7542839).sum := by decide
  have hdescent : baseEnd_7542839 < baseStart_7542839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542845 : List Nat := [1, 4, 1, 3, 1, 1, 3, 9]
def baseStart_7542845 : Nat := 118140960795 + 7542845 * 2 ^ 59
def prefixEnd_7542845 : Nat := 4983230072969 + 3 ^ 40 * 7542845 * 2
def baseEnd_7542845 : Nat := 143448332865283196961059

theorem tailTrace_7542845 : CollatzResearch.WordTrace tailWord_7542845 prefixEnd_7542845 143448332865283196961059 := by
  unfold tailWord_7542845
  simp only [CollatzResearch.WordTrace]
  refine ⟨275110158358568255211045989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183406772239045503474030659 275110158358568255211045989)
  ·
    refine ⟨51583154692231547852071123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275110158358568255211045989 51583154692231547852071123)
    ·
      refine ⟨77374732038347321778106685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51583154692231547852071123 77374732038347321778106685)
      ·
        refine ⟨29015524514380245666790007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77374732038347321778106685 29015524514380245666790007)
        ·
          refine ⟨43523286771570368500185011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29015524514380245666790007 43523286771570368500185011)
          ·
            refine ⟨65284930157355552750277517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43523286771570368500185011 65284930157355552750277517)
            ·
              refine ⟨24481848809008332281354069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65284930157355552750277517 24481848809008332281354069)
              ·
                refine ⟨143448332865283196961059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24481848809008332281354069 143448332865283196961059)
                ·
                  rfl

theorem cell23_7542845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 9].length) (baseStart_7542845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542845 prefixEnd_7542845 := by exact prefixLift 7542845
  have htrace : WordTrace (prefixWord ++ tailWord_7542845) baseStart_7542845 baseEnd_7542845 := by
    simpa [prefixWord, tailWord_7542845, baseEnd_7542845] using wordTrace_append hprefix tailTrace_7542845
  have hstable : (prefixWord ++ tailWord_7542845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542845).length < 2 ^ (prefixWord ++ tailWord_7542845).sum := by decide
  have hdescent : baseEnd_7542845 < baseStart_7542845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542856 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_7542856 : Nat := 118140960795 + 7542856 * 2 ^ 59
def prefixEnd_7542856 : Nat := 4983230072969 + 3 ^ 40 * 7542856 * 2
def baseEnd_7542856 : Nat := 3873110635649845774911043

theorem tailTrace_7542856 : CollatzResearch.WordTrace tailWord_7542856 prefixEnd_7542856 3873110635649845774911043 := by
  unfold tailWord_7542856
  simp only [CollatzResearch.WordTrace]
  refine ⟨137555279780764202044848211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183407039707685602726464281 137555279780764202044848211)
  ·
    refine ⟨206332919671146303067272317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137555279780764202044848211 206332919671146303067272317)
    ·
      refine ⟨77374844876679863650227119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206332919671146303067272317 77374844876679863650227119)
      ·
        refine ⟨116062267315019795475340679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77374844876679863650227119 116062267315019795475340679)
        ·
          refine ⟨174093400972529693213011019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116062267315019795475340679 174093400972529693213011019)
          ·
            refine ⟨261140101458794539819516529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174093400972529693213011019 261140101458794539819516529)
            ·
              refine ⟨195855076094095904864637397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261140101458794539819516529 195855076094095904864637397)
              ·
                refine ⟨4590353345955372770264939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195855076094095904864637397 4590353345955372770264939)
                ·
                  refine ⟨6885530018933059155397409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590353345955372770264939 6885530018933059155397409)
                  ·
                    refine ⟨5164147514199794366548057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885530018933059155397409 5164147514199794366548057)
                    ·
                      refine ⟨3873110635649845774911043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164147514199794366548057 3873110635649845774911043)
                      ·
                        rfl

theorem cell23_7542856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_7542856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542856 prefixEnd_7542856 := by exact prefixLift 7542856
  have htrace : WordTrace (prefixWord ++ tailWord_7542856) baseStart_7542856 baseEnd_7542856 := by
    simpa [prefixWord, tailWord_7542856, baseEnd_7542856] using wordTrace_append hprefix tailTrace_7542856
  have hstable : (prefixWord ++ tailWord_7542856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542856).length < 2 ^ (prefixWord ++ tailWord_7542856).sum := by decide
  have hdescent : baseEnd_7542856 < baseStart_7542856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542873 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 1, 2, 2]
def baseStart_7542873 : Nat := 118140960795 + 7542873 * 2 ^ 59
def prefixEnd_7542873 : Nat := 4983230072969 + 3 ^ 40 * 7542873 * 2
def baseEnd_7542873 : Nat := 3873119364820972208398465

theorem tailTrace_7542873 : CollatzResearch.WordTrace tailWord_7542873 prefixEnd_7542873 3873119364820972208398465 := by
  unfold tailWord_7542873
  simp only [CollatzResearch.WordTrace]
  refine ⟨275111179602466815993065273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183407453068311210662043515 275111179602466815993065273)
  ·
    refine ⟨206333384701850111994798955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275111179602466815993065273 206333384701850111994798955)
    ·
      refine ⟨309500077052775167992198433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206333384701850111994798955 309500077052775167992198433)
      ·
        refine ⟨232125057789581375994148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309500077052775167992198433 232125057789581375994148825)
        ·
          refine ⟨174093793342186031995611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232125057789581375994148825 174093793342186031995611619)
          ·
            refine ⟨261140690013279047993417429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174093793342186031995611619 261140690013279047993417429)
            ·
              refine ⟨6120484922186227687345721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 261140690013279047993417429 6120484922186227687345721)
              ·
                refine ⟨4590363691639670765509291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120484922186227687345721 4590363691639670765509291)
                ·
                  refine ⟨6885545537459506148263937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590363691639670765509291 6885545537459506148263937)
                  ·
                    refine ⟨5164159153094629611197953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885545537459506148263937 5164159153094629611197953)
                    ·
                      refine ⟨3873119364820972208398465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164159153094629611197953 3873119364820972208398465)
                      ·
                        rfl

theorem cell23_7542873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_7542873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542873 prefixEnd_7542873 := by exact prefixLift 7542873
  have htrace : WordTrace (prefixWord ++ tailWord_7542873) baseStart_7542873 baseEnd_7542873 := by
    simpa [prefixWord, tailWord_7542873, baseEnd_7542873] using wordTrace_append hprefix tailTrace_7542873
  have hstable : (prefixWord ++ tailWord_7542873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542873).length < 2 ^ (prefixWord ++ tailWord_7542873).sum := by decide
  have hdescent : baseEnd_7542873 < baseStart_7542873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542889 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_7542889 : Nat := 118140960795 + 7542889 * 2 ^ 59
def prefixEnd_7542889 : Nat := 4983230072969 + 3 ^ 40 * 7542889 * 2
def baseEnd_7542889 : Nat := 3873127580511444145798391

theorem tailTrace_7542889 : CollatzResearch.WordTrace tailWord_7542889 prefixEnd_7542889 3873127580511444145798391 := by
  unfold tailWord_7542889
  simp only [CollatzResearch.WordTrace]
  refine ⟨275111763170408850725647721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183407842113605900483765147 275111763170408850725647721)
  ·
    refine ⟨206333822377806638044235791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275111763170408850725647721 206333822377806638044235791)
    ·
      refine ⟨309500733566709957066353687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206333822377806638044235791 309500733566709957066353687)
      ·
        refine ⟨464251100350064935599530531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309500733566709957066353687 464251100350064935599530531)
        ·
          refine ⟨696376650525097403399295797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464251100350064935599530531 696376650525097403399295797)
          ·
            refine ⟨65285310986727881568683981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 696376650525097403399295797 65285310986727881568683981)
            ·
              refine ⟨24481991620022955588256493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65285310986727881568683981 24481991620022955588256493)
              ·
                refine ⟨9180746857508608345596185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24481991620022955588256493 9180746857508608345596185)
                ·
                  refine ⟨6885560143131456259197139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180746857508608345596185 6885560143131456259197139)
                  ·
                    refine ⟨10328340214697184388795709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6885560143131456259197139 10328340214697184388795709)
                    ·
                      refine ⟨3873127580511444145798391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10328340214697184388795709 3873127580511444145798391)
                      ·
                        rfl

theorem cell23_7542889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_7542889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542889 prefixEnd_7542889 := by exact prefixLift 7542889
  have htrace : WordTrace (prefixWord ++ tailWord_7542889) baseStart_7542889 baseEnd_7542889 := by
    simpa [prefixWord, tailWord_7542889, baseEnd_7542889] using wordTrace_append hprefix tailTrace_7542889
  have hstable : (prefixWord ++ tailWord_7542889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542889).length < 2 ^ (prefixWord ++ tailWord_7542889).sum := by decide
  have hdescent : baseEnd_7542889 < baseStart_7542889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542946 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7542946 : Nat := 118140960795 + 7542946 * 2 ^ 59
def prefixEnd_7542946 : Nat := 4983230072969 + 3 ^ 40 * 7542946 * 2
def baseEnd_7542946 : Nat := 3873156848908750422785629

theorem tailTrace_7542946 : CollatzResearch.WordTrace tailWord_7542946 prefixEnd_7542946 3873156848908750422785629 := by
  unfold tailWord_7542946
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778460532800587365118173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183409228087468232973648461 68778460532800587365118173)
  ·
    refine ⟨25791922699800220261919315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68778460532800587365118173 25791922699800220261919315)
    ·
      refine ⟨38687884049700330392878973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25791922699800220261919315 38687884049700330392878973)
      ·
        refine ⟨14507956518637623897329615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38687884049700330392878973 14507956518637623897329615)
        ·
          refine ⟨21761934777956435845994423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14507956518637623897329615 21761934777956435845994423)
          ·
            refine ⟨32642902166934653768991635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21761934777956435845994423 32642902166934653768991635)
            ·
              refine ⟨48964353250401980653487453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32642902166934653768991635 48964353250401980653487453)
              ·
                refine ⟨18361632468900742745057795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48964353250401980653487453 18361632468900742745057795)
                ·
                  refine ⟨27542448703351114117586693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18361632468900742745057795 27542448703351114117586693)
                  ·
                    refine ⟨5164209131878333897047505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27542448703351114117586693 5164209131878333897047505)
                    ·
                      refine ⟨3873156848908750422785629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164209131878333897047505 3873156848908750422785629)
                      ·
                        rfl

theorem cell23_7542946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7542946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542946 prefixEnd_7542946 := by exact prefixLift 7542946
  have htrace : WordTrace (prefixWord ++ tailWord_7542946) baseStart_7542946 baseEnd_7542946 := by
    simpa [prefixWord, tailWord_7542946, baseEnd_7542946] using wordTrace_append hprefix tailTrace_7542946
  have hstable : (prefixWord ++ tailWord_7542946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542946).length < 2 ^ (prefixWord ++ tailWord_7542946).sum := by decide
  have hdescent : baseEnd_7542946 < baseStart_7542946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542962 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_7542962 : Nat := 118140960795 + 7542962 * 2 ^ 59
def prefixEnd_7542962 : Nat := 4983230072969 + 3 ^ 40 * 7542962 * 2
def baseEnd_7542962 : Nat := 3873165064599222360185555

theorem tailTrace_7542962 : CollatzResearch.WordTrace tailWord_7542962 prefixEnd_7542962 3873165064599222360185555 := by
  unfold tailWord_7542962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778606424786096048263785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183409617132762922795370093 68778606424786096048263785)
  ·
    refine ⟨51583954818589572036197839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68778606424786096048263785 51583954818589572036197839)
    ·
      refine ⟨77375932227884358054296759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51583954818589572036197839 77375932227884358054296759)
      ·
        refine ⟨116063898341826537081445139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77375932227884358054296759 116063898341826537081445139)
        ·
          refine ⟨174095847512739805622167709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116063898341826537081445139 174095847512739805622167709)
          ·
            refine ⟨65285942817277427108312891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174095847512739805622167709 65285942817277427108312891)
            ·
              refine ⟨97928914225916140662469337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65285942817277427108312891 97928914225916140662469337)
              ·
                refine ⟨73446685669437105496852003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97928914225916140662469337 73446685669437105496852003)
                ·
                  refine ⟨110170028504155658245278005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73446685669437105496852003 110170028504155658245278005)
                  ·
                    refine ⟨10328440172264592960494813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110170028504155658245278005 10328440172264592960494813)
                    ·
                      refine ⟨3873165064599222360185555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10328440172264592960494813 3873165064599222360185555)
                      ·
                        rfl

theorem cell23_7542962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_7542962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542962 prefixEnd_7542962 := by exact prefixLift 7542962
  have htrace : WordTrace (prefixWord ++ tailWord_7542962) baseStart_7542962 baseEnd_7542962 := by
    simpa [prefixWord, tailWord_7542962, baseEnd_7542962] using wordTrace_append hprefix tailTrace_7542962
  have hstable : (prefixWord ++ tailWord_7542962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542962).length < 2 ^ (prefixWord ++ tailWord_7542962).sum := by decide
  have hdescent : baseEnd_7542962 < baseStart_7542962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542969 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 5]
def baseStart_7542969 : Nat := 118140960795 + 7542969 * 2 ^ 59
def prefixEnd_7542969 : Nat := 4983230072969 + 3 ^ 40 * 7542969 * 2
def baseEnd_7542969 : Nat := 430352073218200425866447

theorem tailTrace_7542969 : CollatzResearch.WordTrace tailWord_7542969 prefixEnd_7542969 430352073218200425866447 := by
  unfold tailWord_7542969
  simp only [CollatzResearch.WordTrace]
  refine ⟨275114681010119024388559961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183409787340079349592373307 275114681010119024388559961)
  ·
    refine ⟨206336010757589268291419971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275114681010119024388559961 206336010757589268291419971)
    ·
      refine ⟨309504016136383902437129957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206336010757589268291419971 309504016136383902437129957)
      ·
        refine ⟨58032003025571981706961867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309504016136383902437129957 58032003025571981706961867)
        ·
          refine ⟨87048004538357972560442801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58032003025571981706961867 87048004538357972560442801)
          ·
            refine ⟨65286003403768479420332101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87048004538357972560442801 65286003403768479420332101)
            ·
              refine ⟨12241125638206589891312269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65286003403768479420332101 12241125638206589891312269)
              ·
                refine ⟨4590422114327471209242101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12241125638206589891312269 4590422114327471209242101)
                ·
                  refine ⟨430352073218200425866447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590422114327471209242101 430352073218200425866447)
                  ·
                    rfl

theorem cell23_7542969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 5].length) (baseStart_7542969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542969 prefixEnd_7542969 := by exact prefixLift 7542969
  have htrace : WordTrace (prefixWord ++ tailWord_7542969) baseStart_7542969 baseEnd_7542969 := by
    simpa [prefixWord, tailWord_7542969, baseEnd_7542969] using wordTrace_append hprefix tailTrace_7542969
  have hstable : (prefixWord ++ tailWord_7542969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542969).length < 2 ^ (prefixWord ++ tailWord_7542969).sum := by decide
  have hdescent : baseEnd_7542969 < baseStart_7542969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542980 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_7542980 : Nat := 118140960795 + 7542980 * 2 ^ 59
def prefixEnd_7542980 : Nat := 4983230072969 + 3 ^ 40 * 7542980 * 2
def baseEnd_7542980 : Nat := 3873174307251003289760473

theorem tailTrace_7542980 : CollatzResearch.WordTrace tailWord_7542980 prefixEnd_7542980 3873174307251003289760473 := by
  unfold tailWord_7542980
  simp only [CollatzResearch.WordTrace]
  refine ⟨137557541106539586633605197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183410054808719448844806929 137557541106539586633605197)
  ·
    refine ⟨51584077914952344987601949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137557541106539586633605197 51584077914952344987601949)
    ·
      refine ⟨19344029218107129370350731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51584077914952344987601949 19344029218107129370350731)
      ·
        refine ⟨29016043827160694055526097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344029218107129370350731 29016043827160694055526097)
        ·
          refine ⟨21762032870370520541644573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29016043827160694055526097 21762032870370520541644573)
          ·
            refine ⟨8160762326388945203116715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21762032870370520541644573 8160762326388945203116715)
            ·
              refine ⟨12241143489583417804675073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160762326388945203116715 12241143489583417804675073)
              ·
                refine ⟨9180857617187563353506305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12241143489583417804675073 9180857617187563353506305)
                ·
                  refine ⟨6885643212890672515129729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180857617187563353506305 6885643212890672515129729)
                  ·
                    refine ⟨5164232409668004386347297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885643212890672515129729 5164232409668004386347297)
                    ·
                      refine ⟨3873174307251003289760473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164232409668004386347297 3873174307251003289760473)
                      ·
                        rfl

theorem cell23_7542980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_7542980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542980 prefixEnd_7542980 := by exact prefixLift 7542980
  have htrace : WordTrace (prefixWord ++ tailWord_7542980) baseStart_7542980 baseEnd_7542980 := by
    simpa [prefixWord, tailWord_7542980, baseEnd_7542980] using wordTrace_append hprefix tailTrace_7542980
  have hstable : (prefixWord ++ tailWord_7542980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542980).length < 2 ^ (prefixWord ++ tailWord_7542980).sum := by decide
  have hdescent : baseEnd_7542980 < baseStart_7542980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7542995 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 8]
def baseStart_7542995 : Nat := 118140960795 + 7542995 * 2 ^ 59
def prefixEnd_7542995 : Nat := 4983230072969 + 3 ^ 40 * 7542995 * 2
def baseEnd_7542995 : Nat := 1291060669820273577024301

theorem tailTrace_7542995 : CollatzResearch.WordTrace tailWord_7542995 prefixEnd_7542995 1291060669820273577024301 := by
  unfold tailWord_7542995
  simp only [CollatzResearch.WordTrace]
  refine ⟨275115629308024830829006439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183410419538683220552670959 275115629308024830829006439)
  ·
    refine ⟨412673443962037246243509659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275115629308024830829006439 412673443962037246243509659)
    ·
      refine ⟨619010165943055869365264489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412673443962037246243509659 619010165943055869365264489)
      ·
        refine ⟨464257624457291902023948367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619010165943055869365264489 464257624457291902023948367)
        ·
          refine ⟨696386436685937853035922551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464257624457291902023948367 696386436685937853035922551)
          ·
            refine ⟨1044579655028906779553883827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696386436685937853035922551 1044579655028906779553883827)
            ·
              refine ⟨1566869482543360169330825741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044579655028906779553883827 1566869482543360169330825741)
              ·
                refine ⟨587576055953760063499059653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1566869482543360169330825741 587576055953760063499059653)
                ·
                  refine ⟨110170510491330011906073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587576055953760063499059653 110170510491330011906073685)
                  ·
                    refine ⟨1291060669820273577024301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110170510491330011906073685 1291060669820273577024301)
                    ·
                      rfl

theorem cell23_7542995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_7542995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7542995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7542995 prefixEnd_7542995 := by exact prefixLift 7542995
  have htrace : WordTrace (prefixWord ++ tailWord_7542995) baseStart_7542995 baseEnd_7542995 := by
    simpa [prefixWord, tailWord_7542995, baseEnd_7542995] using wordTrace_append hprefix tailTrace_7542995
  have hstable : (prefixWord ++ tailWord_7542995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7542995).length < 2 ^ (prefixWord ++ tailWord_7542995).sum := by decide
  have hdescent : baseEnd_7542995 < baseStart_7542995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7542995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543002 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_7543002 : Nat := 118140960795 + 7543002 * 2 ^ 59
def prefixEnd_7543002 : Nat := 4983230072969 + 3 ^ 40 * 7543002 * 2
def baseEnd_7543002 : Nat := 3873185603825402203685371

theorem tailTrace_7543002 : CollatzResearch.WordTrace tailWord_7543002 prefixEnd_7543002 3873185603825402203685371 := by
  unfold tailWord_7543002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68778971154749867756127815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183410589745999647349674173 68778971154749867756127815)
  ·
    refine ⟨103168456732124801634191723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68778971154749867756127815 103168456732124801634191723)
    ·
      refine ⟨154752685098187202451287585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103168456732124801634191723 154752685098187202451287585)
      ·
        refine ⟨116064513823640401838465689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154752685098187202451287585 116064513823640401838465689)
        ·
          refine ⟨87048385367730301378849267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116064513823640401838465689 87048385367730301378849267)
          ·
            refine ⟨130572578051595452068273901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87048385367730301378849267 130572578051595452068273901)
            ·
              refine ⟨48964716769348294525602713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130572578051595452068273901 48964716769348294525602713)
              ·
                refine ⟨36723537577011220894202035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48964716769348294525602713 36723537577011220894202035)
                ·
                  refine ⟨55085306365516831341303053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36723537577011220894202035 55085306365516831341303053)
                  ·
                    refine ⟨20656989887068811752988645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55085306365516831341303053 20656989887068811752988645)
                    ·
                      refine ⟨3873185603825402203685371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20656989887068811752988645 3873185603825402203685371)
                      ·
                        rfl

theorem cell23_7543002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_7543002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543002 prefixEnd_7543002 := by exact prefixLift 7543002
  have htrace : WordTrace (prefixWord ++ tailWord_7543002) baseStart_7543002 baseEnd_7543002 := by
    simpa [prefixWord, tailWord_7543002, baseEnd_7543002] using wordTrace_append hprefix tailTrace_7543002
  have hstable : (prefixWord ++ tailWord_7543002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543002).length < 2 ^ (prefixWord ++ tailWord_7543002).sum := by decide
  have hdescent : baseEnd_7543002 < baseStart_7543002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543022 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7543022 : Nat := 118140960795 + 7543022 * 2 ^ 59
def prefixEnd_7543022 : Nat := 4983230072969 + 3 ^ 40 * 7543022 * 2
def baseEnd_7543022 : Nat := 3873195873438492125435279

theorem tailTrace_7543022 : CollatzResearch.WordTrace tailWord_7543022 prefixEnd_7543022 3873195873438492125435279 := by
  unfold tailWord_7543022
  simp only [CollatzResearch.WordTrace]
  refine ⟨34389576759865876805029915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183411076052618009626826213 34389576759865876805029915)
  ·
    refine ⟨51584365139798815207544873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34389576759865876805029915 51584365139798815207544873)
    ·
      refine ⟨38688273854849111405658655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51584365139798815207544873 38688273854849111405658655)
      ·
        refine ⟨58032410782273667108487983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38688273854849111405658655 58032410782273667108487983)
        ·
          refine ⟨87048616173410500662731975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58032410782273667108487983 87048616173410500662731975)
          ·
            refine ⟨130572924260115750994097963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87048616173410500662731975 130572924260115750994097963)
            ·
              refine ⟨195859386390173626491146945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130572924260115750994097963 195859386390173626491146945)
              ·
                refine ⟨146894539792630219868360209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195859386390173626491146945 146894539792630219868360209)
                ·
                  refine ⟨110170904844472664901270157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146894539792630219868360209 110170904844472664901270157)
                  ·
                    refine ⟨41314089316677249337976309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110170904844472664901270157 41314089316677249337976309)
                    ·
                      refine ⟨3873195873438492125435279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41314089316677249337976309 3873195873438492125435279)
                      ·
                        rfl

theorem cell23_7543022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7543022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543022 prefixEnd_7543022 := by exact prefixLift 7543022
  have htrace : WordTrace (prefixWord ++ tailWord_7543022) baseStart_7543022 baseEnd_7543022 := by
    simpa [prefixWord, tailWord_7543022, baseEnd_7543022] using wordTrace_append hprefix tailTrace_7543022
  have hstable : (prefixWord ++ tailWord_7543022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543022).length < 2 ^ (prefixWord ++ tailWord_7543022).sum := by decide
  have hdescent : baseEnd_7543022 < baseStart_7543022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543039 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_7543039 : Nat := 118140960795 + 7543039 * 2 ^ 59
def prefixEnd_7543039 : Nat := 4983230072969 + 3 ^ 40 * 7543039 * 2
def baseEnd_7543039 : Nat := 3873204602609618558922701

theorem tailTrace_7543039 : CollatzResearch.WordTrace tailWord_7543039 prefixEnd_7543039 3873204602609618558922701 := by
  unfold tailWord_7543039
  simp only [CollatzResearch.WordTrace]
  refine ⟨275117234119865426343608171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183411489413243617562405447 275117234119865426343608171)
  ·
    refine ⟨412675851179798139515412257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275117234119865426343608171 412675851179798139515412257)
    ·
      refine ⟨309506888384848604636559193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412675851179798139515412257 309506888384848604636559193)
      ·
        refine ⟨232130166288636453477419395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309506888384848604636559193 232130166288636453477419395)
        ·
          refine ⟨348195249432954680216129093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232130166288636453477419395 348195249432954680216129093)
          ·
            refine ⟨65286609268679002540524205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348195249432954680216129093 65286609268679002540524205)
            ·
              refine ⟨24482478475754625952696577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65286609268679002540524205 24482478475754625952696577)
              ·
                refine ⟨18361858856815969464522433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24482478475754625952696577 18361858856815969464522433)
                ·
                  refine ⟨13771394142611977098391825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18361858856815969464522433 13771394142611977098391825)
                  ·
                    refine ⟨10328545606958982823793869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13771394142611977098391825 10328545606958982823793869)
                    ·
                      refine ⟨3873204602609618558922701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10328545606958982823793869 3873204602609618558922701)
                      ·
                        rfl

theorem cell23_7543039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_7543039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543039 prefixEnd_7543039 := by exact prefixLift 7543039
  have htrace : WordTrace (prefixWord ++ tailWord_7543039) baseStart_7543039 baseEnd_7543039 := by
    simpa [prefixWord, tailWord_7543039, baseEnd_7543039] using wordTrace_append hprefix tailTrace_7543039
  have hstable : (prefixWord ++ tailWord_7543039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543039).length < 2 ^ (prefixWord ++ tailWord_7543039).sum := by decide
  have hdescent : baseEnd_7543039 < baseStart_7543039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543096 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_7543096 : Nat := 118140960795 + 7543096 * 2 ^ 59
def prefixEnd_7543096 : Nat := 4983230072969 + 3 ^ 40 * 7543096 * 2
def baseEnd_7543096 : Nat := 3873233871006924835909939

theorem tailTrace_7543096 : CollatzResearch.WordTrace tailWord_7543096 prefixEnd_7543096 3873233871006924835909939 := by
  unfold tailWord_7543096
  simp only [CollatzResearch.WordTrace]
  refine ⟨137559656540329462539216571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183412875387105950052288761 137559656540329462539216571)
  ·
    refine ⟨206339484810494193808824857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137559656540329462539216571 206339484810494193808824857)
    ·
      refine ⟨154754613607870645356618643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206339484810494193808824857 154754613607870645356618643)
      ·
        refine ⟨232131920411805968034927965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154754613607870645356618643 232131920411805968034927965)
        ·
          refine ⟨87049470154427238013097987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232131920411805968034927965 87049470154427238013097987)
          ·
            refine ⟨130574205231640857019646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87049470154427238013097987 130574205231640857019646981)
            ·
              refine ⟨24482663480932660691183809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130574205231640857019646981 24482663480932660691183809)
              ·
                refine ⟨18361997610699495518387857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24482663480932660691183809 18361997610699495518387857)
                ·
                  refine ⟨13771498208024621638790893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18361997610699495518387857 13771498208024621638790893)
                  ·
                    refine ⟨5164311828009233114546585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13771498208024621638790893 5164311828009233114546585)
                    ·
                      refine ⟨3873233871006924835909939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164311828009233114546585 3873233871006924835909939)
                      ·
                        rfl

theorem cell23_7543096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_7543096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543096 prefixEnd_7543096 := by exact prefixLift 7543096
  have htrace : WordTrace (prefixWord ++ tailWord_7543096) baseStart_7543096 baseEnd_7543096 := by
    simpa [prefixWord, tailWord_7543096, baseEnd_7543096] using wordTrace_append hprefix tailTrace_7543096
  have hstable : (prefixWord ++ tailWord_7543096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543096).length < 2 ^ (prefixWord ++ tailWord_7543096).sum := by decide
  have hdescent : baseEnd_7543096 < baseStart_7543096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543103 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 1, 1, 3]
def baseStart_7543103 : Nat := 118140960795 + 7543103 * 2 ^ 59
def prefixEnd_7543103 : Nat := 4983230072969 + 3 ^ 40 * 7543103 * 2
def baseEnd_7543103 : Nat := 3873237465371506308522407

theorem tailTrace_7543103 : CollatzResearch.WordTrace tailWord_7543103 prefixEnd_7543103 3873237465371506308522407 := by
  unfold tailWord_7543103
  simp only [CollatzResearch.WordTrace]
  refine ⟨275119568391633565273937963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183413045594422376849291975 275119568391633565273937963)
  ·
    refine ⟨412679352587450347910906945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275119568391633565273937963 412679352587450347910906945)
    ·
      refine ⟨309509514440587760933180209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412679352587450347910906945 309509514440587760933180209)
      ·
        refine ⟨232132135830440820699885157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309509514440587760933180209 232132135830440820699885157)
        ·
          refine ⟨43524775468207653881228467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232132135830440820699885157 43524775468207653881228467)
          ·
            refine ⟨65287163202311480821842701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43524775468207653881228467 65287163202311480821842701)
            ·
              refine ⟨24482686200866805308191013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65287163202311480821842701 24482686200866805308191013)
              ·
                refine ⟨4590503662662525995285815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24482686200866805308191013 4590503662662525995285815)
                ·
                  refine ⟨6885755493993788992928723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590503662662525995285815 6885755493993788992928723)
                  ·
                    refine ⟨10328633240990683489393085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6885755493993788992928723 10328633240990683489393085)
                    ·
                      refine ⟨3873237465371506308522407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10328633240990683489393085 3873237465371506308522407)
                      ·
                        rfl

theorem cell23_7543103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_7543103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543103 prefixEnd_7543103 := by exact prefixLift 7543103
  have htrace : WordTrace (prefixWord ++ tailWord_7543103) baseStart_7543103 baseEnd_7543103 := by
    simpa [prefixWord, tailWord_7543103, baseEnd_7543103] using wordTrace_append hprefix tailTrace_7543103
  have hstable : (prefixWord ++ tailWord_7543103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543103).length < 2 ^ (prefixWord ++ tailWord_7543103).sum := by decide
  have hdescent : baseEnd_7543103 < baseStart_7543103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543109 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_7543109 : Nat := 118140960795 + 7543109 * 2 ^ 59
def prefixEnd_7543109 : Nat := 4983230072969 + 3 ^ 40 * 7543109 * 2
def baseEnd_7543109 : Nat := 3873240546255433285047379

theorem tailTrace_7543109 : CollatzResearch.WordTrace tailWord_7543109 prefixEnd_7543109 3873240546255433285047379 := by
  unfold tailWord_7543109
  simp only [CollatzResearch.WordTrace]
  refine ⟨275119787229611828298656381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183413191486407885532437587 275119787229611828298656381)
  ·
    refine ⟨103169920211104435611996143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275119787229611828298656381 103169920211104435611996143)
    ·
      refine ⟨154754880316656653417994215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103169920211104435611996143 154754880316656653417994215)
      ·
        refine ⟨232132320474984980126991323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154754880316656653417994215 232132320474984980126991323)
        ·
          refine ⟨348198480712477470190486985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232132320474984980126991323 348198480712477470190486985)
          ·
            refine ⟨261148860534358102642865239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348198480712477470190486985 261148860534358102642865239)
            ·
              refine ⟨391723290801537153964297859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261148860534358102642865239 391723290801537153964297859)
              ·
                refine ⟨587584936202305730946446789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391723290801537153964297859 587584936202305730946446789)
                ·
                  refine ⟨110172175537932324552458773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587584936202305730946446789 110172175537932324552458773)
                  ·
                    refine ⟨5164320728340577713396505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110172175537932324552458773 5164320728340577713396505)
                    ·
                      refine ⟨3873240546255433285047379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164320728340577713396505 3873240546255433285047379)
                      ·
                        rfl

theorem cell23_7543109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_7543109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543109 prefixEnd_7543109 := by exact prefixLift 7543109
  have htrace : WordTrace (prefixWord ++ tailWord_7543109) baseStart_7543109 baseEnd_7543109 := by
    simpa [prefixWord, tailWord_7543109, baseEnd_7543109] using wordTrace_append hprefix tailTrace_7543109
  have hstable : (prefixWord ++ tailWord_7543109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543109).length < 2 ^ (prefixWord ++ tailWord_7543109).sum := by decide
  have hdescent : baseEnd_7543109 < baseStart_7543109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543139 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7543139 : Nat := 118140960795 + 7543139 * 2 ^ 59
def prefixEnd_7543139 : Nat := 4983230072969 + 3 ^ 40 * 7543139 * 2
def baseEnd_7543139 : Nat := 3873255950675068167672241

theorem tailTrace_7543139 : CollatzResearch.WordTrace tailWord_7543139 prefixEnd_7543139 3873255950675068167672241 := by
  unfold tailWord_7543139
  simp only [CollatzResearch.WordTrace]
  refine ⟨275120881419503143422248471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183413920946335428948165647 275120881419503143422248471)
  ·
    refine ⟨412681322129254715133372707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275120881419503143422248471 412681322129254715133372707)
    ·
      refine ⟨619021983193882072700059061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412681322129254715133372707 619021983193882072700059061)
      ·
        refine ⟨58033310924426444315630537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 619021983193882072700059061 58033310924426444315630537)
        ·
          refine ⟨43524983193319833236722903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58033310924426444315630537 43524983193319833236722903)
          ·
            refine ⟨65287474789979749855084355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43524983193319833236722903 65287474789979749855084355)
            ·
              refine ⟨97931212184969624782626533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65287474789979749855084355 97931212184969624782626533)
              ·
                refine ⟨18362102284681804646742475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97931212184969624782626533 18362102284681804646742475)
                ·
                  refine ⟨27543153427022706970113713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18362102284681804646742475 27543153427022706970113713)
                  ·
                    refine ⟨20657365070267030227585285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27543153427022706970113713 20657365070267030227585285)
                    ·
                      refine ⟨3873255950675068167672241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20657365070267030227585285 3873255950675068167672241)
                      ·
                        rfl

theorem cell23_7543139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7543139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543139 prefixEnd_7543139 := by exact prefixLift 7543139
  have htrace : WordTrace (prefixWord ++ tailWord_7543139) baseStart_7543139 baseEnd_7543139 := by
    simpa [prefixWord, tailWord_7543139, baseEnd_7543139] using wordTrace_append hprefix tailTrace_7543139
  have hstable : (prefixWord ++ tailWord_7543139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543139).length < 2 ^ (prefixWord ++ tailWord_7543139).sum := by decide
  have hdescent : baseEnd_7543139 < baseStart_7543139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543143 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_7543143 : Nat := 118140960795 + 7543143 * 2 ^ 59
def prefixEnd_7543143 : Nat := 4983230072969 + 3 ^ 40 * 7543143 * 2
def baseEnd_7543143 : Nat := 3873258004597686152022223

theorem tailTrace_7543143 : CollatzResearch.WordTrace tailWord_7543143 prefixEnd_7543143 3873258004597686152022223 := by
  unfold tailWord_7543143
  simp only [CollatzResearch.WordTrace]
  refine ⟨275121027311488652105394083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183414018207659101403596055 275121027311488652105394083)
  ·
    refine ⟨412681540967232978158091125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275121027311488652105394083 412681540967232978158091125)
    ·
      refine ⟨38688894465678091702321043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412681540967232978158091125 38688894465678091702321043)
      ·
        refine ⟨58033341698517137553481565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38688894465678091702321043 58033341698517137553481565)
        ·
          refine ⟨21762503136943926582555587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58033341698517137553481565 21762503136943926582555587)
          ·
            refine ⟨32643754705415889873833381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21762503136943926582555587 32643754705415889873833381)
            ·
              refine ⟨6120704007265479351343759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32643754705415889873833381 6120704007265479351343759)
              ·
                refine ⟨9181056010898219027015639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120704007265479351343759 9181056010898219027015639)
                ·
                  refine ⟨13771584016347328540523459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181056010898219027015639 13771584016347328540523459)
                  ·
                    refine ⟨20657376024520992810785189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13771584016347328540523459 20657376024520992810785189)
                    ·
                      refine ⟨3873258004597686152022223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20657376024520992810785189 3873258004597686152022223)
                      ·
                        rfl

theorem cell23_7543143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_7543143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543143 prefixEnd_7543143 := by exact prefixLift 7543143
  have htrace : WordTrace (prefixWord ++ tailWord_7543143) baseStart_7543143 baseEnd_7543143 := by
    simpa [prefixWord, tailWord_7543143, baseEnd_7543143] using wordTrace_append hprefix tailTrace_7543143
  have hstable : (prefixWord ++ tailWord_7543143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543143).length < 2 ^ (prefixWord ++ tailWord_7543143).sum := by decide
  have hdescent : baseEnd_7543143 < baseStart_7543143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543170 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7543170 : Nat := 118140960795 + 7543170 * 2 ^ 59
def prefixEnd_7543170 : Nat := 4983230072969 + 3 ^ 40 * 7543170 * 2
def baseEnd_7543170 : Nat := 1291090622858452515461533

theorem tailTrace_7543170 : CollatzResearch.WordTrace tailWord_7543170 prefixEnd_7543170 1291090622858452515461533 := by
  unfold tailWord_7543170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68780503020597708929156741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183414674721593890477751309 68780503020597708929156741)
  ·
    refine ⟨12896344316362070424216889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68780503020597708929156741 12896344316362070424216889)
    ·
      refine ⟨9672258237271552818162667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12896344316362070424216889 9672258237271552818162667)
      ·
        refine ⟨14508387355907329227244001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9672258237271552818162667 14508387355907329227244001)
        ·
          refine ⟨10881290516930496920433001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14508387355907329227244001 10881290516930496920433001)
          ·
            refine ⟨8160967887697872690324751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10881290516930496920433001 8160967887697872690324751)
            ·
              refine ⟨12241451831546809035487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160967887697872690324751 12241451831546809035487127)
              ·
                refine ⟨18362177747320213553230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12241451831546809035487127 18362177747320213553230691)
                ·
                  refine ⟨27543266620980320329846037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18362177747320213553230691 27543266620980320329846037)
                  ·
                    refine ⟨1291090622858452515461533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27543266620980320329846037 1291090622858452515461533)
                    ·
                      rfl

theorem cell23_7543170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7543170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543170 prefixEnd_7543170 := by exact prefixLift 7543170
  have htrace : WordTrace (prefixWord ++ tailWord_7543170) baseStart_7543170 baseEnd_7543170 := by
    simpa [prefixWord, tailWord_7543170, baseEnd_7543170] using wordTrace_append hprefix tailTrace_7543170
  have hstable : (prefixWord ++ tailWord_7543170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543170).length < 2 ^ (prefixWord ++ tailWord_7543170).sum := by decide
  have hdescent : baseEnd_7543170 < baseStart_7543170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543203 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 1, 3, 2]
def baseStart_7543203 : Nat := 118140960795 + 7543203 * 2 ^ 59
def prefixEnd_7543203 : Nat := 4983230072969 + 3 ^ 40 * 7543203 * 2
def baseEnd_7543203 : Nat := 3873288813436955917271947

theorem tailTrace_7543203 : CollatzResearch.WordTrace tailWord_7543203 prefixEnd_7543203 3873288813436955917271947 := by
  unfold tailWord_7543203
  simp only [CollatzResearch.WordTrace]
  refine ⟨275123215691271282352578263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183415477127514188235052175 275123215691271282352578263)
  ·
    refine ⟨412684823536906923528867395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275123215691271282352578263 412684823536906923528867395)
    ·
      refine ⟨619027235305360385293301093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412684823536906923528867395 619027235305360385293301093)
      ·
        refine ⟨116067606619755072242493955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619027235305360385293301093 116067606619755072242493955)
        ·
          refine ⟨174101409929632608363740933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116067606619755072242493955 174101409929632608363740933)
          ·
            refine ⟨32644014361806114068201425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174101409929632608363740933 32644014361806114068201425)
            ·
              refine ⟨24483010771354585551151069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32644014361806114068201425 24483010771354585551151069)
              ·
                refine ⟨9181129039257969581681651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24483010771354585551151069 9181129039257969581681651)
                ·
                  refine ⟨13771693558886954372522477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181129039257969581681651 13771693558886954372522477)
                  ·
                    refine ⟨5164385084582607889695929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13771693558886954372522477 5164385084582607889695929)
                    ·
                      refine ⟨3873288813436955917271947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164385084582607889695929 3873288813436955917271947)
                      ·
                        rfl

theorem cell23_7543203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_7543203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543203 prefixEnd_7543203 := by exact prefixLift 7543203
  have htrace : WordTrace (prefixWord ++ tailWord_7543203) baseStart_7543203 baseEnd_7543203 := by
    simpa [prefixWord, tailWord_7543203, baseEnd_7543203] using wordTrace_append hprefix tailTrace_7543203
  have hstable : (prefixWord ++ tailWord_7543203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543203).length < 2 ^ (prefixWord ++ tailWord_7543203).sum := by decide
  have hdescent : baseEnd_7543203 < baseStart_7543203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543256 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 5]
def baseStart_7543256 : Nat := 118140960795 + 7543256 * 2 ^ 59
def prefixEnd_7543256 : Nat := 4983230072969 + 3 ^ 40 * 7543256 * 2
def baseEnd_7543256 : Nat := 430368447545738245545467

theorem tailTrace_7543256 : CollatzResearch.WordTrace tailWord_7543256 prefixEnd_7543256 430368447545738245545467 := by
  unfold tailWord_7543256
  simp only [CollatzResearch.WordTrace]
  refine ⟨137562574380039636202128811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183416765840052848269505081 137562574380039636202128811)
  ·
    refine ⟨206343861570059454303193217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137562574380039636202128811 206343861570059454303193217)
    ·
      refine ⟨154757896177544590727394913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206343861570059454303193217 154757896177544590727394913)
      ·
        refine ⟨116068422133158443045546185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154757896177544590727394913 116068422133158443045546185)
        ·
          refine ⟨87051316599868832284159639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116068422133158443045546185 87051316599868832284159639)
          ·
            refine ⟨130576974899803248426239459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87051316599868832284159639 130576974899803248426239459)
            ·
              refine ⟨195865462349704872639359189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130576974899803248426239459 195865462349704872639359189)
              ·
                refine ⟨4590596773821207952484981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195865462349704872639359189 4590596773821207952484981)
                ·
                  refine ⟨430368447545738245545467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590596773821207952484981 430368447545738245545467)
                  ·
                    rfl

theorem cell23_7543256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 5].length) (baseStart_7543256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543256 prefixEnd_7543256 := by exact prefixLift 7543256
  have htrace : WordTrace (prefixWord ++ tailWord_7543256) baseStart_7543256 baseEnd_7543256 := by
    simpa [prefixWord, tailWord_7543256, baseEnd_7543256] using wordTrace_append hprefix tailTrace_7543256
  have hstable : (prefixWord ++ tailWord_7543256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543256).length < 2 ^ (prefixWord ++ tailWord_7543256).sum := by decide
  have hdescent : baseEnd_7543256 < baseStart_7543256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543267 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7543267 : Nat := 118140960795 + 7543267 * 2 ^ 59
def prefixEnd_7543267 : Nat := 4983230072969 + 3 ^ 40 * 7543267 * 2
def baseEnd_7543267 : Nat := 3873321676198843666871653

theorem tailTrace_7543267 : CollatzResearch.WordTrace tailWord_7543267 prefixEnd_7543267 3873321676198843666871653 := by
  unfold tailWord_7543267
  simp only [CollatzResearch.WordTrace]
  refine ⟨275125549963039421282908055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183417033308692947521938703 275125549963039421282908055)
  ·
    refine ⟨412688324944559131924362083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275125549963039421282908055 412688324944559131924362083)
    ·
      refine ⟨619032487416838697886543125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412688324944559131924362083 619032487416838697886543125)
      ·
        refine ⟨29017147847664313963431709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 619032487416838697886543125 29017147847664313963431709)
        ·
          refine ⟨10881430442874117736286891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29017147847664313963431709 10881430442874117736286891)
          ·
            refine ⟨16322145664311176604430337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881430442874117736286891 16322145664311176604430337)
            ·
              refine ⟨12241609248233382453322753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16322145664311176604430337 12241609248233382453322753)
              ·
                refine ⟨9181206936175036839992065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12241609248233382453322753 9181206936175036839992065)
                ·
                  refine ⟨6885905202131277629994049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9181206936175036839992065 6885905202131277629994049)
                  ·
                    refine ⟨5164428901598458222495537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6885905202131277629994049 5164428901598458222495537)
                    ·
                      refine ⟨3873321676198843666871653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164428901598458222495537 3873321676198843666871653)
                      ·
                        rfl

theorem cell23_7543267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7543267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543267 prefixEnd_7543267 := by exact prefixLift 7543267
  have htrace : WordTrace (prefixWord ++ tailWord_7543267) baseStart_7543267 baseEnd_7543267 := by
    simpa [prefixWord, tailWord_7543267, baseEnd_7543267] using wordTrace_append hprefix tailTrace_7543267
  have hstable : (prefixWord ++ tailWord_7543267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543267).length < 2 ^ (prefixWord ++ tailWord_7543267).sum := by decide
  have hdescent : baseEnd_7543267 < baseStart_7543267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543276 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_7543276 : Nat := 118140960795 + 7543276 * 2 ^ 59
def prefixEnd_7543276 : Nat := 4983230072969 + 3 ^ 40 * 7543276 * 2
def baseEnd_7543276 : Nat := 3873326297524734131659111

theorem tailTrace_7543276 : CollatzResearch.WordTrace tailWord_7543276 prefixEnd_7543276 3873326297524734131659111 := by
  unfold tailWord_7543276
  simp only [CollatzResearch.WordTrace]
  refine ⟨137562939110003407909992841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183417252146671210546657121 137562939110003407909992841)
  ·
    refine ⟨103172204332502555932494631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137562939110003407909992841 103172204332502555932494631)
    ·
      refine ⟨154758306498753833898741947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103172204332502555932494631 154758306498753833898741947)
      ·
        refine ⟨232137459748130750848112921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154758306498753833898741947 232137459748130750848112921)
        ·
          refine ⟨174103094811098063136084691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232137459748130750848112921 174103094811098063136084691)
          ·
            refine ⟨261154642216647094704127037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174103094811098063136084691 261154642216647094704127037)
            ·
              refine ⟨97932990831242660514047639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261154642216647094704127037 97932990831242660514047639)
              ·
                refine ⟨146899486246863990771071459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97932990831242660514047639 146899486246863990771071459)
                ·
                  refine ⟨220349229370295986156607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146899486246863990771071459 220349229370295986156607189)
                  ·
                    refine ⟨5164435063366312175545481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220349229370295986156607189 5164435063366312175545481)
                    ·
                      refine ⟨3873326297524734131659111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164435063366312175545481 3873326297524734131659111)
                      ·
                        rfl

theorem cell23_7543276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_7543276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543276 prefixEnd_7543276 := by exact prefixLift 7543276
  have htrace : WordTrace (prefixWord ++ tailWord_7543276) baseStart_7543276 baseEnd_7543276 := by
    simpa [prefixWord, tailWord_7543276, baseEnd_7543276] using wordTrace_append hprefix tailTrace_7543276
  have hstable : (prefixWord ++ tailWord_7543276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543276).length < 2 ^ (prefixWord ++ tailWord_7543276).sum := by decide
  have hdescent : baseEnd_7543276 < baseStart_7543276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543286 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7543286 : Nat := 118140960795 + 7543286 * 2 ^ 59
def prefixEnd_7543286 : Nat := 4983230072969 + 3 ^ 40 * 7543286 * 2
def baseEnd_7543286 : Nat := 1291110477443759697511355

theorem tailTrace_7543286 : CollatzResearch.WordTrace tailWord_7543286 prefixEnd_7543286 1291110477443759697511355 := by
  unfold tailWord_7543286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195390184373161720490607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183417495299980391685233141 17195390184373161720490607)
  ·
    refine ⟨25793085276559742580735911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195390184373161720490607 25793085276559742580735911)
    ·
      refine ⟨38689627914839613871103867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25793085276559742580735911 38689627914839613871103867)
      ·
        refine ⟨58034441872259420806655801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38689627914839613871103867 58034441872259420806655801)
        ·
          refine ⟨43525831404194565604991851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58034441872259420806655801 43525831404194565604991851)
          ·
            refine ⟨65288747106291848407487777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43525831404194565604991851 65288747106291848407487777)
            ·
              refine ⟨48966560329718886305615833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65288747106291848407487777 48966560329718886305615833)
              ·
                refine ⟨36724920247289164729211875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48966560329718886305615833 36724920247289164729211875)
                ·
                  refine ⟨55087380370933747093817813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36724920247289164729211875 55087380370933747093817813)
                  ·
                    refine ⟨1291110477443759697511355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55087380370933747093817813 1291110477443759697511355)
                    ·
                      rfl

theorem cell23_7543286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7543286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543286 prefixEnd_7543286 := by exact prefixLift 7543286
  have htrace : WordTrace (prefixWord ++ tailWord_7543286) baseStart_7543286 baseEnd_7543286 := by
    simpa [prefixWord, tailWord_7543286, baseEnd_7543286] using wordTrace_append hprefix tailTrace_7543286
  have hstable : (prefixWord ++ tailWord_7543286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543286).length < 2 ^ (prefixWord ++ tailWord_7543286).sum := by decide
  have hdescent : baseEnd_7543286 < baseStart_7543286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543306 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_7543306 : Nat := 118140960795 + 7543306 * 2 ^ 59
def prefixEnd_7543306 : Nat := 4983230072969 + 3 ^ 40 * 7543306 * 2
def baseEnd_7543306 : Nat := 3873341701944369014283973

theorem tailTrace_7543306 : CollatzResearch.WordTrace tailWord_7543306 prefixEnd_7543306 3873341701944369014283973 := by
  unfold tailWord_7543306
  simp only [CollatzResearch.WordTrace]
  refine ⟨68781743102474532735894443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183417981606598753962385181 68781743102474532735894443)
  ·
    refine ⟨103172614653711799103841665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68781743102474532735894443 103172614653711799103841665)
    ·
      refine ⟨77379460990283849327881249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103172614653711799103841665 77379460990283849327881249)
      ·
        refine ⟨58034595742712886995910937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77379460990283849327881249 58034595742712886995910937)
        ·
          refine ⟨43525946807034665246933203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58034595742712886995910937 43525946807034665246933203)
          ·
            refine ⟨65288920210551997870399805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43525946807034665246933203 65288920210551997870399805)
            ·
              refine ⟨24483345078956999201399927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65288920210551997870399805 24483345078956999201399927)
              ·
                refine ⟨36725017618435498802099891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24483345078956999201399927 36725017618435498802099891)
                ·
                  refine ⟨55087526427653248203149837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36725017618435498802099891 55087526427653248203149837)
                  ·
                    refine ⟨20657822410369968076181189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55087526427653248203149837 20657822410369968076181189)
                    ·
                      refine ⟨3873341701944369014283973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20657822410369968076181189 3873341701944369014283973)
                      ·
                        rfl

theorem cell23_7543306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_7543306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543306 prefixEnd_7543306 := by exact prefixLift 7543306
  have htrace : WordTrace (prefixWord ++ tailWord_7543306) baseStart_7543306 baseEnd_7543306 := by
    simpa [prefixWord, tailWord_7543306, baseEnd_7543306] using wordTrace_append hprefix tailTrace_7543306
  have hstable : (prefixWord ++ tailWord_7543306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543306).length < 2 ^ (prefixWord ++ tailWord_7543306).sum := by decide
  have hdescent : baseEnd_7543306 < baseStart_7543306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543346 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_7543346 : Nat := 118140960795 + 7543346 * 2 ^ 59
def prefixEnd_7543346 : Nat := 4983230072969 + 3 ^ 40 * 7543346 * 2
def baseEnd_7543346 : Nat := 430373582352283206420421

theorem tailTrace_7543346 : CollatzResearch.WordTrace tailWord_7543346 prefixEnd_7543346 430373582352283206420421 := by
  unfold tailWord_7543346
  simp only [CollatzResearch.WordTrace]
  refine ⟨68782107832438304443758473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183418954219835478516689261 68782107832438304443758473)
  ·
    refine ⟨51586580874328728332818855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68782107832438304443758473 51586580874328728332818855)
    ·
      refine ⟨77379871311493092499228283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51586580874328728332818855 77379871311493092499228283)
      ·
        refine ⟨116069806967239638748842425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77379871311493092499228283 116069806967239638748842425)
        ·
          refine ⟨87052355225429729061631819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116069806967239638748842425 87052355225429729061631819)
          ·
            refine ⟨130578532838144593592447729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87052355225429729061631819 130578532838144593592447729)
            ·
              refine ⟨97933899628608445194335797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130578532838144593592447729 97933899628608445194335797)
              ·
                refine ⟨9181303090182041736968981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97933899628608445194335797 9181303090182041736968981)
                ·
                  refine ⟨430373582352283206420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9181303090182041736968981 430373582352283206420421)
                  ·
                    rfl

theorem cell23_7543346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_7543346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543346 prefixEnd_7543346 := by exact prefixLift 7543346
  have htrace : WordTrace (prefixWord ++ tailWord_7543346) baseStart_7543346 baseEnd_7543346 := by
    simpa [prefixWord, tailWord_7543346, baseEnd_7543346] using wordTrace_append hprefix tailTrace_7543346
  have hstable : (prefixWord ++ tailWord_7543346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543346).length < 2 ^ (prefixWord ++ tailWord_7543346).sum := by decide
  have hdescent : baseEnd_7543346 < baseStart_7543346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543350 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7543350 : Nat := 118140960795 + 7543350 * 2 ^ 59
def prefixEnd_7543350 : Nat := 4983230072969 + 3 ^ 40 * 7543350 * 2
def baseEnd_7543350 : Nat := 1291121431697722280711257

theorem tailTrace_7543350 : CollatzResearch.WordTrace tailWord_7543350 prefixEnd_7543350 1291121431697722280711257 := by
  unfold tailWord_7543350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195536076358670403636219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183419051481159150972119669 17195536076358670403636219)
  ·
    refine ⟨25793304114538005605454329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195536076358670403636219 25793304114538005605454329)
    ·
      refine ⟨19344978085903504204090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25793304114538005605454329 19344978085903504204090747)
      ·
        refine ⟨29017467128855256306136121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344978085903504204090747 29017467128855256306136121)
        ·
          refine ⟨21763100346641442229602091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29017467128855256306136121 21763100346641442229602091)
          ·
            refine ⟨32644650519962163344403137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21763100346641442229602091 32644650519962163344403137)
            ·
              refine ⟨24483487889971622508302353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32644650519962163344403137 24483487889971622508302353)
              ·
                refine ⟨18362615917478716881226765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24483487889971622508302353 18362615917478716881226765)
                ·
                  refine ⟨6885980969054518830460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18362615917478716881226765 6885980969054518830460037)
                  ·
                    refine ⟨1291121431697722280711257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885980969054518830460037 1291121431697722280711257)
                    ·
                      rfl

theorem cell23_7543350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7543350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543350 prefixEnd_7543350 := by exact prefixLift 7543350
  have htrace : WordTrace (prefixWord ++ tailWord_7543350) baseStart_7543350 baseEnd_7543350 := by
    simpa [prefixWord, tailWord_7543350, baseEnd_7543350] using wordTrace_append hprefix tailTrace_7543350
  have hstable : (prefixWord ++ tailWord_7543350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543350).length < 2 ^ (prefixWord ++ tailWord_7543350).sum := by decide
  have hdescent : baseEnd_7543350 < baseStart_7543350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543367 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 1, 4]
def baseStart_7543367 : Nat := 118140960795 + 7543367 * 2 ^ 59
def prefixEnd_7543367 : Nat := 4983230072969 + 3 ^ 40 * 7543367 * 2
def baseEnd_7543367 : Nat := 1291124341421431091873731

theorem tailTrace_7543367 : CollatzResearch.WordTrace tailWord_7543367 prefixEnd_7543367 1291124341421431091873731 := by
  unfold tailWord_7543367
  simp only [CollatzResearch.WordTrace]
  refine ⟨275129197262677138361548355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183419464841784758907698903 275129197262677138361548355)
  ·
    refine ⟨412693795894015707542322533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275129197262677138361548355 412693795894015707542322533)
    ·
      refine ⟨77380086730127945164185475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412693795894015707542322533 77380086730127945164185475)
      ·
        refine ⟨116070130095191917746278213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77380086730127945164185475 116070130095191917746278213)
        ·
          refine ⟨21763149392848484577427165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116070130095191917746278213 21763149392848484577427165)
          ·
            refine ⟨8161181022318181716535187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21763149392848484577427165 8161181022318181716535187)
            ·
              refine ⟨12241771533477272574802781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161181022318181716535187 12241771533477272574802781)
              ·
                refine ⟨4590664325053977215551043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12241771533477272574802781 4590664325053977215551043)
                ·
                  refine ⟨6885996487580965823326565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590664325053977215551043 6885996487580965823326565)
                  ·
                    refine ⟨1291124341421431091873731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6885996487580965823326565 1291124341421431091873731)
                    ·
                      rfl

theorem cell23_7543367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_7543367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543367 prefixEnd_7543367 := by exact prefixLift 7543367
  have htrace : WordTrace (prefixWord ++ tailWord_7543367) baseStart_7543367 baseEnd_7543367 := by
    simpa [prefixWord, tailWord_7543367, baseEnd_7543367] using wordTrace_append hprefix tailTrace_7543367
  have hstable : (prefixWord ++ tailWord_7543367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543367).length < 2 ^ (prefixWord ++ tailWord_7543367).sum := by decide
  have hdescent : baseEnd_7543367 < baseStart_7543367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543397 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 6]
def baseStart_7543397 : Nat := 118140960795 + 7543397 * 2 ^ 59
def prefixEnd_7543397 : Nat := 4983230072969 + 3 ^ 40 * 7543397 * 2
def baseEnd_7543397 : Nat := 430376492075992017582895

theorem tailTrace_7543397 : CollatzResearch.WordTrace tailWord_7543397 prefixEnd_7543397 430376492075992017582895 := by
  unfold tailWord_7543397
  simp only [CollatzResearch.WordTrace]
  refine ⟨275130291452568453485140445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183420194301712302323426963 275130291452568453485140445)
  ·
    refine ⟨103173859294713170056927667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275130291452568453485140445 103173859294713170056927667)
    ·
      refine ⟨154760788942069755085391501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103173859294713170056927667 154760788942069755085391501)
      ·
        refine ⟨58035295853276158157021813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154760788942069755085391501 58035295853276158157021813)
        ·
          refine ⟨5440808986244639827220795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58035295853276158157021813 5440808986244639827220795)
          ·
            refine ⟨8161213479366959740831193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440808986244639827220795 8161213479366959740831193)
            ·
              refine ⟨6120910109525219805623395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161213479366959740831193 6120910109525219805623395)
              ·
                refine ⟨9181365164287829708435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120910109525219805623395 9181365164287829708435093)
                ·
                  refine ⟨430376492075992017582895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9181365164287829708435093 430376492075992017582895)
                  ·
                    rfl

theorem cell23_7543397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_7543397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543397 prefixEnd_7543397 := by exact prefixLift 7543397
  have htrace : WordTrace (prefixWord ++ tailWord_7543397) baseStart_7543397 baseEnd_7543397 := by
    simpa [prefixWord, tailWord_7543397, baseEnd_7543397] using wordTrace_append hprefix tailTrace_7543397
  have hstable : (prefixWord ++ tailWord_7543397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543397).length < 2 ^ (prefixWord ++ tailWord_7543397).sum := by decide
  have hdescent : baseEnd_7543397 < baseStart_7543397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543416 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_7543416 : Nat := 118140960795 + 7543416 * 2 ^ 59
def prefixEnd_7543416 : Nat := 4983230072969 + 3 ^ 40 * 7543416 * 2
def baseEnd_7543416 : Nat := 3873398184816363583908467

theorem tailTrace_7543416 : CollatzResearch.WordTrace tailWord_7543416 prefixEnd_7543416 3873398184816363583908467 := by
  unfold tailWord_7543416
  simp only [CollatzResearch.WordTrace]
  refine ⟨137565492219749809865041051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183420656292999746486721401 137565492219749809865041051)
  ·
    refine ⟨206348238329624714797561577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137565492219749809865041051 206348238329624714797561577)
    ·
      refine ⟨154761178747218536098171183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206348238329624714797561577 154761178747218536098171183)
      ·
        refine ⟨232141768120827804147256775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154761178747218536098171183 232141768120827804147256775)
        ·
          refine ⟨348212652181241706220885163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232141768120827804147256775 348212652181241706220885163)
          ·
            refine ⟨522318978271862559331327745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348212652181241706220885163 522318978271862559331327745)
            ·
              refine ⟨391739233703896919498495809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522318978271862559331327745 391739233703896919498495809)
              ·
                refine ⟨293804425277922689623871857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391739233703896919498495809 293804425277922689623871857)
                ·
                  refine ⟨220353318958442017217903893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293804425277922689623871857 220353318958442017217903893)
                  ·
                    refine ⟨10329061826176969557089245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 220353318958442017217903893 10329061826176969557089245)
                    ·
                      refine ⟨3873398184816363583908467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329061826176969557089245 3873398184816363583908467)
                      ·
                        rfl

theorem cell23_7543416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_7543416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543416 prefixEnd_7543416 := by exact prefixLift 7543416
  have htrace : WordTrace (prefixWord ++ tailWord_7543416) baseStart_7543416 baseEnd_7543416 := by
    simpa [prefixWord, tailWord_7543416, baseEnd_7543416] using wordTrace_append hprefix tailTrace_7543416
  have hstable : (prefixWord ++ tailWord_7543416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543416).length < 2 ^ (prefixWord ++ tailWord_7543416).sum := by decide
  have hdescent : baseEnd_7543416 < baseStart_7543416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543503 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 8, 2]
def baseStart_7543503 : Nat := 118140960795 + 7543503 * 2 ^ 59
def prefixEnd_7543503 : Nat := 4983230072969 + 3 ^ 40 * 7543503 * 2
def baseEnd_7543503 : Nat := 3873442857633304743520567

theorem tailTrace_7543503 : CollatzResearch.WordTrace tailWord_7543503 prefixEnd_7543503 3873442857633304743520567 := by
  unfold tailWord_7543503
  simp only [CollatzResearch.WordTrace]
  refine ⟨275134157590184433588499163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183422771726789622392332775 275134157590184433588499163)
  ·
    refine ⟨412701236385276650382748745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275134157590184433588499163 412701236385276650382748745)
    ·
      refine ⟨309525927288957487787061559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412701236385276650382748745 309525927288957487787061559)
      ·
        refine ⟨464288890933436231680592339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309525927288957487787061559 464288890933436231680592339)
        ·
          refine ⟨696433336400154347520888509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464288890933436231680592339 696433336400154347520888509)
          ·
            refine ⟨261162501150057880320333191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696433336400154347520888509 261162501150057880320333191)
            ·
              refine ⟨391743751725086820480499787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261162501150057880320333191 391743751725086820480499787)
              ·
                refine ⟨587615627587630230720749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391743751725086820480499787 587615627587630230720749681)
                ·
                  refine ⟨440711720690722673040562261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 587615627587630230720749681 440711720690722673040562261)
                  ·
                    refine ⟨5164590476844406324694089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 440711720690722673040562261 5164590476844406324694089)
                    ·
                      refine ⟨3873442857633304743520567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164590476844406324694089 3873442857633304743520567)
                      ·
                        rfl

theorem cell23_7543503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8, 2].length) (baseStart_7543503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543503 prefixEnd_7543503 := by exact prefixLift 7543503
  have htrace : WordTrace (prefixWord ++ tailWord_7543503) baseStart_7543503 baseEnd_7543503 := by
    simpa [prefixWord, tailWord_7543503, baseEnd_7543503] using wordTrace_append hprefix tailTrace_7543503
  have hstable : (prefixWord ++ tailWord_7543503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543503).length < 2 ^ (prefixWord ++ tailWord_7543503).sum := by decide
  have hdescent : baseEnd_7543503 < baseStart_7543503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543554 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_7543554 : Nat := 118140960795 + 7543554 * 2 ^ 59
def prefixEnd_7543554 : Nat := 4983230072969 + 3 ^ 40 * 7543554 * 2
def baseEnd_7543554 : Nat := 3873469045146684043982833

theorem tailTrace_7543554 : CollatzResearch.WordTrace tailWord_7543554 prefixEnd_7543554 3873469045146684043982833 := by
  unfold tailWord_7543554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68784004428249917324651429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183424011808666446199070477 68784004428249917324651429)
  ·
    refine ⟨12897000830296859498372143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68784004428249917324651429 12897000830296859498372143)
    ·
      refine ⟨19345501245445289247558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12897000830296859498372143 19345501245445289247558215)
      ·
        refine ⟨29018251868167933871337323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19345501245445289247558215 29018251868167933871337323)
        ·
          refine ⟨43527377802251900807005985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29018251868167933871337323 43527377802251900807005985)
          ·
            refine ⟨32645533351688925605254489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43527377802251900807005985 32645533351688925605254489)
            ·
              refine ⟨24484150013766694203940867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32645533351688925605254489 24484150013766694203940867)
              ·
                refine ⟨36726225020650041305911301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24484150013766694203940867 36726225020650041305911301)
                ·
                  refine ⟨6886167191371882744858369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36726225020650041305911301 6886167191371882744858369)
                  ·
                    refine ⟨5164625393528912058643777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886167191371882744858369 5164625393528912058643777)
                    ·
                      refine ⟨3873469045146684043982833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164625393528912058643777 3873469045146684043982833)
                      ·
                        rfl

theorem cell23_7543554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_7543554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543554 prefixEnd_7543554 := by exact prefixLift 7543554
  have htrace : WordTrace (prefixWord ++ tailWord_7543554) baseStart_7543554 baseEnd_7543554 := by
    simpa [prefixWord, tailWord_7543554, baseEnd_7543554] using wordTrace_append hprefix tailTrace_7543554
  have hstable : (prefixWord ++ tailWord_7543554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543554).length < 2 ^ (prefixWord ++ tailWord_7543554).sum := by decide
  have hdescent : baseEnd_7543554 < baseStart_7543554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543560 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 7]
def baseStart_7543560 : Nat := 118140960795 + 7543560 * 2 ^ 59
def prefixEnd_7543560 : Nat := 4983230072969 + 3 ^ 40 * 7543560 * 2
def baseEnd_7543560 : Nat := 430385791781179002278645

theorem tailTrace_7543560 : CollatzResearch.WordTrace tailWord_7543560 prefixEnd_7543560 430385791781179002278645 := by
  unfold tailWord_7543560
  simp only [CollatzResearch.WordTrace]
  refine ⟨137568118275488966161662067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183424157700651954882216089 137568118275488966161662067)
  ·
    refine ⟨206352177413233449242493101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137568118275488966161662067 206352177413233449242493101)
    ·
      refine ⟨77382066529962543465934913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206352177413233449242493101 77382066529962543465934913)
      ·
        refine ⟨58036549897471907599451185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77382066529962543465934913 58036549897471907599451185)
        ·
          refine ⟨43527412423103930699588389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58036549897471907599451185 43527412423103930699588389)
          ·
            refine ⟨8161389829331987006172823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43527412423103930699588389 8161389829331987006172823)
            ·
              refine ⟨12242084743997980509259235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161389829331987006172823 12242084743997980509259235)
              ·
                refine ⟨18363127115996970763888853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12242084743997980509259235 18363127115996970763888853)
                ·
                  refine ⟨430385791781179002278645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18363127115996970763888853 430385791781179002278645)
                  ·
                    rfl

theorem cell23_7543560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_7543560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543560 prefixEnd_7543560 := by exact prefixLift 7543560
  have htrace : WordTrace (prefixWord ++ tailWord_7543560) baseStart_7543560 baseEnd_7543560 := by
    simpa [prefixWord, tailWord_7543560, baseEnd_7543560] using wordTrace_append hprefix tailTrace_7543560
  have hstable : (prefixWord ++ tailWord_7543560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543560).length < 2 ^ (prefixWord ++ tailWord_7543560).sum := by decide
  have hdescent : baseEnd_7543560 < baseStart_7543560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543573 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7543573 : Nat := 118140960795 + 7543573 * 2 ^ 59
def prefixEnd_7543573 : Nat := 4983230072969 + 3 ^ 40 * 7543573 * 2
def baseEnd_7543573 : Nat := 1291159600426373156548415

theorem tailTrace_7543573 : CollatzResearch.WordTrace tailWord_7543573 prefixEnd_7543573 1291159600426373156548415 := by
  unfold tailWord_7543573
  simp only [CollatzResearch.WordTrace]
  refine ⟨275136710699930835543547373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183424473799953890362364915 275136710699930835543547373)
  ·
    refine ⟨103176266512474063328830265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275136710699930835543547373 103176266512474063328830265)
    ·
      refine ⟨77382199884355547496622699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103176266512474063328830265 77382199884355547496622699)
      ·
        refine ⟨116073299826533321244934049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77382199884355547496622699 116073299826533321244934049)
        ·
          refine ⟨87054974869899990933700537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116073299826533321244934049 87054974869899990933700537)
          ·
            refine ⟨65291231152424993200275403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87054974869899990933700537 65291231152424993200275403)
            ·
              refine ⟨97936846728637489800413105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65291231152424993200275403 97936846728637489800413105)
              ·
                refine ⟨73452635046478117350309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97936846728637489800413105 73452635046478117350309829)
                ·
                  refine ⟨13772369071214647003183093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73452635046478117350309829 13772369071214647003183093)
                  ·
                    refine ⟨1291159600426373156548415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13772369071214647003183093 1291159600426373156548415)
                    ·
                      rfl

theorem cell23_7543573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7543573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543573 prefixEnd_7543573 := by exact prefixLift 7543573
  have htrace : WordTrace (prefixWord ++ tailWord_7543573) baseStart_7543573 baseEnd_7543573 := by
    simpa [prefixWord, tailWord_7543573, baseEnd_7543573] using wordTrace_append hprefix tailTrace_7543573
  have hstable : (prefixWord ++ tailWord_7543573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543573).length < 2 ^ (prefixWord ++ tailWord_7543573).sum := by decide
  have hdescent : baseEnd_7543573 < baseStart_7543573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543593 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_7543593 : Nat := 118140960795 + 7543593 * 2 ^ 59
def prefixEnd_7543593 : Nat := 4983230072969 + 3 ^ 40 * 7543593 * 2
def baseEnd_7543593 : Nat := 3873489070892209391395153

theorem tailTrace_7543593 : CollatzResearch.WordTrace tailWord_7543593 prefixEnd_7543593 3873489070892209391395153 := by
  unfold tailWord_7543593
  simp only [CollatzResearch.WordTrace]
  refine ⟨275137440159858378959275433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183424960106572252639516955 275137440159858378959275433)
  ·
    refine ⟨206353080119893784219456575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275137440159858378959275433 206353080119893784219456575)
    ·
      refine ⟨309529620179840676329184863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206353080119893784219456575 309529620179840676329184863)
      ·
        refine ⟨464294430269761014493777295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309529620179840676329184863 464294430269761014493777295)
        ·
          refine ⟨696441645404641521740665943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464294430269761014493777295 696441645404641521740665943)
          ·
            refine ⟨1044662468106962282610998915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696441645404641521740665943 1044662468106962282610998915)
            ·
              refine ⟨1566993702160443423916498373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044662468106962282610998915 1566993702160443423916498373)
              ·
                refine ⟨293811319155083141984343445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1566993702160443423916498373 293811319155083141984343445)
                ·
                  refine ⟨13772405585394522280516099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293811319155083141984343445 13772405585394522280516099)
                  ·
                    refine ⟨20658608378091783420774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13772405585394522280516099 20658608378091783420774149)
                    ·
                      refine ⟨3873489070892209391395153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20658608378091783420774149 3873489070892209391395153)
                      ·
                        rfl

theorem cell23_7543593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_7543593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543593 prefixEnd_7543593 := by exact prefixLift 7543593
  have htrace : WordTrace (prefixWord ++ tailWord_7543593) baseStart_7543593 baseEnd_7543593 := by
    simpa [prefixWord, tailWord_7543593, baseEnd_7543593] using wordTrace_append hprefix tailTrace_7543593
  have hstable : (prefixWord ++ tailWord_7543593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543593).length < 2 ^ (prefixWord ++ tailWord_7543593).sum := by decide
  have hdescent : baseEnd_7543593 < baseStart_7543593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543623 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_7543623 : Nat := 118140960795 + 7543623 * 2 ^ 59
def prefixEnd_7543623 : Nat := 4983230072969 + 3 ^ 40 * 7543623 * 2
def baseEnd_7543623 : Nat := 3873504475311844274020015

theorem tailTrace_7543623 : CollatzResearch.WordTrace tailWord_7543623 prefixEnd_7543623 3873504475311844274020015 := by
  unfold tailWord_7543623
  simp only [CollatzResearch.WordTrace]
  refine ⟨275138534349749694082867523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183425689566499796055245015 275138534349749694082867523)
  ·
    refine ⟨412707801524624541124301285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275138534349749694082867523 412707801524624541124301285)
    ·
      refine ⟨77382712785867101460806491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412707801524624541124301285 77382712785867101460806491)
      ·
        refine ⟨116074069178800652191209737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77382712785867101460806491 116074069178800652191209737)
        ·
          refine ⟨87055551884100489143407303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116074069178800652191209737 87055551884100489143407303)
          ·
            refine ⟨130583327826150733715110955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87055551884100489143407303 130583327826150733715110955)
            ·
              refine ⟨195874991739226100572666433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130583327826150733715110955 195874991739226100572666433)
              ·
                refine ⟨146906243804419575429499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195874991739226100572666433 146906243804419575429499825)
                ·
                  refine ⟨110179682853314681572124869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146906243804419575429499825 110179682853314681572124869)
                  ·
                    refine ⟨20658690534996502794773413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110179682853314681572124869 20658690534996502794773413)
                    ·
                      refine ⟨3873504475311844274020015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20658690534996502794773413 3873504475311844274020015)
                      ·
                        rfl

theorem cell23_7543623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_7543623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543623 prefixEnd_7543623 := by exact prefixLift 7543623
  have htrace : WordTrace (prefixWord ++ tailWord_7543623) baseStart_7543623 baseEnd_7543623 := by
    simpa [prefixWord, tailWord_7543623, baseEnd_7543623] using wordTrace_append hprefix tailTrace_7543623
  have hstable : (prefixWord ++ tailWord_7543623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543623).length < 2 ^ (prefixWord ++ tailWord_7543623).sum := by decide
  have hdescent : baseEnd_7543623 < baseStart_7543623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543630 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_7543630 : Nat := 118140960795 + 7543630 * 2 ^ 59
def prefixEnd_7543630 : Nat := 4983230072969 + 3 ^ 40 * 7543630 * 2
def baseEnd_7543630 : Nat := 3873508069676425746632483

theorem tailTrace_7543630 : CollatzResearch.WordTrace tailWord_7543630 prefixEnd_7543630 3873508069676425746632483 := by
  unfold tailWord_7543630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34392348707590541784796543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183425859773816222852248229 34392348707590541784796543)
  ·
    refine ⟨51588523061385812677194815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34392348707590541784796543 51588523061385812677194815)
    ·
      refine ⟨77382784592078719015792223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51588523061385812677194815 77382784592078719015792223)
      ·
        refine ⟨116074176888118078523688335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77382784592078719015792223 116074176888118078523688335)
        ·
          refine ⟨174111265332177117785532503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116074176888118078523688335 174111265332177117785532503)
          ·
            refine ⟨261166897998265676678298755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174111265332177117785532503 261166897998265676678298755)
            ·
              refine ⟨391750346997398515017448133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261166897998265676678298755 391750346997398515017448133)
              ·
                refine ⟨73453190062012221565771525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391750346997398515017448133 73453190062012221565771525)
                ·
                  refine ⟨13772473136627291543582161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73453190062012221565771525 13772473136627291543582161)
                  ·
                    refine ⟨10329354852470468657686621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13772473136627291543582161 10329354852470468657686621)
                    ·
                      refine ⟨3873508069676425746632483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329354852470468657686621 3873508069676425746632483)
                      ·
                        rfl

theorem cell23_7543630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_7543630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543630 prefixEnd_7543630 := by exact prefixLift 7543630
  have htrace : WordTrace (prefixWord ++ tailWord_7543630) baseStart_7543630 baseEnd_7543630 := by
    simpa [prefixWord, tailWord_7543630, baseEnd_7543630] using wordTrace_append hprefix tailTrace_7543630
  have hstable : (prefixWord ++ tailWord_7543630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543630).length < 2 ^ (prefixWord ++ tailWord_7543630).sum := by decide
  have hdescent : baseEnd_7543630 < baseStart_7543630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543644 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7543644 : Nat := 118140960795 + 7543644 * 2 ^ 59
def prefixEnd_7543644 : Nat := 4983230072969 + 3 ^ 40 * 7543644 * 2
def baseEnd_7543644 : Nat := 3873515258405588691857419

theorem tailTrace_7543644 : CollatzResearch.WordTrace tailWord_7543644 prefixEnd_7543644 3873515258405588691857419 := by
  unfold tailWord_7543644
  simp only [CollatzResearch.WordTrace]
  refine ⟨137569650141336807334690993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183426200188449076446254657 137569650141336807334690993)
  ·
    refine ⟨103177237606002605501018245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137569650141336807334690993 103177237606002605501018245)
    ·
      refine ⟨19345732051125488531440921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103177237606002605501018245 19345732051125488531440921)
      ·
        refine ⟨14509299038344116398580691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19345732051125488531440921 14509299038344116398580691)
        ·
          refine ⟨21763948557516174597871037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509299038344116398580691 21763948557516174597871037)
          ·
            refine ⟨8161480709068565474201639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21763948557516174597871037 8161480709068565474201639)
            ·
              refine ⟨12242221063602848211302459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161480709068565474201639 12242221063602848211302459)
              ·
                refine ⟨18363331595404272316953689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12242221063602848211302459 18363331595404272316953689)
                ·
                  refine ⟨13772498696553204237715267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18363331595404272316953689 13772498696553204237715267)
                  ·
                    refine ⟨20658748044829806356572901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13772498696553204237715267 20658748044829806356572901)
                    ·
                      refine ⟨3873515258405588691857419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20658748044829806356572901 3873515258405588691857419)
                      ·
                        rfl

theorem cell23_7543644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7543644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543644 prefixEnd_7543644 := by exact prefixLift 7543644
  have htrace : WordTrace (prefixWord ++ tailWord_7543644) baseStart_7543644 baseEnd_7543644 := by
    simpa [prefixWord, tailWord_7543644, baseEnd_7543644] using wordTrace_append hprefix tailTrace_7543644
  have hstable : (prefixWord ++ tailWord_7543644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543644).length < 2 ^ (prefixWord ++ tailWord_7543644).sum := by decide
  have hdescent : baseEnd_7543644 < baseStart_7543644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543677 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_7543677 : Nat := 118140960795 + 7543677 * 2 ^ 59
def prefixEnd_7543677 : Nat := 4983230072969 + 3 ^ 40 * 7543677 * 2
def baseEnd_7543677 : Nat := 3873532203267187062744767

theorem tailTrace_7543677 : CollatzResearch.WordTrace tailWord_7543677 prefixEnd_7543677 3873532203267187062744767 := by
  unfold tailWord_7543677
  simp only [CollatzResearch.WordTrace]
  refine ⟨275140503891554061305333285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183427002594369374203555523 275140503891554061305333285)
  ·
    refine ⟨51588844479666386494749991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275140503891554061305333285 51588844479666386494749991)
    ·
      refine ⟨77383266719499579742124987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51588844479666386494749991 77383266719499579742124987)
      ·
        refine ⟨116074900079249369613187481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77383266719499579742124987 116074900079249369613187481)
        ·
          refine ⟨87056175059437027209890611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116074900079249369613187481 87056175059437027209890611)
          ·
            refine ⟨130584262589155540814835917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87056175059437027209890611 130584262589155540814835917)
            ·
              refine ⟨48969098470933327805563469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130584262589155540814835917 48969098470933327805563469)
              ·
                refine ⟨18363411926599997927086301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48969098470933327805563469 18363411926599997927086301)
                ·
                  refine ⟨6886279472474999222657363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18363411926599997927086301 6886279472474999222657363)
                  ·
                    refine ⟨10329419208712498833986045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886279472474999222657363 10329419208712498833986045)
                    ·
                      refine ⟨3873532203267187062744767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329419208712498833986045 3873532203267187062744767)
                      ·
                        rfl

theorem cell23_7543677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_7543677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543677 prefixEnd_7543677 := by exact prefixLift 7543677
  have htrace : WordTrace (prefixWord ++ tailWord_7543677) baseStart_7543677 baseEnd_7543677 := by
    simpa [prefixWord, tailWord_7543677, baseEnd_7543677] using wordTrace_append hprefix tailTrace_7543677
  have hstable : (prefixWord ++ tailWord_7543677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543677).length < 2 ^ (prefixWord ++ tailWord_7543677).sum := by decide
  have hdescent : baseEnd_7543677 < baseStart_7543677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543687 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_7543687 : Nat := 118140960795 + 7543687 * 2 ^ 59
def prefixEnd_7543687 : Nat := 4983230072969 + 3 ^ 40 * 7543687 * 2
def baseEnd_7543687 : Nat := 3873537338073732023619721

theorem tailTrace_7543687 : CollatzResearch.WordTrace tailWord_7543687 prefixEnd_7543687 3873537338073732023619721 := by
  unfold tailWord_7543687
  simp only [CollatzResearch.WordTrace]
  refine ⟨275140868621517833013197315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183427245747678555342131543 275140868621517833013197315)
  ·
    refine ⟨412711302932276749519795973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275140868621517833013197315 412711302932276749519795973)
    ·
      refine ⟨77383369299801890534961745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412711302932276749519795973 77383369299801890534961745)
      ·
        refine ⟨58037526974851417901221309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77383369299801890534961745 58037526974851417901221309)
        ·
          refine ⟨21764072615569281712957991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58037526974851417901221309 21764072615569281712957991)
          ·
            refine ⟨32646108923353922569436987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21764072615569281712957991 32646108923353922569436987)
            ·
              refine ⟨48969163385030883854155481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32646108923353922569436987 48969163385030883854155481)
              ·
                refine ⟨36726872538773162890616611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48969163385030883854155481 36726872538773162890616611)
                ·
                  refine ⟨55090308808159744335924917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36726872538773162890616611 55090308808159744335924917)
                  ·
                    refine ⟨5164716450764976031492961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55090308808159744335924917 5164716450764976031492961)
                    ·
                      refine ⟨3873537338073732023619721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164716450764976031492961 3873537338073732023619721)
                      ·
                        rfl

theorem cell23_7543687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_7543687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543687 prefixEnd_7543687 := by exact prefixLift 7543687
  have htrace : WordTrace (prefixWord ++ tailWord_7543687) baseStart_7543687 baseEnd_7543687 := by
    simpa [prefixWord, tailWord_7543687, baseEnd_7543687] using wordTrace_append hprefix tailTrace_7543687
  have hstable : (prefixWord ++ tailWord_7543687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543687).length < 2 ^ (prefixWord ++ tailWord_7543687).sum := by decide
  have hdescent : baseEnd_7543687 < baseStart_7543687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543711 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7543711 : Nat := 118140960795 + 7543711 * 2 ^ 59
def prefixEnd_7543711 : Nat := 4983230072969 + 3 ^ 40 * 7543711 * 2
def baseEnd_7543711 : Nat := 3873549661609439929719611

theorem tailTrace_7543711 : CollatzResearch.WordTrace tailWord_7543711 prefixEnd_7543711 3873549661609439929719611 := by
  unfold tailWord_7543711
  simp only [CollatzResearch.WordTrace]
  refine ⟨275141743973430885112070987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183427829315620590074713991 275141743973430885112070987)
  ·
    refine ⟨412712615960146327668106481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275141743973430885112070987 412712615960146327668106481)
    ·
      refine ⟨309534461970109745751079861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412712615960146327668106481 309534461970109745751079861)
      ·
        refine ⟨29018855809697788664163737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309534461970109745751079861 29018855809697788664163737)
        ·
          refine ⟨21764141857273341498122803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29018855809697788664163737 21764141857273341498122803)
          ·
            refine ⟨32646212785910012247184205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21764141857273341498122803 32646212785910012247184205)
            ·
              refine ⟨12242329794716254592694077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32646212785910012247184205 12242329794716254592694077)
              ·
                refine ⟨4590873673018595472260279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12242329794716254592694077 4590873673018595472260279)
                ·
                  refine ⟨6886310509527893208390419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590873673018595472260279 6886310509527893208390419)
                  ·
                    refine ⟨10329465764291839812585629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886310509527893208390419 10329465764291839812585629)
                    ·
                      refine ⟨3873549661609439929719611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329465764291839812585629 3873549661609439929719611)
                      ·
                        rfl

theorem cell23_7543711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7543711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543711 prefixEnd_7543711 := by exact prefixLift 7543711
  have htrace : WordTrace (prefixWord ++ tailWord_7543711) baseStart_7543711 baseEnd_7543711 := by
    simpa [prefixWord, tailWord_7543711, baseEnd_7543711] using wordTrace_append hprefix tailTrace_7543711
  have hstable : (prefixWord ++ tailWord_7543711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543711).length < 2 ^ (prefixWord ++ tailWord_7543711).sum := by decide
  have hdescent : baseEnd_7543711 < baseStart_7543711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543744 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_7543744 : Nat := 118140960795 + 7543744 * 2 ^ 59
def prefixEnd_7543744 : Nat := 4983230072969 + 3 ^ 40 * 7543744 * 2
def baseEnd_7543744 : Nat := 1291188868823679433535653

theorem tailTrace_7543744 : CollatzResearch.WordTrace tailWord_7543744 prefixEnd_7543744 1291188868823679433535653 := by
  unfold tailWord_7543744
  simp only [CollatzResearch.WordTrace]
  refine ⟨137571473791155665874011143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183428631721540887832014857 137571473791155665874011143)
  ·
    refine ⟨206357210686733498811016715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137571473791155665874011143 206357210686733498811016715)
    ·
      refine ⟨309535816030100248216525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206357210686733498811016715 309535816030100248216525073)
      ·
        refine ⟨232151862022575186162393805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309535816030100248216525073 232151862022575186162393805)
        ·
          refine ⟨87056948258465694810897677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232151862022575186162393805 87056948258465694810897677)
          ·
            refine ⟨32646355596924635554086629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87056948258465694810897677 32646355596924635554086629)
            ·
              refine ⟨6121191674423369166391243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32646355596924635554086629 6121191674423369166391243)
              ·
                refine ⟨9181787511635053749586865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121191674423369166391243 9181787511635053749586865)
                ·
                  refine ⟨6886340633726290312190149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9181787511635053749586865 6886340633726290312190149)
                  ·
                    refine ⟨1291188868823679433535653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886340633726290312190149 1291188868823679433535653)
                    ·
                      rfl

theorem cell23_7543744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_7543744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543744 prefixEnd_7543744 := by exact prefixLift 7543744
  have htrace : WordTrace (prefixWord ++ tailWord_7543744) baseStart_7543744 baseEnd_7543744 := by
    simpa [prefixWord, tailWord_7543744, baseEnd_7543744] using wordTrace_append hprefix tailTrace_7543744
  have hstable : (prefixWord ++ tailWord_7543744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543744).length < 2 ^ (prefixWord ++ tailWord_7543744).sum := by decide
  have hdescent : baseEnd_7543744 < baseStart_7543744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543748 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7543748 : Nat := 118140960795 + 7543748 * 2 ^ 59
def prefixEnd_7543748 : Nat := 4983230072969 + 3 ^ 40 * 7543748 * 2
def baseEnd_7543748 : Nat := 1291189553464552094985647

theorem tailTrace_7543748 : CollatzResearch.WordTrace tailWord_7543748 prefixEnd_7543748 1291189553464552094985647 := by
  unfold tailWord_7543748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137571546737148420215583949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183428728982864560287445265 137571546737148420215583949)
  ·
    refine ⟨51589330026430657580843981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137571546737148420215583949 51589330026430657580843981)
    ·
      refine ⟨19345998759911496592816493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51589330026430657580843981 19345998759911496592816493)
      ·
        refine ⟨7254749534966811222306185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19345998759911496592816493 7254749534966811222306185)
        ·
          refine ⟨5441062151225108416729639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254749534966811222306185 5441062151225108416729639)
          ·
            refine ⟨8161593226837662625094459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441062151225108416729639 8161593226837662625094459)
            ·
              refine ⟨12242389840256493937641689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161593226837662625094459 12242389840256493937641689)
              ·
                refine ⟨9181792380192370453231267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12242389840256493937641689 9181792380192370453231267)
                ·
                  refine ⟨13772688570288555679846901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9181792380192370453231267 13772688570288555679846901)
                  ·
                    refine ⟨1291189553464552094985647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13772688570288555679846901 1291189553464552094985647)
                    ·
                      rfl

theorem cell23_7543748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7543748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543748 prefixEnd_7543748 := by exact prefixLift 7543748
  have htrace : WordTrace (prefixWord ++ tailWord_7543748) baseStart_7543748 baseEnd_7543748 := by
    simpa [prefixWord, tailWord_7543748, baseEnd_7543748] using wordTrace_append hprefix tailTrace_7543748
  have hstable : (prefixWord ++ tailWord_7543748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543748).length < 2 ^ (prefixWord ++ tailWord_7543748).sum := by decide
  have hdescent : baseEnd_7543748 < baseStart_7543748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543767 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_7543767 : Nat := 118140960795 + 7543767 * 2 ^ 59
def prefixEnd_7543767 : Nat := 4983230072969 + 3 ^ 40 * 7543767 * 2
def baseEnd_7543767 : Nat := 3873578416526091710619353

theorem tailTrace_7543767 : CollatzResearch.WordTrace tailWord_7543767 prefixEnd_7543767 3873578416526091710619353 := by
  unfold tailWord_7543767
  simp only [CollatzResearch.WordTrace]
  refine ⟨275143786461228006676109555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183429190974152004450739703 275143786461228006676109555)
  ·
    refine ⟨412715679691842010014164333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275143786461228006676109555 412715679691842010014164333)
    ·
      refine ⟨154768379884440753755311625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412715679691842010014164333 154768379884440753755311625)
      ·
        refine ⟨116076284913330565316483719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154768379884440753755311625 116076284913330565316483719)
        ·
          refine ⟨174114427369995847974725579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116076284913330565316483719 174114427369995847974725579)
          ·
            refine ⟨261171641054993771962088369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174114427369995847974725579 261171641054993771962088369)
            ·
              refine ⟨195878730791245328971566277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261171641054993771962088369 195878730791245328971566277)
              ·
                refine ⟨36727262023358499182168677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195878730791245328971566277 36727262023358499182168677)
                ·
                  refine ⟨6886361629379718596656627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36727262023358499182168677 6886361629379718596656627)
                  ·
                    refine ⟨10329542444069577894984941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886361629379718596656627 10329542444069577894984941)
                    ·
                      refine ⟨3873578416526091710619353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329542444069577894984941 3873578416526091710619353)
                      ·
                        rfl

theorem cell23_7543767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_7543767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543767 prefixEnd_7543767 := by exact prefixLift 7543767
  have htrace : WordTrace (prefixWord ++ tailWord_7543767) baseStart_7543767 baseEnd_7543767 := by
    simpa [prefixWord, tailWord_7543767, baseEnd_7543767] using wordTrace_append hprefix tailTrace_7543767
  have hstable : (prefixWord ++ tailWord_7543767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543767).length < 2 ^ (prefixWord ++ tailWord_7543767).sum := by decide
  have hdescent : baseEnd_7543767 < baseStart_7543767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543784 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7543784 : Nat := 118140960795 + 7543784 * 2 ^ 59
def prefixEnd_7543784 : Nat := 4983230072969 + 3 ^ 40 * 7543784 * 2
def baseEnd_7543784 : Nat := 3873587145697218144106775

theorem tailTrace_7543784 : CollatzResearch.WordTrace tailWord_7543784 prefixEnd_7543784 3873587145697218144106775 := by
  unfold tailWord_7543784
  simp only [CollatzResearch.WordTrace]
  refine ⟨137572203251083209289739203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183429604334777612386318937 137572203251083209289739203)
  ·
    refine ⟨206358304876624813934608805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137572203251083209289739203 206358304876624813934608805)
    ·
      refine ⟨38692182164367152612739151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206358304876624813934608805 38692182164367152612739151)
      ·
        refine ⟨58038273246550728919108727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38692182164367152612739151 58038273246550728919108727)
        ·
          refine ⟨87057409869826093378663091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58038273246550728919108727 87057409869826093378663091)
          ·
            refine ⟨130586114804739140067994637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87057409869826093378663091 130586114804739140067994637)
            ·
              refine ⟨48969793051777177525497989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130586114804739140067994637 48969793051777177525497989)
              ·
                refine ⟨9181836197208220786030873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48969793051777177525497989 9181836197208220786030873)
                ·
                  refine ⟨6886377147906165589523155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9181836197208220786030873 6886377147906165589523155)
                  ·
                    refine ⟨10329565721859248384284733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886377147906165589523155 10329565721859248384284733)
                    ·
                      refine ⟨3873587145697218144106775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329565721859248384284733 3873587145697218144106775)
                      ·
                        rfl

theorem cell23_7543784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7543784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543784 prefixEnd_7543784 := by exact prefixLift 7543784
  have htrace : WordTrace (prefixWord ++ tailWord_7543784) baseStart_7543784 baseEnd_7543784 := by
    simpa [prefixWord, tailWord_7543784, baseEnd_7543784] using wordTrace_append hprefix tailTrace_7543784
  have hstable : (prefixWord ++ tailWord_7543784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543784).length < 2 ^ (prefixWord ++ tailWord_7543784).sum := by decide
  have hdescent : baseEnd_7543784 < baseStart_7543784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543841 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7543841 : Nat := 118140960795 + 7543841 * 2 ^ 59
def prefixEnd_7543841 : Nat := 4983230072969 + 3 ^ 40 * 7543841 * 2
def baseEnd_7543841 : Nat := 3873616414094524421094013

theorem tailTrace_7543841 : CollatzResearch.WordTrace tailWord_7543841 prefixEnd_7543841 3873616414094524421094013 := by
  unfold tailWord_7543841
  simp only [CollatzResearch.WordTrace]
  refine ⟨275146485462959917314303377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183430990308639944876202251 275146485462959917314303377)
  ·
    refine ⟨206359864097219937985727533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275146485462959917314303377 206359864097219937985727533)
    ·
      refine ⟨77384949036457476744647825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206359864097219937985727533 77384949036457476744647825)
      ·
        refine ⟨58038711777343107558485869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77384949036457476744647825 58038711777343107558485869)
        ·
          refine ⟨21764516916503665334432201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58038711777343107558485869 21764516916503665334432201)
          ·
            refine ⟨16323387687377749000824151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21764516916503665334432201 16323387687377749000824151)
            ·
              refine ⟨24485081531066623501236227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16323387687377749000824151 24485081531066623501236227)
              ·
                refine ⟨36727622296599935251854341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24485081531066623501236227 36727622296599935251854341)
                ·
                  refine ⟨6886429180612487859722689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36727622296599935251854341 6886429180612487859722689)
                  ·
                    refine ⟨5164821885459365894792017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886429180612487859722689 5164821885459365894792017)
                    ·
                      refine ⟨3873616414094524421094013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164821885459365894792017 3873616414094524421094013)
                      ·
                        rfl

theorem cell23_7543841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7543841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543841 prefixEnd_7543841 := by exact prefixLift 7543841
  have htrace : WordTrace (prefixWord ++ tailWord_7543841) baseStart_7543841 baseEnd_7543841 := by
    simpa [prefixWord, tailWord_7543841, baseEnd_7543841] using wordTrace_append hprefix tailTrace_7543841
  have hstable : (prefixWord ++ tailWord_7543841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543841).length < 2 ^ (prefixWord ++ tailWord_7543841).sum := by decide
  have hdescent : baseEnd_7543841 < baseStart_7543841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543857 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_7543857 : Nat := 118140960795 + 7543857 * 2 ^ 59
def prefixEnd_7543857 : Nat := 4983230072969 + 3 ^ 40 * 7543857 * 2
def baseEnd_7543857 : Nat := 3873624629784996358493939

theorem tailTrace_7543857 : CollatzResearch.WordTrace tailWord_7543857 prefixEnd_7543857 3873624629784996358493939 := by
  unfold tailWord_7543857
  simp only [CollatzResearch.WordTrace]
  refine ⟨275147069030901952046885825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183431379353934634697923883 275147069030901952046885825)
  ·
    refine ⟨206360301773176464035164369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275147069030901952046885825 206360301773176464035164369)
    ·
      refine ⟨154770226329882348026373277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206360301773176464035164369 154770226329882348026373277)
      ·
        refine ⟨58038834873705880509889979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154770226329882348026373277 58038834873705880509889979)
        ·
          refine ⟨87058252310558820764834969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58038834873705880509889979 87058252310558820764834969)
          ·
            refine ⟨65293689232919115573626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87058252310558820764834969 65293689232919115573626227)
            ·
              refine ⟨97940533849378673360439341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65293689232919115573626227 97940533849378673360439341)
              ·
                refine ⟨36727700193517002510164753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97940533849378673360439341 36727700193517002510164753)
                ·
                  refine ⟨27545775145137751882623565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36727700193517002510164753 27545775145137751882623565)
                  ·
                    refine ⟨10329665679426656955983837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27545775145137751882623565 10329665679426656955983837)
                    ·
                      refine ⟨3873624629784996358493939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329665679426656955983837 3873624629784996358493939)
                      ·
                        rfl

theorem cell23_7543857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_7543857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543857 prefixEnd_7543857 := by exact prefixLift 7543857
  have htrace : WordTrace (prefixWord ++ tailWord_7543857) baseStart_7543857 baseEnd_7543857 := by
    simpa [prefixWord, tailWord_7543857, baseEnd_7543857] using wordTrace_append hprefix tailTrace_7543857
  have hstable : (prefixWord ++ tailWord_7543857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543857).length < 2 ^ (prefixWord ++ tailWord_7543857).sum := by decide
  have hdescent : baseEnd_7543857 < baseStart_7543857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543858 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_7543858 : Nat := 118140960795 + 7543858 * 2 ^ 59
def prefixEnd_7543858 : Nat := 4983230072969 + 3 ^ 40 * 7543858 * 2
def baseEnd_7543858 : Nat := 3873625143265650854581435

theorem tailTrace_7543858 : CollatzResearch.WordTrace tailWord_7543858 prefixEnd_7543858 3873625143265650854581435 := by
  unfold tailWord_7543858
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786776375974582304418057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183431403669265552811781485 68786776375974582304418057)
  ·
    refine ⟨51590082281980936728313543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68786776375974582304418057 51590082281980936728313543)
    ·
      refine ⟨77385123422971405092470315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51590082281980936728313543 77385123422971405092470315)
      ·
        refine ⟨116077685134457107638705473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77385123422971405092470315 116077685134457107638705473)
        ·
          refine ⟨87058263850842830729029105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116077685134457107638705473 87058263850842830729029105)
          ·
            refine ⟨65293697888132123046771829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87058263850842830729029105 65293697888132123046771829)
            ·
              refine ⟨6121284177012386535634859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65293697888132123046771829 6121284177012386535634859)
              ·
                refine ⟨9181926265518579803452289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121284177012386535634859 9181926265518579803452289)
                ·
                  refine ⟨6886444699138934852589217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9181926265518579803452289 6886444699138934852589217)
                  ·
                    refine ⟨5164833524354201139441913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886444699138934852589217 5164833524354201139441913)
                    ·
                      refine ⟨3873625143265650854581435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164833524354201139441913 3873625143265650854581435)
                      ·
                        rfl

theorem cell23_7543858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_7543858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543858 prefixEnd_7543858 := by exact prefixLift 7543858
  have htrace : WordTrace (prefixWord ++ tailWord_7543858) baseStart_7543858 baseEnd_7543858 := by
    simpa [prefixWord, tailWord_7543858, baseEnd_7543858] using wordTrace_append hprefix tailTrace_7543858
  have hstable : (prefixWord ++ tailWord_7543858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543858).length < 2 ^ (prefixWord ++ tailWord_7543858).sum := by decide
  have hdescent : baseEnd_7543858 < baseStart_7543858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7543954 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_7543954 : Nat := 118140960795 + 7543954 * 2 ^ 59
def prefixEnd_7543954 : Nat := 4983230072969 + 3 ^ 40 * 7543954 * 2
def baseEnd_7543954 : Nat := 430408270823164719886777

theorem tailTrace_7543954 : CollatzResearch.WordTrace tailWord_7543954 prefixEnd_7543954 430408270823164719886777 := by
  unfold tailWord_7543954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68787651727887634403291729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183433737941033691742111277 68787651727887634403291729)
  ·
    refine ⟨51590738795915725802468797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68787651727887634403291729 51590738795915725802468797)
    ·
      refine ⟨19346527048468397175925799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51590738795915725802468797 19346527048468397175925799)
      ·
        refine ⟨29019790572702595763888699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19346527048468397175925799 29019790572702595763888699)
        ·
          refine ⟨43529685859053893645833049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29019790572702595763888699 43529685859053893645833049)
          ·
            refine ⟨32647264394290420234374787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43529685859053893645833049 32647264394290420234374787)
            ·
              refine ⟨48970896591435630351562181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32647264394290420234374787 48970896591435630351562181)
              ·
                refine ⟨9182043110894180690917909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48970896591435630351562181 9182043110894180690917909)
                ·
                  refine ⟨430408270823164719886777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9182043110894180690917909 430408270823164719886777)
                  ·
                    rfl

theorem cell23_7543954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_7543954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7543954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7543954 prefixEnd_7543954 := by exact prefixLift 7543954
  have htrace : WordTrace (prefixWord ++ tailWord_7543954) baseStart_7543954 baseEnd_7543954 := by
    simpa [prefixWord, tailWord_7543954, baseEnd_7543954] using wordTrace_append hprefix tailTrace_7543954
  have hstable : (prefixWord ++ tailWord_7543954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7543954).length < 2 ^ (prefixWord ++ tailWord_7543954).sum := by decide
  have hdescent : baseEnd_7543954 < baseStart_7543954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7543954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_7544007 : Nat := 118140960795 + 7544007 * 2 ^ 59
def prefixEnd_7544007 : Nat := 4983230072969 + 3 ^ 40 * 7544007 * 2
def baseEnd_7544007 : Nat := 3873701651883170771618249

theorem tailTrace_7544007 : CollatzResearch.WordTrace tailWord_7544007 prefixEnd_7544007 3873701651883170771618249 := by
  unfold tailWord_7544007
  simp only [CollatzResearch.WordTrace]
  refine ⟨275152539980358527664846275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183435026653572351776564183 275152539980358527664846275)
  ·
    refine ⟨412728809970537791497269413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275152539980358527664846275 412728809970537791497269413)
    ·
      refine ⟨77386651869475835905738015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412728809970537791497269413 77386651869475835905738015)
      ·
        refine ⟨116079977804213753858607023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77386651869475835905738015 116079977804213753858607023)
        ·
          refine ⟨174119966706320630787910535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116079977804213753858607023 174119966706320630787910535)
          ·
            refine ⟨261179950059480946181865803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174119966706320630787910535 261179950059480946181865803)
            ·
              refine ⟨391769925089221419272798705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261179950059480946181865803 391769925089221419272798705)
              ·
                refine ⟨293827443816916064454599029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391769925089221419272798705 293827443816916064454599029)
                ·
                  refine ⟨27546322857835881042618659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293827443816916064454599029 27546322857835881042618659)
                  ·
                    refine ⟨41319484286753821563927989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27546322857835881042618659 41319484286753821563927989)
                    ·
                      refine ⟨3873701651883170771618249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41319484286753821563927989 3873701651883170771618249)
                      ·
                        rfl

theorem cell23_7544007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_7544007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544007 prefixEnd_7544007 := by exact prefixLift 7544007
  have htrace : WordTrace (prefixWord ++ tailWord_7544007) baseStart_7544007 baseEnd_7544007 := by
    simpa [prefixWord, tailWord_7544007, baseEnd_7544007] using wordTrace_append hprefix tailTrace_7544007
  have hstable : (prefixWord ++ tailWord_7544007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544007).length < 2 ^ (prefixWord ++ tailWord_7544007).sum := by decide
  have hdescent : baseEnd_7544007 < baseStart_7544007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544017 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_7544017 : Nat := 118140960795 + 7544017 * 2 ^ 59
def prefixEnd_7544017 : Nat := 4983230072969 + 3 ^ 40 * 7544017 * 2
def baseEnd_7544017 : Nat := 3873706786689715732493203

theorem tailTrace_7544017 : CollatzResearch.WordTrace tailWord_7544017 prefixEnd_7544017 3873706786689715732493203 := by
  unfold tailWord_7544017
  simp only [CollatzResearch.WordTrace]
  refine ⟨275152904710322299372710305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183435269806881532915140203 275152904710322299372710305)
  ·
    refine ⟨206364678532741724529532729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275152904710322299372710305 206364678532741724529532729)
    ·
      refine ⟨154773508899556293397149547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206364678532741724529532729 154773508899556293397149547)
      ·
        refine ⟨232160263349334440095724321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154773508899556293397149547 232160263349334440095724321)
        ·
          refine ⟨174120197512000830071793241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232160263349334440095724321 174120197512000830071793241)
          ·
            refine ⟨130590148134000622553844931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174120197512000830071793241 130590148134000622553844931)
            ·
              refine ⟨195885222201000933830767397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130590148134000622553844931 195885222201000933830767397)
              ·
                refine ⟨36728479162687675093268887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195885222201000933830767397 36728479162687675093268887)
                ·
                  refine ⟨55092718744031512639903331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36728479162687675093268887 55092718744031512639903331)
                  ·
                    refine ⟨82639078116047268959854997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55092718744031512639903331 82639078116047268959854997)
                    ·
                      refine ⟨3873706786689715732493203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82639078116047268959854997 3873706786689715732493203)
                      ·
                        rfl

theorem cell23_7544017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_7544017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544017 prefixEnd_7544017 := by exact prefixLift 7544017
  have htrace : WordTrace (prefixWord ++ tailWord_7544017) baseStart_7544017 baseEnd_7544017 := by
    simpa [prefixWord, tailWord_7544017, baseEnd_7544017] using wordTrace_append hprefix tailTrace_7544017
  have hstable : (prefixWord ++ tailWord_7544017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544017).length < 2 ^ (prefixWord ++ tailWord_7544017).sum := by decide
  have hdescent : baseEnd_7544017 < baseStart_7544017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544044 : List Nat := [2, 2, 1, 1, 2, 4, 4, 7]
def baseStart_7544044 : Nat := 118140960795 + 7544044 * 2 ^ 59
def prefixEnd_7544044 : Nat := 4983230072969 + 3 ^ 40 * 7544044 * 2
def baseEnd_7544044 : Nat := 143471135209903226920577

theorem tailTrace_7544044 : CollatzResearch.WordTrace tailWord_7544044 prefixEnd_7544044 143471135209903226920577 := by
  unfold tailWord_7544044
  simp only [CollatzResearch.WordTrace]
  refine ⟨137576944740612241491971593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183435926320816321989295457 137576944740612241491971593)
  ·
    refine ⟨103182708555459181118978695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137576944740612241491971593 103182708555459181118978695)
    ·
      refine ⟨154774062833188771678468043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103182708555459181118978695 154774062833188771678468043)
      ·
        refine ⟨232161094249783157517702065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154774062833188771678468043 232161094249783157517702065)
        ·
          refine ⟨174120820687337368138276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232161094249783157517702065 174120820687337368138276549)
          ·
            refine ⟨32647653878875756525926853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174120820687337368138276549 32647653878875756525926853)
            ·
              refine ⟨6121435102289204348611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32647653878875756525926853 6121435102289204348611285)
              ·
                refine ⟨143471135209903226920577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6121435102289204348611285 143471135209903226920577)
                ·
                  rfl

theorem cell23_7544044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 7].length) (baseStart_7544044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544044 prefixEnd_7544044 := by exact prefixLift 7544044
  have htrace : WordTrace (prefixWord ++ tailWord_7544044) baseStart_7544044 baseEnd_7544044 := by
    simpa [prefixWord, tailWord_7544044, baseEnd_7544044] using wordTrace_append hprefix tailTrace_7544044
  have hstable : (prefixWord ++ tailWord_7544044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544044).length < 2 ^ (prefixWord ++ tailWord_7544044).sum := by decide
  have hdescent : baseEnd_7544044 < baseStart_7544044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544072 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_7544072 : Nat := 118140960795 + 7544072 * 2 ^ 59
def prefixEnd_7544072 : Nat := 4983230072969 + 3 ^ 40 * 7544072 * 2
def baseEnd_7544072 : Nat := 3873735028125713017305451

theorem tailTrace_7544072 : CollatzResearch.WordTrace tailWord_7544072 prefixEnd_7544072 3873735028125713017305451 := by
  unfold tailWord_7544072
  simp only [CollatzResearch.WordTrace]
  refine ⟨137577455362561521882981235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183436607150082029177308313 137577455362561521882981235)
  ·
    refine ⟨206366183043842282824471853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137577455362561521882981235 206366183043842282824471853)
    ·
      refine ⟨77387318641440856059176945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206366183043842282824471853 77387318641440856059176945)
      ·
        refine ⟨58040488981080642044382709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77387318641440856059176945 58040488981080642044382709)
        ·
          refine ⟨5441295841976310191660879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58040488981080642044382709 5441295841976310191660879)
          ·
            refine ⟨8161943762964465287491319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441295841976310191660879 8161943762964465287491319)
            ·
              refine ⟨12242915644446697931236979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8161943762964465287491319 12242915644446697931236979)
              ·
                refine ⟨18364373466670046896855469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12242915644446697931236979 18364373466670046896855469)
                ·
                  refine ⟨6886640050001267586320801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18364373466670046896855469 6886640050001267586320801)
                  ·
                    refine ⟨5164980037500950689740601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886640050001267586320801 5164980037500950689740601)
                    ·
                      refine ⟨3873735028125713017305451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164980037500950689740601 3873735028125713017305451)
                      ·
                        rfl

theorem cell23_7544072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_7544072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544072 prefixEnd_7544072 := by exact prefixLift 7544072
  have htrace : WordTrace (prefixWord ++ tailWord_7544072) baseStart_7544072 baseEnd_7544072 := by
    simpa [prefixWord, tailWord_7544072, baseEnd_7544072] using wordTrace_append hprefix tailTrace_7544072
  have hstable : (prefixWord ++ tailWord_7544072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544072).length < 2 ^ (prefixWord ++ tailWord_7544072).sum := by decide
  have hdescent : baseEnd_7544072 < baseStart_7544072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544081 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_7544081 : Nat := 118140960795 + 7544081 * 2 ^ 59
def prefixEnd_7544081 : Nat := 4983230072969 + 3 ^ 40 * 7544081 * 2
def baseEnd_7544081 : Nat := 3873739649451603482092909

theorem tailTrace_7544081 : CollatzResearch.WordTrace tailWord_7544081 prefixEnd_7544081 3873739649451603482092909 := by
  unfold tailWord_7544081
  simp only [CollatzResearch.WordTrace]
  refine ⟨275155238982090438303040097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183436825988060292202026731 275155238982090438303040097)
  ·
    refine ⟨206366429236567828727280073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275155238982090438303040097 206366429236567828727280073)
    ·
      refine ⟨154774821927425871545460055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206366429236567828727280073 154774821927425871545460055)
      ·
        refine ⟨232162232891138807318190083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154774821927425871545460055 232162232891138807318190083)
        ·
          refine ⟨348243349336708210977285125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232162232891138807318190083 348243349336708210977285125)
          ·
            refine ⟨65295628000632789558240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348243349336708210977285125 65295628000632789558240961)
            ·
              refine ⟨48971721000474592168680721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65295628000632789558240961 48971721000474592168680721)
              ·
                refine ⟨36728790750355944126510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48971721000474592168680721 36728790750355944126510541)
                ·
                  refine ⟨13773296531383479047441453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36728790750355944126510541 13773296531383479047441453)
                  ·
                    refine ⟨5164986199268804642790545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13773296531383479047441453 5164986199268804642790545)
                    ·
                      refine ⟨3873739649451603482092909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5164986199268804642790545 3873739649451603482092909)
                      ·
                        rfl

theorem cell23_7544081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_7544081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544081 prefixEnd_7544081 := by exact prefixLift 7544081
  have htrace : WordTrace (prefixWord ++ tailWord_7544081) baseStart_7544081 baseEnd_7544081 := by
    simpa [prefixWord, tailWord_7544081, baseEnd_7544081] using wordTrace_append hprefix tailTrace_7544081
  have hstable : (prefixWord ++ tailWord_7544081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544081).length < 2 ^ (prefixWord ++ tailWord_7544081).sum := by decide
  have hdescent : baseEnd_7544081 < baseStart_7544081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544088 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_7544088 : Nat := 118140960795 + 7544088 * 2 ^ 59
def prefixEnd_7544088 : Nat := 4983230072969 + 3 ^ 40 * 7544088 * 2
def baseEnd_7544088 : Nat := 3873743243816184954705377

theorem tailTrace_7544088 : CollatzResearch.WordTrace tailWord_7544088 prefixEnd_7544088 3873743243816184954705377 := by
  unfold tailWord_7544088
  simp only [CollatzResearch.WordTrace]
  refine ⟨137577747146532539249272459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183436996195376718999029945 137577747146532539249272459)
  ·
    refine ⟨206366620719798808873908689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137577747146532539249272459 206366620719798808873908689)
    ·
      refine ⟨154774965539849106655431517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206366620719798808873908689 154774965539849106655431517)
      ·
        refine ⟨58040612077443414995786819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154774965539849106655431517 58040612077443414995786819)
        ·
          refine ⟨87060918116165122493680229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58040612077443414995786819 87060918116165122493680229)
          ·
            refine ⟨16323922146780960467565043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87060918116165122493680229 16323922146780960467565043)
            ·
              refine ⟨24485883220171440701347565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16323922146780960467565043 24485883220171440701347565)
              ·
                refine ⟨9182206207564290263005337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24485883220171440701347565 9182206207564290263005337)
                ·
                  refine ⟨6886654655673217697254003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182206207564290263005337 6886654655673217697254003)
                  ·
                    refine ⟨10329981983509826545881005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886654655673217697254003 10329981983509826545881005)
                    ·
                      refine ⟨3873743243816184954705377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10329981983509826545881005 3873743243816184954705377)
                      ·
                        rfl

theorem cell23_7544088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_7544088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544088 prefixEnd_7544088 := by exact prefixLift 7544088
  have htrace : WordTrace (prefixWord ++ tailWord_7544088) baseStart_7544088 baseEnd_7544088 := by
    simpa [prefixWord, tailWord_7544088, baseEnd_7544088] using wordTrace_append hprefix tailTrace_7544088
  have hstable : (prefixWord ++ tailWord_7544088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544088).length < 2 ^ (prefixWord ++ tailWord_7544088).sum := by decide
  have hdescent : baseEnd_7544088 < baseStart_7544088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544115 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 1, 3, 2]
def baseStart_7544115 : Nat := 118140960795 + 7544115 * 2 ^ 59
def prefixEnd_7544115 : Nat := 4983230072969 + 3 ^ 40 * 7544115 * 2
def baseEnd_7544115 : Nat := 3873757107793856349067753

theorem tailTrace_7544115 : CollatzResearch.WordTrace tailWord_7544115 prefixEnd_7544115 3873757107793856349067753 := by
  unfold tailWord_7544115
  simp only [CollatzResearch.WordTrace]
  refine ⟨275156479063967262109777799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183437652709311508073185199 275156479063967262109777799)
  ·
    refine ⟨412734718595950893164666699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275156479063967262109777799 412734718595950893164666699)
    ·
      refine ⟨619102077893926339747000049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412734718595950893164666699 619102077893926339747000049)
      ·
        refine ⟨464326558420444754810250037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619102077893926339747000049 464326558420444754810250037)
        ·
          refine ⟨43530614851916695763460941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464326558420444754810250037 43530614851916695763460941)
          ·
            refine ⟨16323980569468760911297853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43530614851916695763460941 16323980569468760911297853)
            ·
              refine ⟨6121492713550785341736695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16323980569468760911297853 6121492713550785341736695)
              ·
                refine ⟨9182239070326178012605043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121492713550785341736695 9182239070326178012605043)
                ·
                  refine ⟨13773358605489267018907565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9182239070326178012605043 13773358605489267018907565)
                  ·
                    refine ⟨5165009477058475132090337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13773358605489267018907565 5165009477058475132090337)
                    ·
                      refine ⟨3873757107793856349067753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165009477058475132090337 3873757107793856349067753)
                      ·
                        rfl

theorem cell23_7544115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 1, 3, 2].length) (baseStart_7544115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544115 prefixEnd_7544115 := by exact prefixLift 7544115
  have htrace : WordTrace (prefixWord ++ tailWord_7544115) baseStart_7544115 baseEnd_7544115 := by
    simpa [prefixWord, tailWord_7544115, baseEnd_7544115] using wordTrace_append hprefix tailTrace_7544115
  have hstable : (prefixWord ++ tailWord_7544115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544115).length < 2 ^ (prefixWord ++ tailWord_7544115).sum := by decide
  have hdescent : baseEnd_7544115 < baseStart_7544115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544224 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 10]
def baseStart_7544224 : Nat := 118140960795 + 7544224 * 2 ^ 59
def prefixEnd_7544224 : Nat := 4983230072969 + 3 ^ 40 * 7544224 * 2
def baseEnd_7544224 : Nat := 430423675242799602511639

theorem tailTrace_7544224 : CollatzResearch.WordTrace tailWord_7544224 prefixEnd_7544224 430423675242799602511639 := by
  unfold tailWord_7544224
  simp only [CollatzResearch.WordTrace]
  refine ⟨137580227310286186862747863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183440303080381582483663817 137580227310286186862747863)
  ·
    refine ⟨206370340965429280294121795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137580227310286186862747863 206370340965429280294121795)
    ·
      refine ⟨309555511448143920441182693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206370340965429280294121795 309555511448143920441182693)
      ·
        refine ⟨58041658396526985082721755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309555511448143920441182693 58041658396526985082721755)
        ·
          refine ⟨87062487594790477624082633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58041658396526985082721755 87062487594790477624082633)
          ·
            refine ⟨65296865696092858218061975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87062487594790477624082633 65296865696092858218061975)
            ·
              refine ⟨97945298544139287327092963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65296865696092858218061975 97945298544139287327092963)
              ·
                refine ⟨146917947816208930990639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97945298544139287327092963 146917947816208930990639445)
                ·
                  refine ⟨430423675242799602511639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146917947816208930990639445 430423675242799602511639)
                  ·
                    rfl

theorem cell23_7544224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_7544224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544224 prefixEnd_7544224 := by exact prefixLift 7544224
  have htrace : WordTrace (prefixWord ++ tailWord_7544224) baseStart_7544224 baseEnd_7544224 := by
    simpa [prefixWord, tailWord_7544224, baseEnd_7544224] using wordTrace_append hprefix tailTrace_7544224
  have hstable : (prefixWord ++ tailWord_7544224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544224).length < 2 ^ (prefixWord ++ tailWord_7544224).sum := by decide
  have hdescent : baseEnd_7544224 < baseStart_7544224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544241 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 6]
def baseStart_7544241 : Nat := 118140960795 + 7544241 * 2 ^ 59
def prefixEnd_7544241 : Nat := 4983230072969 + 3 ^ 40 * 7544241 * 2
def baseEnd_7544241 : Nat := 430424645150702539565797

theorem tailTrace_7544241 : CollatzResearch.WordTrace tailWord_7544241 prefixEnd_7544241 430424645150702539565797 := by
  unfold tailWord_7544241
  simp only [CollatzResearch.WordTrace]
  refine ⟨275161074661510785628864577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183440716441007190419243051 275161074661510785628864577)
  ·
    refine ⟨206370805996133089221648433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275161074661510785628864577 206370805996133089221648433)
    ·
      refine ⟨154778104497099816916236325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206370805996133089221648433 154778104497099816916236325)
      ·
        refine ⟨29020894593206215671794311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154778104497099816916236325 29020894593206215671794311)
        ·
          refine ⟨43531341889809323507691467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29020894593206215671794311 43531341889809323507691467)
          ·
            refine ⟨65297012834713985261537201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43531341889809323507691467 65297012834713985261537201)
            ·
              refine ⟨48972759626035488946152901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65297012834713985261537201 48972759626035488946152901)
              ·
                refine ⟨9182392429881654177403669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48972759626035488946152901 9182392429881654177403669)
                ·
                  refine ⟨430424645150702539565797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9182392429881654177403669 430424645150702539565797)
                  ·
                    rfl

theorem cell23_7544241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_7544241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544241 prefixEnd_7544241 := by exact prefixLift 7544241
  have htrace : WordTrace (prefixWord ++ tailWord_7544241) baseStart_7544241 baseEnd_7544241 := by
    simpa [prefixWord, tailWord_7544241, baseEnd_7544241] using wordTrace_append hprefix tailTrace_7544241
  have hstable : (prefixWord ++ tailWord_7544241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544241).length < 2 ^ (prefixWord ++ tailWord_7544241).sum := by decide
  have hdescent : baseEnd_7544241 < baseStart_7544241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544245 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7544245 : Nat := 118140960795 + 7544245 * 2 ^ 59
def prefixEnd_7544245 : Nat := 4983230072969 + 3 ^ 40 * 7544245 * 2
def baseEnd_7544245 : Nat := 1291274620092980280147385

theorem tailTrace_7544245 : CollatzResearch.WordTrace tailWord_7544245 prefixEnd_7544245 1291274620092980280147385 := by
  unfold tailWord_7544245
  simp only [CollatzResearch.WordTrace]
  refine ⟨275161220553496294312010189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183440813702330862874673459 275161220553496294312010189)
  ·
    refine ⟨103185457707561110367003821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275161220553496294312010189 103185457707561110367003821)
    ·
      refine ⟨38694546640335416387626433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103185457707561110367003821 38694546640335416387626433)
      ·
        refine ⟨29020909980251562290719825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38694546640335416387626433 29020909980251562290719825)
        ·
          refine ⟨21765682485188671718039869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29020909980251562290719825 21765682485188671718039869)
          ·
            refine ⟨8162130931945751894264951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21765682485188671718039869 8162130931945751894264951)
            ·
              refine ⟨12243196397918627841397427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162130931945751894264951 12243196397918627841397427)
              ·
                refine ⟨18364794596877941762096141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243196397918627841397427 18364794596877941762096141)
                ·
                  refine ⟨6886797973829228160786053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18364794596877941762096141 6886797973829228160786053)
                  ·
                    refine ⟨1291274620092980280147385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886797973829228160786053 1291274620092980280147385)
                    ·
                      rfl

theorem cell23_7544245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7544245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544245 prefixEnd_7544245 := by exact prefixLift 7544245
  have htrace : WordTrace (prefixWord ++ tailWord_7544245) baseStart_7544245 baseEnd_7544245 := by
    simpa [prefixWord, tailWord_7544245, baseEnd_7544245] using wordTrace_append hprefix tailTrace_7544245
  have hstable : (prefixWord ++ tailWord_7544245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544245).length < 2 ^ (prefixWord ++ tailWord_7544245).sum := by decide
  have hdescent : baseEnd_7544245 < baseStart_7544245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544295 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7544295 : Nat := 118140960795 + 7544295 * 2 ^ 59
def prefixEnd_7544295 : Nat := 4983230072969 + 3 ^ 40 * 7544295 * 2
def baseEnd_7544295 : Nat := 3873849534311665644816925

theorem tailTrace_7544295 : CollatzResearch.WordTrace tailWord_7544295 prefixEnd_7544295 3873849534311665644816925 := by
  unfold tailWord_7544295
  simp only [CollatzResearch.WordTrace]
  refine ⟨275163044203315152851330339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183442029468876768567553559 275163044203315152851330339)
  ·
    refine ⟨412744566304972729276995509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275163044203315152851330339 412744566304972729276995509)
    ·
      refine ⟨38694803091091193369718329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412744566304972729276995509 38694803091091193369718329)
      ·
        refine ⟨29021102318318395027288747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38694803091091193369718329 29021102318318395027288747)
        ·
          refine ⟨43531653477477592540933121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29021102318318395027288747 43531653477477592540933121)
          ·
            refine ⟨32648740108108194405699841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43531653477477592540933121 32648740108108194405699841)
            ·
              refine ⟨24486555081081145804274881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32648740108108194405699841 24486555081081145804274881)
              ·
                refine ⟨18364916310810859353206161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24486555081081145804274881 18364916310810859353206161)
                ·
                  refine ⟨13773687233108144514904621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18364916310810859353206161 13773687233108144514904621)
                  ·
                    refine ⟨5165132712415554193089233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13773687233108144514904621 5165132712415554193089233)
                    ·
                      refine ⟨3873849534311665644816925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165132712415554193089233 3873849534311665644816925)
                      ·
                        rfl

theorem cell23_7544295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7544295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544295 prefixEnd_7544295 := by exact prefixLift 7544295
  have htrace : WordTrace (prefixWord ++ tailWord_7544295) baseStart_7544295 baseEnd_7544295 := by
    simpa [prefixWord, tailWord_7544295, baseEnd_7544295] using wordTrace_append hprefix tailTrace_7544295
  have hstable : (prefixWord ++ tailWord_7544295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544295).length < 2 ^ (prefixWord ++ tailWord_7544295).sum := by decide
  have hdescent : baseEnd_7544295 < baseStart_7544295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544302 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_7544302 : Nat := 118140960795 + 7544302 * 2 ^ 59
def prefixEnd_7544302 : Nat := 4983230072969 + 3 ^ 40 * 7544302 * 2
def baseEnd_7544302 : Nat := 3873853128676247117429393

theorem tailTrace_7544302 : CollatzResearch.WordTrace tailWord_7544302 prefixEnd_7544302 3873853128676247117429393 := by
  unfold tailWord_7544302
  simp only [CollatzResearch.WordTrace]
  refine ⟨34395412439286224130854395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183442199676193195364556773 34395412439286224130854395)
  ·
    refine ⟨51593118658929336196281593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34395412439286224130854395 51593118658929336196281593)
    ·
      refine ⟨38694838994197002147211195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51593118658929336196281593 38694838994197002147211195)
      ·
        refine ⟨58042258491295503220816793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38694838994197002147211195 58042258491295503220816793)
        ·
          refine ⟨43531693868471627415612595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58042258491295503220816793 43531693868471627415612595)
          ·
            refine ⟨65297540802707441123418893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43531693868471627415612595 65297540802707441123418893)
            ·
              refine ⟨24486577801015290421282085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65297540802707441123418893 24486577801015290421282085)
              ·
                refine ⟨4591233337690366953990391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24486577801015290421282085 4591233337690366953990391)
                ·
                  refine ⟨6886850006535550430985587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591233337690366953990391 6886850006535550430985587)
                  ·
                    refine ⟨10330275009803325646478381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6886850006535550430985587 10330275009803325646478381)
                    ·
                      refine ⟨3873853128676247117429393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10330275009803325646478381 3873853128676247117429393)
                      ·
                        rfl

theorem cell23_7544302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_7544302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544302 prefixEnd_7544302 := by exact prefixLift 7544302
  have htrace : WordTrace (prefixWord ++ tailWord_7544302) baseStart_7544302 baseEnd_7544302 := by
    simpa [prefixWord, tailWord_7544302, baseEnd_7544302] using wordTrace_append hprefix tailTrace_7544302
  have hstable : (prefixWord ++ tailWord_7544302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544302).length < 2 ^ (prefixWord ++ tailWord_7544302).sum := by decide
  have hdescent : baseEnd_7544302 < baseStart_7544302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544328 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_7544328 : Nat := 118140960795 + 7544328 * 2 ^ 59
def prefixEnd_7544328 : Nat := 4983230072969 + 3 ^ 40 * 7544328 * 2
def baseEnd_7544328 : Nat := 3873866479173264015704273

theorem tailTrace_7544328 : CollatzResearch.WordTrace tailWord_7544328 prefixEnd_7544328 3873866479173264015704273 := by
  unfold tailWord_7544328
  simp only [CollatzResearch.WordTrace]
  refine ⟨137582123906097799743640819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183442831874797066324854425 137582123906097799743640819)
  ·
    refine ⟨206373185859146699615461229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137582123906097799743640819 206373185859146699615461229)
    ·
      refine ⟨77389944697180012355797961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206373185859146699615461229 77389944697180012355797961)
      ·
        refine ⟨58042458522885009266848471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77389944697180012355797961 58042458522885009266848471)
        ·
          refine ⟨87063687784327513900272707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58042458522885009266848471 87063687784327513900272707)
          ·
            refine ⟨130595531676491270850409061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87063687784327513900272707 130595531676491270850409061)
            ·
              refine ⟨24486662189342113284451699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130595531676491270850409061 24486662189342113284451699)
              ·
                refine ⟨36729993284013169926677549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24486662189342113284451699 36729993284013169926677549)
                ·
                  refine ⟨13773747481504938722504081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36729993284013169926677549 13773747481504938722504081)
                  ·
                    refine ⟨10330310611128704041878061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13773747481504938722504081 10330310611128704041878061)
                    ·
                      refine ⟨3873866479173264015704273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10330310611128704041878061 3873866479173264015704273)
                      ·
                        rfl

theorem cell23_7544328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_7544328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544328 prefixEnd_7544328 := by exact prefixLift 7544328
  have htrace : WordTrace (prefixWord ++ tailWord_7544328) baseStart_7544328 baseEnd_7544328 := by
    simpa [prefixWord, tailWord_7544328, baseEnd_7544328] using wordTrace_append hprefix tailTrace_7544328
  have hstable : (prefixWord ++ tailWord_7544328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544328).length < 2 ^ (prefixWord ++ tailWord_7544328).sum := by decide
  have hdescent : baseEnd_7544328 < baseStart_7544328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544352 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_7544352 : Nat := 118140960795 + 7544352 * 2 ^ 59
def prefixEnd_7544352 : Nat := 4983230072969 + 3 ^ 40 * 7544352 * 2
def baseEnd_7544352 : Nat := 1291292934236323973934721

theorem tailTrace_7544352 : CollatzResearch.WordTrace tailWord_7544352 prefixEnd_7544352 1291292934236323973934721 := by
  unfold tailWord_7544352
  simp only [CollatzResearch.WordTrace]
  refine ⟨137582561582054325793077655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183443415442739101057436873 137582561582054325793077655)
  ·
    refine ⟨206373842373081488689616483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137582561582054325793077655 206373842373081488689616483)
    ·
      refine ⟨309560763559622233034424725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206373842373081488689616483 309560763559622233034424725)
      ·
        refine ⟨14510660791857292173488659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309560763559622233034424725 14510660791857292173488659)
        ·
          refine ⟨21765991187785938260232989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14510660791857292173488659 21765991187785938260232989)
          ·
            refine ⟨8162246695419726847587371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21765991187785938260232989 8162246695419726847587371)
            ·
              refine ⟨12243370043129590271381057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162246695419726847587371 12243370043129590271381057)
              ·
                refine ⟨9182527532347192703535793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243370043129590271381057 9182527532347192703535793)
                ·
                  refine ⟨6886895649260394527651845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182527532347192703535793 6886895649260394527651845)
                  ·
                    refine ⟨1291292934236323973934721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6886895649260394527651845 1291292934236323973934721)
                    ·
                      rfl

theorem cell23_7544352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_7544352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544352 prefixEnd_7544352 := by exact prefixLift 7544352
  have htrace : WordTrace (prefixWord ++ tailWord_7544352) baseStart_7544352 baseEnd_7544352 := by
    simpa [prefixWord, tailWord_7544352, baseEnd_7544352] using wordTrace_append hprefix tailTrace_7544352
  have hstable : (prefixWord ++ tailWord_7544352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544352).length < 2 ^ (prefixWord ++ tailWord_7544352).sum := by decide
  have hdescent : baseEnd_7544352 < baseStart_7544352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544375 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_7544375 : Nat := 118140960795 + 7544375 * 2 ^ 59
def prefixEnd_7544375 : Nat := 4983230072969 + 3 ^ 40 * 7544375 * 2
def baseEnd_7544375 : Nat := 3873890612764025331816557

theorem tailTrace_7544375 : CollatzResearch.WordTrace tailWord_7544375 prefixEnd_7544375 3873890612764025331816557 := by
  unfold tailWord_7544375
  simp only [CollatzResearch.WordTrace]
  refine ⟨275165962043025326514242579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183443974695350217676161719 275165962043025326514242579)
  ·
    refine ⟨412748943064537989771363869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275165962043025326514242579 412748943064537989771363869)
    ·
      refine ⟨154780853649201746164261451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412748943064537989771363869 154780853649201746164261451)
      ·
        refine ⟨232171280473802619246392177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154780853649201746164261451 232171280473802619246392177)
        ·
          refine ⟨174128460355351964434794133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232171280473802619246392177 174128460355351964434794133)
          ·
            refine ⟨8162271579157123332880975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174128460355351964434794133 8162271579157123332880975)
            ·
              refine ⟨12243407368735684999321463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162271579157123332880975 12243407368735684999321463)
              ·
                refine ⟨18365111053103527498982195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243407368735684999321463 18365111053103527498982195)
                ·
                  refine ⟨27547666579655291248473293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18365111053103527498982195 27547666579655291248473293)
                  ·
                    refine ⟨10330374967370734218177485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27547666579655291248473293 10330374967370734218177485)
                    ·
                      refine ⟨3873890612764025331816557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10330374967370734218177485 3873890612764025331816557)
                      ·
                        rfl

theorem cell23_7544375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_7544375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544375 prefixEnd_7544375 := by exact prefixLift 7544375
  have htrace : WordTrace (prefixWord ++ tailWord_7544375) baseStart_7544375 baseEnd_7544375 := by
    simpa [prefixWord, tailWord_7544375, baseEnd_7544375] using wordTrace_append hprefix tailTrace_7544375
  have hstable : (prefixWord ++ tailWord_7544375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544375).length < 2 ^ (prefixWord ++ tailWord_7544375).sum := by decide
  have hdescent : baseEnd_7544375 < baseStart_7544375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544402 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_7544402 : Nat := 118140960795 + 7544402 * 2 ^ 59
def prefixEnd_7544402 : Nat := 4983230072969 + 3 ^ 40 * 7544402 * 2
def baseEnd_7544402 : Nat := 3873904476741696726178933

theorem tailTrace_7544402 : CollatzResearch.WordTrace tailWord_7544402 prefixEnd_7544402 3873904476741696726178933 := by
  unfold tailWord_7544402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68791736703481877531368865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183444631209285006750316973 68791736703481877531368865)
  ·
    refine ⟨51593802527611408148526649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68791736703481877531368865 51593802527611408148526649)
    ·
      refine ⟨38695351895708556111394987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51593802527611408148526649 38695351895708556111394987)
      ·
        refine ⟨58043027843562834167092481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38695351895708556111394987 58043027843562834167092481)
        ·
          refine ⟨43532270882672125625319361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58043027843562834167092481 43532270882672125625319361)
          ·
            refine ⟨32649203162004094218989521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43532270882672125625319361 32649203162004094218989521)
            ·
              refine ⟨24486902371503070664242141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32649203162004094218989521 24486902371503070664242141)
              ·
                refine ⟨9182588389313651499090803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24486902371503070664242141 9182588389313651499090803)
                ·
                  refine ⟨13773882583970477248636205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9182588389313651499090803 13773882583970477248636205)
                  ·
                    refine ⟨5165205968988928968238577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13773882583970477248636205 5165205968988928968238577)
                    ·
                      refine ⟨3873904476741696726178933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165205968988928968238577 3873904476741696726178933)
                      ·
                        rfl

theorem cell23_7544402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_7544402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544402 prefixEnd_7544402 := by exact prefixLift 7544402
  have htrace : WordTrace (prefixWord ++ tailWord_7544402) baseStart_7544402 baseEnd_7544402 := by
    simpa [prefixWord, tailWord_7544402, baseEnd_7544402] using wordTrace_append hprefix tailTrace_7544402
  have hstable : (prefixWord ++ tailWord_7544402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544402).length < 2 ^ (prefixWord ++ tailWord_7544402).sum := by decide
  have hdescent : baseEnd_7544402 < baseStart_7544402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544466 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7544466 : Nat := 118140960795 + 7544466 * 2 ^ 59
def prefixEnd_7544466 : Nat := 4983230072969 + 3 ^ 40 * 7544466 * 2
def baseEnd_7544466 : Nat := 3873937339503584475778639

theorem tailTrace_7544466 : CollatzResearch.WordTrace tailWord_7544466 prefixEnd_7544466 3873937339503584475778639 := by
  unfold tailWord_7544466
  simp only [CollatzResearch.WordTrace]
  refine ⟨68792320271423912263951313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183446187390463766037203501 68792320271423912263951313)
  ·
    refine ⟨51594240203567934197963485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68792320271423912263951313 51594240203567934197963485)
    ·
      refine ⟨19347840076337975324236307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51594240203567934197963485 19347840076337975324236307)
      ·
        refine ⟨29021760114506962986354461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19347840076337975324236307 29021760114506962986354461)
        ·
          refine ⟨10883160042940111119882923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29021760114506962986354461 10883160042940111119882923)
          ·
            refine ⟨16324740064410166679824385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10883160042940111119882923 16324740064410166679824385)
            ·
              refine ⟨12243555048307625009868289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16324740064410166679824385 12243555048307625009868289)
              ·
                refine ⟨9182666286230718757401217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243555048307625009868289 9182666286230718757401217)
                ·
                  refine ⟨6886999714673039068050913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182666286230718757401217 6886999714673039068050913)
                  ·
                    refine ⟨5165249786004779301038185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6886999714673039068050913 5165249786004779301038185)
                    ·
                      refine ⟨3873937339503584475778639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165249786004779301038185 3873937339503584475778639)
                      ·
                        rfl

theorem cell23_7544466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7544466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544466 prefixEnd_7544466 := by exact prefixLift 7544466
  have htrace : WordTrace (prefixWord ++ tailWord_7544466) baseStart_7544466 baseEnd_7544466 := by
    simpa [prefixWord, tailWord_7544466, baseEnd_7544466] using wordTrace_append hprefix tailTrace_7544466
  have hstable : (prefixWord ++ tailWord_7544466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544466).length < 2 ^ (prefixWord ++ tailWord_7544466).sum := by decide
  have hdescent : baseEnd_7544466 < baseStart_7544466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544472 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 5]
def baseStart_7544472 : Nat := 118140960795 + 7544472 * 2 ^ 59
def prefixEnd_7544472 : Nat := 4983230072969 + 3 ^ 40 * 7544472 * 2
def baseEnd_7544472 : Nat := 430437824487501272478179

theorem tailTrace_7544472 : CollatzResearch.WordTrace tailWord_7544472 prefixEnd_7544472 430437824487501272478179 := by
  unfold tailWord_7544472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137584749961836956040261835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183446333282449274720349113 137584749961836956040261835)
  ·
    refine ⟨206377124942755434060392753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137584749961836956040261835 206377124942755434060392753)
    ·
      refine ⟨154782843707066575545294565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206377124942755434060392753 154782843707066575545294565)
      ·
        refine ⟨29021783195074982914742731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154782843707066575545294565 29021783195074982914742731)
        ·
          refine ⟨43532674792612474372114097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29021783195074982914742731 43532674792612474372114097)
          ·
            refine ⟨32649506094459355779085573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43532674792612474372114097 32649506094459355779085573)
            ·
              refine ⟨6121782392711129208578545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32649506094459355779085573 6121782392711129208578545)
              ·
                refine ⟨4591336794533346906433909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6121782392711129208578545 4591336794533346906433909)
                ·
                  refine ⟨430437824487501272478179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4591336794533346906433909 430437824487501272478179)
                  ·
                    rfl

theorem cell23_7544472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 5].length) (baseStart_7544472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544472 prefixEnd_7544472 := by exact prefixLift 7544472
  have htrace : WordTrace (prefixWord ++ tailWord_7544472) baseStart_7544472 baseEnd_7544472 := by
    simpa [prefixWord, tailWord_7544472, baseEnd_7544472] using wordTrace_append hprefix tailTrace_7544472
  have hstable : (prefixWord ++ tailWord_7544472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544472).length < 2 ^ (prefixWord ++ tailWord_7544472).sum := by decide
  have hdescent : baseEnd_7544472 < baseStart_7544472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544502 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7544502 : Nat := 118140960795 + 7544502 * 2 ^ 59
def prefixEnd_7544502 : Nat := 4983230072969 + 3 ^ 40 * 7544502 * 2
def baseEnd_7544502 : Nat := 1291318608269048778309491

theorem tailTrace_7544502 : CollatzResearch.WordTrace tailWord_7544502 prefixEnd_7544502 1291318608269048778309491 := by
  unfold tailWord_7544502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198162132097826700257235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183447062742376818136077173 17198162132097826700257235)
  ·
    refine ⟨25797243198146740050385853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198162132097826700257235 25797243198146740050385853)
    ·
      refine ⟨9673966199305027518894695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25797243198146740050385853 9673966199305027518894695)
      ·
        refine ⟨14510949298957541278342043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673966199305027518894695 14510949298957541278342043)
        ·
          refine ⟨21766423948436311917513065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14510949298957541278342043 21766423948436311917513065)
          ·
            refine ⟨16324817961327233938134799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21766423948436311917513065 16324817961327233938134799)
            ·
              refine ⟨24487226941990850907202199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16324817961327233938134799 24487226941990850907202199)
              ·
                refine ⟨36730840412986276360803299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24487226941990850907202199 36730840412986276360803299)
                ·
                  refine ⟨55096260619479414541204949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36730840412986276360803299 55096260619479414541204949)
                  ·
                    refine ⟨1291318608269048778309491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55096260619479414541204949 1291318608269048778309491)
                    ·
                      rfl

theorem cell23_7544502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7544502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544502 prefixEnd_7544502 := by exact prefixLift 7544502
  have htrace : WordTrace (prefixWord ++ tailWord_7544502) baseStart_7544502 baseEnd_7544502 := by
    simpa [prefixWord, tailWord_7544502, baseEnd_7544502] using wordTrace_append hprefix tailTrace_7544502
  have hstable : (prefixWord ++ tailWord_7544502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544502).length < 2 ^ (prefixWord ++ tailWord_7544502).sum := by decide
  have hdescent : baseEnd_7544502 < baseStart_7544502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544505 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7544505 : Nat := 118140960795 + 7544505 * 2 ^ 59
def prefixEnd_7544505 : Nat := 4983230072969 + 3 ^ 40 * 7544505 * 2
def baseEnd_7544505 : Nat := 3873957365249109823190959

theorem tailTrace_7544505 : CollatzResearch.WordTrace tailWord_7544505 prefixEnd_7544505 3873957365249109823190959 := by
  unfold tailWord_7544505
  simp only [CollatzResearch.WordTrace]
  refine ⟨275170703532554358716474969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183447135688369572477649979 275170703532554358716474969)
  ·
    refine ⟨206378027649415769037356227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275170703532554358716474969 206378027649415769037356227)
    ·
      refine ⟨309567041474123653556034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206378027649415769037356227 309567041474123653556034341)
      ·
        refine ⟨58043820276398185041756439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309567041474123653556034341 58043820276398185041756439)
        ·
          refine ⟨87065730414597277562634659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58043820276398185041756439 87065730414597277562634659)
          ·
            refine ⟨130598595621895916343951989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87065730414597277562634659 130598595621895916343951989)
            ·
              refine ⟨12243618339552742157245499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130598595621895916343951989 12243618339552742157245499)
              ·
                refine ⟨18365427509329113235868249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243618339552742157245499 18365427509329113235868249)
                ·
                  refine ⟨13774070631996834926901187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18365427509329113235868249 13774070631996834926901187)
                  ·
                    refine ⟨20661105947995252390351781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13774070631996834926901187 20661105947995252390351781)
                    ·
                      refine ⟨3873957365249109823190959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20661105947995252390351781 3873957365249109823190959)
                      ·
                        rfl

theorem cell23_7544505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7544505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544505 prefixEnd_7544505 := by exact prefixLift 7544505
  have htrace : WordTrace (prefixWord ++ tailWord_7544505) baseStart_7544505 baseEnd_7544505 := by
    simpa [prefixWord, tailWord_7544505, baseEnd_7544505] using wordTrace_append hprefix tailTrace_7544505
  have hstable : (prefixWord ++ tailWord_7544505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544505).length < 2 ^ (prefixWord ++ tailWord_7544505).sum := by decide
  have hdescent : baseEnd_7544505 < baseStart_7544505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544528 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 6]
def baseStart_7544528 : Nat := 118140960795 + 7544528 * 2 ^ 59
def prefixEnd_7544528 : Nat := 4983230072969 + 3 ^ 40 * 7544528 * 2
def baseEnd_7544528 : Nat := 430441019478240359244817

theorem tailTrace_7544528 : CollatzResearch.WordTrace tailWord_7544528 prefixEnd_7544528 430441019478240359244817 := by
  unfold tailWord_7544528
  simp only [CollatzResearch.WordTrace]
  refine ⟨137585771205735516822281119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183447694940980689096374825 137585771205735516822281119)
  ·
    refine ⟨206378656808603275233421679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137585771205735516822281119 206378656808603275233421679)
    ·
      refine ⟨309567985212904912850132519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206378656808603275233421679 309567985212904912850132519)
      ·
        refine ⟨464351977819357369275198779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309567985212904912850132519 464351977819357369275198779)
        ·
          refine ⟨696527966729036053912798169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464351977819357369275198779 696527966729036053912798169)
          ·
            refine ⟨522395975046777040434598627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696527966729036053912798169 522395975046777040434598627)
            ·
              refine ⟨783593962570165560651897941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522395975046777040434598627 783593962570165560651897941)
              ·
                refine ⟨9182741748869127663889429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 783593962570165560651897941 9182741748869127663889429)
                ·
                  refine ⟨430441019478240359244817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9182741748869127663889429 430441019478240359244817)
                  ·
                    rfl

theorem cell23_7544528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_7544528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544528 prefixEnd_7544528 := by exact prefixLift 7544528
  have htrace : WordTrace (prefixWord ++ tailWord_7544528) baseStart_7544528 baseEnd_7544528 := by
    simpa [prefixWord, tailWord_7544528, baseEnd_7544528] using wordTrace_append hprefix tailTrace_7544528
  have hstable : (prefixWord ++ tailWord_7544528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544528).length < 2 ^ (prefixWord ++ tailWord_7544528).sum := by decide
  have hdescent : baseEnd_7544528 < baseStart_7544528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544532 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_7544532 : Nat := 118140960795 + 7544532 * 2 ^ 59
def prefixEnd_7544532 : Nat := 4983230072969 + 3 ^ 40 * 7544532 * 2
def baseEnd_7544532 : Nat := 1291323743075593739184445

theorem tailTrace_7544532 : CollatzResearch.WordTrace tailWord_7544532 prefixEnd_7544532 1291323743075593739184445 := by
  unfold tailWord_7544532
  simp only [CollatzResearch.WordTrace]
  refine ⟨137585844151728271163853925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183447792202304361551805233 137585844151728271163853925)
  ·
    refine ⟨25797345778449050843222611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137585844151728271163853925 25797345778449050843222611)
    ·
      refine ⟨38696018667673576264833917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25797345778449050843222611 38696018667673576264833917)
      ·
        refine ⟨14511007000377591099312719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38696018667673576264833917 14511007000377591099312719)
        ·
          refine ⟨21766510500566386648969079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14511007000377591099312719 21766510500566386648969079)
          ·
            refine ⟨32649765750849579973453619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21766510500566386648969079 32649765750849579973453619)
            ·
              refine ⟨48974648626274369960180429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32649765750849579973453619 48974648626274369960180429)
              ·
                refine ⟨18365493234852888735067661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48974648626274369960180429 18365493234852888735067661)
                ·
                  refine ⟨6887059963069833275650373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18365493234852888735067661 6887059963069833275650373)
                  ·
                    refine ⟨1291323743075593739184445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887059963069833275650373 1291323743075593739184445)
                    ·
                      rfl

theorem cell23_7544532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_7544532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544532 prefixEnd_7544532 := by exact prefixLift 7544532
  have htrace : WordTrace (prefixWord ++ tailWord_7544532) baseStart_7544532 baseEnd_7544532 := by
    simpa [prefixWord, tailWord_7544532, baseEnd_7544532] using wordTrace_append hprefix tailTrace_7544532
  have hstable : (prefixWord ++ tailWord_7544532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544532).length < 2 ^ (prefixWord ++ tailWord_7544532).sum := by decide
  have hdescent : baseEnd_7544532 < baseStart_7544532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544548 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7544548 : Nat := 118140960795 + 7544548 * 2 ^ 59
def prefixEnd_7544548 : Nat := 4983230072969 + 3 ^ 40 * 7544548 * 2
def baseEnd_7544548 : Nat := 3873979444917253154953261

theorem tailTrace_7544548 : CollatzResearch.WordTrace tailWord_7544548 prefixEnd_7544548 3873979444917253154953261 := by
  unfold tailWord_7544548
  simp only [CollatzResearch.WordTrace]
  refine ⟨137586135935699288530145149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183448181247599051373526865 137586135935699288530145149)
  ·
    refine ⟨51594800975887233198804431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137586135935699288530145149 51594800975887233198804431)
    ·
      refine ⟨77392201463830849798206647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51594800975887233198804431 77392201463830849798206647)
      ·
        refine ⟨116088302195746274697309971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77392201463830849798206647 116088302195746274697309971)
        ·
          refine ⟨174132453293619412045964957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116088302195746274697309971 174132453293619412045964957)
          ·
            refine ⟨65299669985107279517236859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174132453293619412045964957 65299669985107279517236859)
            ·
              refine ⟨97949504977660919275855289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65299669985107279517236859 97949504977660919275855289)
              ·
                refine ⟨73462128733245689456891467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97949504977660919275855289 73462128733245689456891467)
                ·
                  refine ⟨110193193099868534185337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73462128733245689456891467 110193193099868534185337201)
                  ·
                    refine ⟨82644894824901400639002901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110193193099868534185337201 82644894824901400639002901)
                    ·
                      refine ⟨3873979444917253154953261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82644894824901400639002901 3873979444917253154953261)
                      ·
                        rfl

theorem cell23_7544548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7544548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544548 prefixEnd_7544548 := by exact prefixLift 7544548
  have htrace : WordTrace (prefixWord ++ tailWord_7544548) baseStart_7544548 baseEnd_7544548 := by
    simpa [prefixWord, tailWord_7544548, baseEnd_7544548] using wordTrace_append hprefix tailTrace_7544548
  have hstable : (prefixWord ++ tailWord_7544548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544548).length < 2 ^ (prefixWord ++ tailWord_7544548).sum := by decide
  have hdescent : baseEnd_7544548 < baseStart_7544548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544566 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_7544566 : Nat := 118140960795 + 7544566 * 2 ^ 59
def prefixEnd_7544566 : Nat := 4983230072969 + 3 ^ 40 * 7544566 * 2
def baseEnd_7544566 : Nat := 1291329562523011361509393

theorem tailTrace_7544566 : CollatzResearch.WordTrace tailWord_7544566 prefixEnd_7544566 1291329562523011361509393 := by
  unfold tailWord_7544566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198308024083335383402847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183448618923555577422963701 17198308024083335383402847)
  ·
    refine ⟨25797462036125003075104271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198308024083335383402847 25797462036125003075104271)
    ·
      refine ⟨38696193054187504612656407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25797462036125003075104271 38696193054187504612656407)
      ·
        refine ⟨58044289581281256918984611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38696193054187504612656407 58044289581281256918984611)
        ·
          refine ⟨87066434371921885378476917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58044289581281256918984611 87066434371921885378476917)
          ·
            refine ⟨8162478222367676754232211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87066434371921885378476917 8162478222367676754232211)
            ·
              refine ⟨12243717333551515131348317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162478222367676754232211 12243717333551515131348317)
              ·
                refine ⟨4591394000081818174255619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12243717333551515131348317 4591394000081818174255619)
                ·
                  refine ⟨6887091000122727261383429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591394000081818174255619 6887091000122727261383429)
                  ·
                    refine ⟨1291329562523011361509393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887091000122727261383429 1291329562523011361509393)
                    ·
                      rfl

theorem cell23_7544566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_7544566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544566 prefixEnd_7544566 := by exact prefixLift 7544566
  have htrace : WordTrace (prefixWord ++ tailWord_7544566) baseStart_7544566 baseEnd_7544566 := by
    simpa [prefixWord, tailWord_7544566, baseEnd_7544566] using wordTrace_append hprefix tailTrace_7544566
  have hstable : (prefixWord ++ tailWord_7544566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544566).length < 2 ^ (prefixWord ++ tailWord_7544566).sum := by decide
  have hdescent : baseEnd_7544566 < baseStart_7544566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544575 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 1, 5]
def baseStart_7544575 : Nat := 118140960795 + 7544575 * 2 ^ 59
def prefixEnd_7544575 : Nat := 4983230072969 + 3 ^ 40 * 7544575 * 2
def baseEnd_7544575 : Nat := 1291331102964974849771879

theorem tailTrace_7544575 : CollatzResearch.WordTrace tailWord_7544575 prefixEnd_7544575 1291331102964974849771879 := by
  unfold tailWord_7544575
  simp only [CollatzResearch.WordTrace]
  refine ⟨275173256642300760671523179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183448837761533840447682119 275173256642300760671523179)
  ·
    refine ⟨412759884963451141007284769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275173256642300760671523179 412759884963451141007284769)
    ·
      refine ⟨309569913722588355755463577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412759884963451141007284769 309569913722588355755463577)
      ·
        refine ⟨232177435291941266816597683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309569913722588355755463577 232177435291941266816597683)
        ·
          refine ⟨348266152937911900224896525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232177435291941266816597683 348266152937911900224896525)
          ·
            refine ⟨130599807351716962584336197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348266152937911900224896525 130599807351716962584336197)
            ·
              refine ⟨24487463878446930484563037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130599807351716962584336197 24487463878446930484563037)
              ·
                refine ⟨9182798954417598931711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24487463878446930484563037 9182798954417598931711139)
                ·
                  refine ⟨13774198431626398397566709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9182798954417598931711139 13774198431626398397566709)
                  ·
                    refine ⟨1291331102964974849771879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13774198431626398397566709 1291331102964974849771879)
                    ·
                      rfl

theorem cell23_7544575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_7544575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544575 prefixEnd_7544575 := by exact prefixLift 7544575
  have htrace : WordTrace (prefixWord ++ tailWord_7544575) baseStart_7544575 baseEnd_7544575 := by
    simpa [prefixWord, tailWord_7544575, baseEnd_7544575] using wordTrace_append hprefix tailTrace_7544575
  have hstable : (prefixWord ++ tailWord_7544575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544575).length < 2 ^ (prefixWord ++ tailWord_7544575).sum := by decide
  have hdescent : baseEnd_7544575 < baseStart_7544575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544595 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 6, 2]
def baseStart_7544595 : Nat := 118140960795 + 7544595 * 2 ^ 59
def prefixEnd_7544595 : Nat := 4983230072969 + 3 ^ 40 * 7544595 * 2
def baseEnd_7544595 : Nat := 3874003578508014471065545

theorem tailTrace_7544595 : CollatzResearch.WordTrace tailWord_7544595 prefixEnd_7544595 3874003578508014471065545 := by
  unfold tailWord_7544595
  simp only [CollatzResearch.WordTrace]
  refine ⟨275173986102228304087251239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183449324068152202724834159 275173986102228304087251239)
  ·
    refine ⟨412760979153342456130876859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275173986102228304087251239 412760979153342456130876859)
    ·
      refine ⟨619141468730013684196315289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412760979153342456130876859 619141468730013684196315289)
      ·
        refine ⟨464356101547510263147236467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619141468730013684196315289 464356101547510263147236467)
        ·
          refine ⟨696534152321265394720854701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464356101547510263147236467 696534152321265394720854701)
          ·
            refine ⟨261200307120474523020320513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696534152321265394720854701 261200307120474523020320513)
            ·
              refine ⟨195900230340355892265240385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261200307120474523020320513 195900230340355892265240385)
              ·
                refine ⟨146925172755266919198930289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195900230340355892265240385 146925172755266919198930289)
                ·
                  refine ⟨110193879566450189399197717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146925172755266919198930289 110193879566450189399197717)
                  ·
                    refine ⟨5165338104677352628087393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110193879566450189399197717 5165338104677352628087393)
                    ·
                      refine ⟨3874003578508014471065545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165338104677352628087393 3874003578508014471065545)
                      ·
                        rfl

theorem cell23_7544595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6, 2].length) (baseStart_7544595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544595 prefixEnd_7544595 := by exact prefixLift 7544595
  have htrace : WordTrace (prefixWord ++ tailWord_7544595) baseStart_7544595 baseEnd_7544595 := by
    simpa [prefixWord, tailWord_7544595, baseEnd_7544595] using wordTrace_append hprefix tailTrace_7544595
  have hstable : (prefixWord ++ tailWord_7544595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544595).length < 2 ^ (prefixWord ++ tailWord_7544595).sum := by decide
  have hdescent : baseEnd_7544595 < baseStart_7544595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544596 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 6]
def baseStart_7544596 : Nat := 118140960795 + 7544596 * 2 ^ 59
def prefixEnd_7544596 : Nat := 4983230072969 + 3 ^ 40 * 7544596 * 2
def baseEnd_7544596 : Nat := 430444899109852107461449

theorem tailTrace_7544596 : CollatzResearch.WordTrace tailWord_7544596 prefixEnd_7544596 430444899109852107461449 := by
  unfold tailWord_7544596
  simp only [CollatzResearch.WordTrace]
  refine ⟨137587011287612340629018821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183449348383483120838691761 137587011287612340629018821)
  ·
    refine ⟨25797564616427313867941029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137587011287612340629018821 25797564616427313867941029)
    ·
      refine ⟨4837043365580121350238943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25797564616427313867941029 4837043365580121350238943)
      ·
        refine ⟨7255565048370182025358415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837043365580121350238943 7255565048370182025358415)
        ·
          refine ⟨10883347572555273038037623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255565048370182025358415 10883347572555273038037623)
          ·
            refine ⟨16325021358832909557056435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10883347572555273038037623 16325021358832909557056435)
            ·
              refine ⟨24487532038249364335584653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16325021358832909557056435 24487532038249364335584653)
              ·
                refine ⟨9182824514343511625844245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24487532038249364335584653 9182824514343511625844245)
                ·
                  refine ⟨430444899109852107461449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9182824514343511625844245 430444899109852107461449)
                  ·
                    rfl

theorem cell23_7544596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_7544596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544596 prefixEnd_7544596 := by exact prefixLift 7544596
  have htrace : WordTrace (prefixWord ++ tailWord_7544596) baseStart_7544596 baseEnd_7544596 := by
    simpa [prefixWord, tailWord_7544596, baseEnd_7544596] using wordTrace_append hprefix tailTrace_7544596
  have hstable : (prefixWord ++ tailWord_7544596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544596).length < 2 ^ (prefixWord ++ tailWord_7544596).sum := by decide
  have hdescent : baseEnd_7544596 < baseStart_7544596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544612 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7544612 : Nat := 118140960795 + 7544612 * 2 ^ 59
def prefixEnd_7544612 : Nat := 4983230072969 + 3 ^ 40 * 7544612 * 2
def baseEnd_7544612 : Nat := 3874012307679140904552967

theorem tailTrace_7544612 : CollatzResearch.WordTrace tailWord_7544612 prefixEnd_7544612 3874012307679140904552967 := by
  unfold tailWord_7544612
  simp only [CollatzResearch.WordTrace]
  refine ⟨137587303071583357995310045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183449737428777810660413393 137587303071583357995310045)
  ·
    refine ⟨51595238651843759248241267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137587303071583357995310045 51595238651843759248241267)
    ·
      refine ⟨77392857977765638872361901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51595238651843759248241267 77392857977765638872361901)
      ·
        refine ⟨29022321741662114577135713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77392857977765638872361901 29022321741662114577135713)
        ·
          refine ⟨21766741306246585932851785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29022321741662114577135713 21766741306246585932851785)
          ·
            refine ⟨16325055979684939449638839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21766741306246585932851785 16325055979684939449638839)
            ·
              refine ⟨24487583969527409174458259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16325055979684939449638839 24487583969527409174458259)
              ·
                refine ⟨36731375954291113761687389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24487583969527409174458259 36731375954291113761687389)
                ·
                  refine ⟨13774265982859167660632771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36731375954291113761687389 13774265982859167660632771)
                  ·
                    refine ⟨20661398974288751490949157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13774265982859167660632771 20661398974288751490949157)
                    ·
                      refine ⟨3874012307679140904552967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20661398974288751490949157 3874012307679140904552967)
                      ·
                        rfl

theorem cell23_7544612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7544612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544612 prefixEnd_7544612 := by exact prefixLift 7544612
  have htrace : WordTrace (prefixWord ++ tailWord_7544612) baseStart_7544612 baseEnd_7544612 := by
    simpa [prefixWord, tailWord_7544612, baseEnd_7544612] using wordTrace_append hprefix tailTrace_7544612
  have hstable : (prefixWord ++ tailWord_7544612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544612).length < 2 ^ (prefixWord ++ tailWord_7544612).sum := by decide
  have hdescent : baseEnd_7544612 < baseStart_7544612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544625 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7544625 : Nat := 118140960795 + 7544625 * 2 ^ 59
def prefixEnd_7544625 : Nat := 4983230072969 + 3 ^ 40 * 7544625 * 2
def baseEnd_7544625 : Nat := 3874018982927649353690407

theorem tailTrace_7544625 : CollatzResearch.WordTrace tailWord_7544625 prefixEnd_7544625 3874018982927649353690407 := by
  unfold tailWord_7544625
  simp only [CollatzResearch.WordTrace]
  refine ⟨275175080292119619210843329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183450053528079746140562219 275175080292119619210843329)
  ·
    refine ⟨206381310219089714408132497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275175080292119619210843329 206381310219089714408132497)
    ·
      refine ⟨154785982664317285806099373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206381310219089714408132497 154785982664317285806099373)
      ·
        refine ⟨58044743499118982177287265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154785982664317285806099373 58044743499118982177287265)
        ·
          refine ⟨43533557624339236632965449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58044743499118982177287265 43533557624339236632965449)
          ·
            refine ⟨32650168218254427474724087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43533557624339236632965449 32650168218254427474724087)
            ·
              refine ⟨48975252327381641212086131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32650168218254427474724087 48975252327381641212086131)
              ·
                refine ⟨73462878491072461818129197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48975252327381641212086131 73462878491072461818129197)
                ·
                  refine ⟨27548579434152173181798449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73462878491072461818129197 27548579434152173181798449)
                  ·
                    refine ⟨20661434575614129886348837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27548579434152173181798449 20661434575614129886348837)
                    ·
                      refine ⟨3874018982927649353690407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20661434575614129886348837 3874018982927649353690407)
                      ·
                        rfl

theorem cell23_7544625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7544625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544625 prefixEnd_7544625 := by exact prefixLift 7544625
  have htrace : WordTrace (prefixWord ++ tailWord_7544625) baseStart_7544625 baseEnd_7544625 := by
    simpa [prefixWord, tailWord_7544625, baseEnd_7544625] using wordTrace_append hprefix tailTrace_7544625
  have hstable : (prefixWord ++ tailWord_7544625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544625).length < 2 ^ (prefixWord ++ tailWord_7544625).sum := by decide
  have hdescent : baseEnd_7544625 < baseStart_7544625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544632 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_7544632 : Nat := 118140960795 + 7544632 * 2 ^ 59
def prefixEnd_7544632 : Nat := 4983230072969 + 3 ^ 40 * 7544632 * 2
def baseEnd_7544632 : Nat := 3874022577292230826302875

theorem tailTrace_7544632 : CollatzResearch.WordTrace tailWord_7544632 prefixEnd_7544632 3874022577292230826302875 := by
  unfold tailWord_7544632
  simp only [CollatzResearch.WordTrace]
  refine ⟨137587667801547129703174075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183450223735396172937565433 137587667801547129703174075)
  ·
    refine ⟨206381501702320694554761113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137587667801547129703174075 206381501702320694554761113)
    ·
      refine ⟨154786126276740520916070835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206381501702320694554761113 154786126276740520916070835)
      ·
        refine ⟨232179189415110781374106253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154786126276740520916070835 232179189415110781374106253)
        ·
          refine ⟨87067196030666543015289845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232179189415110781374106253 87067196030666543015289845)
          ·
            refine ⟨8162549627874988407683423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87067196030666543015289845 8162549627874988407683423)
            ·
              refine ⟨12243824441812482611525135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162549627874988407683423 12243824441812482611525135)
              ·
                refine ⟨18365736662718723917287703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12243824441812482611525135 18365736662718723917287703)
                ·
                  refine ⟨27548604994078085875931555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18365736662718723917287703 27548604994078085875931555)
                  ·
                    refine ⟨41322907491117128813897333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27548604994078085875931555 41322907491117128813897333)
                    ·
                      refine ⟨3874022577292230826302875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41322907491117128813897333 3874022577292230826302875)
                      ·
                        rfl

theorem cell23_7544632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_7544632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544632 prefixEnd_7544632 := by exact prefixLift 7544632
  have htrace : WordTrace (prefixWord ++ tailWord_7544632) baseStart_7544632 baseEnd_7544632 := by
    simpa [prefixWord, tailWord_7544632, baseEnd_7544632] using wordTrace_append hprefix tailTrace_7544632
  have hstable : (prefixWord ++ tailWord_7544632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544632).length < 2 ^ (prefixWord ++ tailWord_7544632).sum := by decide
  have hdescent : baseEnd_7544632 < baseStart_7544632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544639 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 2, 4]
def baseStart_7544639 : Nat := 118140960795 + 7544639 * 2 ^ 59
def prefixEnd_7544639 : Nat := 4983230072969 + 3 ^ 40 * 7544639 * 2
def baseEnd_7544639 : Nat := 1291342057218937432971781

theorem tailTrace_7544639 : CollatzResearch.WordTrace tailWord_7544639 prefixEnd_7544639 1291342057218937432971781 := by
  unfold tailWord_7544639
  simp only [CollatzResearch.WordTrace]
  refine ⟨275175590914068899601852971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183450393942712599734568647 275175590914068899601852971)
  ·
    refine ⟨412763386371103349402779457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275175590914068899601852971 412763386371103349402779457)
    ·
      refine ⟨309572539778327512052084593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412763386371103349402779457 309572539778327512052084593)
      ·
        refine ⟨232179404833745634039063445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309572539778327512052084593 232179404833745634039063445)
        ·
          refine ⟨10883409601581826595581099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232179404833745634039063445 10883409601581826595581099)
          ·
            refine ⟨16325114402372739893371649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10883409601581826595581099 16325114402372739893371649)
            ·
              refine ⟨12243835801779554920028737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16325114402372739893371649 12243835801779554920028737)
              ·
                refine ⟨9182876851334666190021553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12243835801779554920028737 9182876851334666190021553)
                ·
                  refine ⟨6887157638500999642516165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9182876851334666190021553 6887157638500999642516165)
                  ·
                    refine ⟨1291342057218937432971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887157638500999642516165 1291342057218937432971781)
                    ·
                      rfl

theorem cell23_7544639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_7544639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544639 prefixEnd_7544639 := by exact prefixLift 7544639
  have htrace : WordTrace (prefixWord ++ tailWord_7544639) baseStart_7544639 baseEnd_7544639 := by
    simpa [prefixWord, tailWord_7544639, baseEnd_7544639] using wordTrace_append hprefix tailTrace_7544639
  have hstable : (prefixWord ++ tailWord_7544639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544639).length < 2 ^ (prefixWord ++ tailWord_7544639).sum := by decide
  have hdescent : baseEnd_7544639 < baseStart_7544639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544645 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_7544645 : Nat := 118140960795 + 7544645 * 2 ^ 59
def prefixEnd_7544645 : Nat := 4983230072969 + 3 ^ 40 * 7544645 * 2
def baseEnd_7544645 : Nat := 3874029252540739275440315

theorem tailTrace_7544645 : CollatzResearch.WordTrace tailWord_7544645 prefixEnd_7544645 3874029252540739275440315 := by
  unfold tailWord_7544645
  simp only [CollatzResearch.WordTrace]
  refine ⟨275175809752047162626571389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183450539834698108417714259 275175809752047162626571389)
  ·
    refine ⟨103190928657017685984964271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275175809752047162626571389 103190928657017685984964271)
    ·
      refine ⟨154786392985526528977446407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103190928657017685984964271 154786392985526528977446407)
      ·
        refine ⟨232179589478289793466169611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154786392985526528977446407 232179589478289793466169611)
        ·
          refine ⟨348269384217434690199254417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232179589478289793466169611 348269384217434690199254417)
          ·
            refine ⟨261202038163076017649440813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348269384217434690199254417 261202038163076017649440813)
            ·
              refine ⟨97950764311153506618540305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261202038163076017649440813 97950764311153506618540305)
              ·
                refine ⟨73463073233365129963905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97950764311153506618540305 73463073233365129963905229)
                ·
                  refine ⟨27548652462511923736464461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73463073233365129963905229 27548652462511923736464461)
                  ·
                    refine ⟨10330744673441971401174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27548652462511923736464461 10330744673441971401174173)
                    ·
                      refine ⟨3874029252540739275440315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10330744673441971401174173 3874029252540739275440315)
                      ·
                        rfl

theorem cell23_7544645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_7544645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544645 prefixEnd_7544645 := by exact prefixLift 7544645
  have htrace : WordTrace (prefixWord ++ tailWord_7544645) baseStart_7544645 baseEnd_7544645 := by
    simpa [prefixWord, tailWord_7544645, baseEnd_7544645] using wordTrace_append hprefix tailTrace_7544645
  have hstable : (prefixWord ++ tailWord_7544645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544645).length < 2 ^ (prefixWord ++ tailWord_7544645).sum := by decide
  have hdescent : baseEnd_7544645 < baseStart_7544645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544652 : List Nat := [2, 2, 1, 3, 4, 2, 1, 8]
def baseStart_7544652 : Nat := 118140960795 + 7544652 * 2 ^ 59
def prefixEnd_7544652 : Nat := 4983230072969 + 3 ^ 40 * 7544652 * 2
def baseEnd_7544652 : Nat := 143482698033530398076029

theorem tailTrace_7544652 : CollatzResearch.WordTrace tailWord_7544652 prefixEnd_7544652 143482698033530398076029 := by
  unfold tailWord_7544652
  simp only [CollatzResearch.WordTrace]
  refine ⟨137588032531510901411038105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183450710042014535214717473 137588032531510901411038105)
  ·
    refine ⟨103191024398633176058278579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137588032531510901411038105 103191024398633176058278579)
    ·
      refine ⟨154786536597949764087417869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103191024398633176058278579 154786536597949764087417869)
      ·
        refine ⟨58044951224231161532781701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154786536597949764087417869 58044951224231161532781701)
        ·
          refine ⟨10883428354543342787396569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58044951224231161532781701 10883428354543342787396569)
          ·
            refine ⟨8162571265907507090547427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10883428354543342787396569 8162571265907507090547427)
            ·
              refine ⟨12243856898861260635821141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162571265907507090547427 12243856898861260635821141)
              ·
                refine ⟨143482698033530398076029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12243856898861260635821141 143482698033530398076029)
                ·
                  rfl

theorem cell23_7544652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 8].length) (baseStart_7544652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544652 prefixEnd_7544652 := by exact prefixLift 7544652
  have htrace : WordTrace (prefixWord ++ tailWord_7544652) baseStart_7544652 baseEnd_7544652 := by
    simpa [prefixWord, tailWord_7544652, baseEnd_7544652] using wordTrace_append hprefix tailTrace_7544652
  have hstable : (prefixWord ++ tailWord_7544652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544652).length < 2 ^ (prefixWord ++ tailWord_7544652).sum := by decide
  have hdescent : baseEnd_7544652 < baseStart_7544652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544689 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_7544689 : Nat := 118140960795 + 7544689 * 2 ^ 59
def prefixEnd_7544689 : Nat := 4983230072969 + 3 ^ 40 * 7544689 * 2
def baseEnd_7544689 : Nat := 3874051845689537103290113

theorem tailTrace_7544689 : CollatzResearch.WordTrace tailWord_7544689 prefixEnd_7544689 3874051845689537103290113 := by
  unfold tailWord_7544689
  simp only [CollatzResearch.WordTrace]
  refine ⟨275177414563887758141173121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183451609709258505427448747 275177414563887758141173121)
  ·
    refine ⟨206383060922915818605879841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275177414563887758141173121 206383060922915818605879841)
    ·
      refine ⟨154787295692186863954409881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206383060922915818605879841 154787295692186863954409881)
      ·
        refine ⟨116090471769140147965807411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154787295692186863954409881 116090471769140147965807411)
        ·
          refine ⟨174135707653710221948711117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116090471769140147965807411 174135707653710221948711117)
          ·
            refine ⟨65300890370141333230766669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174135707653710221948711117 65300890370141333230766669)
            ·
              refine ⟨24487833888802999961537501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65300890370141333230766669 24487833888802999961537501)
              ·
                refine ⟨9182937708301124985576563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24487833888802999961537501 9182937708301124985576563)
                ·
                  refine ⟨13774406562451687478364845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9182937708301124985576563 13774406562451687478364845)
                  ·
                    refine ⟨5165402460919382804386817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13774406562451687478364845 5165402460919382804386817)
                    ·
                      refine ⟨3874051845689537103290113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165402460919382804386817 3874051845689537103290113)
                      ·
                        rfl

theorem cell23_7544689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_7544689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544689 prefixEnd_7544689 := by exact prefixLift 7544689
  have htrace : WordTrace (prefixWord ++ tailWord_7544689) baseStart_7544689 baseEnd_7544689 := by
    simpa [prefixWord, tailWord_7544689, baseEnd_7544689] using wordTrace_append hprefix tailTrace_7544689
  have hstable : (prefixWord ++ tailWord_7544689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544689).length < 2 ^ (prefixWord ++ tailWord_7544689).sum := by decide
  have hdescent : baseEnd_7544689 < baseStart_7544689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544725 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 7]
def baseStart_7544725 : Nat := 118140960795 + 7544725 * 2 ^ 59
def prefixEnd_7544725 : Nat := 4983230072969 + 3 ^ 40 * 7544725 * 2
def baseEnd_7544725 : Nat := 430452258999233218048883

theorem tailTrace_7544725 : CollatzResearch.WordTrace tailWord_7544725 prefixEnd_7544725 430452258999233218048883 := by
  unfold tailWord_7544725
  simp only [CollatzResearch.WordTrace]
  refine ⟨275178727591757336289483629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183452485061171557526322419 275178727591757336289483629)
  ·
    refine ⟨103192022846909001108556361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275178727591757336289483629 103192022846909001108556361)
    ·
      refine ⟨77394017135181750831417271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103192022846909001108556361 77394017135181750831417271)
      ·
        refine ⟨116091025702772626247125907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77394017135181750831417271 116091025702772626247125907)
        ·
          refine ⟨174136538554158939370688861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116091025702772626247125907 174136538554158939370688861)
          ·
            refine ⟨65301201957809602264008323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174136538554158939370688861 65301201957809602264008323)
            ·
              refine ⟨97951802936714403396012485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65301201957809602264008323 97951802936714403396012485)
              ·
                refine ⟨18365963050633950636752341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97951802936714403396012485 18365963050633950636752341)
                ·
                  refine ⟨430452258999233218048883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18365963050633950636752341 430452258999233218048883)
                  ·
                    rfl

theorem cell23_7544725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_7544725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544725 prefixEnd_7544725 := by exact prefixLift 7544725
  have htrace : WordTrace (prefixWord ++ tailWord_7544725) baseStart_7544725 baseEnd_7544725 := by
    simpa [prefixWord, tailWord_7544725, baseEnd_7544725] using wordTrace_append hprefix tailTrace_7544725
  have hstable : (prefixWord ++ tailWord_7544725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544725).length < 2 ^ (prefixWord ++ tailWord_7544725).sum := by decide
  have hdescent : baseEnd_7544725 < baseStart_7544725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544789 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7544789 : Nat := 118140960795 + 7544789 * 2 ^ 59
def prefixEnd_7544789 : Nat := 4983230072969 + 3 ^ 40 * 7544789 * 2
def baseEnd_7544789 : Nat := 1291367731251662237346551

theorem tailTrace_7544789 : CollatzResearch.WordTrace tailWord_7544789 prefixEnd_7544789 1291367731251662237346551 := by
  unfold tailWord_7544789
  simp only [CollatzResearch.WordTrace]
  refine ⟨275181061863525475219813421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183454041242350316813208947 275181061863525475219813421)
  ·
    refine ⟨103192898198822053207430033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275181061863525475219813421 103192898198822053207430033)
    ·
      refine ⟨77394673649116539905572525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103192898198822053207430033 77394673649116539905572525)
      ·
        refine ⟨29023002618418702464589697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77394673649116539905572525 29023002618418702464589697)
        ·
          refine ⟨21767251963814026848442273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29023002618418702464589697 21767251963814026848442273)
          ·
            refine ⟨16325438972860520136331705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21767251963814026848442273 16325438972860520136331705)
            ·
              refine ⟨12244079229645390102248779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16325438972860520136331705 12244079229645390102248779)
              ·
                refine ⟨18366118844468085153373169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12244079229645390102248779 18366118844468085153373169)
                ·
                  refine ⟨13774589133351063865029877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18366118844468085153373169 13774589133351063865029877)
                  ·
                    refine ⟨1291367731251662237346551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13774589133351063865029877 1291367731251662237346551)
                    ·
                      rfl

theorem cell23_7544789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7544789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544789 prefixEnd_7544789 := by exact prefixLift 7544789
  have htrace : WordTrace (prefixWord ++ tailWord_7544789) baseStart_7544789 baseEnd_7544789 := by
    simpa [prefixWord, tailWord_7544789, baseEnd_7544789] using wordTrace_append hprefix tailTrace_7544789
  have hstable : (prefixWord ++ tailWord_7544789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544789).length < 2 ^ (prefixWord ++ tailWord_7544789).sum := by decide
  have hdescent : baseEnd_7544789 < baseStart_7544789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544853 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_7544853 : Nat := 118140960795 + 7544853 * 2 ^ 59
def prefixEnd_7544853 : Nat := 4983230072969 + 3 ^ 40 * 7544853 * 2
def baseEnd_7544853 : Nat := 1291378685505624820546453

theorem tailTrace_7544853 : CollatzResearch.WordTrace tailWord_7544853 prefixEnd_7544853 1291378685505624820546453 := by
  unfold tailWord_7544853
  simp only [CollatzResearch.WordTrace]
  refine ⟨275183396135293614150143213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183455597423529076100095475 275183396135293614150143213)
  ·
    refine ⟨103193773550735105306303705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275183396135293614150143213 103193773550735105306303705)
    ·
      refine ⟨77395330163051328979727779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103193773550735105306303705 77395330163051328979727779)
      ·
        refine ⟨116092995244576993469591669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77395330163051328979727779 116092995244576993469591669)
        ·
          refine ⟨10883718304179093137774219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116092995244576993469591669 10883718304179093137774219)
          ·
            refine ⟨16325577456268639706661329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10883718304179093137774219 16325577456268639706661329)
            ·
              refine ⟨12244183092201479779995997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16325577456268639706661329 12244183092201479779995997)
              ·
                refine ⟨4591568659575554917498499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244183092201479779995997 4591568659575554917498499)
                ·
                  refine ⟨6887352989363332376247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591568659575554917498499 6887352989363332376247749)
                  ·
                    refine ⟨1291378685505624820546453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887352989363332376247749 1291378685505624820546453)
                    ·
                      rfl

theorem cell23_7544853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_7544853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544853 prefixEnd_7544853 := by exact prefixLift 7544853
  have htrace : WordTrace (prefixWord ++ tailWord_7544853) baseStart_7544853 baseEnd_7544853 := by
    simpa [prefixWord, tailWord_7544853, baseEnd_7544853] using wordTrace_append hprefix tailTrace_7544853
  have hstable : (prefixWord ++ tailWord_7544853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544853).length < 2 ^ (prefixWord ++ tailWord_7544853).sum := by decide
  have hdescent : baseEnd_7544853 < baseStart_7544853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544886 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7544886 : Nat := 118140960795 + 7544886 * 2 ^ 59
def prefixEnd_7544886 : Nat := 4983230072969 + 3 ^ 40 * 7544886 * 2
def baseEnd_7544886 : Nat := 3874153001378472832526707

theorem tailTrace_7544886 : CollatzResearch.WordTrace tailWord_7544886 prefixEnd_7544886 3874153001378472832526707 := by
  unfold tailWord_7544886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17199037484010878799130907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183456399829449373857396341 17199037484010878799130907)
  ·
    refine ⟨25798556226016318198696361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17199037484010878799130907 25798556226016318198696361)
    ·
      refine ⟨19348917169512238649022271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25798556226016318198696361 19348917169512238649022271)
      ·
        refine ⟨29023375754268357973533407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19348917169512238649022271 29023375754268357973533407)
        ·
          refine ⟨43535063631402536960300111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29023375754268357973533407 43535063631402536960300111)
          ·
            refine ⟨65302595447103805440450167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43535063631402536960300111 65302595447103805440450167)
            ·
              refine ⟨97953893170655708160675251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65302595447103805440450167 97953893170655708160675251)
              ·
                refine ⟨146930839755983562241012877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97953893170655708160675251 146930839755983562241012877)
                ·
                  refine ⟨55099064908493835840379829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146930839755983562241012877 55099064908493835840379829)
                  ·
                    refine ⟨5165537335171297110035609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55099064908493835840379829 5165537335171297110035609)
                    ·
                      refine ⟨3874153001378472832526707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165537335171297110035609 3874153001378472832526707)
                      ·
                        rfl

theorem cell23_7544886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7544886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544886 prefixEnd_7544886 := by exact prefixLift 7544886
  have htrace : WordTrace (prefixWord ++ tailWord_7544886) baseStart_7544886 baseEnd_7544886 := by
    simpa [prefixWord, tailWord_7544886, baseEnd_7544886] using wordTrace_append hprefix tailTrace_7544886
  have hstable : (prefixWord ++ tailWord_7544886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544886).length < 2 ^ (prefixWord ++ tailWord_7544886).sum := by decide
  have hdescent : baseEnd_7544886 < baseStart_7544886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544909 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7544909 : Nat := 118140960795 + 7544909 * 2 ^ 59
def prefixEnd_7544909 : Nat := 4983230072969 + 3 ^ 40 * 7544909 * 2
def baseEnd_7544909 : Nat := 1291388270477842080846367

theorem tailTrace_7544909 : CollatzResearch.WordTrace tailWord_7544909 prefixEnd_7544909 1291388270477842080846367 := by
  unfold tailWord_7544909
  simp only [CollatzResearch.WordTrace]
  refine ⟨275185438623090735714181781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183456959082060490476121187 275185438623090735714181781)
  ·
    refine ⟨12899317435457378236602271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275185438623090735714181781 12899317435457378236602271)
    ·
      refine ⟨19348976153186067354903407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12899317435457378236602271 19348976153186067354903407)
      ·
        refine ⟨29023464229779101032355111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19348976153186067354903407 29023464229779101032355111)
        ·
          refine ⟨43535196344668651548532667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29023464229779101032355111 43535196344668651548532667)
          ·
            refine ⟨65302794517002977322799001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43535196344668651548532667 65302794517002977322799001)
            ·
              refine ⟨48977095887752232992099251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65302794517002977322799001 48977095887752232992099251)
              ·
                refine ⟨73465643831628349488148877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48977095887752232992099251 73465643831628349488148877)
                ·
                  refine ⟨27549616436860631058055829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73465643831628349488148877 27549616436860631058055829)
                  ·
                    refine ⟨1291388270477842080846367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27549616436860631058055829 1291388270477842080846367)
                    ·
                      rfl

theorem cell23_7544909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7544909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544909 prefixEnd_7544909 := by exact prefixLift 7544909
  have htrace : WordTrace (prefixWord ++ tailWord_7544909) baseStart_7544909 baseEnd_7544909 := by
    simpa [prefixWord, tailWord_7544909, baseEnd_7544909] using wordTrace_append hprefix tailTrace_7544909
  have hstable : (prefixWord ++ tailWord_7544909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544909).length < 2 ^ (prefixWord ++ tailWord_7544909).sum := by decide
  have hdescent : baseEnd_7544909 < baseStart_7544909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544910 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_7544910 : Nat := 118140960795 + 7544910 * 2 ^ 59
def prefixEnd_7544910 : Nat := 4983230072969 + 3 ^ 40 * 7544910 * 2
def baseEnd_7544910 : Nat := 3874165324914180738626597

theorem tailTrace_7544910 : CollatzResearch.WordTrace tailWord_7544910 prefixEnd_7544910 3874165324914180738626597 := by
  unfold tailWord_7544910
  simp only [CollatzResearch.WordTrace]
  refine ⟨34398184387010889110621023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183456983397391408589978789 34398184387010889110621023)
  ·
    refine ⟨51597276580516333665931535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34398184387010889110621023 51597276580516333665931535)
    ·
      refine ⟨77395914870774500498897303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51597276580516333665931535 77395914870774500498897303)
      ·
        refine ⟨116093872306161750748345955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77395914870774500498897303 116093872306161750748345955)
        ·
          refine ⟨174140808459242626122518933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116093872306161750748345955 174140808459242626122518933)
          ·
            refine ⟨8162850396526998099493075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174140808459242626122518933 8162850396526998099493075)
            ·
              refine ⟨12244275594790497149239613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162850396526998099493075 12244275594790497149239613)
              ·
                refine ⟨4591603348046436430964855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244275594790497149239613 4591603348046436430964855)
                ·
                  refine ⟨6887405022069654646447283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591603348046436430964855 6887405022069654646447283)
                  ·
                    refine ⟨10331107533104481969670925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887405022069654646447283 10331107533104481969670925)
                    ·
                      refine ⟨3874165324914180738626597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331107533104481969670925 3874165324914180738626597)
                      ·
                        rfl

theorem cell23_7544910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_7544910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544910 prefixEnd_7544910 := by exact prefixLift 7544910
  have htrace : WordTrace (prefixWord ++ tailWord_7544910) baseStart_7544910 baseEnd_7544910 := by
    simpa [prefixWord, tailWord_7544910, baseEnd_7544910] using wordTrace_append hprefix tailTrace_7544910
  have hstable : (prefixWord ++ tailWord_7544910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544910).length < 2 ^ (prefixWord ++ tailWord_7544910).sum := by decide
  have hdescent : baseEnd_7544910 < baseStart_7544910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544933 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_7544933 : Nat := 118140960795 + 7544933 * 2 ^ 59
def prefixEnd_7544933 : Nat := 4983230072969 + 3 ^ 40 * 7544933 * 2
def baseEnd_7544933 : Nat := 3874177134969234148638991

theorem tailTrace_7544933 : CollatzResearch.WordTrace tailWord_7544933 prefixEnd_7544933 3874177134969234148638991 := by
  unfold tailWord_7544933
  simp only [CollatzResearch.WordTrace]
  refine ⟨275186313975003787813055453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183457542650002525208703635 275186313975003787813055453)
  ·
    refine ⟨103194867740626420429895795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275186313975003787813055453 103194867740626420429895795)
    ·
      refine ⟨154792301610939630644843693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103194867740626420429895795 154792301610939630644843693)
      ·
        refine ⟨58047113104102361491816385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154792301610939630644843693 58047113104102361491816385)
        ·
          refine ⟨43535334828076771118862289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58047113104102361491816385 43535334828076771118862289)
          ·
            refine ⟨32651501121057578339146717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43535334828076771118862289 32651501121057578339146717)
            ·
              refine ⟨12244312920396591877180019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32651501121057578339146717 12244312920396591877180019)
              ·
                refine ⟨18366469380594887815770029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12244312920396591877180019 18366469380594887815770029)
                ·
                  refine ⟨6887426017723082930913761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18366469380594887815770029 6887426017723082930913761)
                  ·
                    refine ⟨5165569513292312198185321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6887426017723082930913761 5165569513292312198185321)
                    ·
                      refine ⟨3874177134969234148638991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165569513292312198185321 3874177134969234148638991)
                      ·
                        rfl

theorem cell23_7544933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_7544933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544933 prefixEnd_7544933 := by exact prefixLift 7544933
  have htrace : WordTrace (prefixWord ++ tailWord_7544933) baseStart_7544933 baseEnd_7544933 := by
    simpa [prefixWord, tailWord_7544933, baseEnd_7544933] using wordTrace_append hprefix tailTrace_7544933
  have hstable : (prefixWord ++ tailWord_7544933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544933).length < 2 ^ (prefixWord ++ tailWord_7544933).sum := by decide
  have hdescent : baseEnd_7544933 < baseStart_7544933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544943 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 2, 4]
def baseStart_7544943 : Nat := 118140960795 + 7544943 * 2 ^ 59
def prefixEnd_7544943 : Nat := 4983230072969 + 3 ^ 40 * 7544943 * 2
def baseEnd_7544943 : Nat := 1291394089925259703171315

theorem tailTrace_7544943 : CollatzResearch.WordTrace tailWord_7544943 prefixEnd_7544943 1291394089925259703171315 := by
  unfold tailWord_7544943
  simp only [CollatzResearch.WordTrace]
  refine ⟨275186678704967559520919483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183457785803311706347279655 275186678704967559520919483)
  ·
    refine ⟨412780018057451339281379225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275186678704967559520919483 412780018057451339281379225)
    ·
      refine ⟨309585013543088504461034419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412780018057451339281379225 309585013543088504461034419)
      ·
        refine ⟨464377520314632756691551629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309585013543088504461034419 464377520314632756691551629)
        ·
          refine ⟨174141570117987283759331861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464377520314632756691551629 174141570117987283759331861)
          ·
            refine ⟨8162886099280653926218681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174141570117987283759331861 8162886099280653926218681)
            ·
              refine ⟨6122164574460490444664011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8162886099280653926218681 6122164574460490444664011)
              ·
                refine ⟨9183246861690735666996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122164574460490444664011 9183246861690735666996017)
                ·
                  refine ⟨6887435146268051750247013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9183246861690735666996017 6887435146268051750247013)
                  ·
                    refine ⟨1291394089925259703171315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887435146268051750247013 1291394089925259703171315)
                    ·
                      rfl

theorem cell23_7544943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_7544943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544943 prefixEnd_7544943 := by exact prefixLift 7544943
  have htrace : WordTrace (prefixWord ++ tailWord_7544943) baseStart_7544943 baseEnd_7544943 := by
    simpa [prefixWord, tailWord_7544943, baseEnd_7544943] using wordTrace_append hprefix tailTrace_7544943
  have hstable : (prefixWord ++ tailWord_7544943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544943).length < 2 ^ (prefixWord ++ tailWord_7544943).sum := by decide
  have hdescent : baseEnd_7544943 < baseStart_7544943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544953 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7544953 : Nat := 118140960795 + 7544953 * 2 ^ 59
def prefixEnd_7544953 : Nat := 4983230072969 + 3 ^ 40 * 7544953 * 2
def baseEnd_7544953 : Nat := 3874187404582324070388899

theorem tailTrace_7544953 : CollatzResearch.WordTrace tailWord_7544953 prefixEnd_7544953 3874187404582324070388899 := by
  unfold tailWord_7544953
  simp only [CollatzResearch.WordTrace]
  refine ⟨275187043434931331228783513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183458028956620887485855675 275187043434931331228783513)
  ·
    refine ⟨206390282576198498421587635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275187043434931331228783513 206390282576198498421587635)
    ·
      refine ⟨309585423864297747632381453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206390282576198498421587635 309585423864297747632381453)
      ·
        refine ⟨116094533949111655362143045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309585423864297747632381453 116094533949111655362143045)
        ·
          refine ⟨21767725115458435380401821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116094533949111655362143045 21767725115458435380401821)
          ·
            refine ⟨8162896918296913267650683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21767725115458435380401821 8162896918296913267650683)
            ·
              refine ⟨12244345377445369901476025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8162896918296913267650683 12244345377445369901476025)
              ·
                refine ⟨9183259033084027426107019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12244345377445369901476025 9183259033084027426107019)
                ·
                  refine ⟨13774888549626041139160529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183259033084027426107019 13774888549626041139160529)
                  ·
                    refine ⟨10331166412219530854370397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13774888549626041139160529 10331166412219530854370397)
                    ·
                      refine ⟨3874187404582324070388899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331166412219530854370397 3874187404582324070388899)
                      ·
                        rfl

theorem cell23_7544953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7544953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544953 prefixEnd_7544953 := by exact prefixLift 7544953
  have htrace : WordTrace (prefixWord ++ tailWord_7544953) baseStart_7544953 baseEnd_7544953 := by
    simpa [prefixWord, tailWord_7544953, baseEnd_7544953] using wordTrace_append hprefix tailTrace_7544953
  have hstable : (prefixWord ++ tailWord_7544953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544953).length < 2 ^ (prefixWord ++ tailWord_7544953).sum := by decide
  have hdescent : baseEnd_7544953 < baseStart_7544953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544984 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7544984 : Nat := 118140960795 + 7544984 * 2 ^ 59
def prefixEnd_7544984 : Nat := 4983230072969 + 3 ^ 40 * 7544984 * 2
def baseEnd_7544984 : Nat := 3874203322482613449101257

theorem tailTrace_7544984 : CollatzResearch.WordTrace tailWord_7544984 prefixEnd_7544984 3874203322482613449101257 := by
  unfold tailWord_7544984
  simp only [CollatzResearch.WordTrace]
  refine ⟨137594087048909511761581003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183458782731879349015441337 137594087048909511761581003)
  ·
    refine ⟨206391130573364267642371505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137594087048909511761581003 206391130573364267642371505)
    ·
      refine ⟨154793347930023200731778629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206391130573364267642371505 154793347930023200731778629)
      ·
        refine ⟨29023752736879350137208493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154793347930023200731778629 29023752736879350137208493)
        ·
          refine ⟨10883907276329756301453185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29023752736879350137208493 10883907276329756301453185)
          ·
            refine ⟨8162930457247317226089889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10883907276329756301453185 8162930457247317226089889)
            ·
              refine ⟨6122197842935487919567417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8162930457247317226089889 6122197842935487919567417)
              ·
                refine ⟨4591648382201615939675563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122197842935487919567417 4591648382201615939675563)
                ·
                  refine ⟨6887472573302423909513345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591648382201615939675563 6887472573302423909513345)
                  ·
                    refine ⟨5165604429976817932135009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6887472573302423909513345 5165604429976817932135009)
                    ·
                      refine ⟨3874203322482613449101257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165604429976817932135009 3874203322482613449101257)
                      ·
                        rfl

theorem cell23_7544984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7544984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544984 prefixEnd_7544984 := by exact prefixLift 7544984
  have htrace : WordTrace (prefixWord ++ tailWord_7544984) baseStart_7544984 baseEnd_7544984 := by
    simpa [prefixWord, tailWord_7544984, baseEnd_7544984] using wordTrace_append hprefix tailTrace_7544984
  have hstable : (prefixWord ++ tailWord_7544984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544984).length < 2 ^ (prefixWord ++ tailWord_7544984).sum := by decide
  have hdescent : baseEnd_7544984 < baseStart_7544984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7544989 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_7544989 : Nat := 118140960795 + 7544989 * 2 ^ 59
def prefixEnd_7544989 : Nat := 4983230072969 + 3 ^ 40 * 7544989 * 2
def baseEnd_7544989 : Nat := 3874205889885885929538733

theorem tailTrace_7544989 : CollatzResearch.WordTrace tailWord_7544989 prefixEnd_7544989 3874205889885885929538733 := by
  unfold tailWord_7544989
  simp only [CollatzResearch.WordTrace]
  refine ⟨275188356462800909377094021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183458904308533939584729347 275188356462800909377094021)
  ·
    refine ⟨51597816836775170508205129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275188356462800909377094021 51597816836775170508205129)
    ·
      refine ⟨38698362627581377881153847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51597816836775170508205129 38698362627581377881153847)
      ·
        refine ⟨58047543941372066821730771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38698362627581377881153847 58047543941372066821730771)
        ·
          refine ⟨87071315912058100232596157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58047543941372066821730771 87071315912058100232596157)
          ·
            refine ⟨32651743467021787587223559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87071315912058100232596157 32651743467021787587223559)
            ·
              refine ⟨48977615200532681380835339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32651743467021787587223559 48977615200532681380835339)
              ·
                refine ⟨73466422800799022071253009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48977615200532681380835339 73466422800799022071253009)
                ·
                  refine ⟨55099817100599266553439757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73466422800799022071253009 55099817100599266553439757)
                  ·
                    refine ⟨20662431412724724957539909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55099817100599266553439757 20662431412724724957539909)
                    ·
                      refine ⟨3874205889885885929538733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20662431412724724957539909 3874205889885885929538733)
                      ·
                        rfl

theorem cell23_7544989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_7544989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7544989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7544989 prefixEnd_7544989 := by exact prefixLift 7544989
  have htrace : WordTrace (prefixWord ++ tailWord_7544989) baseStart_7544989 baseEnd_7544989 := by
    simpa [prefixWord, tailWord_7544989, baseEnd_7544989] using wordTrace_append hprefix tailTrace_7544989
  have hstable : (prefixWord ++ tailWord_7544989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7544989).length < 2 ^ (prefixWord ++ tailWord_7544989).sum := by decide
  have hdescent : baseEnd_7544989 < baseStart_7544989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7544989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545039 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_7545039 : Nat := 118140960795 + 7545039 * 2 ^ 59
def prefixEnd_7545039 : Nat := 4983230072969 + 3 ^ 40 * 7545039 * 2
def baseEnd_7545039 : Nat := 3874231563918610733913503

theorem tailTrace_7545039 : CollatzResearch.WordTrace tailWord_7545039 prefixEnd_7545039 3874231563918610733913503 := by
  unfold tailWord_7545039
  simp only [CollatzResearch.WordTrace]
  refine ⟨275190180112619767916414171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183460120075079845277609447 275190180112619767916414171)
  ·
    refine ⟨412785270168929651874621257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275190180112619767916414171 412785270168929651874621257)
    ·
      refine ⟨309588952626697238905965943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412785270168929651874621257 309588952626697238905965943)
      ·
        refine ⟨464383428940045858358948915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309588952626697238905965943 464383428940045858358948915)
        ·
          refine ⟨696575143410068787538423373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464383428940045858358948915 696575143410068787538423373)
          ·
            refine ⟨261215678778775795326908765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696575143410068787538423373 261215678778775795326908765)
            ·
              refine ⟨97955879542040923247590787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261215678778775795326908765 97955879542040923247590787)
              ·
                refine ⟨146933819313061384871386181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97955879542040923247590787 146933819313061384871386181)
                ·
                  refine ⟨27550091121199009663384909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146933819313061384871386181 27550091121199009663384909)
                  ·
                    refine ⟨10331284170449628623769341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27550091121199009663384909 10331284170449628623769341)
                    ·
                      refine ⟨3874231563918610733913503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331284170449628623769341 3874231563918610733913503)
                      ·
                        rfl

theorem cell23_7545039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_7545039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545039 prefixEnd_7545039 := by exact prefixLift 7545039
  have htrace : WordTrace (prefixWord ++ tailWord_7545039) baseStart_7545039 baseEnd_7545039 := by
    simpa [prefixWord, tailWord_7545039, baseEnd_7545039] using wordTrace_append hprefix tailTrace_7545039
  have hstable : (prefixWord ++ tailWord_7545039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545039).length < 2 ^ (prefixWord ++ tailWord_7545039).sum := by decide
  have hdescent : baseEnd_7545039 < baseStart_7545039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545086 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7545086 : Nat := 118140960795 + 7545086 * 2 ^ 59
def prefixEnd_7545086 : Nat := 4983230072969 + 3 ^ 40 * 7545086 * 2
def baseEnd_7545086 : Nat := 3874255697509372050025787

theorem tailTrace_7545086 : CollatzResearch.WordTrace tailWord_7545086 prefixEnd_7545086 3874255697509372050025787 := by
  unfold tailWord_7545086
  simp only [CollatzResearch.WordTrace]
  refine ⟨34398986792931186867921889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183461262895632996628916741 34398986792931186867921889)
  ·
    refine ⟨25799240094698390150941417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34398986792931186867921889 25799240094698390150941417)
    ·
      refine ⟨19349430071023792613206063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25799240094698390150941417 19349430071023792613206063)
      ·
        refine ⟨29024145106535688919809095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19349430071023792613206063 29024145106535688919809095)
        ·
          refine ⟨43536217659803533379713643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29024145106535688919809095 43536217659803533379713643)
          ·
            refine ⟨65304326489705300069570465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43536217659803533379713643 65304326489705300069570465)
            ·
              refine ⟨48978244867278975052177849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65304326489705300069570465 48978244867278975052177849)
              ·
                refine ⟨36733683650459231289133387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48978244867278975052177849 36733683650459231289133387)
                ·
                  refine ⟨55100525475688846933700081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36733683650459231289133387 55100525475688846933700081)
                  ·
                    refine ⟨41325394106766635200275061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55100525475688846933700081 41325394106766635200275061)
                    ·
                      refine ⟨3874255697509372050025787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41325394106766635200275061 3874255697509372050025787)
                      ·
                        rfl

theorem cell23_7545086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7545086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545086 prefixEnd_7545086 := by exact prefixLift 7545086
  have htrace : WordTrace (prefixWord ++ tailWord_7545086) baseStart_7545086 baseEnd_7545086 := by
    simpa [prefixWord, tailWord_7545086, baseEnd_7545086] using wordTrace_append hprefix tailTrace_7545086
  have hstable : (prefixWord ++ tailWord_7545086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545086).length < 2 ^ (prefixWord ++ tailWord_7545086).sum := by decide
  have hdescent : baseEnd_7545086 < baseStart_7545086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545096 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7545096 : Nat := 118140960795 + 7545096 * 2 ^ 59
def prefixEnd_7545096 : Nat := 4983230072969 + 3 ^ 40 * 7545096 * 2
def baseEnd_7545096 : Nat := 3874260832315917010900741

theorem tailTrace_7545096 : CollatzResearch.WordTrace tailWord_7545096 prefixEnd_7545096 3874260832315917010900741 := by
  unfold tailWord_7545096
  simp only [CollatzResearch.WordTrace]
  refine ⟨137596129536706633325619571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183461506048942177767492761 137596129536706633325619571)
  ·
    refine ⟨206394194305059949988429357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137596129536706633325619571 206394194305059949988429357)
    ·
      refine ⟨77397822864397481245661009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206394194305059949988429357 77397822864397481245661009)
      ·
        refine ⟨58048367148298110934245757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77397822864397481245661009 58048367148298110934245757)
        ·
          refine ⟨21768137680611791600342159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58048367148298110934245757 21768137680611791600342159)
          ·
            refine ⟨32652206520917687400513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768137680611791600342159 32652206520917687400513239)
            ·
              refine ⟨48978309781376531100769859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32652206520917687400513239 48978309781376531100769859)
              ·
                refine ⟨73467464672064796651154789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48978309781376531100769859 73467464672064796651154789)
                ·
                  refine ⟨13775149626012149372091523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73467464672064796651154789 13775149626012149372091523)
                  ·
                    refine ⟨20662724439018224058137285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13775149626012149372091523 20662724439018224058137285)
                    ·
                      refine ⟨3874260832315917010900741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20662724439018224058137285 3874260832315917010900741)
                      ·
                        rfl

theorem cell23_7545096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7545096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545096 prefixEnd_7545096 := by exact prefixLift 7545096
  have htrace : WordTrace (prefixWord ++ tailWord_7545096) baseStart_7545096 baseEnd_7545096 := by
    simpa [prefixWord, tailWord_7545096, baseEnd_7545096] using wordTrace_append hprefix tailTrace_7545096
  have hstable : (prefixWord ++ tailWord_7545096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545096).length < 2 ^ (prefixWord ++ tailWord_7545096).sum := by decide
  have hdescent : baseEnd_7545096 < baseStart_7545096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545109 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7545109 : Nat := 118140960795 + 7545109 * 2 ^ 59
def prefixEnd_7545109 : Nat := 4983230072969 + 3 ^ 40 * 7545109 * 2
def baseEnd_7545109 : Nat := 3874267507564425460038181

theorem tailTrace_7545109 : CollatzResearch.WordTrace tailWord_7545109 prefixEnd_7545109 3874267507564425460038181 := by
  unfold tailWord_7545109
  simp only [CollatzResearch.WordTrace]
  refine ⟨275192733222366169871462381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183461822148244113247641587 275192733222366169871462381)
  ·
    refine ⟨103197274958387313701798393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275192733222366169871462381 103197274958387313701798393)
    ·
      refine ⟨77397956218790485276348795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103197274958387313701798393 77397956218790485276348795)
      ·
        refine ⟨116096934328185727914523193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77397956218790485276348795 116096934328185727914523193)
        ·
          refine ⟨87072700746139295935892395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116096934328185727914523193 87072700746139295935892395)
          ·
            refine ⟨130609051119208943903838593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87072700746139295935892395 130609051119208943903838593)
            ·
              refine ⟨97956788339406707927878945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130609051119208943903838593 97956788339406707927878945)
              ·
                refine ⟨73467591254555030945909209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97956788339406707927878945 73467591254555030945909209)
                ·
                  refine ⟨55100693440916273209431907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73467591254555030945909209 55100693440916273209431907)
                  ·
                    refine ⟨82651040161374409814147861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55100693440916273209431907 82651040161374409814147861)
                    ·
                      refine ⟨3874267507564425460038181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82651040161374409814147861 3874267507564425460038181)
                      ·
                        rfl

theorem cell23_7545109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7545109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545109 prefixEnd_7545109 := by exact prefixLift 7545109
  have htrace : WordTrace (prefixWord ++ tailWord_7545109) baseStart_7545109 baseEnd_7545109 := by
    simpa [prefixWord, tailWord_7545109, baseEnd_7545109] using wordTrace_append hprefix tailTrace_7545109
  have hstable : (prefixWord ++ tailWord_7545109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545109).length < 2 ^ (prefixWord ++ tailWord_7545109).sum := by decide
  have hdescent : baseEnd_7545109 < baseStart_7545109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545116 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7545116 : Nat := 118140960795 + 7545116 * 2 ^ 59
def prefixEnd_7545116 : Nat := 4983230072969 + 3 ^ 40 * 7545116 * 2
def baseEnd_7545116 : Nat := 3874271101929006932650649

theorem tailTrace_7545116 : CollatzResearch.WordTrace tailWord_7545116 prefixEnd_7545116 3874271101929006932650649 := by
  unfold tailWord_7545116
  simp only [CollatzResearch.WordTrace]
  refine ⟨137596494266670405033483601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183461992355560540044644801 137596494266670405033483601)
  ·
    refine ⟨103197370700002803775112701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137596494266670405033483601 103197370700002803775112701)
    ·
      refine ⟨38699014012501051415667263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103197370700002803775112701 38699014012501051415667263)
      ·
        refine ⟨58048521018751577123500895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38699014012501051415667263 58048521018751577123500895)
        ·
          refine ⟨87072781528127365685251343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58048521018751577123500895 87072781528127365685251343)
          ·
            refine ⟨130609172292191048527877015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87072781528127365685251343 130609172292191048527877015)
            ·
              refine ⟨195913758438286572791815523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130609172292191048527877015 195913758438286572791815523)
              ·
                refine ⟨293870637657429859187723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195913758438286572791815523 293870637657429859187723285)
                ·
                  refine ⟨13775186140192024649424529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293870637657429859187723285 13775186140192024649424529)
                  ·
                    refine ⟨10331389605144018487068397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13775186140192024649424529 10331389605144018487068397)
                    ·
                      refine ⟨3874271101929006932650649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331389605144018487068397 3874271101929006932650649)
                      ·
                        rfl

theorem cell23_7545116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7545116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545116 prefixEnd_7545116 := by exact prefixLift 7545116
  have htrace : WordTrace (prefixWord ++ tailWord_7545116) baseStart_7545116 baseEnd_7545116 := by
    simpa [prefixWord, tailWord_7545116, baseEnd_7545116] using wordTrace_append hprefix tailTrace_7545116
  have hstable : (prefixWord ++ tailWord_7545116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545116).length < 2 ^ (prefixWord ++ tailWord_7545116).sum := by decide
  have hdescent : baseEnd_7545116 < baseStart_7545116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545127 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7545127 : Nat := 118140960795 + 7545127 * 2 ^ 59
def prefixEnd_7545127 : Nat := 4983230072969 + 3 ^ 40 * 7545127 * 2
def baseEnd_7545127 : Nat := 1291425583405402129871033

theorem tailTrace_7545127 : CollatzResearch.WordTrace tailWord_7545127 prefixEnd_7545127 1291425583405402129871033 := by
  unfold tailWord_7545127
  simp only [CollatzResearch.WordTrace]
  refine ⟨275193389736300958945617635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183462259824200639297078423 275193389736300958945617635)
  ·
    refine ⟨412790084604451438418426453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275193389736300958945617635 412790084604451438418426453)
    ·
      refine ⟨4837383803958415293965935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 412790084604451438418426453 4837383803958415293965935)
      ·
        refine ⟨7256075705937622940948903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837383803958415293965935 7256075705937622940948903)
        ·
          refine ⟨10884113558906434411423355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256075705937622940948903 10884113558906434411423355)
          ·
            refine ⟨16326170338359651617135033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884113558906434411423355 16326170338359651617135033)
            ·
              refine ⟨12244627753769738712851275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16326170338359651617135033 12244627753769738712851275)
              ·
                refine ⟨18366941630654608069276913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12244627753769738712851275 18366941630654608069276913)
                ·
                  refine ⟨13775206222990956051957685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18366941630654608069276913 13775206222990956051957685)
                  ·
                    refine ⟨1291425583405402129871033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13775206222990956051957685 1291425583405402129871033)
                    ·
                      rfl

theorem cell23_7545127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7545127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545127 prefixEnd_7545127 := by exact prefixLift 7545127
  have htrace : WordTrace (prefixWord ++ tailWord_7545127) baseStart_7545127 baseEnd_7545127 := by
    simpa [prefixWord, tailWord_7545127, baseEnd_7545127] using wordTrace_append hprefix tailTrace_7545127
  have hstable : (prefixWord ++ tailWord_7545127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545127).length < 2 ^ (prefixWord ++ tailWord_7545127).sum := by decide
  have hdescent : baseEnd_7545127 < baseStart_7545127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545130 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7545130 : Nat := 118140960795 + 7545130 * 2 ^ 59
def prefixEnd_7545130 : Nat := 4983230072969 + 3 ^ 40 * 7545130 * 2
def baseEnd_7545130 : Nat := 3874278290658169877875585

theorem tailTrace_7545130 : CollatzResearch.WordTrace tailWord_7545130 prefixEnd_7545130 3874278290658169877875585 := by
  unfold tailWord_7545130
  simp only [CollatzResearch.WordTrace]
  refine ⟨68798374788822522614494211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183462332770193393638651229 68798374788822522614494211)
  ·
    refine ⟨103197562183233783921741317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68798374788822522614494211 103197562183233783921741317)
    ·
      refine ⟨19349542909356334485326497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103197562183233783921741317 19349542909356334485326497)
      ·
        refine ⟨14512157182017250863994873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19349542909356334485326497 14512157182017250863994873)
        ·
          refine ⟨10884117886512938147996155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14512157182017250863994873 10884117886512938147996155)
          ·
            refine ⟨16326176829769407221994233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884117886512938147996155 16326176829769407221994233)
            ·
              refine ⟨12244632622327055416495675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16326176829769407221994233 12244632622327055416495675)
              ·
                refine ⟨18366948933490583124743513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12244632622327055416495675 18366948933490583124743513)
                ·
                  refine ⟨13775211700117937343557635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18366948933490583124743513 13775211700117937343557635)
                  ·
                    refine ⟨20662817550176906015336453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13775211700117937343557635 20662817550176906015336453)
                    ·
                      refine ⟨3874278290658169877875585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20662817550176906015336453 3874278290658169877875585)
                      ·
                        rfl

theorem cell23_7545130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7545130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545130 prefixEnd_7545130 := by exact prefixLift 7545130
  have htrace : WordTrace (prefixWord ++ tailWord_7545130) baseStart_7545130 baseEnd_7545130 := by
    simpa [prefixWord, tailWord_7545130, baseEnd_7545130] using wordTrace_append hprefix tailTrace_7545130
  have hstable : (prefixWord ++ tailWord_7545130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545130).length < 2 ^ (prefixWord ++ tailWord_7545130).sum := by decide
  have hdescent : baseEnd_7545130 < baseStart_7545130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545197 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7545197 : Nat := 118140960795 + 7545197 * 2 ^ 59
def prefixEnd_7545197 : Nat := 4983230072969 + 3 ^ 40 * 7545197 * 2
def baseEnd_7545197 : Nat := 3874312693862021115737777

theorem tailTrace_7545197 : CollatzResearch.WordTrace tailWord_7545197 prefixEnd_7545197 3874312693862021115737777 := by
  unfold tailWord_7545197
  simp only [CollatzResearch.WordTrace]
  refine ⟨275195942846047360900665845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183463961897364907267110563 275195942846047360900665845)
  ·
    refine ⟨25799619641816940084437423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275195942846047360900665845 25799619641816940084437423)
    ·
      refine ⟨38699429462725410126656135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25799619641816940084437423 38699429462725410126656135)
      ·
        refine ⟨58049144194088115189984203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38699429462725410126656135 58049144194088115189984203)
        ·
          refine ⟨87073716291132172784976305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58049144194088115189984203 87073716291132172784976305)
          ·
            refine ⟨65305287218349129588732229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87073716291132172784976305 65305287218349129588732229)
            ·
              refine ⟨12244741353440461797887293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65305287218349129588732229 12244741353440461797887293)
              ·
                refine ⟨4591778007540173174207735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12244741353440461797887293 4591778007540173174207735)
                ·
                  refine ⟨6887667011310259761311603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591778007540173174207735 6887667011310259761311603)
                  ·
                    refine ⟨10331500516965389641967405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887667011310259761311603 10331500516965389641967405)
                    ·
                      refine ⟨3874312693862021115737777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331500516965389641967405 3874312693862021115737777)
                      ·
                        rfl

theorem cell23_7545197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7545197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545197 prefixEnd_7545197 := by exact prefixLift 7545197
  have htrace : WordTrace (prefixWord ++ tailWord_7545197) baseStart_7545197 baseEnd_7545197 := by
    simpa [prefixWord, tailWord_7545197, baseEnd_7545197] using wordTrace_append hprefix tailTrace_7545197
  have hstable : (prefixWord ++ tailWord_7545197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545197).length < 2 ^ (prefixWord ++ tailWord_7545197).sum := by decide
  have hdescent : baseEnd_7545197 < baseStart_7545197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545200 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_7545200 : Nat := 118140960795 + 7545200 * 2 ^ 59
def prefixEnd_7545200 : Nat := 4983230072969 + 3 ^ 40 * 7545200 * 2
def baseEnd_7545200 : Nat := 1291438078101328201333421

theorem tailTrace_7545200 : CollatzResearch.WordTrace tailWord_7545200 prefixEnd_7545200 1291438078101328201333421 := by
  unfold tailWord_7545200
  simp only [CollatzResearch.WordTrace]
  refine ⟨137598026132518246206512527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183464034843357661608683369 137598026132518246206512527)
  ·
    refine ⟨206397039198777369309768791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137598026132518246206512527 206397039198777369309768791)
    ·
      refine ⟨309595558798166053964653187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206397039198777369309768791 309595558798166053964653187)
      ·
        refine ⟨464393338197249080946979781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309595558798166053964653187 464393338197249080946979781)
        ·
          refine ⟨87073750911984202677558709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464393338197249080946979781 87073750911984202677558709)
          ·
            refine ⟨8163164147998519001021129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87073750911984202677558709 8163164147998519001021129)
            ·
              refine ⟨6122373110998889250765847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163164147998519001021129 6122373110998889250765847)
              ·
                refine ⟨9183559666498333876148771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122373110998889250765847 9183559666498333876148771)
                ·
                  refine ⟨13775339499747500814223157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183559666498333876148771 13775339499747500814223157)
                  ·
                    refine ⟨1291438078101328201333421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13775339499747500814223157 1291438078101328201333421)
                    ·
                      rfl

theorem cell23_7545200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_7545200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545200 prefixEnd_7545200 := by exact prefixLift 7545200
  have htrace : WordTrace (prefixWord ++ tailWord_7545200) baseStart_7545200 baseEnd_7545200 := by
    simpa [prefixWord, tailWord_7545200, baseEnd_7545200] using wordTrace_append hprefix tailTrace_7545200
  have hstable : (prefixWord ++ tailWord_7545200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545200).length < 2 ^ (prefixWord ++ tailWord_7545200).sum := by decide
  have hdescent : baseEnd_7545200 < baseStart_7545200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545213 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_7545213 : Nat := 118140960795 + 7545213 * 2 ^ 59
def prefixEnd_7545213 : Nat := 4983230072969 + 3 ^ 40 * 7545213 * 2
def baseEnd_7545213 : Nat := 1291440303184164351045901

theorem tailTrace_7545213 : CollatzResearch.WordTrace tailWord_7545213 prefixEnd_7545213 1291440303184164351045901 := by
  unfold tailWord_7545213
  simp only [CollatzResearch.WordTrace]
  refine ⟨275196526413989395633248293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183464350942659597088832195 275196526413989395633248293)
  ·
    refine ⟨51599348702623011681234055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275196526413989395633248293 51599348702623011681234055)
    ·
      refine ⟨77399023053934517521851083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51599348702623011681234055 77399023053934517521851083)
      ·
        refine ⟨116098534580901776282776625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77399023053934517521851083 116098534580901776282776625)
        ·
          refine ⟨87073900935676332212082469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116098534580901776282776625 87073900935676332212082469)
          ·
            refine ⟨16326356425439312289765463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87073900935676332212082469 16326356425439312289765463)
            ·
              refine ⟨24489534638158968434648195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16326356425439312289765463 24489534638158968434648195)
              ·
                refine ⟨36734301957238452651972293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24489534638158968434648195 36734301957238452651972293)
                ·
                  refine ⟨6887681616982209872244805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36734301957238452651972293 6887681616982209872244805)
                  ·
                    refine ⟨1291440303184164351045901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887681616982209872244805 1291440303184164351045901)
                    ·
                      rfl

theorem cell23_7545213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_7545213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545213 prefixEnd_7545213 := by exact prefixLift 7545213
  have htrace : WordTrace (prefixWord ++ tailWord_7545213) baseStart_7545213 baseEnd_7545213 := by
    simpa [prefixWord, tailWord_7545213, baseEnd_7545213] using wordTrace_append hprefix tailTrace_7545213
  have hstable : (prefixWord ++ tailWord_7545213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545213).length < 2 ^ (prefixWord ++ tailWord_7545213).sum := by decide
  have hdescent : baseEnd_7545213 < baseStart_7545213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545230 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_7545230 : Nat := 118140960795 + 7545230 * 2 ^ 59
def prefixEnd_7545230 : Nat := 4983230072969 + 3 ^ 40 * 7545230 * 2
def baseEnd_7545230 : Nat := 1291443212907873162208375

theorem tailTrace_7545230 : CollatzResearch.WordTrace tailWord_7545230 prefixEnd_7545230 1291443212907873162208375 := by
  unfold tailWord_7545230
  simp only [CollatzResearch.WordTrace]
  refine ⟨34399643306865975942077143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183464764303285205024411429 34399643306865975942077143)
  ·
    refine ⟨51599464960298963913115715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34399643306865975942077143 51599464960298963913115715)
    ·
      refine ⟨77399197440448445869673573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51599464960298963913115715 77399197440448445869673573)
      ·
        refine ⟨14512349520084083600563795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77399197440448445869673573 14512349520084083600563795)
        ·
          refine ⟨21768524280126125400845693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512349520084083600563795 21768524280126125400845693)
          ·
            refine ⟨8163196605047297025317135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21768524280126125400845693 8163196605047297025317135)
            ·
              refine ⟨12244794907570945537975703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163196605047297025317135 12244794907570945537975703)
              ·
                refine ⟨18367192361356418306963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12244794907570945537975703 18367192361356418306963555)
                ·
                  refine ⟨27550788542034627460445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18367192361356418306963555 27550788542034627460445333)
                  ·
                    refine ⟨1291443212907873162208375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27550788542034627460445333 1291443212907873162208375)
                    ·
                      rfl

theorem cell23_7545230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_7545230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545230 prefixEnd_7545230 := by exact prefixLift 7545230
  have htrace : WordTrace (prefixWord ++ tailWord_7545230) baseStart_7545230 baseEnd_7545230 := by
    simpa [prefixWord, tailWord_7545230, baseEnd_7545230] using wordTrace_append hprefix tailTrace_7545230
  have hstable : (prefixWord ++ tailWord_7545230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545230).length < 2 ^ (prefixWord ++ tailWord_7545230).sum := by decide
  have hdescent : baseEnd_7545230 < baseStart_7545230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545240 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7545240 : Nat := 118140960795 + 7545240 * 2 ^ 59
def prefixEnd_7545240 : Nat := 4983230072969 + 3 ^ 40 * 7545240 * 2
def baseEnd_7545240 : Nat := 3874334773530164447500079

theorem tailTrace_7545240 : CollatzResearch.WordTrace tailWord_7545240 prefixEnd_7545240 3874334773530164447500079 := by
  unfold tailWord_7545240
  simp only [CollatzResearch.WordTrace]
  refine ⟨137598755592445789622240587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183465007456594386162987449 137598755592445789622240587)
  ·
    refine ⟨206398133388668684433360881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137598755592445789622240587 206398133388668684433360881)
    ·
      refine ⟨154798600041501513325020661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206398133388668684433360881 154798600041501513325020661)
      ·
        refine ⟨14512368753890766874220687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154798600041501513325020661 14512368753890766874220687)
        ·
          refine ⟨21768553130836150311331031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14512368753890766874220687 21768553130836150311331031)
          ·
            refine ⟨32652829696254225466996547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21768553130836150311331031 32652829696254225466996547)
            ·
              refine ⟨48979244544381338200494821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32652829696254225466996547 48979244544381338200494821)
              ·
                refine ⟨9183608352071500912592779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48979244544381338200494821 9183608352071500912592779)
                ·
                  refine ⟨13775412528107251368889169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183608352071500912592779 13775412528107251368889169)
                  ·
                    refine ⟨10331559396080438526666877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13775412528107251368889169 10331559396080438526666877)
                    ·
                      refine ⟨3874334773530164447500079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331559396080438526666877 3874334773530164447500079)
                      ·
                        rfl

theorem cell23_7545240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7545240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545240 prefixEnd_7545240 := by exact prefixLift 7545240
  have htrace : WordTrace (prefixWord ++ tailWord_7545240) baseStart_7545240 baseEnd_7545240 := by
    simpa [prefixWord, tailWord_7545240, baseEnd_7545240] using wordTrace_append hprefix tailTrace_7545240
  have hstable : (prefixWord ++ tailWord_7545240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545240).length < 2 ^ (prefixWord ++ tailWord_7545240).sum := by decide
  have hdescent : baseEnd_7545240 < baseStart_7545240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545253 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_7545253 : Nat := 118140960795 + 7545253 * 2 ^ 59
def prefixEnd_7545253 : Nat := 4983230072969 + 3 ^ 40 * 7545253 * 2
def baseEnd_7545253 : Nat := 3874341448778672896637519

theorem tailTrace_7545253 : CollatzResearch.WordTrace tailWord_7545253 prefixEnd_7545253 3874341448778672896637519 := by
  unfold tailWord_7545253
  simp only [CollatzResearch.WordTrace]
  refine ⟨275197985333844482464704413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183465323555896321643136275 275197985333844482464704413)
  ·
    refine ⟨103199244500191680924264155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275197985333844482464704413 103199244500191680924264155)
    ·
      refine ⟨154798866750287521386396233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103199244500191680924264155 154798866750287521386396233)
      ·
        refine ⟨116099150062715641039797175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154798866750287521386396233 116099150062715641039797175)
        ·
          refine ⟨174148725094073461559695763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116099150062715641039797175 174148725094073461559695763)
          ·
            refine ⟨261223087641110192339543645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174148725094073461559695763 261223087641110192339543645)
            ·
              refine ⟨97958657865416322127328867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261223087641110192339543645 97958657865416322127328867)
              ·
                refine ⟨146937986798124483190993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97958657865416322127328867 146937986798124483190993301)
                ·
                  refine ⟨6887718131162085149577811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146937986798124483190993301 6887718131162085149577811)
                  ·
                    refine ⟨10331577196743127724366717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887718131162085149577811 10331577196743127724366717)
                    ·
                      refine ⟨3874341448778672896637519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331577196743127724366717 3874341448778672896637519)
                      ·
                        rfl

theorem cell23_7545253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_7545253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545253 prefixEnd_7545253 := by exact prefixLift 7545253
  have htrace : WordTrace (prefixWord ++ tailWord_7545253) baseStart_7545253 baseEnd_7545253 := by
    simpa [prefixWord, tailWord_7545253, baseEnd_7545253] using wordTrace_append hprefix tailTrace_7545253
  have hstable : (prefixWord ++ tailWord_7545253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545253).length < 2 ^ (prefixWord ++ tailWord_7545253).sum := by decide
  have hdescent : baseEnd_7545253 < baseStart_7545253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545263 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 7, 3, 2]
def baseStart_7545263 : Nat := 118140960795 + 7545263 * 2 ^ 59
def prefixEnd_7545263 : Nat := 4983230072969 + 3 ^ 40 * 7545263 * 2
def baseEnd_7545263 : Nat := 3874346583585217857512473

theorem tailTrace_7545263 : CollatzResearch.WordTrace tailWord_7545263 prefixEnd_7545263 3874346583585217857512473 := by
  unfold tailWord_7545263
  simp only [CollatzResearch.WordTrace]
  refine ⟨275198350063808254172568443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183465566709205502781712295 275198350063808254172568443)
  ·
    refine ⟨412797525095712381258852665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275198350063808254172568443 412797525095712381258852665)
    ·
      refine ⟨309598143821784285944139499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412797525095712381258852665 309598143821784285944139499)
      ·
        refine ⟨464397215732676428916209249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309598143821784285944139499 464397215732676428916209249)
        ·
          refine ⟨348297911799507321687156937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464397215732676428916209249 348297911799507321687156937)
          ·
            refine ⟨261223433849630491265367703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348297911799507321687156937 261223433849630491265367703)
            ·
              refine ⟨391835150774445736898051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261223433849630491265367703 391835150774445736898051555)
              ·
                refine ⟨587752726161668605347077333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391835150774445736898051555 587752726161668605347077333)
                ·
                  refine ⟨13775454519414107937822125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 587752726161668605347077333 13775454519414107937822125)
                  ·
                    refine ⟨5165795444780290476683297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13775454519414107937822125 5165795444780290476683297)
                    ·
                      refine ⟨3874346583585217857512473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165795444780290476683297 3874346583585217857512473)
                      ·
                        rfl

theorem cell23_7545263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3, 2].length) (baseStart_7545263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545263 prefixEnd_7545263 := by exact prefixLift 7545263
  have htrace : WordTrace (prefixWord ++ tailWord_7545263) baseStart_7545263 baseEnd_7545263 := by
    simpa [prefixWord, tailWord_7545263, baseEnd_7545263] using wordTrace_append hprefix tailTrace_7545263
  have hstable : (prefixWord ++ tailWord_7545263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545263).length < 2 ^ (prefixWord ++ tailWord_7545263).sum := by decide
  have hdescent : baseEnd_7545263 < baseStart_7545263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545266 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_7545266 : Nat := 118140960795 + 7545266 * 2 ^ 59
def prefixEnd_7545266 : Nat := 4983230072969 + 3 ^ 40 * 7545266 * 2
def baseEnd_7545266 : Nat := 3874348124027181345774959

theorem tailTrace_7545266 : CollatzResearch.WordTrace tailWord_7545266 prefixEnd_7545266 3874348124027181345774959 := by
  unfold tailWord_7545266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68799614870699346421231913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183465639655198257123285101 68799614870699346421231913)
  ·
    refine ⟨51599711153024509815923935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68799614870699346421231913 51599711153024509815923935)
    ·
      refine ⟨77399566729536764723885903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51599711153024509815923935 77399566729536764723885903)
      ·
        refine ⟨116099350094305147085828855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77399566729536764723885903 116099350094305147085828855)
        ·
          refine ⟨174149025141457720628743283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116099350094305147085828855 174149025141457720628743283)
          ·
            refine ⟨261223537712186580943114925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174149025141457720628743283 261223537712186580943114925)
            ·
              refine ⟨97958826642069967853668097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261223537712186580943114925 97958826642069967853668097)
              ·
                refine ⟨73469119981552475890251073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97958826642069967853668097 73469119981552475890251073)
                ·
                  refine ⟨55101839986164356917688305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73469119981552475890251073 55101839986164356917688305)
                  ·
                    refine ⟨41326379989623267688266229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55101839986164356917688305 41326379989623267688266229)
                    ·
                      refine ⟨3874348124027181345774959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41326379989623267688266229 3874348124027181345774959)
                      ·
                        rfl

theorem cell23_7545266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_7545266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545266 prefixEnd_7545266 := by exact prefixLift 7545266
  have htrace : WordTrace (prefixWord ++ tailWord_7545266) baseStart_7545266 baseEnd_7545266 := by
    simpa [prefixWord, tailWord_7545266, baseEnd_7545266] using wordTrace_append hprefix tailTrace_7545266
  have hstable : (prefixWord ++ tailWord_7545266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545266).length < 2 ^ (prefixWord ++ tailWord_7545266).sum := by decide
  have hdescent : baseEnd_7545266 < baseStart_7545266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545287 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_7545287 : Nat := 118140960795 + 7545287 * 2 ^ 59
def prefixEnd_7545287 : Nat := 4983230072969 + 3 ^ 40 * 7545287 * 2
def baseEnd_7545287 : Nat := 3874358907120925763612363

theorem tailTrace_7545287 : CollatzResearch.WordTrace tailWord_7545287 prefixEnd_7545287 3874358907120925763612363 := by
  unfold tailWord_7545287
  simp only [CollatzResearch.WordTrace]
  refine ⟨275199225415721306271442115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183466150277147537514294743 275199225415721306271442115)
  ·
    refine ⟨412798838123581959407163173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275199225415721306271442115 412798838123581959407163173)
    ·
      refine ⟨77399782148171617388843095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412798838123581959407163173 77399782148171617388843095)
      ·
        refine ⟨116099673222257426083264643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77399782148171617388843095 116099673222257426083264643)
        ·
          refine ⟨174149509833386139124896965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116099673222257426083264643 174149509833386139124896965)
          ·
            refine ⟨32653033093759901085918181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174149509833386139124896965 32653033093759901085918181)
            ·
              refine ⟨6122443705079981453609659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32653033093759901085918181 6122443705079981453609659)
              ·
                refine ⟨9183665557619972180414489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122443705079981453609659 9183665557619972180414489)
                ·
                  refine ⟨6887749168214979135310867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9183665557619972180414489 6887749168214979135310867)
                  ·
                    refine ⟨10331623752322468702966301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887749168214979135310867 10331623752322468702966301)
                    ·
                      refine ⟨3874358907120925763612363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331623752322468702966301 3874358907120925763612363)
                      ·
                        rfl

theorem cell23_7545287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_7545287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545287 prefixEnd_7545287 := by exact prefixLift 7545287
  have htrace : WordTrace (prefixWord ++ tailWord_7545287) baseStart_7545287 baseEnd_7545287 := by
    simpa [prefixWord, tailWord_7545287, baseEnd_7545287] using wordTrace_append hprefix tailTrace_7545287
  have hstable : (prefixWord ++ tailWord_7545287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545287).length < 2 ^ (prefixWord ++ tailWord_7545287).sum := by decide
  have hdescent : baseEnd_7545287 < baseStart_7545287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545343 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_7545343 : Nat := 118140960795 + 7545343 * 2 ^ 59
def prefixEnd_7545343 : Nat := 4983230072969 + 3 ^ 40 * 7545343 * 2
def baseEnd_7545343 : Nat := 3874387662037577544512105

theorem tailTrace_7545343 : CollatzResearch.WordTrace tailWord_7545343 prefixEnd_7545343 3874387662037577544512105 := by
  unfold tailWord_7545343
  simp only [CollatzResearch.WordTrace]
  refine ⟨275201267903518427835480683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183467511935678951890320455 275201267903518427835480683)
  ·
    refine ⟨412801901855277641753221025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275201267903518427835480683 412801901855277641753221025)
    ·
      refine ⟨309601426391458231314915769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412801901855277641753221025 309601426391458231314915769)
      ·
        refine ⟨232201069793593673486186827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309601426391458231314915769 232201069793593673486186827)
        ·
          refine ⟨348301604690390510229280241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232201069793593673486186827 348301604690390510229280241)
          ·
            refine ⟨261226203517792882671960181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348301604690390510229280241 261226203517792882671960181)
            ·
              refine ⟨24489956579793082750496267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261226203517792882671960181 24489956579793082750496267)
              ·
                refine ⟨36734934869689624125744401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24489956579793082750496267 36734934869689624125744401)
                ·
                  refine ⟨27551201152267218094308301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36734934869689624125744401 27551201152267218094308301)
                  ·
                    refine ⟨10331700432100206785365613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27551201152267218094308301 10331700432100206785365613)
                    ·
                      refine ⟨3874387662037577544512105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331700432100206785365613 3874387662037577544512105)
                      ·
                        rfl

theorem cell23_7545343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_7545343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545343 prefixEnd_7545343 := by exact prefixLift 7545343
  have htrace : WordTrace (prefixWord ++ tailWord_7545343) baseStart_7545343 baseEnd_7545343 := by
    simpa [prefixWord, tailWord_7545343, baseEnd_7545343] using wordTrace_append hprefix tailTrace_7545343
  have hstable : (prefixWord ++ tailWord_7545343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545343).length < 2 ^ (prefixWord ++ tailWord_7545343).sum := by decide
  have hdescent : baseEnd_7545343 < baseStart_7545343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545400 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_7545400 : Nat := 118140960795 + 7545400 * 2 ^ 59
def prefixEnd_7545400 : Nat := 4983230072969 + 3 ^ 40 * 7545400 * 2
def baseEnd_7545400 : Nat := 3874416930434883821499343

theorem tailTrace_7545400 : CollatzResearch.WordTrace tailWord_7545400 prefixEnd_7545400 3874416930434883821499343 := by
  unfold tailWord_7545400
  simp only [CollatzResearch.WordTrace]
  refine ⟨137601673432155963285152827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183468897909541284380203769 137601673432155963285152827)
  ·
    refine ⟨206402510148233944927729241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137601673432155963285152827 206402510148233944927729241)
    ·
      refine ⟨154801882611175458695796931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206402510148233944927729241 154801882611175458695796931)
      ·
        refine ⟨232202823916763188043695397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154801882611175458695796931 232202823916763188043695397)
        ·
          refine ⟨43538029484393097758192887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232202823916763188043695397 43538029484393097758192887)
          ·
            refine ⟨65307044226589646637289331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43538029484393097758192887 65307044226589646637289331)
            ·
              refine ⟨97960566339884469955933997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65307044226589646637289331 97960566339884469955933997)
              ·
                refine ⟨36735212377456676233475249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97960566339884469955933997 36735212377456676233475249)
                ·
                  refine ⟨27551409283092507175106437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36735212377456676233475249 27551409283092507175106437)
                  ·
                    refine ⟨5165889240579845095332457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27551409283092507175106437 5165889240579845095332457)
                    ·
                      refine ⟨3874416930434883821499343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165889240579845095332457 3874416930434883821499343)
                      ·
                        rfl

theorem cell23_7545400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_7545400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545400 prefixEnd_7545400 := by exact prefixLift 7545400
  have htrace : WordTrace (prefixWord ++ tailWord_7545400) baseStart_7545400 baseEnd_7545400 := by
    simpa [prefixWord, tailWord_7545400, baseEnd_7545400] using wordTrace_append hprefix tailTrace_7545400
  have hstable : (prefixWord ++ tailWord_7545400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545400).length < 2 ^ (prefixWord ++ tailWord_7545400).sum := by decide
  have hdescent : baseEnd_7545400 < baseStart_7545400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545420 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7545420 : Nat := 118140960795 + 7545420 * 2 ^ 59
def prefixEnd_7545420 : Nat := 4983230072969 + 3 ^ 40 * 7545420 * 2
def baseEnd_7545420 : Nat := 3874427200047973743249251

theorem tailTrace_7545420 : CollatzResearch.WordTrace tailWord_7545420 prefixEnd_7545420 3874427200047973743249251 := by
  unfold tailWord_7545420
  simp only [CollatzResearch.WordTrace]
  refine ⟨137602038162119734993016857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183469384216159646657355809 137602038162119734993016857)
  ·
    refine ⟨103201528621589801244762643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137602038162119734993016857 103201528621589801244762643)
    ·
      refine ⟨154802292932384701867143965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103201528621589801244762643 154802292932384701867143965)
      ·
        refine ⟨58050859849644263200178987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154802292932384701867143965 58050859849644263200178987)
        ·
          refine ⟨87076289774466394800268481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58050859849644263200178987 87076289774466394800268481)
          ·
            refine ⟨65307217330849796100201361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87076289774466394800268481 65307217330849796100201361)
            ·
              refine ⟨48980412998137347075151021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65307217330849796100201361 48980412998137347075151021)
              ·
                refine ⟨18367654874301505153181633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48980412998137347075151021 18367654874301505153181633)
                ·
                  refine ⟨13775741155726128864886225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18367654874301505153181633 13775741155726128864886225)
                  ·
                    refine ⟨10331805866794596648664669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13775741155726128864886225 10331805866794596648664669)
                    ·
                      refine ⟨3874427200047973743249251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331805866794596648664669 3874427200047973743249251)
                      ·
                        rfl

theorem cell23_7545420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7545420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545420 prefixEnd_7545420 := by exact prefixLift 7545420
  have htrace : WordTrace (prefixWord ++ tailWord_7545420) baseStart_7545420 baseEnd_7545420 := by
    simpa [prefixWord, tailWord_7545420, baseEnd_7545420] using wordTrace_append hprefix tailTrace_7545420
  have hstable : (prefixWord ++ tailWord_7545420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545420).length < 2 ^ (prefixWord ++ tailWord_7545420).sum := by decide
  have hdescent : baseEnd_7545420 < baseStart_7545420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545444 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_7545444 : Nat := 118140960795 + 7545444 * 2 ^ 59
def prefixEnd_7545444 : Nat := 4983230072969 + 3 ^ 40 * 7545444 * 2
def baseEnd_7545444 : Nat := 1291479841194560549783047

theorem tailTrace_7545444 : CollatzResearch.WordTrace tailWord_7545444 prefixEnd_7545444 1291479841194560549783047 := by
  unfold tailWord_7545444
  simp only [CollatzResearch.WordTrace]
  refine ⟨137602475838076261042453693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183469967784101681389938257 137602475838076261042453693)
  ·
    refine ⟨51600928439278597890920135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137602475838076261042453693 51600928439278597890920135)
    ·
      refine ⟨77401392658917896836380203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51600928439278597890920135 77401392658917896836380203)
      ·
        refine ⟨116102088988376845254570305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77401392658917896836380203 116102088988376845254570305)
        ·
          refine ⟨87076566741282633940927729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116102088988376845254570305 87076566741282633940927729)
          ·
            refine ⟨65307425055961975455695797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87076566741282633940927729 65307425055961975455695797)
            ·
              refine ⟨6122571098996435198971481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65307425055961975455695797 6122571098996435198971481)
              ·
                refine ⟨4591928324247326399228611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122571098996435198971481 4591928324247326399228611)
                ·
                  refine ⟨6887892486370989598842917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591928324247326399228611 6887892486370989598842917)
                  ·
                    refine ⟨1291479841194560549783047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6887892486370989598842917 1291479841194560549783047)
                    ·
                      rfl

theorem cell23_7545444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_7545444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545444 prefixEnd_7545444 := by exact prefixLift 7545444
  have htrace : WordTrace (prefixWord ++ tailWord_7545444) baseStart_7545444 baseEnd_7545444 := by
    simpa [prefixWord, tailWord_7545444, baseEnd_7545444] using wordTrace_append hprefix tailTrace_7545444
  have hstable : (prefixWord ++ tailWord_7545444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545444).length < 2 ^ (prefixWord ++ tailWord_7545444).sum := by decide
  have hdescent : baseEnd_7545444 < baseStart_7545444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545477 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_7545477 : Nat := 118140960795 + 7545477 * 2 ^ 59
def prefixEnd_7545477 : Nat := 4983230072969 + 3 ^ 40 * 7545477 * 2
def baseEnd_7545477 : Nat := 3874456468445280020236489

theorem tailTrace_7545477 : CollatzResearch.WordTrace tailWord_7545477 prefixEnd_7545477 3874456468445280020236489 := by
  unfold tailWord_7545477
  simp only [CollatzResearch.WordTrace]
  refine ⟨275206155285032968720858685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183470770190021979147239123 275206155285032968720858685)
  ·
    refine ⟨103202308231887363270322007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275206155285032968720858685 103202308231887363270322007)
    ·
      refine ⟨154803462347831044905483011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103202308231887363270322007 154803462347831044905483011)
      ·
        refine ⟨232205193521746567358224517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154803462347831044905483011 232205193521746567358224517)
        ·
          refine ⟨43538473785327481379667097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232205193521746567358224517 43538473785327481379667097)
          ·
            refine ⟨32653855338995611034750323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43538473785327481379667097 32653855338995611034750323)
            ·
              refine ⟨48980783008493416552125485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32653855338995611034750323 48980783008493416552125485)
              ·
                refine ⟨18367793628185031207047057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48980783008493416552125485 18367793628185031207047057)
                ·
                  refine ⟨13775845221138773405285293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18367793628185031207047057 13775845221138773405285293)
                  ·
                    refine ⟨5165941957927040026981985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13775845221138773405285293 5165941957927040026981985)
                    ·
                      refine ⟨3874456468445280020236489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5165941957927040026981985 3874456468445280020236489)
                      ·
                        rfl

theorem cell23_7545477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_7545477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545477 prefixEnd_7545477 := by exact prefixLift 7545477
  have htrace : WordTrace (prefixWord ++ tailWord_7545477) baseStart_7545477 baseEnd_7545477 := by
    simpa [prefixWord, tailWord_7545477, baseEnd_7545477] using wordTrace_append hprefix tailTrace_7545477
  have hstable : (prefixWord ++ tailWord_7545477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545477).length < 2 ^ (prefixWord ++ tailWord_7545477).sum := by decide
  have hdescent : baseEnd_7545477 < baseStart_7545477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545501 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_7545501 : Nat := 118140960795 + 7545501 * 2 ^ 59
def prefixEnd_7545501 : Nat := 4983230072969 + 3 ^ 40 * 7545501 * 2
def baseEnd_7545501 : Nat := 3874468791980987926336379

theorem tailTrace_7545501 : CollatzResearch.WordTrace tailWord_7545501 prefixEnd_7545501 3874468791980987926336379 := by
  unfold tailWord_7545501
  simp only [CollatzResearch.WordTrace]
  refine ⟨275207030636946020819732357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183471353757964013879821571 275207030636946020819732357)
  ·
    refine ⟨51601318244427378903699817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275207030636946020819732357 51601318244427378903699817)
    ·
      refine ⟨38700988683320534177774863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51601318244427378903699817 38700988683320534177774863)
      ·
        refine ⟨58051483024980801266662295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38700988683320534177774863 58051483024980801266662295)
        ·
          refine ⟨87077224537471201899993443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58051483024980801266662295 87077224537471201899993443)
          ·
            refine ⟨130615836806206802849990165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87077224537471201899993443 130615836806206802849990165)
            ·
              refine ⟨6122617350290943883593289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130615836806206802849990165 6122617350290943883593289)
              ·
                refine ⟨4591963012718207912694967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122617350290943883593289 4591963012718207912694967)
                ·
                  refine ⟨6887944519077311869042451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4591963012718207912694967 6887944519077311869042451)
                  ·
                    refine ⟨10331916778615967803563677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6887944519077311869042451 10331916778615967803563677)
                    ·
                      refine ⟨3874468791980987926336379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331916778615967803563677 3874468791980987926336379)
                      ·
                        rfl

theorem cell23_7545501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_7545501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545501 prefixEnd_7545501 := by exact prefixLift 7545501
  have htrace : WordTrace (prefixWord ++ tailWord_7545501) baseStart_7545501 baseEnd_7545501 := by
    simpa [prefixWord, tailWord_7545501, baseEnd_7545501] using wordTrace_append hprefix tailTrace_7545501
  have hstable : (prefixWord ++ tailWord_7545501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545501).length < 2 ^ (prefixWord ++ tailWord_7545501).sum := by decide
  have hdescent : baseEnd_7545501 < baseStart_7545501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545517 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7545517 : Nat := 118140960795 + 7545517 * 2 ^ 59
def prefixEnd_7545517 : Nat := 4983230072969 + 3 ^ 40 * 7545517 * 2
def baseEnd_7545517 : Nat := 1291492335890486621245435

theorem tailTrace_7545517 : CollatzResearch.WordTrace tailWord_7545517 prefixEnd_7545517 1291492335890486621245435 := by
  unfold tailWord_7545517
  simp only [CollatzResearch.WordTrace]
  refine ⟨275207614204888055552314805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183471742803258703701543203 275207614204888055552314805)
  ·
    refine ⟨25800713831708255208029513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275207614204888055552314805 25800713831708255208029513)
    ·
      refine ⟨19350535373781191406022135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25800713831708255208029513 19350535373781191406022135)
      ·
        refine ⟨29025803060671787109033203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19350535373781191406022135 29025803060671787109033203)
        ·
          refine ⟨43538704591007680663549805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29025803060671787109033203 43538704591007680663549805)
          ·
            refine ⟨16327014221627880248831177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43538704591007680663549805 16327014221627880248831177)
            ·
              refine ⟨12245260666220910186623383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16327014221627880248831177 12245260666220910186623383)
              ·
                refine ⟨18367890999331365279935075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245260666220910186623383 18367890999331365279935075)
                ·
                  refine ⟨27551836498997047919902613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18367890999331365279935075 27551836498997047919902613)
                  ·
                    refine ⟨1291492335890486621245435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27551836498997047919902613 1291492335890486621245435)
                    ·
                      rfl

theorem cell23_7545517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7545517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545517 prefixEnd_7545517 := by exact prefixLift 7545517
  have htrace : WordTrace (prefixWord ++ tailWord_7545517) baseStart_7545517 baseEnd_7545517 := by
    simpa [prefixWord, tailWord_7545517, baseEnd_7545517] using wordTrace_append hprefix tailTrace_7545517
  have hstable : (prefixWord ++ tailWord_7545517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545517).length < 2 ^ (prefixWord ++ tailWord_7545517).sum := by decide
  have hdescent : baseEnd_7545517 < baseStart_7545517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545530 : List Nat := [3, 1, 1, 1, 2, 3, 5, 7]
def baseStart_7545530 : Nat := 118140960795 + 7545530 * 2 ^ 59
def prefixEnd_7545530 : Nat := 4983230072969 + 3 ^ 40 * 7545530 * 2
def baseEnd_7545530 : Nat := 143499395663702530106435

theorem tailTrace_7545530 : CollatzResearch.WordTrace tailWord_7545530 prefixEnd_7545530 143499395663702530106435 := by
  unfold tailWord_7545530
  simp only [CollatzResearch.WordTrace]
  refine ⟨68802022088460239693134511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183472058902560639181692029 68802022088460239693134511)
  ·
    refine ⟨103203033132690359539701767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68802022088460239693134511 103203033132690359539701767)
    ·
      refine ⟨154804549699035539309552651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103203033132690359539701767 154804549699035539309552651)
      ·
        refine ⟨232206824548553308964328977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154804549699035539309552651 232206824548553308964328977)
        ·
          refine ⟨174155118411414981723246733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232206824548553308964328977 174155118411414981723246733)
          ·
            refine ⟨65308169404280618146217525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174155118411414981723246733 65308169404280618146217525)
            ·
              refine ⟨6122640881651307951207893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65308169404280618146217525 6122640881651307951207893)
              ·
                refine ⟨143499395663702530106435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6122640881651307951207893 143499395663702530106435)
                ·
                  rfl

theorem cell23_7545530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_7545530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545530 prefixEnd_7545530 := by exact prefixLift 7545530
  have htrace : WordTrace (prefixWord ++ tailWord_7545530) baseStart_7545530 baseEnd_7545530 := by
    simpa [prefixWord, tailWord_7545530, baseEnd_7545530] using wordTrace_append hprefix tailTrace_7545530
  have hstable : (prefixWord ++ tailWord_7545530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545530).length < 2 ^ (prefixWord ++ tailWord_7545530).sum := by decide
  have hdescent : baseEnd_7545530 < baseStart_7545530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545543 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 1, 9]
def baseStart_7545543 : Nat := 118140960795 + 7545543 * 2 ^ 59
def prefixEnd_7545543 : Nat := 4983230072969 + 3 ^ 40 * 7545543 * 2
def baseEnd_7545543 : Nat := 1291496786056158920670395

theorem tailTrace_7545543 : CollatzResearch.WordTrace tailWord_7545543 prefixEnd_7545543 1291496786056158920670395 := by
  unfold tailWord_7545543
  simp only [CollatzResearch.WordTrace]
  refine ⟨275208562502793861992761283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183472375001862574661840855 275208562502793861992761283)
  ·
    refine ⟨412812843754190792989141925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275208562502793861992761283 412812843754190792989141925)
    ·
      refine ⟨77402408203910773685464111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412812843754190792989141925 77402408203910773685464111)
      ·
        refine ⟨116103612305866160528196167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77402408203910773685464111 116103612305866160528196167)
        ·
          refine ⟨174155418458799240792294251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116103612305866160528196167 174155418458799240792294251)
          ·
            refine ⟨261233127688198861188441377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174155418458799240792294251 261233127688198861188441377)
            ·
              refine ⟨195924845766149145891331033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261233127688198861188441377 195924845766149145891331033)
              ·
                refine ⟨146943634324611859418498275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195924845766149145891331033 146943634324611859418498275)
                ·
                  refine ⟨220415451486917789127747413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146943634324611859418498275 220415451486917789127747413)
                  ·
                    refine ⟨1291496786056158920670395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220415451486917789127747413 1291496786056158920670395)
                    ·
                      rfl

theorem cell23_7545543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_7545543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545543 prefixEnd_7545543 := by exact prefixLift 7545543
  have htrace : WordTrace (prefixWord ++ tailWord_7545543) baseStart_7545543 baseEnd_7545543 := by
    simpa [prefixWord, tailWord_7545543, baseEnd_7545543] using wordTrace_append hprefix tailTrace_7545543
  have hstable : (prefixWord ++ tailWord_7545543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545543).length < 2 ^ (prefixWord ++ tailWord_7545543).sum := by decide
  have hdescent : baseEnd_7545543 < baseStart_7545543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545544 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_7545544 : Nat := 118140960795 + 7545544 * 2 ^ 59
def prefixEnd_7545544 : Nat := 4983230072969 + 3 ^ 40 * 7545544 * 2
def baseEnd_7545544 : Nat := 3874490871649131258098681

theorem tailTrace_7545544 : CollatzResearch.WordTrace tailWord_7545544 prefixEnd_7545544 3874490871649131258098681 := by
  unfold tailWord_7545544
  simp only [CollatzResearch.WordTrace]
  refine ⟨137604299487895119581773843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183472399317193492775698457 137604299487895119581773843)
  ·
    refine ⟨206406449231842679372660765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137604299487895119581773843 206406449231842679372660765)
    ·
      refine ⟨77402418461941004764747787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206406449231842679372660765 77402418461941004764747787)
      ·
        refine ⟨116103627692911507147121681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77402418461941004764747787 116103627692911507147121681)
        ·
          refine ⟨87077720769683630360341261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116103627692911507147121681 87077720769683630360341261)
          ·
            refine ⟨32654145288631361385127973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87077720769683630360341261 32654145288631361385127973)
            ·
              refine ⟨6122652241618380259711495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32654145288631361385127973 6122652241618380259711495)
              ·
                refine ⟨9183978362427570389567243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122652241618380259711495 9183978362427570389567243)
                ·
                  refine ⟨13775967543641355584350865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9183978362427570389567243 13775967543641355584350865)
                  ·
                    refine ⟨10331975657731016688263149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13775967543641355584350865 10331975657731016688263149)
                    ·
                      refine ⟨3874490871649131258098681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10331975657731016688263149 3874490871649131258098681)
                      ·
                        rfl

theorem cell23_7545544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_7545544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545544 prefixEnd_7545544 := by exact prefixLift 7545544
  have htrace : WordTrace (prefixWord ++ tailWord_7545544) baseStart_7545544 baseEnd_7545544 := by
    simpa [prefixWord, tailWord_7545544, baseEnd_7545544] using wordTrace_append hprefix tailTrace_7545544
  have hstable : (prefixWord ++ tailWord_7545544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545544).length < 2 ^ (prefixWord ++ tailWord_7545544).sum := by decide
  have hdescent : baseEnd_7545544 < baseStart_7545544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545584 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2]
def baseStart_7545584 : Nat := 118140960795 + 7545584 * 2 ^ 59
def prefixEnd_7545584 : Nat := 4983230072969 + 3 ^ 40 * 7545584 * 2
def baseEnd_7545584 : Nat := 3874511410875311101598497

theorem tailTrace_7545584 : CollatzResearch.WordTrace tailWord_7545584 prefixEnd_7545584 3874511410875311101598497 := by
  unfold tailWord_7545584
  simp only [CollatzResearch.WordTrace]
  refine ⟨137605028947822662997501903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183473371930430217330002537 137605028947822662997501903)
  ·
    refine ⟨206407543421733994496252855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137605028947822662997501903 206407543421733994496252855)
    ·
      refine ⟨309611315132600991744379283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206407543421733994496252855 309611315132600991744379283)
      ·
        refine ⟨464416972698901487616568925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309611315132600991744379283 464416972698901487616568925)
        ·
          refine ⟨174156364762088057856213347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464416972698901487616568925 174156364762088057856213347)
          ·
            refine ⟨261234547143132086784320021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174156364762088057856213347 261234547143132086784320021)
            ·
              refine ⟨12245369397334316568015001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261234547143132086784320021 12245369397334316568015001)
              ·
                refine ⟨9184027048000737426011251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245369397334316568015001 9184027048000737426011251)
                ·
                  refine ⟨13776040572001106139016877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184027048000737426011251 13776040572001106139016877)
                  ·
                    refine ⟨5166015214500414802131329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13776040572001106139016877 5166015214500414802131329)
                    ·
                      refine ⟨3874511410875311101598497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166015214500414802131329 3874511410875311101598497)
                      ·
                        rfl

theorem cell23_7545584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 1, 3, 2].length) (baseStart_7545584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545584 prefixEnd_7545584 := by exact prefixLift 7545584
  have htrace : WordTrace (prefixWord ++ tailWord_7545584) baseStart_7545584 baseEnd_7545584 := by
    simpa [prefixWord, tailWord_7545584, baseEnd_7545584] using wordTrace_append hprefix tailTrace_7545584
  have hstable : (prefixWord ++ tailWord_7545584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545584).length < 2 ^ (prefixWord ++ tailWord_7545584).sum := by decide
  have hdescent : baseEnd_7545584 < baseStart_7545584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545597 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_7545597 : Nat := 118140960795 + 7545597 * 2 ^ 59
def prefixEnd_7545597 : Nat := 4983230072969 + 3 ^ 40 * 7545597 * 2
def baseEnd_7545597 : Nat := 3874518086123819550735937

theorem tailTrace_7545597 : CollatzResearch.WordTrace tailWord_7545597 prefixEnd_7545597 3874518086123819550735937 := by
  unfold tailWord_7545597
  simp only [CollatzResearch.WordTrace]
  refine ⟨275210532044598229215227045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183473688029732152810151363 275210532044598229215227045)
  ·
    refine ⟨51601974758362167977855071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275210532044598229215227045 51601974758362167977855071)
    ·
      refine ⟨77402962137543251966782607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51601974758362167977855071 77402962137543251966782607)
      ·
        refine ⟨116104443206314877950173911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77402962137543251966782607 116104443206314877950173911)
        ·
          refine ⟨174156664809472316925260867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116104443206314877950173911 174156664809472316925260867)
          ·
            refine ⟨261234997214208475387891301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174156664809472316925260867 261234997214208475387891301)
            ·
              refine ⟨48981561977664089135229619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261234997214208475387891301 48981561977664089135229619)
              ·
                refine ⟨73472342966496133702844429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48981561977664089135229619 73472342966496133702844429)
                ·
                  refine ⟨27552128612436050138566661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73472342966496133702844429 27552128612436050138566661)
                  ·
                    refine ⟨5166024114831759400981249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27552128612436050138566661 5166024114831759400981249)
                    ·
                      refine ⟨3874518086123819550735937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166024114831759400981249 3874518086123819550735937)
                      ·
                        rfl

theorem cell23_7545597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_7545597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545597 prefixEnd_7545597 := by exact prefixLift 7545597
  have htrace : WordTrace (prefixWord ++ tailWord_7545597) baseStart_7545597 baseEnd_7545597 := by
    simpa [prefixWord, tailWord_7545597, baseEnd_7545597] using wordTrace_append hprefix tailTrace_7545597
  have hstable : (prefixWord ++ tailWord_7545597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545597).length < 2 ^ (prefixWord ++ tailWord_7545597).sum := by decide
  have hdescent : baseEnd_7545597 < baseStart_7545597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545631 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 2, 2, 2]
def baseStart_7545631 : Nat := 118140960795 + 7545631 * 2 ^ 59
def prefixEnd_7545631 : Nat := 4983230072969 + 3 ^ 40 * 7545631 * 2
def baseEnd_7545631 : Nat := 3874535544466072417710781

theorem tailTrace_7545631 : CollatzResearch.WordTrace tailWord_7545631 prefixEnd_7545631 3874535544466072417710781 := by
  unfold tailWord_7545631
  simp only [CollatzResearch.WordTrace]
  refine ⟨275211772126475053021964747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183474514750983368681309831 275211772126475053021964747)
  ·
    refine ⟨412817658189712579532947121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275211772126475053021964747 412817658189712579532947121)
    ·
      refine ⟨309613243642284434649710341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412817658189712579532947121 309613243642284434649710341)
      ·
        refine ⟨58052483182928331496820689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309613243642284434649710341 58052483182928331496820689)
        ·
          refine ⟨43539362387196248622615517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58052483182928331496820689 43539362387196248622615517)
          ·
            refine ⟨16327260895198593233480819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43539362387196248622615517 16327260895198593233480819)
            ·
              refine ⟨24490891342797889850221229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16327260895198593233480819 24490891342797889850221229)
              ·
                refine ⟨9184084253549208693832961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24490891342797889850221229 9184084253549208693832961)
                ·
                  refine ⟨6888063190161906520374721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184084253549208693832961 6888063190161906520374721)
                  ·
                    refine ⟨5166047392621429890281041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6888063190161906520374721 5166047392621429890281041)
                    ·
                      refine ⟨3874535544466072417710781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166047392621429890281041 3874535544466072417710781)
                      ·
                        rfl

theorem cell23_7545631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_7545631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545631 prefixEnd_7545631 := by exact prefixLift 7545631
  have htrace : WordTrace (prefixWord ++ tailWord_7545631) baseStart_7545631 baseEnd_7545631 := by
    simpa [prefixWord, tailWord_7545631, baseEnd_7545631] using wordTrace_append hprefix tailTrace_7545631
  have hstable : (prefixWord ++ tailWord_7545631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545631).length < 2 ^ (prefixWord ++ tailWord_7545631).sum := by decide
  have hdescent : baseEnd_7545631 < baseStart_7545631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545665 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7545665 : Nat := 118140960795 + 7545665 * 2 ^ 59
def prefixEnd_7545665 : Nat := 4983230072969 + 3 ^ 40 * 7545665 * 2
def baseEnd_7545665 : Nat := 3874553002808325284685625

theorem tailTrace_7545665 : CollatzResearch.WordTrace tailWord_7545665 prefixEnd_7545665 3874553002808325284685625 := by
  unfold tailWord_7545665
  simp only [CollatzResearch.WordTrace]
  refine ⟨275213012208351876828702449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183475341472234584552468299 275213012208351876828702449)
  ·
    refine ⟨206409759156263907621526837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275213012208351876828702449 206409759156263907621526837)
    ·
      refine ⟨19350914920899741339518141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206409759156263907621526837 19350914920899741339518141)
      ·
        refine ⟨7256593095337403002319303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19350914920899741339518141 7256593095337403002319303)
        ·
          refine ⟨10884889643006104503478955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256593095337403002319303 10884889643006104503478955)
          ·
            refine ⟨16327334464509156755218433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884889643006104503478955 16327334464509156755218433)
            ·
              refine ⟨12245500848381867566413825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16327334464509156755218433 12245500848381867566413825)
              ·
                refine ⟨9184125636286400674810369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245500848381867566413825 9184125636286400674810369)
                ·
                  refine ⟨6888094227214800506107777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184125636286400674810369 6888094227214800506107777)
                  ·
                    refine ⟨5166070670411100379580833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6888094227214800506107777 5166070670411100379580833)
                    ·
                      refine ⟨3874553002808325284685625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166070670411100379580833 3874553002808325284685625)
                      ·
                        rfl

theorem cell23_7545665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7545665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545665 prefixEnd_7545665 := by exact prefixLift 7545665
  have htrace : WordTrace (prefixWord ++ tailWord_7545665) baseStart_7545665 baseEnd_7545665 := by
    simpa [prefixWord, tailWord_7545665, baseEnd_7545665] using wordTrace_append hprefix tailTrace_7545665
  have hstable : (prefixWord ++ tailWord_7545665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545665).length < 2 ^ (prefixWord ++ tailWord_7545665).sum := by decide
  have hdescent : baseEnd_7545665 < baseStart_7545665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545704 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7545704 : Nat := 118140960795 + 7545704 * 2 ^ 59
def prefixEnd_7545704 : Nat := 4983230072969 + 3 ^ 40 * 7545704 * 2
def baseEnd_7545704 : Nat := 3874573028553850632097945

theorem tailTrace_7545704 : CollatzResearch.WordTrace tailWord_7545704 prefixEnd_7545704 3874573028553850632097945 := by
  unfold tailWord_7545704
  simp only [CollatzResearch.WordTrace]
  refine ⟨137607217327605293244686083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183476289770140390992914777 137607217327605293244686083)
  ·
    refine ⟨206410825991407939867029125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137607217327605293244686083 206410825991407939867029125)
    ·
      refine ⟨38702029873388988725067961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206410825991407939867029125 38702029873388988725067961)
      ·
        refine ⟨29026522405041741543800971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38702029873388988725067961 29026522405041741543800971)
        ·
          refine ⟨43539783607562612315701457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29026522405041741543800971 43539783607562612315701457)
          ·
            refine ⟨32654837705671959236776093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43539783607562612315701457 32654837705671959236776093)
            ·
              refine ⟨12245564139626984713791035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32654837705671959236776093 12245564139626984713791035)
              ·
                refine ⟨18368346209440477070686553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245564139626984713791035 18368346209440477070686553)
                ·
                  refine ⟨13776259657080357803014915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18368346209440477070686553 13776259657080357803014915)
                  ·
                    refine ⟨20664389485620536704522373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13776259657080357803014915 20664389485620536704522373)
                    ·
                      refine ⟨3874573028553850632097945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20664389485620536704522373 3874573028553850632097945)
                      ·
                        rfl

theorem cell23_7545704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7545704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545704 prefixEnd_7545704 := by exact prefixLift 7545704
  have htrace : WordTrace (prefixWord ++ tailWord_7545704) baseStart_7545704 baseEnd_7545704 := by
    simpa [prefixWord, tailWord_7545704, baseEnd_7545704] using wordTrace_append hprefix tailTrace_7545704
  have hstable : (prefixWord ++ tailWord_7545704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545704).length < 2 ^ (prefixWord ++ tailWord_7545704).sum := by decide
  have hdescent : baseEnd_7545704 < baseStart_7545704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545717 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7545717 : Nat := 118140960795 + 7545717 * 2 ^ 59
def prefixEnd_7545717 : Nat := 4983230072969 + 3 ^ 40 * 7545717 * 2
def baseEnd_7545717 : Nat := 3874579703802359081235385

theorem tailTrace_7545717 : CollatzResearch.WordTrace tailWord_7545717 prefixEnd_7545717 3874579703802359081235385 := by
  unfold tailWord_7545717
  simp only [CollatzResearch.WordTrace]
  refine ⟨275214908804163489709595405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183476605869442326473063603 275214908804163489709595405)
  ·
    refine ⟨103205590801561308641098277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275214908804163489709595405 103205590801561308641098277)
    ·
      refine ⟨19351048275292745370205927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103205590801561308641098277 19351048275292745370205927)
      ·
        refine ⟨29026572412939118055308891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19351048275292745370205927 29026572412939118055308891)
        ·
          refine ⟨43539858619408677082963337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29026572412939118055308891 43539858619408677082963337)
          ·
            refine ⟨32654893964556507812222503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43539858619408677082963337 32654893964556507812222503)
            ·
              refine ⟨48982340946834761718333755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32654893964556507812222503 48982340946834761718333755)
              ·
                refine ⟨73473511420252142577500633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48982340946834761718333755 73473511420252142577500633)
                ·
                  refine ⟨55105133565189106933125475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73473511420252142577500633 55105133565189106933125475)
                  ·
                    refine ⟨82657700347783660399688213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55105133565189106933125475 82657700347783660399688213)
                    ·
                      refine ⟨3874579703802359081235385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82657700347783660399688213 3874579703802359081235385)
                      ·
                        rfl

theorem cell23_7545717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7545717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545717 prefixEnd_7545717 := by exact prefixLift 7545717
  have htrace : WordTrace (prefixWord ++ tailWord_7545717) baseStart_7545717 baseEnd_7545717 := by
    simpa [prefixWord, tailWord_7545717, baseEnd_7545717] using wordTrace_append hprefix tailTrace_7545717
  have hstable : (prefixWord ++ tailWord_7545717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545717).length < 2 ^ (prefixWord ++ tailWord_7545717).sum := by decide
  have hdescent : baseEnd_7545717 < baseStart_7545717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545727 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 6]
def baseStart_7545727 : Nat := 118140960795 + 7545727 * 2 ^ 59
def prefixEnd_7545727 : Nat := 4983230072969 + 3 ^ 40 * 7545727 * 2
def baseEnd_7545727 : Nat := 430509426512100449123371

theorem tailTrace_7545727 : CollatzResearch.WordTrace tailWord_7545727 prefixEnd_7545727 430509426512100449123371 := by
  unfold tailWord_7545727
  simp only [CollatzResearch.WordTrace]
  refine ⟨275215273534127261417459435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183476849022751507611639623 275215273534127261417459435)
  ·
    refine ⟨412822910301190892126189153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275215273534127261417459435 412822910301190892126189153)
    ·
      refine ⟨309617182725893169094641865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412822910301190892126189153 309617182725893169094641865)
      ·
        refine ⟨232212887044419876820981399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309617182725893169094641865 232212887044419876820981399)
        ·
          refine ⟨348319330566629815231472099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232212887044419876820981399 348319330566629815231472099)
          ·
            refine ⟨522478995849944722847208149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348319330566629815231472099 522478995849944722847208149)
            ·
              refine ⟨12245601465233079441731441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 522478995849944722847208149 12245601465233079441731441)
              ·
                refine ⟨9184201098924809581298581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245601465233079441731441 9184201098924809581298581)
                ·
                  refine ⟨430509426512100449123371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9184201098924809581298581 430509426512100449123371)
                  ·
                    rfl

theorem cell23_7545727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 6].length) (baseStart_7545727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545727 prefixEnd_7545727 := by exact prefixLift 7545727
  have htrace : WordTrace (prefixWord ++ tailWord_7545727) baseStart_7545727 baseEnd_7545727 := by
    simpa [prefixWord, tailWord_7545727, baseEnd_7545727] using wordTrace_append hprefix tailTrace_7545727
  have hstable : (prefixWord ++ tailWord_7545727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545727).length < 2 ^ (prefixWord ++ tailWord_7545727).sum := by decide
  have hdescent : baseEnd_7545727 < baseStart_7545727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545764 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_7545764 : Nat := 118140960795 + 7545764 * 2 ^ 59
def prefixEnd_7545764 : Nat := 4983230072969 + 3 ^ 40 * 7545764 * 2
def baseEnd_7545764 : Nat := 3874603837393120397347669

theorem tailTrace_7545764 : CollatzResearch.WordTrace tailWord_7545764 prefixEnd_7545764 3874603837393120397347669 := by
  unfold tailWord_7545764
  simp only [CollatzResearch.WordTrace]
  refine ⟨137608311517496608368278173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183477748689995477824370897 137608311517496608368278173)
  ·
    refine ⟨51603116819061228138104315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137608311517496608368278173 51603116819061228138104315)
    ·
      refine ⟨77404675228591842207156473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51603116819061228138104315 77404675228591842207156473)
      ·
        refine ⟨58053506421443881655367355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77404675228591842207156473 58053506421443881655367355)
        ·
          refine ⟨87080259632165822483051033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58053506421443881655367355 87080259632165822483051033)
          ·
            refine ⟨65310194724124366862288275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87080259632165822483051033 65310194724124366862288275)
            ·
              refine ⟨97965292086186550293432413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65310194724124366862288275 97965292086186550293432413)
              ·
                refine ⟨36736984532319956360037155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97965292086186550293432413 36736984532319956360037155)
                ·
                  refine ⟨55105476798479934540055733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36736984532319956360037155 55105476798479934540055733)
                  ·
                    refine ⟨5166138449857493863130225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55105476798479934540055733 5166138449857493863130225)
                    ·
                      refine ⟨3874603837393120397347669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166138449857493863130225 3874603837393120397347669)
                      ·
                        rfl

theorem cell23_7545764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_7545764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545764 prefixEnd_7545764 := by exact prefixLift 7545764
  have htrace : WordTrace (prefixWord ++ tailWord_7545764) baseStart_7545764 baseEnd_7545764 := by
    simpa [prefixWord, tailWord_7545764, baseEnd_7545764] using wordTrace_append hprefix tailTrace_7545764
  have hstable : (prefixWord ++ tailWord_7545764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545764).length < 2 ^ (prefixWord ++ tailWord_7545764).sum := by decide
  have hdescent : baseEnd_7545764 < baseStart_7545764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545781 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7545781 : Nat := 118140960795 + 7545781 * 2 ^ 59
def prefixEnd_7545781 : Nat := 4983230072969 + 3 ^ 40 * 7545781 * 2
def baseEnd_7545781 : Nat := 3874612566564246830835091

theorem tailTrace_7545781 : CollatzResearch.WordTrace tailWord_7545781 prefixEnd_7545781 3874612566564246830835091 := by
  unfold tailWord_7545781
  simp only [CollatzResearch.WordTrace]
  refine ⟨275217243075931628639925197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183478162050621085759950131 275217243075931628639925197)
  ·
    refine ⟨103206466153474360739971949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275217243075931628639925197 103206466153474360739971949)
    ·
      refine ⟨38702424807552885277489481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103206466153474360739971949 38702424807552885277489481)
      ·
        refine ⟨29026818605664663958117111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38702424807552885277489481 29026818605664663958117111)
        ·
          refine ⟨43540227908496995937175667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29026818605664663958117111 43540227908496995937175667)
          ·
            refine ⟨65310341862745493905763501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43540227908496995937175667 65310341862745493905763501)
            ·
              refine ⟨24491378198529560214661313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65310341862745493905763501 24491378198529560214661313)
              ·
                refine ⟨18368533648897170160995985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24491378198529560214661313 18368533648897170160995985)
                ·
                  refine ⟨13776400236672877620746989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18368533648897170160995985 13776400236672877620746989)
                  ·
                    refine ⟨5166150088752329107780121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13776400236672877620746989 5166150088752329107780121)
                    ·
                      refine ⟨3874612566564246830835091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166150088752329107780121 3874612566564246830835091)
                      ·
                        rfl

theorem cell23_7545781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7545781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545781 prefixEnd_7545781 := by exact prefixLift 7545781
  have htrace : WordTrace (prefixWord ++ tailWord_7545781) baseStart_7545781 baseEnd_7545781 := by
    simpa [prefixWord, tailWord_7545781, baseEnd_7545781] using wordTrace_append hprefix tailTrace_7545781
  have hstable : (prefixWord ++ tailWord_7545781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545781).length < 2 ^ (prefixWord ++ tailWord_7545781).sum := by decide
  have hdescent : baseEnd_7545781 < baseStart_7545781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545782 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7545782 : Nat := 118140960795 + 7545782 * 2 ^ 59
def prefixEnd_7545782 : Nat := 4983230072969 + 3 ^ 40 * 7545782 * 2
def baseEnd_7545782 : Nat := 1291537693348300442307529

theorem tailTrace_7545782 : CollatzResearch.WordTrace tailWord_7545782 prefixEnd_7545782 1291537693348300442307529 := by
  unfold tailWord_7545782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201079971808000363169475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183478186365952003873807733 17201079971808000363169475)
  ·
    refine ⟨25801619957712000544754213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17201079971808000363169475 25801619957712000544754213)
    ·
      refine ⟨4837803742071000102141415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25801619957712000544754213 4837803742071000102141415)
      ·
        refine ⟨7256705613106500153212123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837803742071000102141415 7256705613106500153212123)
        ·
          refine ⟨10885058419659750229818185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256705613106500153212123 10885058419659750229818185)
          ·
            refine ⟨8163793814744812672363639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10885058419659750229818185 8163793814744812672363639)
            ·
              refine ⟨12245690722117219008545459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163793814744812672363639 12245690722117219008545459)
              ·
                refine ⟨18368536083175828512818189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245690722117219008545459 18368536083175828512818189)
                ·
                  refine ⟨6888201031190935692306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18368536083175828512818189 6888201031190935692306821)
                  ·
                    refine ⟨1291537693348300442307529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888201031190935692306821 1291537693348300442307529)
                    ·
                      rfl

theorem cell23_7545782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7545782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545782 prefixEnd_7545782 := by exact prefixLift 7545782
  have htrace : WordTrace (prefixWord ++ tailWord_7545782) baseStart_7545782 baseEnd_7545782 := by
    simpa [prefixWord, tailWord_7545782, baseEnd_7545782] using wordTrace_append hprefix tailTrace_7545782
  have hstable : (prefixWord ++ tailWord_7545782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545782).length < 2 ^ (prefixWord ++ tailWord_7545782).sum := by decide
  have hdescent : baseEnd_7545782 < baseStart_7545782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545787 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 8, 4]
def baseStart_7545787 : Nat := 118140960795 + 7545787 * 2 ^ 59
def prefixEnd_7545787 : Nat := 4983230072969 + 3 ^ 40 * 7545787 * 2
def baseEnd_7545787 : Nat := 1291538549149391269120021

theorem tailTrace_7545787 : CollatzResearch.WordTrace tailWord_7545787 prefixEnd_7545787 1291538549149391269120021 := by
  unfold tailWord_7545787
  simp only [CollatzResearch.WordTrace]
  refine ⟨275217461913909891664643615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183478307942606594443095743 275217461913909891664643615)
  ·
    refine ⟨412826192870864837496965423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275217461913909891664643615 412826192870864837496965423)
    ·
      refine ⟨619239289306297256245448135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412826192870864837496965423 619239289306297256245448135)
      ·
        refine ⟨928858933959445884368172203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619239289306297256245448135 928858933959445884368172203)
        ·
          refine ⟨1393288400939168826552258305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928858933959445884368172203 1393288400939168826552258305)
          ·
            refine ⟨1044966300704376619914193729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393288400939168826552258305 1044966300704376619914193729)
            ·
              refine ⟨783724725528282464935645297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044966300704376619914193729 783724725528282464935645297)
              ·
                refine ⟨587793544146211848701733973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783724725528282464935645297 587793544146211848701733973)
                ·
                  refine ⟨6888205595463420101973445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 587793544146211848701733973 6888205595463420101973445)
                  ·
                    refine ⟨1291538549149391269120021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888205595463420101973445 1291538549149391269120021)
                    ·
                      rfl

theorem cell23_7545787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 4].length) (baseStart_7545787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545787 prefixEnd_7545787 := by exact prefixLift 7545787
  have htrace : WordTrace (prefixWord ++ tailWord_7545787) baseStart_7545787 baseEnd_7545787 := by
    simpa [prefixWord, tailWord_7545787, baseEnd_7545787] using wordTrace_append hprefix tailTrace_7545787
  have hstable : (prefixWord ++ tailWord_7545787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545787).length < 2 ^ (prefixWord ++ tailWord_7545787).sum := by decide
  have hdescent : baseEnd_7545787 < baseStart_7545787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545807 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_7545807 : Nat := 118140960795 + 7545807 * 2 ^ 59
def prefixEnd_7545807 : Nat := 4983230072969 + 3 ^ 40 * 7545807 * 2
def baseEnd_7545807 : Nat := 3874625917061263729109971

theorem tailTrace_7545807 : CollatzResearch.WordTrace tailWord_7545807 prefixEnd_7545807 3874625917061263729109971 := by
  unfold tailWord_7545807
  simp only [CollatzResearch.WordTrace]
  refine ⟨275218191373837435080371675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183478794249224956720247783 275218191373837435080371675)
  ·
    refine ⟨412827287060756152620557513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275218191373837435080371675 412827287060756152620557513)
    ·
      refine ⟨309620465295567114465418135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412827287060756152620557513 309620465295567114465418135)
      ·
        refine ⟨464430697943350671698127203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309620465295567114465418135 464430697943350671698127203)
        ·
          refine ⟨696646046915026007547190805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464430697943350671698127203 696646046915026007547190805)
          ·
            refine ⟨32655283449141844103774569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 696646046915026007547190805 32655283449141844103774569)
            ·
              refine ⟨24491462586856383077830927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32655283449141844103774569 24491462586856383077830927)
              ·
                refine ⟨36737193880284574616746391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24491462586856383077830927 36737193880284574616746391)
                ·
                  refine ⟨55105790820426861925119587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36737193880284574616746391 55105790820426861925119587)
                  ·
                    refine ⟨82658686230640292887679381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55105790820426861925119587 82658686230640292887679381)
                    ·
                      refine ⟨3874625917061263729109971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82658686230640292887679381 3874625917061263729109971)
                      ·
                        rfl

theorem cell23_7545807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_7545807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545807 prefixEnd_7545807 := by exact prefixLift 7545807
  have htrace : WordTrace (prefixWord ++ tailWord_7545807) baseStart_7545807 baseEnd_7545807 := by
    simpa [prefixWord, tailWord_7545807, baseEnd_7545807] using wordTrace_append hprefix tailTrace_7545807
  have hstable : (prefixWord ++ tailWord_7545807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545807).length < 2 ^ (prefixWord ++ tailWord_7545807).sum := by decide
  have hdescent : baseEnd_7545807 < baseStart_7545807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545817 : List Nat := [1, 2, 1, 2, 5, 1, 2, 9]
def baseStart_7545817 : Nat := 118140960795 + 7545817 * 2 ^ 59
def prefixEnd_7545817 : Nat := 4983230072969 + 3 ^ 40 * 7545817 * 2
def baseEnd_7545817 : Nat := 143504853772881803332775

theorem tailTrace_7545817 : CollatzResearch.WordTrace tailWord_7545817 prefixEnd_7545817 143504853772881803332775 := by
  unfold tailWord_7545817
  simp only [CollatzResearch.WordTrace]
  refine ⟨275218556103801206788235705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183479037402534137858823803 275218556103801206788235705)
  ·
    refine ⟨206413917077850905091176779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275218556103801206788235705 206413917077850905091176779)
    ·
      refine ⟨309620875616776357636765169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206413917077850905091176779 309620875616776357636765169)
      ·
        refine ⟨232215656712582268227573877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309620875616776357636765169 232215656712582268227573877)
        ·
          refine ⟨21770217816804587646335051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232215656712582268227573877 21770217816804587646335051)
          ·
            refine ⟨32655326725206881469502577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21770217816804587646335051 32655326725206881469502577)
            ·
              refine ⟨24491495043905161102126933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32655326725206881469502577 24491495043905161102126933)
              ·
                refine ⟨143504853772881803332775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24491495043905161102126933 143504853772881803332775)
                ·
                  rfl

theorem cell23_7545817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 9].length) (baseStart_7545817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545817 prefixEnd_7545817 := by exact prefixLift 7545817
  have htrace : WordTrace (prefixWord ++ tailWord_7545817) baseStart_7545817 baseEnd_7545817 := by
    simpa [prefixWord, tailWord_7545817, baseEnd_7545817] using wordTrace_append hprefix tailTrace_7545817
  have hstable : (prefixWord ++ tailWord_7545817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545817).length < 2 ^ (prefixWord ++ tailWord_7545817).sum := by decide
  have hdescent : baseEnd_7545817 < baseStart_7545817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545831 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7545831 : Nat := 118140960795 + 7545831 * 2 ^ 59
def prefixEnd_7545831 : Nat := 4983230072969 + 3 ^ 40 * 7545831 * 2
def baseEnd_7545831 : Nat := 3874638240596971635209861

theorem tailTrace_7545831 : CollatzResearch.WordTrace tailWord_7545831 prefixEnd_7545831 3874638240596971635209861 := by
  unfold tailWord_7545831
  simp only [CollatzResearch.WordTrace]
  refine ⟨275219066725750487179245347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183479377817166991452830231 275219066725750487179245347)
  ·
    refine ⟨412828600088625730768868021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275219066725750487179245347 412828600088625730768868021)
    ·
      refine ⟨38702681258308662259581377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412828600088625730768868021 38702681258308662259581377)
      ·
        refine ⟨29027010943731496694686033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38702681258308662259581377 29027010943731496694686033)
        ·
          refine ⟨21770258207798622521014525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29027010943731496694686033 21770258207798622521014525)
          ·
            refine ⟨8163846827924483445380447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21770258207798622521014525 8163846827924483445380447)
            ·
              refine ⟨12245770241886725168070671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163846827924483445380447 12245770241886725168070671)
              ·
                refine ⟨18368655362830087752106007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12245770241886725168070671 18368655362830087752106007)
                ·
                  refine ⟨27552983044245131628159011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18368655362830087752106007 27552983044245131628159011)
                  ·
                    refine ⟨41329474566367697442238517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27552983044245131628159011 41329474566367697442238517)
                    ·
                      refine ⟨3874638240596971635209861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41329474566367697442238517 3874638240596971635209861)
                      ·
                        rfl

theorem cell23_7545831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7545831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545831 prefixEnd_7545831 := by exact prefixLift 7545831
  have htrace : WordTrace (prefixWord ++ tailWord_7545831) baseStart_7545831 baseEnd_7545831 := by
    simpa [prefixWord, tailWord_7545831, baseEnd_7545831] using wordTrace_append hprefix tailTrace_7545831
  have hstable : (prefixWord ++ tailWord_7545831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545831).length < 2 ^ (prefixWord ++ tailWord_7545831).sum := by decide
  have hdescent : baseEnd_7545831 < baseStart_7545831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545838 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7545838 : Nat := 118140960795 + 7545838 * 2 ^ 59
def prefixEnd_7545838 : Nat := 4983230072969 + 3 ^ 40 * 7545838 * 2
def baseEnd_7545838 : Nat := 1291547278320517702607443

theorem tailTrace_7545838 : CollatzResearch.WordTrace tailWord_7545838 prefixEnd_7545838 1291547278320517702607443 := by
  unfold tailWord_7545838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34402415254590640921843771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183479548024483418249833445 34402415254590640921843771)
  ·
    refine ⟨51603622881885961382765657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34402415254590640921843771 51603622881885961382765657)
    ·
      refine ⟨38702717161414471037074243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51603622881885961382765657 38702717161414471037074243)
      ·
        refine ⟨58054075742121706555611365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38702717161414471037074243 58054075742121706555611365)
        ·
          refine ⟨10885139201647819979177131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58054075742121706555611365 10885139201647819979177131)
          ·
            refine ⟨16327708802471729968765697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885139201647819979177131 16327708802471729968765697)
            ·
              refine ⟨12245781601853797476574273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16327708802471729968765697 12245781601853797476574273)
              ·
                refine ⟨9184336201390348107430705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245781601853797476574273 9184336201390348107430705)
                ·
                  refine ⟨6888252151042761080573029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184336201390348107430705 6888252151042761080573029)
                  ·
                    refine ⟨1291547278320517702607443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888252151042761080573029 1291547278320517702607443)
                    ·
                      rfl

theorem cell23_7545838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7545838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545838 prefixEnd_7545838 := by exact prefixLift 7545838
  have htrace : WordTrace (prefixWord ++ tailWord_7545838) baseStart_7545838 baseEnd_7545838 := by
    simpa [prefixWord, tailWord_7545838, baseEnd_7545838] using wordTrace_append hprefix tailTrace_7545838
  have hstable : (prefixWord ++ tailWord_7545838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545838).length < 2 ^ (prefixWord ++ tailWord_7545838).sum := by decide
  have hdescent : baseEnd_7545838 < baseStart_7545838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545861 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_7545861 : Nat := 118140960795 + 7545861 * 2 ^ 59
def prefixEnd_7545861 : Nat := 4983230072969 + 3 ^ 40 * 7545861 * 2
def baseEnd_7545861 : Nat := 3874653645016606517834723

theorem tailTrace_7545861 : CollatzResearch.WordTrace tailWord_7545861 prefixEnd_7545861 3874653645016606517834723 := by
  unfold tailWord_7545861
  simp only [CollatzResearch.WordTrace]
  refine ⟨275220160915641802302837437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183480107277094534868558291 275220160915641802302837437)
  ·
    refine ⟨103207560343365675863564039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275220160915641802302837437 103207560343365675863564039)
    ·
      refine ⟨154811340515048513795346059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103207560343365675863564039 154811340515048513795346059)
      ·
        refine ⟨232217010772572770693019089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154811340515048513795346059 232217010772572770693019089)
        ·
          refine ⟨174162758079429578019764317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232217010772572770693019089 174162758079429578019764317)
          ·
            refine ⟨65311034279786091757411619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174162758079429578019764317 65311034279786091757411619)
            ·
              refine ⟨97966551419679137636117429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65311034279786091757411619 97966551419679137636117429)
              ·
                refine ⟨9184364195594919153386009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97966551419679137636117429 9184364195594919153386009)
                ·
                  refine ⟨6888273146696189365039507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184364195594919153386009 6888273146696189365039507)
                  ·
                    refine ⟨10332409720044284047559261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888273146696189365039507 10332409720044284047559261)
                    ·
                      refine ⟨3874653645016606517834723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10332409720044284047559261 3874653645016606517834723)
                      ·
                        rfl

theorem cell23_7545861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_7545861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545861 prefixEnd_7545861 := by exact prefixLift 7545861
  have htrace : WordTrace (prefixWord ++ tailWord_7545861) baseStart_7545861 baseEnd_7545861 := by
    simpa [prefixWord, tailWord_7545861, baseEnd_7545861] using wordTrace_append hprefix tailTrace_7545861
  have hstable : (prefixWord ++ tailWord_7545861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545861).length < 2 ^ (prefixWord ++ tailWord_7545861).sum := by decide
  have hdescent : baseEnd_7545861 < baseStart_7545861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545895 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7545895 : Nat := 118140960795 + 7545895 * 2 ^ 59
def prefixEnd_7545895 : Nat := 4983230072969 + 3 ^ 40 * 7545895 * 2
def baseEnd_7545895 : Nat := 3874671103358859384809567

theorem tailTrace_7545895 : CollatzResearch.WordTrace tailWord_7545895 prefixEnd_7545895 3874671103358859384809567 := by
  unfold tailWord_7545895
  simp only [CollatzResearch.WordTrace]
  refine ⟨275221400997518626109575139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183480933998345750739716759 275221400997518626109575139)
  ·
    refine ⟨412832101496277939164362709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275221400997518626109575139 412832101496277939164362709)
    ·
      refine ⟨9675752378819014199164751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 412832101496277939164362709 9675752378819014199164751)
      ·
        refine ⟨14513628568228521298747127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675752378819014199164751 14513628568228521298747127)
        ·
          refine ⟨21770442852342781948120691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14513628568228521298747127 21770442852342781948120691)
          ·
            refine ⟨32655664278514172922181037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21770442852342781948120691 32655664278514172922181037)
            ·
              refine ⟨12245874104442814845817889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32655664278514172922181037 12245874104442814845817889)
              ·
                refine ⟨9184405578332111134363417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12245874104442814845817889 9184405578332111134363417)
                ·
                  refine ⟨6888304183749083350772563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9184405578332111134363417 6888304183749083350772563)
                  ·
                    refine ⟨10332456275623625026158845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888304183749083350772563 10332456275623625026158845)
                    ·
                      refine ⟨3874671103358859384809567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10332456275623625026158845 3874671103358859384809567)
                      ·
                        rfl

theorem cell23_7545895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7545895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545895 prefixEnd_7545895 := by exact prefixLift 7545895
  have htrace : WordTrace (prefixWord ++ tailWord_7545895) baseStart_7545895 baseEnd_7545895 := by
    simpa [prefixWord, tailWord_7545895, baseEnd_7545895] using wordTrace_append hprefix tailTrace_7545895
  have hstable : (prefixWord ++ tailWord_7545895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545895).length < 2 ^ (prefixWord ++ tailWord_7545895).sum := by decide
  have hdescent : baseEnd_7545895 < baseStart_7545895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545897 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_7545897 : Nat := 118140960795 + 7545897 * 2 ^ 59
def prefixEnd_7545897 : Nat := 4983230072969 + 3 ^ 40 * 7545897 * 2
def baseEnd_7545897 : Nat := 3874672130320168376984557

theorem tailTrace_7545897 : CollatzResearch.WordTrace tailWord_7545897 prefixEnd_7545897 3874672130320168376984557 := by
  unfold tailWord_7545897
  simp only [CollatzResearch.WordTrace]
  refine ⟨275221473943511380451147945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183480982629007586967431963 275221473943511380451147945)
  ·
    refine ⟨206416105457633535338360959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275221473943511380451147945 206416105457633535338360959)
    ·
      refine ⟨309624158186450303007541439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206416105457633535338360959 309624158186450303007541439)
      ·
        refine ⟨464436237279675454511312159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309624158186450303007541439 464436237279675454511312159)
        ·
          refine ⟨696654355919513181766968239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464436237279675454511312159 696654355919513181766968239)
          ·
            refine ⟨1044981533879269772650452359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696654355919513181766968239 1044981533879269772650452359)
            ·
              refine ⟨1567472300818904658975678539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044981533879269772650452359 1567472300818904658975678539)
              ·
                refine ⟨2351208451228356988463517809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567472300818904658975678539 2351208451228356988463517809)
                ·
                  refine ⟨1763406338421267741347638357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2351208451228356988463517809 1763406338421267741347638357)
                  ·
                    refine ⟨20664918028374231343917637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1763406338421267741347638357 20664918028374231343917637)
                    ·
                      refine ⟨3874672130320168376984557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20664918028374231343917637 3874672130320168376984557)
                      ·
                        rfl

theorem cell23_7545897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_7545897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545897 prefixEnd_7545897 := by exact prefixLift 7545897
  have htrace : WordTrace (prefixWord ++ tailWord_7545897) baseStart_7545897 baseEnd_7545897 := by
    simpa [prefixWord, tailWord_7545897, baseEnd_7545897] using wordTrace_append hprefix tailTrace_7545897
  have hstable : (prefixWord ++ tailWord_7545897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545897).length < 2 ^ (prefixWord ++ tailWord_7545897).sum := by decide
  have hdescent : baseEnd_7545897 < baseStart_7545897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545914 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_7545914 : Nat := 118140960795 + 7545914 * 2 ^ 59
def prefixEnd_7545914 : Nat := 4983230072969 + 3 ^ 40 * 7545914 * 2
def baseEnd_7545914 : Nat := 3874680859491294810471979

theorem tailTrace_7545914 : CollatzResearch.WordTrace tailWord_7545914 prefixEnd_7545914 3874680859491294810471979 := by
  unfold tailWord_7545914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68805523496112448088629199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183481395989633194903011197 68805523496112448088629199)
  ·
    refine ⟨103208285244168672132943799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68805523496112448088629199 103208285244168672132943799)
    ·
      refine ⟨154812427866253008199415699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103208285244168672132943799 154812427866253008199415699)
      ·
        refine ⟨232218641799379512299123549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154812427866253008199415699 232218641799379512299123549)
        ·
          refine ⟨87081990674767317112171331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232218641799379512299123549 87081990674767317112171331)
          ·
            refine ⟨130622986012150975668256997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87081990674767317112171331 130622986012150975668256997)
            ·
              refine ⟨24491809877278307937798187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130622986012150975668256997 24491809877278307937798187)
              ·
                refine ⟨36737714815917461906697281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24491809877278307937798187 36737714815917461906697281)
                ·
                  refine ⟨27553286111938096430022961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36737714815917461906697281 27553286111938096430022961)
                  ·
                    refine ⟨20664964583953572322517221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27553286111938096430022961 20664964583953572322517221)
                    ·
                      refine ⟨3874680859491294810471979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20664964583953572322517221 3874680859491294810471979)
                      ·
                        rfl

theorem cell23_7545914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_7545914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545914 prefixEnd_7545914 := by exact prefixLift 7545914
  have htrace : WordTrace (prefixWord ++ tailWord_7545914) baseStart_7545914 baseEnd_7545914 := by
    simpa [prefixWord, tailWord_7545914, baseEnd_7545914] using wordTrace_append hprefix tailTrace_7545914
  have hstable : (prefixWord ++ tailWord_7545914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545914).length < 2 ^ (prefixWord ++ tailWord_7545914).sum := by decide
  have hdescent : baseEnd_7545914 < baseStart_7545914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545964 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_7545964 : Nat := 118140960795 + 7545964 * 2 ^ 59
def prefixEnd_7545964 : Nat := 4983230072969 + 3 ^ 40 * 7545964 * 2
def baseEnd_7545964 : Nat := 3874706533524019614846749

theorem tailTrace_7545964 : CollatzResearch.WordTrace tailWord_7545964 prefixEnd_7545964 3874706533524019614846749 := by
  unfold tailWord_7545964
  simp only [CollatzResearch.WordTrace]
  refine ⟨137611958817134325446918473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183482611756179100595891297 137611958817134325446918473)
  ·
    refine ⟨103208969112850744085188855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137611958817134325446918473 103208969112850744085188855)
    ·
      refine ⟨154813453669276116127783283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103208969112850744085188855 154813453669276116127783283)
      ·
        refine ⟨232220180503914174191674925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154813453669276116127783283 232220180503914174191674925)
        ·
          refine ⟨87082567688967815321878097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232220180503914174191674925 87082567688967815321878097)
          ·
            refine ⟨65311925766725861491408573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87082567688967815321878097 65311925766725861491408573)
            ·
              refine ⟨24491972162522198059278215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65311925766725861491408573 24491972162522198059278215)
              ·
                refine ⟨36737958243783297088917323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24491972162522198059278215 36737958243783297088917323)
                ·
                  refine ⟨55106937365674945633375985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36737958243783297088917323 55106937365674945633375985)
                  ·
                    refine ⟨41330203024256209225031989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55106937365674945633375985 41330203024256209225031989)
                    ·
                      refine ⟨3874706533524019614846749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41330203024256209225031989 3874706533524019614846749)
                      ·
                        rfl

theorem cell23_7545964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_7545964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545964 prefixEnd_7545964 := by exact prefixLift 7545964
  have htrace : WordTrace (prefixWord ++ tailWord_7545964) baseStart_7545964 baseEnd_7545964 := by
    simpa [prefixWord, tailWord_7545964, baseEnd_7545964] using wordTrace_append hprefix tailTrace_7545964
  have hstable : (prefixWord ++ tailWord_7545964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545964).length < 2 ^ (prefixWord ++ tailWord_7545964).sum := by decide
  have hdescent : baseEnd_7545964 < baseStart_7545964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7545991 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_7545991 : Nat := 118140960795 + 7545991 * 2 ^ 59
def prefixEnd_7545991 : Nat := 4983230072969 + 3 ^ 40 * 7545991 * 2
def baseEnd_7545991 : Nat := 3874720397501691009209125

theorem tailTrace_7545991 : CollatzResearch.WordTrace tailWord_7545991 prefixEnd_7545991 3874720397501691009209125 := by
  unfold tailWord_7545991
  simp only [CollatzResearch.WordTrace]
  refine ⟨275224902405170834505069827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183483268270113889670046551 275224902405170834505069827)
  ·
    refine ⟨412837353607756251757604741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275224902405170834505069827 412837353607756251757604741)
    ·
      refine ⟨77407003801454297204550889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412837353607756251757604741 77407003801454297204550889)
      ·
        refine ⟨58055252851090722903413167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77407003801454297204550889 58055252851090722903413167)
        ·
          refine ⟨87082879276636084355119751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58055252851090722903413167 87082879276636084355119751)
          ·
            refine ⟨130624318914954126532679627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87082879276636084355119751 130624318914954126532679627)
            ·
              refine ⟨195936478372431189799019441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130624318914954126532679627 195936478372431189799019441)
              ·
                refine ⟨146952358779323392349264581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195936478372431189799019441 146952358779323392349264581)
                ·
                  refine ⟨27553567271123136065487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146952358779323392349264581 27553567271123136065487109)
                  ·
                    refine ⟨5166293863335588012278833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27553567271123136065487109 5166293863335588012278833)
                    ·
                      refine ⟨3874720397501691009209125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166293863335588012278833 3874720397501691009209125)
                      ·
                        rfl

theorem cell23_7545991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_7545991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7545991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7545991 prefixEnd_7545991 := by exact prefixLift 7545991
  have htrace : WordTrace (prefixWord ++ tailWord_7545991) baseStart_7545991 baseEnd_7545991 := by
    simpa [prefixWord, tailWord_7545991, baseEnd_7545991] using wordTrace_append hprefix tailTrace_7545991
  have hstable : (prefixWord ++ tailWord_7545991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7545991).length < 2 ^ (prefixWord ++ tailWord_7545991).sum := by decide
  have hdescent : baseEnd_7545991 < baseStart_7545991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7545991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546052 : List Nat := [2, 3, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7546052 : Nat := 118140960795 + 7546052 * 2 ^ 59
def prefixEnd_7546052 : Nat := 4983230072969 + 3 ^ 40 * 7546052 * 2
def baseEnd_7546052 : Nat := 1291583906607205090182115

theorem tailTrace_7546052 : CollatzResearch.WordTrace tailWord_7546052 prefixEnd_7546052 1291583906607205090182115 := by
  unfold tailWord_7546052
  simp only [CollatzResearch.WordTrace]
  refine ⟨137613563628974920961520205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183484751505299894615360273 137613563628974920961520205)
  ·
    refine ⟨51605086360865595360570077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137613563628974920961520205 51605086360865595360570077)
    ·
      refine ⟨19351907385324598260213779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51605086360865595360570077 19351907385324598260213779)
      ·
        refine ⟨29027861077986897390320669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19351907385324598260213779 29027861077986897390320669)
        ·
          refine ⟨10885447904245086521370251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29027861077986897390320669 10885447904245086521370251)
          ·
            refine ⟨16328171856367629782055377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10885447904245086521370251 16328171856367629782055377)
            ·
              refine ⟨12246128892275722336541533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16328171856367629782055377 12246128892275722336541533)
              ·
                refine ⟨4592298334603395876203075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12246128892275722336541533 4592298334603395876203075)
                ·
                  refine ⟨6888447501905093814304613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592298334603395876203075 6888447501905093814304613)
                  ·
                    refine ⟨1291583906607205090182115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888447501905093814304613 1291583906607205090182115)
                    ·
                      rfl

theorem cell23_7546052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7546052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546052 prefixEnd_7546052 := by exact prefixLift 7546052
  have htrace : WordTrace (prefixWord ++ tailWord_7546052) baseStart_7546052 baseEnd_7546052 := by
    simpa [prefixWord, tailWord_7546052, baseEnd_7546052] using wordTrace_append hprefix tailTrace_7546052
  have hstable : (prefixWord ++ tailWord_7546052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546052).length < 2 ^ (prefixWord ++ tailWord_7546052).sum := by decide
  have hdescent : baseEnd_7546052 < baseStart_7546052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546091 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 1, 6]
def baseStart_7546091 : Nat := 118140960795 + 7546091 * 2 ^ 59
def prefixEnd_7546091 : Nat := 4983230072969 + 3 ^ 40 * 7546091 * 2
def baseEnd_7546091 : Nat := 1291590581855713539319555

theorem tailTrace_7546091 : CollatzResearch.WordTrace tailWord_7546091 prefixEnd_7546091 1291590581855713539319555 := by
  unfold tailWord_7546091
  simp only [CollatzResearch.WordTrace]
  refine ⟨275228549704808551583710127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183485699803205701055806751 275228549704808551583710127)
  ·
    refine ⟨412842824557212827375565191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275228549704808551583710127 412842824557212827375565191)
    ·
      refine ⟨619264236835819241063347787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412842824557212827375565191 619264236835819241063347787)
      ·
        refine ⟨928896355253728861595021681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619264236835819241063347787 928896355253728861595021681)
        ·
          refine ⟨696672266440296646196266261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928896355253728861595021681 696672266440296646196266261)
          ·
            refine ⟨32656512489388905290449981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 696672266440296646196266261 32656512489388905290449981)
            ·
              refine ⟨12246192183520839483918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32656512489388905290449981 12246192183520839483918743)
              ·
                refine ⟨18369288275281259225878115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246192183520839483918743 18369288275281259225878115)
                ·
                  refine ⟨27553932412921888838817173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18369288275281259225878115 27553932412921888838817173)
                  ·
                    refine ⟨1291590581855713539319555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27553932412921888838817173 1291590581855713539319555)
                    ·
                      rfl

theorem cell23_7546091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].length) (baseStart_7546091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546091 prefixEnd_7546091 := by exact prefixLift 7546091
  have htrace : WordTrace (prefixWord ++ tailWord_7546091) baseStart_7546091 baseEnd_7546091 := by
    simpa [prefixWord, tailWord_7546091, baseEnd_7546091] using wordTrace_append hprefix tailTrace_7546091
  have hstable : (prefixWord ++ tailWord_7546091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546091).length < 2 ^ (prefixWord ++ tailWord_7546091).sum := by decide
  have hdescent : baseEnd_7546091 < baseStart_7546091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546148 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_7546148 : Nat := 118140960795 + 7546148 * 2 ^ 59
def prefixEnd_7546148 : Nat := 4983230072969 + 3 ^ 40 * 7546148 * 2
def baseEnd_7546148 : Nat := 3874801013964446894945903

theorem tailTrace_7546148 : CollatzResearch.WordTrace tailWord_7546148 prefixEnd_7546148 3874801013964446894945903 := by
  unfold tailWord_7546148
  simp only [CollatzResearch.WordTrace]
  refine ⟨137615314332801025159267549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183487085777068033545690065 137615314332801025159267549)
  ·
    refine ⟨51605742874800384434725331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137615314332801025159267549 51605742874800384434725331)
    ·
      refine ⟨77408614312200576652087997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51605742874800384434725331 77408614312200576652087997)
      ·
        refine ⟨29028230367075216244532999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77408614312200576652087997 29028230367075216244532999)
        ·
          refine ⟨43542345550612824366799499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29028230367075216244532999 43542345550612824366799499)
          ·
            refine ⟨65313518325919236550199249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43542345550612824366799499 65313518325919236550199249)
            ·
              refine ⟨48985138744439427412649437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65313518325919236550199249 48985138744439427412649437)
              ·
                refine ⟨18369427029164785279743539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48985138744439427412649437 18369427029164785279743539)
                ·
                  refine ⟨27554140543747177919615309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18369427029164785279743539 27554140543747177919615309)
                  ·
                    refine ⟨10332802703905191719855741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27554140543747177919615309 10332802703905191719855741)
                    ·
                      refine ⟨3874801013964446894945903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10332802703905191719855741 3874801013964446894945903)
                      ·
                        rfl

theorem cell23_7546148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_7546148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546148 prefixEnd_7546148 := by exact prefixLift 7546148
  have htrace : WordTrace (prefixWord ++ tailWord_7546148) baseStart_7546148 baseEnd_7546148 := by
    simpa [prefixWord, tailWord_7546148, baseEnd_7546148] using wordTrace_append hprefix tailTrace_7546148
  have hstable : (prefixWord ++ tailWord_7546148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546148).length < 2 ^ (prefixWord ++ tailWord_7546148).sum := by decide
  have hdescent : baseEnd_7546148 < baseStart_7546148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546152 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7546152 : Nat := 118140960795 + 7546152 * 2 ^ 59
def prefixEnd_7546152 : Nat := 4983230072969 + 3 ^ 40 * 7546152 * 2
def baseEnd_7546152 : Nat := 3874803067887064879295885

theorem tailTrace_7546152 : CollatzResearch.WordTrace tailWord_7546152 prefixEnd_7546152 3874803067887064879295885 := by
  unfold tailWord_7546152
  simp only [CollatzResearch.WordTrace]
  refine ⟨137615387278793779500840355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183487183038391706001120473 137615387278793779500840355)
  ·
    refine ⟨206423080918190669251260533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137615387278793779500840355 206423080918190669251260533)
    ·
      refine ⟨19352163836080375242305675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206423080918190669251260533 19352163836080375242305675)
      ·
        refine ⟨29028245754120562863458513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19352163836080375242305675 29028245754120562863458513)
        ·
          refine ⟨21771184315590422147593885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29028245754120562863458513 21771184315590422147593885)
          ·
            refine ⟨8164194118346408305347707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21771184315590422147593885 8164194118346408305347707)
            ·
              refine ⟨12246291177519612458021561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164194118346408305347707 12246291177519612458021561)
              ·
                refine ⟨9184718383139709343516171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12246291177519612458021561 9184718383139709343516171)
                ·
                  refine ⟨13777077574709564015274257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9184718383139709343516171 13777077574709564015274257)
                  ·
                    refine ⟨10332808181032173011455693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13777077574709564015274257 10332808181032173011455693)
                    ·
                      refine ⟨3874803067887064879295885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10332808181032173011455693 3874803067887064879295885)
                      ·
                        rfl

theorem cell23_7546152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7546152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546152 prefixEnd_7546152 := by exact prefixLift 7546152
  have htrace : WordTrace (prefixWord ++ tailWord_7546152) baseStart_7546152 baseEnd_7546152 := by
    simpa [prefixWord, tailWord_7546152, baseEnd_7546152] using wordTrace_append hprefix tailTrace_7546152
  have hstable : (prefixWord ++ tailWord_7546152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546152).length < 2 ^ (prefixWord ++ tailWord_7546152).sum := by decide
  have hdescent : baseEnd_7546152 < baseStart_7546152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546201 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_7546201 : Nat := 118140960795 + 7546201 * 2 ^ 59
def prefixEnd_7546201 : Nat := 4983230072969 + 3 ^ 40 * 7546201 * 2
def baseEnd_7546201 : Nat := 3874828228439135187583159

theorem tailTrace_7546201 : CollatzResearch.WordTrace tailWord_7546201 prefixEnd_7546201 3874828228439135187583159 := by
  unfold tailWord_7546201
  simp only [CollatzResearch.WordTrace]
  refine ⟨275232561734410040370214457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183488374489606693580142971 275232561734410040370214457)
  ·
    refine ⟨206424421300807530277660843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275232561734410040370214457 206424421300807530277660843)
    ·
      refine ⟨309636631951211295416491265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206424421300807530277660843 309636631951211295416491265)
      ·
        refine ⟨232227473963408471562368449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309636631951211295416491265 232227473963408471562368449)
        ·
          refine ⟨174170605472556353671776337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232227473963408471562368449 174170605472556353671776337)
          ·
            refine ⟨130627954104417265253832253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174170605472556353671776337 130627954104417265253832253)
            ·
              refine ⟨48985482789156474470187095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130627954104417265253832253 48985482789156474470187095)
              ·
                refine ⟨73478224183734711705280643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48985482789156474470187095 73478224183734711705280643)
                ·
                  refine ⟨110217336275602067557920965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73478224183734711705280643 110217336275602067557920965)
                  ·
                    refine ⟨20665750551675387667110181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110217336275602067557920965 20665750551675387667110181)
                    ·
                      refine ⟨3874828228439135187583159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20665750551675387667110181 3874828228439135187583159)
                      ·
                        rfl

theorem cell23_7546201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_7546201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546201 prefixEnd_7546201 := by exact prefixLift 7546201
  have htrace : WordTrace (prefixWord ++ tailWord_7546201) baseStart_7546201 baseEnd_7546201 := by
    simpa [prefixWord, tailWord_7546201, baseEnd_7546201] using wordTrace_append hprefix tailTrace_7546201
  have hstable : (prefixWord ++ tailWord_7546201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546201).length < 2 ^ (prefixWord ++ tailWord_7546201).sum := by decide
  have hdescent : baseEnd_7546201 < baseStart_7546201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546211 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 9]
def baseStart_7546211 : Nat := 118140960795 + 7546211 * 2 ^ 59
def prefixEnd_7546211 : Nat := 4983230072969 + 3 ^ 40 * 7546211 * 2
def baseEnd_7546211 : Nat := 430537040360631127606457

theorem tailTrace_7546211 : CollatzResearch.WordTrace tailWord_7546211 prefixEnd_7546211 430537040360631127606457 := by
  unfold tailWord_7546211
  simp only [CollatzResearch.WordTrace]
  refine ⟨275232926464373812078078487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183488617642915874718718991 275232926464373812078078487)
  ·
    refine ⟨412849389696560718117117731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275232926464373812078078487 412849389696560718117117731)
    ·
      refine ⟨619274084544841077175676597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412849389696560718117117731 619274084544841077175676597)
      ·
        refine ⟨58056945426078850985219681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 619274084544841077175676597 58056945426078850985219681)
        ·
          refine ⟨43542709069559138238914761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58056945426078850985219681 43542709069559138238914761)
          ·
            refine ⟨32657031802169353679186071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43542709069559138238914761 32657031802169353679186071)
            ·
              refine ⟨48985547703254030518779107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32657031802169353679186071 48985547703254030518779107)
              ·
                refine ⟨73478321554881045778168661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48985547703254030518779107 73478321554881045778168661)
                ·
                  refine ⟨430537040360631127606457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73478321554881045778168661 430537040360631127606457)
                  ·
                    rfl

theorem cell23_7546211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 9].length) (baseStart_7546211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546211 prefixEnd_7546211 := by exact prefixLift 7546211
  have htrace : WordTrace (prefixWord ++ tailWord_7546211) baseStart_7546211 baseEnd_7546211 := by
    simpa [prefixWord, tailWord_7546211, baseEnd_7546211] using wordTrace_append hprefix tailTrace_7546211
  have hstable : (prefixWord ++ tailWord_7546211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546211).length < 2 ^ (prefixWord ++ tailWord_7546211).sum := by decide
  have hdescent : baseEnd_7546211 < baseStart_7546211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546251 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_7546251 : Nat := 118140960795 + 7546251 * 2 ^ 59
def prefixEnd_7546251 : Nat := 4983230072969 + 3 ^ 40 * 7546251 * 2
def baseEnd_7546251 : Nat := 3874853902471859991957929

theorem tailTrace_7546251 : CollatzResearch.WordTrace tailWord_7546251 prefixEnd_7546251 3874853902471859991957929 := by
  unfold tailWord_7546251
  simp only [CollatzResearch.WordTrace]
  refine ⟨275234385384228898909534607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183489590256152599273023071 275234385384228898909534607)
  ·
    refine ⟨412851578076343348364301911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275234385384228898909534607 412851578076343348364301911)
    ·
      refine ⟨619277367114515022546452867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412851578076343348364301911 619277367114515022546452867)
      ·
        refine ⟨928916050671772533819679301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619277367114515022546452867 928916050671772533819679301)
        ·
          refine ⟨174171759500957350091189869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928916050671772533819679301 174171759500957350091189869)
          ·
            refine ⟨65314409812859006284196201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174171759500957350091189869 65314409812859006284196201)
            ·
              refine ⟨48985807359644254713147151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65314409812859006284196201 48985807359644254713147151)
              ·
                refine ⟨73478711039466382069720727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48985807359644254713147151 73478711039466382069720727)
                ·
                  refine ⟨110218066559199573104581091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73478711039466382069720727 110218066559199573104581091)
                  ·
                    refine ⟨165327099838799359656871637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110218066559199573104581091 165327099838799359656871637)
                    ·
                      refine ⟨3874853902471859991957929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165327099838799359656871637 3874853902471859991957929)
                      ·
                        rfl

theorem cell23_7546251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_7546251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546251 prefixEnd_7546251 := by exact prefixLift 7546251
  have htrace : WordTrace (prefixWord ++ tailWord_7546251) baseStart_7546251 baseEnd_7546251 := by
    simpa [prefixWord, tailWord_7546251, baseEnd_7546251] using wordTrace_append hprefix tailTrace_7546251
  have hstable : (prefixWord ++ tailWord_7546251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546251).length < 2 ^ (prefixWord ++ tailWord_7546251).sum := by decide
  have hdescent : baseEnd_7546251 < baseStart_7546251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546281 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_7546281 : Nat := 118140960795 + 7546281 * 2 ^ 59
def prefixEnd_7546281 : Nat := 4983230072969 + 3 ^ 40 * 7546281 * 2
def baseEnd_7546281 : Nat := 3874869306891494874582791

theorem tailTrace_7546281 : CollatzResearch.WordTrace tailWord_7546281 prefixEnd_7546281 3874869306891494874582791 := by
  unfold tailWord_7546281
  simp only [CollatzResearch.WordTrace]
  refine ⟨275235479574120214033126697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183490319716080142688751131 275235479574120214033126697)
  ·
    refine ⟨206426609680590160524845023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275235479574120214033126697 206426609680590160524845023)
    ·
      refine ⟨309639914520885240787267535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206426609680590160524845023 309639914520885240787267535)
      ·
        refine ⟨464459871781327861180901303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309639914520885240787267535 464459871781327861180901303)
        ·
          refine ⟨696689807671991791771351955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464459871781327861180901303 696689807671991791771351955)
          ·
            refine ⟨1045034711507987687657027933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696689807671991791771351955 1045034711507987687657027933)
            ·
              refine ⟨391888016815495382871385475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1045034711507987687657027933 391888016815495382871385475)
              ·
                refine ⟨587832025223243074307078213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391888016815495382871385475 587832025223243074307078213)
                ·
                  refine ⟨110218504729358076432577165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587832025223243074307078213 110218504729358076432577165)
                  ·
                    refine ⟨41331939273509278662216437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110218504729358076432577165 41331939273509278662216437)
                    ·
                      refine ⟨3874869306891494874582791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41331939273509278662216437 3874869306891494874582791)
                      ·
                        rfl

theorem cell23_7546281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_7546281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546281 prefixEnd_7546281 := by exact prefixLift 7546281
  have htrace : WordTrace (prefixWord ++ tailWord_7546281) baseStart_7546281 baseEnd_7546281 := by
    simpa [prefixWord, tailWord_7546281, baseEnd_7546281] using wordTrace_append hprefix tailTrace_7546281
  have hstable : (prefixWord ++ tailWord_7546281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546281).length < 2 ^ (prefixWord ++ tailWord_7546281).sum := by decide
  have hdescent : baseEnd_7546281 < baseStart_7546281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546291 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_7546291 : Nat := 118140960795 + 7546291 * 2 ^ 59
def prefixEnd_7546291 : Nat := 4983230072969 + 3 ^ 40 * 7546291 * 2
def baseEnd_7546291 : Nat := 3874874441698039835457745

theorem tailTrace_7546291 : CollatzResearch.WordTrace tailWord_7546291 prefixEnd_7546291 3874874441698039835457745 := by
  unfold tailWord_7546291
  simp only [CollatzResearch.WordTrace]
  refine ⟨275235844304083985740990727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183490562869389323827327151 275235844304083985740990727)
  ·
    refine ⟨412853766456125978611486091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275235844304083985740990727 412853766456125978611486091)
    ·
      refine ⟨619280649684188967917229137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412853766456125978611486091 619280649684188967917229137)
      ·
        refine ⟨464460487263141725937921853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619280649684188967917229137 464460487263141725937921853)
        ·
          refine ⟨174172682723678147226720695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464460487263141725937921853 174172682723678147226720695)
          ·
            refine ⟨261259024085517220840081043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174172682723678147226720695 261259024085517220840081043)
            ·
              refine ⟨391888536128275831260121565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261259024085517220840081043 391888536128275831260121565)
              ·
                refine ⟨146958201048103436722545587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391888536128275831260121565 146958201048103436722545587)
                ·
                  refine ⟨220437301572155155083818381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146958201048103436722545587 220437301572155155083818381)
                  ·
                    refine ⟨82663988089558183156431893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220437301572155155083818381 82663988089558183156431893)
                    ·
                      refine ⟨3874874441698039835457745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82663988089558183156431893 3874874441698039835457745)
                      ·
                        rfl

theorem cell23_7546291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_7546291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546291 prefixEnd_7546291 := by exact prefixLift 7546291
  have htrace : WordTrace (prefixWord ++ tailWord_7546291) baseStart_7546291 baseEnd_7546291 := by
    simpa [prefixWord, tailWord_7546291, baseEnd_7546291] using wordTrace_append hprefix tailTrace_7546291
  have hstable : (prefixWord ++ tailWord_7546291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546291).length < 2 ^ (prefixWord ++ tailWord_7546291).sum := by decide
  have hdescent : baseEnd_7546291 < baseStart_7546291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546328 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_7546328 : Nat := 118140960795 + 7546328 * 2 ^ 59
def prefixEnd_7546328 : Nat := 4983230072969 + 3 ^ 40 * 7546328 * 2
def baseEnd_7546328 : Nat := 3874893440482256190695075

theorem tailTrace_7546328 : CollatzResearch.WordTrace tailWord_7546328 prefixEnd_7546328 3874893440482256190695075 := by
  unfold tailWord_7546328
  simp only [CollatzResearch.WordTrace]
  refine ⟨137618596902474970530043819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183491462536633294040058425 137618596902474970530043819)
  ·
    refine ⟨206427895353712455795065729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137618596902474970530043819 206427895353712455795065729)
    ·
      refine ⟨154820921515284341846299297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206427895353712455795065729 154820921515284341846299297)
      ·
        refine ⟨116115691136463256384724473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154820921515284341846299297 116115691136463256384724473)
        ·
          refine ⟨87086768352347442288543355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116115691136463256384724473 87086768352347442288543355)
          ·
            refine ⟨130630152528521163432815033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87086768352347442288543355 130630152528521163432815033)
            ·
              refine ⟨97972614396390872574611275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130630152528521163432815033 97972614396390872574611275)
              ·
                refine ⟨146958921594586308861916913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97972614396390872574611275 146958921594586308861916913)
                ·
                  refine ⟨110219191195939731646437685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146958921594586308861916913 110219191195939731646437685)
                  ·
                    refine ⟨10333049174619349841853533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110219191195939731646437685 10333049174619349841853533)
                    ·
                      refine ⟨3874893440482256190695075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333049174619349841853533 3874893440482256190695075)
                      ·
                        rfl

theorem cell23_7546328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_7546328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546328 prefixEnd_7546328 := by exact prefixLift 7546328
  have htrace : WordTrace (prefixWord ++ tailWord_7546328) baseStart_7546328 baseEnd_7546328 := by
    simpa [prefixWord, tailWord_7546328, baseEnd_7546328] using wordTrace_append hprefix tailTrace_7546328
  have hstable : (prefixWord ++ tailWord_7546328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546328).length < 2 ^ (prefixWord ++ tailWord_7546328).sum := by decide
  have hdescent : baseEnd_7546328 < baseStart_7546328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546331 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 11]
def baseStart_7546331 : Nat := 118140960795 + 7546331 * 2 ^ 59
def prefixEnd_7546331 : Nat := 4983230072969 + 3 ^ 40 * 7546331 * 2
def baseEnd_7546331 : Nat := 1291631660308073226319187

theorem tailTrace_7546331 : CollatzResearch.WordTrace tailWord_7546331 prefixEnd_7546331 1291631660308073226319187 := by
  unfold tailWord_7546331
  simp only [CollatzResearch.WordTrace]
  refine ⟨275237303223939072572446847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183491535482626048381631231 275237303223939072572446847)
  ·
    refine ⟨412855954835908608858670271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275237303223939072572446847 412855954835908608858670271)
    ·
      refine ⟨619283932253862913288005407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412855954835908608858670271 619283932253862913288005407)
      ·
        refine ⟨928925898380794369932008111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619283932253862913288005407 928925898380794369932008111)
        ·
          refine ⟨1393388847571191554898012167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928925898380794369932008111 1393388847571191554898012167)
          ·
            refine ⟨2090083271356787332347018251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393388847571191554898012167 2090083271356787332347018251)
            ·
              refine ⟨3135124907035180998520527377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2090083271356787332347018251 3135124907035180998520527377)
              ·
                refine ⟨2351343680276385748890395533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3135124907035180998520527377 2351343680276385748890395533)
                ·
                  refine ⟨881753880103644655833898325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2351343680276385748890395533 881753880103644655833898325)
                  ·
                    refine ⟨1291631660308073226319187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 881753880103644655833898325 1291631660308073226319187)
                    ·
                      rfl

theorem cell23_7546331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_7546331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546331 prefixEnd_7546331 := by exact prefixLift 7546331
  have htrace : WordTrace (prefixWord ++ tailWord_7546331) baseStart_7546331 baseEnd_7546331 := by
    simpa [prefixWord, tailWord_7546331, baseEnd_7546331] using wordTrace_append hprefix tailTrace_7546331
  have hstable : (prefixWord ++ tailWord_7546331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546331).length < 2 ^ (prefixWord ++ tailWord_7546331).sum := by decide
  have hdescent : baseEnd_7546331 < baseStart_7546331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 4, 3, 2]
def baseStart_7546355 : Nat := 118140960795 + 7546355 * 2 ^ 59
def prefixEnd_7546355 : Nat := 4983230072969 + 3 ^ 40 * 7546355 * 2
def baseEnd_7546355 : Nat := 3874907304459927585057451

theorem tailTrace_7546355 : CollatzResearch.WordTrace tailWord_7546355 prefixEnd_7546355 3874907304459927585057451 := by
  unfold tailWord_7546355
  simp only [CollatzResearch.WordTrace]
  refine ⟨275238178575852124671320519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183492119050568083114213679 275238178575852124671320519)
  ·
    refine ⟨412857267863778187006980779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275238178575852124671320519 412857267863778187006980779)
    ·
      refine ⟨619285901795667280510471169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412857267863778187006980779 619285901795667280510471169)
      ·
        refine ⟨464464426346750460382853377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619285901795667280510471169 464464426346750460382853377)
        ·
          refine ⟨348348319760062845287140033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464464426346750460382853377 348348319760062845287140033)
          ·
            refine ⟨261261239820047133965355025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348348319760062845287140033 261261239820047133965355025)
            ·
              refine ⟨195945929865035350474016269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261261239820047133965355025 195945929865035350474016269)
              ·
                refine ⟨73479723699388256427756101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195945929865035350474016269 73479723699388256427756101)
                ·
                  refine ⟨13777448193635298080204269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73479723699388256427756101 13777448193635298080204269)
                  ·
                    refine ⟨5166543072613236780076601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13777448193635298080204269 5166543072613236780076601)
                    ·
                      refine ⟨3874907304459927585057451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166543072613236780076601 3874907304459927585057451)
                      ·
                        rfl

theorem cell23_7546355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3, 2].length) (baseStart_7546355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546355 prefixEnd_7546355 := by exact prefixLift 7546355
  have htrace : WordTrace (prefixWord ++ tailWord_7546355) baseStart_7546355 baseEnd_7546355 := by
    simpa [prefixWord, tailWord_7546355, baseEnd_7546355] using wordTrace_append hprefix tailTrace_7546355
  have hstable : (prefixWord ++ tailWord_7546355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546355).length < 2 ^ (prefixWord ++ tailWord_7546355).sum := by decide
  have hdescent : baseEnd_7546355 < baseStart_7546355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546385 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_7546385 : Nat := 118140960795 + 7546385 * 2 ^ 59
def prefixEnd_7546385 : Nat := 4983230072969 + 3 ^ 40 * 7546385 * 2
def baseEnd_7546385 : Nat := 3874922708879562467682313

theorem tailTrace_7546385 : CollatzResearch.WordTrace tailWord_7546385 prefixEnd_7546385 3874922708879562467682313 := by
  unfold tailWord_7546385
  simp only [CollatzResearch.WordTrace]
  refine ⟨275239272765743439794912609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183492848510495626529941739 275239272765743439794912609)
  ·
    refine ⟨206429454574307579846184457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275239272765743439794912609 206429454574307579846184457)
    ·
      refine ⟨154822090930730684884638343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206429454574307579846184457 154822090930730684884638343)
      ·
        refine ⟨232233136396096027326957515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154822090930730684884638343 232233136396096027326957515)
        ·
          refine ⟨348349704594144040990436273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232233136396096027326957515 348349704594144040990436273)
          ·
            refine ⟨261262278445608030742827205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348349704594144040990436273 261262278445608030742827205)
            ·
              refine ⟨48986677208551505764280101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261262278445608030742827205 48986677208551505764280101)
              ·
                refine ⟨9185001976603407330802519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48986677208551505764280101 9185001976603407330802519)
                ·
                  refine ⟨13777502964905110996203779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9185001976603407330802519 13777502964905110996203779)
                  ·
                    refine ⟨20666254447357666494305669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13777502964905110996203779 20666254447357666494305669)
                    ·
                      refine ⟨3874922708879562467682313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20666254447357666494305669 3874922708879562467682313)
                      ·
                        rfl

theorem cell23_7546385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_7546385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546385 prefixEnd_7546385 := by exact prefixLift 7546385
  have htrace : WordTrace (prefixWord ++ tailWord_7546385) baseStart_7546385 baseEnd_7546385 := by
    simpa [prefixWord, tailWord_7546385, baseEnd_7546385] using wordTrace_append hprefix tailTrace_7546385
  have hstable : (prefixWord ++ tailWord_7546385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546385).length < 2 ^ (prefixWord ++ tailWord_7546385).sum := by decide
  have hdescent : baseEnd_7546385 < baseStart_7546385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546389 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_7546389 : Nat := 118140960795 + 7546389 * 2 ^ 59
def prefixEnd_7546389 : Nat := 4983230072969 + 3 ^ 40 * 7546389 * 2
def baseEnd_7546389 : Nat := 3874924762802180452032295

theorem tailTrace_7546389 : CollatzResearch.WordTrace tailWord_7546389 prefixEnd_7546389 3874924762802180452032295 := by
  unfold tailWord_7546389
  simp only [CollatzResearch.WordTrace]
  refine ⟨275239418657728948478058221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183492945771819298985372147 275239418657728948478058221)
  ·
    refine ⟨103214781996648355679271833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275239418657728948478058221 103214781996648355679271833)
    ·
      refine ⟨77411086497486266759453875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103214781996648355679271833 77411086497486266759453875)
      ·
        refine ⟨116116629746229400139180813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77411086497486266759453875 116116629746229400139180813)
        ·
          refine ⟨43543736154836025052192805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116116629746229400139180813 43543736154836025052192805)
          ·
            refine ⟨8164450529031754697286151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43543736154836025052192805 8164450529031754697286151)
            ·
              refine ⟨12246675793547632045929227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164450529031754697286151 12246675793547632045929227)
              ·
                refine ⟨18370013690321448068893841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246675793547632045929227 18370013690321448068893841)
                ·
                  refine ⟨13777510267741086051670381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18370013690321448068893841 13777510267741086051670381)
                  ·
                    refine ⟨5166566350402907269376393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13777510267741086051670381 5166566350402907269376393)
                    ·
                      refine ⟨3874924762802180452032295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166566350402907269376393 3874924762802180452032295)
                      ·
                        rfl

theorem cell23_7546389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_7546389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546389 prefixEnd_7546389 := by exact prefixLift 7546389
  have htrace : WordTrace (prefixWord ++ tailWord_7546389) baseStart_7546389 baseEnd_7546389 := by
    simpa [prefixWord, tailWord_7546389, baseEnd_7546389] using wordTrace_append hprefix tailTrace_7546389
  have hstable : (prefixWord ++ tailWord_7546389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546389).length < 2 ^ (prefixWord ++ tailWord_7546389).sum := by decide
  have hdescent : baseEnd_7546389 < baseStart_7546389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546418 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_7546418 : Nat := 118140960795 + 7546418 * 2 ^ 59
def prefixEnd_7546418 : Nat := 4983230072969 + 3 ^ 40 * 7546418 * 2
def baseEnd_7546418 : Nat := 3874939653741160838569661

theorem tailTrace_7546418 : CollatzResearch.WordTrace tailWord_7546418 prefixEnd_7546418 3874939653741160838569661 := by
  unfold tailWord_7546418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68810119093655971607715977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183493650916415924287242605 68810119093655971607715977)
  ·
    refine ⟨51607589320241978705786983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68810119093655971607715977 51607589320241978705786983)
    ·
      refine ⟨77411383980362968058680475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51607589320241978705786983 77411383980362968058680475)
      ·
        refine ⟨116117075970544452088020713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77411383980362968058680475 116117075970544452088020713)
        ·
          refine ⟨87087806977908339066015535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116117075970544452088020713 87087806977908339066015535)
          ·
            refine ⟨130631710466862508599023303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87087806977908339066015535 130631710466862508599023303)
            ·
              refine ⟨195947565700293762898534955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130631710466862508599023303 195947565700293762898534955)
              ·
                refine ⟨293921348550440644347802433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195947565700293762898534955 293921348550440644347802433)
                ·
                  refine ⟨220441011412830483260851825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293921348550440644347802433 220441011412830483260851825)
                  ·
                    refine ⟨165330758559622862445638869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220441011412830483260851825 165330758559622862445638869)
                    ·
                      refine ⟨3874939653741160838569661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165330758559622862445638869 3874939653741160838569661)
                      ·
                        rfl

theorem cell23_7546418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_7546418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546418 prefixEnd_7546418 := by exact prefixLift 7546418
  have htrace : WordTrace (prefixWord ++ tailWord_7546418) baseStart_7546418 baseEnd_7546418 := by
    simpa [prefixWord, tailWord_7546418, baseEnd_7546418] using wordTrace_append hprefix tailTrace_7546418
  have hstable : (prefixWord ++ tailWord_7546418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546418).length < 2 ^ (prefixWord ++ tailWord_7546418).sum := by decide
  have hdescent : baseEnd_7546418 < baseStart_7546418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546419 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 3, 2, 2]
def baseStart_7546419 : Nat := 118140960795 + 7546419 * 2 ^ 59
def prefixEnd_7546419 : Nat := 4983230072969 + 3 ^ 40 * 7546419 * 2
def baseEnd_7546419 : Nat := 3874940167221815334657157

theorem tailTrace_7546419 : CollatzResearch.WordTrace tailWord_7546419 prefixEnd_7546419 3874940167221815334657157 := by
  unfold tailWord_7546419
  simp only [CollatzResearch.WordTrace]
  refine ⟨275240512847620263601650311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183493675231746842401100207 275240512847620263601650311)
  ·
    refine ⟨412860769271430395402475467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275240512847620263601650311 412860769271430395402475467)
    ·
      refine ⟨619291153907145593103713201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412860769271430395402475467 619291153907145593103713201)
      ·
        refine ⟨464468365430359194827784901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619291153907145593103713201 464468365430359194827784901)
        ·
          refine ⟨87087818518192349030209669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464468365430359194827784901 87087818518192349030209669)
          ·
            refine ⟨16328965972161065443164313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87087818518192349030209669 16328965972161065443164313)
            ·
              refine ⟨12246724479120799082373235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16328965972161065443164313 12246724479120799082373235)
              ·
                refine ⟨18370086718681198623559853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246724479120799082373235 18370086718681198623559853)
                ·
                  refine ⟨6888782519505449483834945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18370086718681198623559853 6888782519505449483834945)
                  ·
                    refine ⟨5166586889629087112876209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6888782519505449483834945 5166586889629087112876209)
                    ·
                      refine ⟨3874940167221815334657157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166586889629087112876209 3874940167221815334657157)
                      ·
                        rfl

theorem cell23_7546419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2, 2].length) (baseStart_7546419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546419 prefixEnd_7546419 := by exact prefixLift 7546419
  have htrace : WordTrace (prefixWord ++ tailWord_7546419) baseStart_7546419 baseEnd_7546419 := by
    simpa [prefixWord, tailWord_7546419, baseEnd_7546419] using wordTrace_append hprefix tailTrace_7546419
  have hstable : (prefixWord ++ tailWord_7546419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546419).length < 2 ^ (prefixWord ++ tailWord_7546419).sum := by decide
  have hdescent : baseEnd_7546419 < baseStart_7546419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546429 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_7546429 : Nat := 118140960795 + 7546429 * 2 ^ 59
def prefixEnd_7546429 : Nat := 4983230072969 + 3 ^ 40 * 7546429 * 2
def baseEnd_7546429 : Nat := 1291648434009453431844037

theorem tailTrace_7546429 : CollatzResearch.WordTrace tailWord_7546429 prefixEnd_7546429 1291648434009453431844037 := by
  unfold tailWord_7546429
  simp only [CollatzResearch.WordTrace]
  refine ⟨275240877577584035309514341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183493918385056023539676227 275240877577584035309514341)
  ·
    refine ⟨51607664545797006620533939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275240877577584035309514341 51607664545797006620533939)
    ·
      refine ⟨77411496818695509930800909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51607664545797006620533939 77411496818695509930800909)
      ·
        refine ⟨29029311307010816224050341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77411496818695509930800909 29029311307010816224050341)
        ·
          refine ⟨5442995870064528042009439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29029311307010816224050341 5442995870064528042009439)
          ·
            refine ⟨8164493805096792063014159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442995870064528042009439 8164493805096792063014159)
            ·
              refine ⟨12246740707645188094521239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164493805096792063014159 12246740707645188094521239)
              ·
                refine ⟨18370111061467782141781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246740707645188094521239 18370111061467782141781859)
                ·
                  refine ⟨27555166592201673212672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18370111061467782141781859 27555166592201673212672789)
                  ·
                    refine ⟨1291648434009453431844037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27555166592201673212672789 1291648434009453431844037)
                    ·
                      rfl

theorem cell23_7546429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_7546429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546429 prefixEnd_7546429 := by exact prefixLift 7546429
  have htrace : WordTrace (prefixWord ++ tailWord_7546429) baseStart_7546429 baseEnd_7546429 := by
    simpa [prefixWord, tailWord_7546429, baseEnd_7546429] using wordTrace_append hprefix tailTrace_7546429
  have hstable : (prefixWord ++ tailWord_7546429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546429).length < 2 ^ (prefixWord ++ tailWord_7546429).sum := by decide
  have hdescent : baseEnd_7546429 < baseStart_7546429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546439 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_7546439 : Nat := 118140960795 + 7546439 * 2 ^ 59
def prefixEnd_7546439 : Nat := 4983230072969 + 3 ^ 40 * 7546439 * 2
def baseEnd_7546439 : Nat := 3874950436834905256407065

theorem tailTrace_7546439 : CollatzResearch.WordTrace tailWord_7546439 prefixEnd_7546439 3874950436834905256407065 := by
  unfold tailWord_7546439
  simp only [CollatzResearch.WordTrace]
  refine ⟨275241242307547807017378371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183494161538365204678252247 275241242307547807017378371)
  ·
    refine ⟨412861863461321710526067557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275241242307547807017378371 412861863461321710526067557)
    ·
      refine ⟨77411599398997820723637667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412861863461321710526067557 77411599398997820723637667)
      ·
        refine ⟨116117399098496731085456501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77411599398997820723637667 116117399098496731085456501)
        ·
          refine ⟨10886006165484068539261547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116117399098496731085456501 10886006165484068539261547)
          ·
            refine ⟨16329009248226102808892321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886006165484068539261547 16329009248226102808892321)
            ·
              refine ⟨12246756936169577106669241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16329009248226102808892321 12246756936169577106669241)
              ·
                refine ⟨9185067702127182830001931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12246756936169577106669241 9185067702127182830001931)
                ·
                  refine ⟨13777601553190774245002897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9185067702127182830001931 13777601553190774245002897)
                  ·
                    refine ⟨10333201164893080683752173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13777601553190774245002897 10333201164893080683752173)
                    ·
                      refine ⟨3874950436834905256407065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333201164893080683752173 3874950436834905256407065)
                      ·
                        rfl

theorem cell23_7546439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_7546439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546439 prefixEnd_7546439 := by exact prefixLift 7546439
  have htrace : WordTrace (prefixWord ++ tailWord_7546439) baseStart_7546439 baseEnd_7546439 := by
    simpa [prefixWord, tailWord_7546439, baseEnd_7546439] using wordTrace_append hprefix tailTrace_7546439
  have hstable : (prefixWord ++ tailWord_7546439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546439).length < 2 ^ (prefixWord ++ tailWord_7546439).sum := by decide
  have hdescent : baseEnd_7546439 < baseStart_7546439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546448 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_7546448 : Nat := 118140960795 + 7546448 * 2 ^ 59
def prefixEnd_7546448 : Nat := 4983230072969 + 3 ^ 40 * 7546448 * 2
def baseEnd_7546448 : Nat := 3874955058160795721194523

theorem tailTrace_7546448 : CollatzResearch.WordTrace tailWord_7546448 prefixEnd_7546448 3874955058160795721194523 := by
  unfold tailWord_7546448
  simp only [CollatzResearch.WordTrace]
  refine ⟨137620785282257600777227999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183494380376343467702970665 137620785282257600777227999)
  ·
    refine ⟨206431177923386401165841999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137620785282257600777227999 206431177923386401165841999)
    ·
      refine ⟨309646766885079601748762999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206431177923386401165841999 309646766885079601748762999)
      ·
        refine ⟨464470150327619402623144499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309646766885079601748762999 464470150327619402623144499)
        ·
          refine ⟨696705225491429103934716749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464470150327619402623144499 696705225491429103934716749)
          ·
            refine ⟨261264459559285913975518781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696705225491429103934716749 261264459559285913975518781)
            ·
              refine ⟨97974172334732217740819543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261264459559285913975518781 97974172334732217740819543)
              ·
                refine ⟨146961258502098326611229315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97974172334732217740819543 146961258502098326611229315)
                ·
                  refine ⟨220441887753147489916843973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146961258502098326611229315 220441887753147489916843973)
                  ·
                    refine ⟨41332853953715154359408245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220441887753147489916843973 41332853953715154359408245)
                    ·
                      refine ⟨3874955058160795721194523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41332853953715154359408245 3874955058160795721194523)
                      ·
                        rfl

theorem cell23_7546448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_7546448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546448 prefixEnd_7546448 := by exact prefixLift 7546448
  have htrace : WordTrace (prefixWord ++ tailWord_7546448) baseStart_7546448 baseEnd_7546448 := by
    simpa [prefixWord, tailWord_7546448, baseEnd_7546448] using wordTrace_append hprefix tailTrace_7546448
  have hstable : (prefixWord ++ tailWord_7546448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546448).length < 2 ^ (prefixWord ++ tailWord_7546448).sum := by decide
  have hdescent : baseEnd_7546448 < baseStart_7546448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546452 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_7546452 : Nat := 118140960795 + 7546452 * 2 ^ 59
def prefixEnd_7546452 : Nat := 4983230072969 + 3 ^ 40 * 7546452 * 2
def baseEnd_7546452 : Nat := 3874957112083413705544505

theorem tailTrace_7546452 : CollatzResearch.WordTrace tailWord_7546452 prefixEnd_7546452 3874957112083413705544505 := by
  unfold tailWord_7546452
  simp only [CollatzResearch.WordTrace]
  refine ⟨137620858228250355118800805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183494477637667140158401073 137620858228250355118800805)
  ·
    refine ⟨25803910917796941584775151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137620858228250355118800805 25803910917796941584775151)
    ·
      refine ⟨38705866376695412377162727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25803910917796941584775151 38705866376695412377162727)
      ·
        refine ⟨58058799565043118565744091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38705866376695412377162727 58058799565043118565744091)
        ·
          refine ⟨87088199347564677848616137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58058799565043118565744091 87088199347564677848616137)
          ·
            refine ⟨65316149510673508386462103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87088199347564677848616137 65316149510673508386462103)
            ·
              refine ⟨97974224266010262579693155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65316149510673508386462103 97974224266010262579693155)
              ·
                refine ⟨146961336399015393869539733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97974224266010262579693155 146961336399015393869539733)
                ·
                  refine ⟨6888812643703846587634675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146961336399015393869539733 6888812643703846587634675)
                  ·
                    refine ⟨10333218965555769881452013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888812643703846587634675 10333218965555769881452013)
                    ·
                      refine ⟨3874957112083413705544505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333218965555769881452013 3874957112083413705544505)
                      ·
                        rfl

theorem cell23_7546452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_7546452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546452 prefixEnd_7546452 := by exact prefixLift 7546452
  have htrace : WordTrace (prefixWord ++ tailWord_7546452) baseStart_7546452 baseEnd_7546452 := by
    simpa [prefixWord, tailWord_7546452, baseEnd_7546452] using wordTrace_append hprefix tailTrace_7546452
  have hstable : (prefixWord ++ tailWord_7546452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546452).length < 2 ^ (prefixWord ++ tailWord_7546452).sum := by decide
  have hdescent : baseEnd_7546452 < baseStart_7546452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546458 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7546458 : Nat := 118140960795 + 7546458 * 2 ^ 59
def prefixEnd_7546458 : Nat := 4983230072969 + 3 ^ 40 * 7546458 * 2
def baseEnd_7546458 : Nat := 3874960192967340682069477

theorem tailTrace_7546458 : CollatzResearch.WordTrace tailWord_7546458 prefixEnd_7546458 3874960192967340682069477 := by
  unfold tailWord_7546458
  simp only [CollatzResearch.WordTrace]
  refine ⟨68810483823619743315580007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183494623529652648841546685 68810483823619743315580007)
  ·
    refine ⟨103215725735429614973370011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68810483823619743315580007 103215725735429614973370011)
    ·
      refine ⟨154823588603144422460055017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103215725735429614973370011 154823588603144422460055017)
      ·
        refine ⟨116117691452358316845041263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154823588603144422460055017 116117691452358316845041263)
        ·
          refine ⟨174176537178537475267561895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116117691452358316845041263 174176537178537475267561895)
          ·
            refine ⟨261264805767806212901342843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174176537178537475267561895 261264805767806212901342843)
            ·
              refine ⟨391897208651709319352014265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261264805767806212901342843 391897208651709319352014265)
              ·
                refine ⟨293922906488781989514010699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391897208651709319352014265 293922906488781989514010699)
                ·
                  refine ⟨440884359733172984271016049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293922906488781989514010699 440884359733172984271016049)
                  ·
                    refine ⟨330663269799879738203262037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 440884359733172984271016049 330663269799879738203262037)
                    ·
                      refine ⟨3874960192967340682069477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 330663269799879738203262037 3874960192967340682069477)
                      ·
                        rfl

theorem cell23_7546458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7546458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546458 prefixEnd_7546458 := by exact prefixLift 7546458
  have htrace : WordTrace (prefixWord ++ tailWord_7546458) baseStart_7546458 baseEnd_7546458 := by
    simpa [prefixWord, tailWord_7546458, baseEnd_7546458] using wordTrace_append hprefix tailTrace_7546458
  have hstable : (prefixWord ++ tailWord_7546458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546458).length < 2 ^ (prefixWord ++ tailWord_7546458).sum := by decide
  have hdescent : baseEnd_7546458 < baseStart_7546458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546486 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7546486 : Nat := 118140960795 + 7546486 * 2 ^ 59
def prefixEnd_7546486 : Nat := 4983230072969 + 3 ^ 40 * 7546486 * 2
def baseEnd_7546486 : Nat := 3874974570425666572519349

theorem tailTrace_7546486 : CollatzResearch.WordTrace tailWord_7546486 prefixEnd_7546486 3874974570425666572519349 := by
  unfold tailWord_7546486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202684783648595877771207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183495304358918356029559541 17202684783648595877771207)
  ·
    refine ⟨25804027175472893816656811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17202684783648595877771207 25804027175472893816656811)
    ·
      refine ⟨38706040763209340724985217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25804027175472893816656811 38706040763209340724985217)
      ·
        refine ⟨29029530572407005543738913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38706040763209340724985217 29029530572407005543738913)
        ·
          refine ⟨21772147929305254157804185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29029530572407005543738913 21772147929305254157804185)
          ·
            refine ⟨16329110946978940618353139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21772147929305254157804185 16329110946978940618353139)
            ·
              refine ⟨24493666420468410927529709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16329110946978940618353139 24493666420468410927529709)
              ·
                refine ⟨9185124907675654097823641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24493666420468410927529709 9185124907675654097823641)
                ·
                  refine ⟨6888843680756740573367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185124907675654097823641 6888843680756740573367731)
                  ·
                    refine ⟨10333265521135110860051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6888843680756740573367731 10333265521135110860051597)
                    ·
                      refine ⟨3874974570425666572519349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333265521135110860051597 3874974570425666572519349)
                      ·
                        rfl

theorem cell23_7546486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7546486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546486 prefixEnd_7546486 := by exact prefixLift 7546486
  have htrace : WordTrace (prefixWord ++ tailWord_7546486) baseStart_7546486 baseEnd_7546486 := by
    simpa [prefixWord, tailWord_7546486, baseEnd_7546486] using wordTrace_append hprefix tailTrace_7546486
  have hstable : (prefixWord ++ tailWord_7546486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546486).length < 2 ^ (prefixWord ++ tailWord_7546486).sum := by decide
  have hdescent : baseEnd_7546486 < baseStart_7546486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546492 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_7546492 : Nat := 118140960795 + 7546492 * 2 ^ 59
def prefixEnd_7546492 : Nat := 4983230072969 + 3 ^ 40 * 7546492 * 2
def baseEnd_7546492 : Nat := 3874977651309593549044321

theorem tailTrace_7546492 : CollatzResearch.WordTrace tailWord_7546492 prefixEnd_7546492 3874977651309593549044321 := by
  unfold tailWord_7546492
  simp only [CollatzResearch.WordTrace]
  refine ⟨137621587688177898534528865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183495450250903864712705153 137621587688177898534528865)
  ·
    refine ⟨103216190766133423900896649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137621587688177898534528865 103216190766133423900896649)
    ·
      refine ⟨77412143074600067925672487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103216190766133423900896649 77412143074600067925672487)
      ·
        refine ⟨116118214611900101888508731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77412143074600067925672487 116118214611900101888508731)
        ·
          refine ⟨174177321917850152832763097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116118214611900101888508731 174177321917850152832763097)
          ·
            refine ⟨130632991438387614624572323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174177321917850152832763097 130632991438387614624572323)
            ·
              refine ⟨195949487157581421936858485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130632991438387614624572323 195949487157581421936858485)
              ·
                refine ⟨18370264421023258306580483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195949487157581421936858485 18370264421023258306580483)
                ·
                  refine ⟨27555396631534887459870725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18370264421023258306580483 27555396631534887459870725)
                  ·
                    refine ⟨5166636868412791398725761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27555396631534887459870725 5166636868412791398725761)
                    ·
                      refine ⟨3874977651309593549044321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166636868412791398725761 3874977651309593549044321)
                      ·
                        rfl

theorem cell23_7546492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_7546492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546492 prefixEnd_7546492 := by exact prefixLift 7546492
  have htrace : WordTrace (prefixWord ++ tailWord_7546492) baseStart_7546492 baseEnd_7546492 := by
    simpa [prefixWord, tailWord_7546492, baseEnd_7546492] using wordTrace_append hprefix tailTrace_7546492
  have hstable : (prefixWord ++ tailWord_7546492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546492).length < 2 ^ (prefixWord ++ tailWord_7546492).sum := by decide
  have hdescent : baseEnd_7546492 < baseStart_7546492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546536 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7546536 : Nat := 118140960795 + 7546536 * 2 ^ 59
def prefixEnd_7546536 : Nat := 4983230072969 + 3 ^ 40 * 7546536 * 2
def baseEnd_7546536 : Nat := 1291666748152797125631373

theorem tailTrace_7546536 : CollatzResearch.WordTrace tailWord_7546536 prefixEnd_7546536 1291666748152797125631373 := by
  unfold tailWord_7546536
  simp only [CollatzResearch.WordTrace]
  refine ⟨137622390094098196291829731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183496520125464261722439641 137622390094098196291829731)
  ·
    refine ⟨206433585141147294437744597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137622390094098196291829731 206433585141147294437744597)
    ·
      refine ⟨4838287151745639713384639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 206433585141147294437744597 4838287151745639713384639)
      ·
        refine ⟨7257430727618459570076959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4838287151745639713384639 7257430727618459570076959)
        ·
          refine ⟨10886146091427689355115439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257430727618459570076959 10886146091427689355115439)
          ·
            refine ⟨16329219137141534032673159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886146091427689355115439 16329219137141534032673159)
            ·
              refine ⟨24493828705712301049009739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16329219137141534032673159 24493828705712301049009739)
              ·
                refine ⟨36740743058568451573514609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24493828705712301049009739 36740743058568451573514609)
                ·
                  refine ⟨27555557293926338680135957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36740743058568451573514609 27555557293926338680135957)
                  ·
                    refine ⟨1291666748152797125631373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27555557293926338680135957 1291666748152797125631373)
                    ·
                      rfl

theorem cell23_7546536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7546536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546536 prefixEnd_7546536 := by exact prefixLift 7546536
  have htrace : WordTrace (prefixWord ++ tailWord_7546536) baseStart_7546536 baseEnd_7546536 := by
    simpa [prefixWord, tailWord_7546536, baseEnd_7546536] using wordTrace_append hprefix tailTrace_7546536
  have hstable : (prefixWord ++ tailWord_7546536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546536).length < 2 ^ (prefixWord ++ tailWord_7546536).sum := by decide
  have hdescent : baseEnd_7546536 < baseStart_7546536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546565 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_7546565 : Nat := 118140960795 + 7546565 * 2 ^ 59
def prefixEnd_7546565 : Nat := 4983230072969 + 3 ^ 40 * 7546565 * 2
def baseEnd_7546565 : Nat := 3875015135397371763431485

theorem tailTrace_7546565 : CollatzResearch.WordTrace tailWord_7546565 prefixEnd_7546565 3875015135397371763431485 := by
  unfold tailWord_7546565
  simp only [CollatzResearch.WordTrace]
  refine ⟨275245837905091330536465149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183497225270060887024310099 275245837905091330536465149)
  ·
    refine ⟨103217189214409248951174431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275245837905091330536465149 103217189214409248951174431)
    ·
      refine ⟨154825783821613873426761647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103217189214409248951174431 154825783821613873426761647)
      ·
        refine ⟨232238675732420810140142471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154825783821613873426761647 232238675732420810140142471)
        ·
          refine ⟨348358013598631215210213707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232238675732420810140142471 348358013598631215210213707)
          ·
            refine ⟨522537020397946822815320561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348358013598631215210213707 522537020397946822815320561)
            ·
              refine ⟨391902765298460117111490421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522537020397946822815320561 391902765298460117111490421)
              ·
                refine ⟨36740884246730635979202227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391902765298460117111490421 36740884246730635979202227)
                ·
                  refine ⟨55111326370095953968803341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36740884246730635979202227 55111326370095953968803341)
                  ·
                    refine ⟨20666747388785982738301253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55111326370095953968803341 20666747388785982738301253)
                    ·
                      refine ⟨3875015135397371763431485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20666747388785982738301253 3875015135397371763431485)
                      ·
                        rfl

theorem cell23_7546565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_7546565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546565 prefixEnd_7546565 := by exact prefixLift 7546565
  have htrace : WordTrace (prefixWord ++ tailWord_7546565) baseStart_7546565 baseEnd_7546565 := by
    simpa [prefixWord, tailWord_7546565, baseEnd_7546565] using wordTrace_append hprefix tailTrace_7546565
  have hstable : (prefixWord ++ tailWord_7546565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546565).length < 2 ^ (prefixWord ++ tailWord_7546565).sum := by decide
  have hdescent : baseEnd_7546565 < baseStart_7546565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546592 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_7546592 : Nat := 118140960795 + 7546592 * 2 ^ 59
def prefixEnd_7546592 : Nat := 4983230072969 + 3 ^ 40 * 7546592 * 2
def baseEnd_7546592 : Nat := 1291676333125014385931287

theorem tailTrace_7546592 : CollatzResearch.WordTrace tailWord_7546592 prefixEnd_7546592 1291676333125014385931287 := by
  unfold tailWord_7546592
  simp only [CollatzResearch.WordTrace]
  refine ⟨137623411337996757073849015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183497881783995676098465353 137623411337996757073849015)
  ·
    refine ⟨206435117006995135610773523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137623411337996757073849015 206435117006995135610773523)
    ·
      refine ⟨309652675510492703416160285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206435117006995135610773523 309652675510492703416160285)
      ·
        refine ⟨116119753316434763781060107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309652675510492703416160285 116119753316434763781060107)
        ·
          refine ⟨174179629974652145671590161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116119753316434763781060107 174179629974652145671590161)
          ·
            refine ⟨130634722480989109253692621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174179629974652145671590161 130634722480989109253692621)
            ·
              refine ⟨48988020930370915970134733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130634722480989109253692621 48988020930370915970134733)
              ·
                refine ⟨18370507848889093488800525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48988020930370915970134733 18370507848889093488800525)
                ·
                  refine ⟨6888940443333410058300197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18370507848889093488800525 6888940443333410058300197)
                  ·
                    refine ⟨1291676333125014385931287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6888940443333410058300197 1291676333125014385931287)
                    ·
                      rfl

theorem cell23_7546592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_7546592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546592 prefixEnd_7546592 := by exact prefixLift 7546592
  have htrace : WordTrace (prefixWord ++ tailWord_7546592) baseStart_7546592 baseEnd_7546592 := by
    simpa [prefixWord, tailWord_7546592, baseEnd_7546592] using wordTrace_append hprefix tailTrace_7546592
  have hstable : (prefixWord ++ tailWord_7546592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546592).length < 2 ^ (prefixWord ++ tailWord_7546592).sum := by decide
  have hdescent : baseEnd_7546592 < baseStart_7546592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546602 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_7546602 : Nat := 118140960795 + 7546602 * 2 ^ 59
def prefixEnd_7546602 : Nat := 4983230072969 + 3 ^ 40 * 7546602 * 2
def baseEnd_7546602 : Nat := 3875034134181588118668815

theorem tailTrace_7546602 : CollatzResearch.WordTrace tailWord_7546602 prefixEnd_7546602 3875034134181588118668815 := by
  unfold tailWord_7546602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68811796851489321463890515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183498124937304857237041373 68811796851489321463890515)
  ·
    refine ⟨103217695277233982195835773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68811796851489321463890515 103217695277233982195835773)
    ·
      refine ⟨38706635728962743323438415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103217695277233982195835773 38706635728962743323438415)
      ·
        refine ⟨58059953593444114985157623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38706635728962743323438415 58059953593444114985157623)
        ·
          refine ⟨87089930390166172477736435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58059953593444114985157623 87089930390166172477736435)
          ·
            refine ⟨130634895585249258716604653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87089930390166172477736435 130634895585249258716604653)
            ·
              refine ⟨48988085844468472018726745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130634895585249258716604653 48988085844468472018726745)
              ·
                refine ⟨36741064383351354014045059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48988085844468472018726745 36741064383351354014045059)
                ·
                  refine ⟨55111596575027031021067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36741064383351354014045059 55111596575027031021067589)
                  ·
                    refine ⟨10333424357817568316450173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55111596575027031021067589 10333424357817568316450173)
                    ·
                      refine ⟨3875034134181588118668815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333424357817568316450173 3875034134181588118668815)
                      ·
                        rfl

theorem cell23_7546602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_7546602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546602 prefixEnd_7546602 := by exact prefixLift 7546602
  have htrace : WordTrace (prefixWord ++ tailWord_7546602) baseStart_7546602 baseEnd_7546602 := by
    simpa [prefixWord, tailWord_7546602, baseEnd_7546602] using wordTrace_append hprefix tailTrace_7546602
  have hstable : (prefixWord ++ tailWord_7546602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546602).length < 2 ^ (prefixWord ++ tailWord_7546602).sum := by decide
  have hdescent : baseEnd_7546602 < baseStart_7546602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546652 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7546652 : Nat := 118140960795 + 7546652 * 2 ^ 59
def prefixEnd_7546652 : Nat := 4983230072969 + 3 ^ 40 * 7546652 * 2
def baseEnd_7546652 : Nat := 1291686602738104307681195

theorem tailTrace_7546652 : CollatzResearch.WordTrace tailWord_7546652 prefixEnd_7546652 1291686602738104307681195 := by
  unfold tailWord_7546652
  simp only [CollatzResearch.WordTrace]
  refine ⟨137624505527888072197441105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183499340703850762929921473 137624505527888072197441105)
  ·
    refine ⟨103218379145916054148080829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137624505527888072197441105 103218379145916054148080829)
    ·
      refine ⟨38706892179718520305530311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103218379145916054148080829 38706892179718520305530311)
      ·
        refine ⟨58060338269577780458295467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38706892179718520305530311 58060338269577780458295467)
        ·
          refine ⟨87090507404366670687443201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58060338269577780458295467 87090507404366670687443201)
          ·
            refine ⟨65317880553275003015582401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87090507404366670687443201 65317880553275003015582401)
            ·
              refine ⟨48988410414956252261686801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65317880553275003015582401 48988410414956252261686801)
              ·
                refine ⟨36741307811217189196265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48988410414956252261686801 36741307811217189196265101)
                ·
                  refine ⟨13777990429206445948599413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36741307811217189196265101 13777990429206445948599413)
                  ·
                    refine ⟨1291686602738104307681195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13777990429206445948599413 1291686602738104307681195)
                    ·
                      rfl

theorem cell23_7546652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7546652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546652 prefixEnd_7546652 := by exact prefixLift 7546652
  have htrace : WordTrace (prefixWord ++ tailWord_7546652) baseStart_7546652 baseEnd_7546652 := by
    simpa [prefixWord, tailWord_7546652, baseEnd_7546652] using wordTrace_append hprefix tailTrace_7546652
  have hstable : (prefixWord ++ tailWord_7546652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546652).length < 2 ^ (prefixWord ++ tailWord_7546652).sum := by decide
  have hdescent : baseEnd_7546652 < baseStart_7546652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546682 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_7546682 : Nat := 118140960795 + 7546682 * 2 ^ 59
def prefixEnd_7546682 : Nat := 4983230072969 + 3 ^ 40 * 7546682 * 2
def baseEnd_7546682 : Nat := 1291691737544649268556149

theorem tailTrace_7546682 : CollatzResearch.WordTrace tailWord_7546682 prefixEnd_7546682 1291691737544649268556149 := by
  unfold tailWord_7546682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68812526311416864879618575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183500070163778306345649533 68812526311416864879618575)
  ·
    refine ⟨103218789467125297319427863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68812526311416864879618575 103218789467125297319427863)
    ·
      refine ⟨154828184200687945979141795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103218789467125297319427863 154828184200687945979141795)
      ·
        refine ⟨232242276301031918968712693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154828184200687945979141795 232242276301031918968712693)
        ·
          refine ⟨21772713403221742403316815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232242276301031918968712693 21772713403221742403316815)
          ·
            refine ⟨32659070104832613604975223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21772713403221742403316815 32659070104832613604975223)
            ·
              refine ⟨48988605157248920407462835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32659070104832613604975223 48988605157248920407462835)
              ·
                refine ⟨73482907735873380611194253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48988605157248920407462835 73482907735873380611194253)
                ·
                  refine ⟨27556090400952517729197845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73482907735873380611194253 27556090400952517729197845)
                  ·
                    refine ⟨1291691737544649268556149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27556090400952517729197845 1291691737544649268556149)
                    ·
                      rfl

theorem cell23_7546682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_7546682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546682 prefixEnd_7546682 := by exact prefixLift 7546682
  have htrace : WordTrace (prefixWord ++ tailWord_7546682) baseStart_7546682 baseEnd_7546682 := by
    simpa [prefixWord, tailWord_7546682, baseEnd_7546682] using wordTrace_append hprefix tailTrace_7546682
  have hstable : (prefixWord ++ tailWord_7546682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546682).length < 2 ^ (prefixWord ++ tailWord_7546682).sum := by decide
  have hdescent : baseEnd_7546682 < baseStart_7546682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546709 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7546709 : Nat := 118140960795 + 7546709 * 2 ^ 59
def prefixEnd_7546709 : Nat := 4983230072969 + 3 ^ 40 * 7546709 * 2
def baseEnd_7546709 : Nat := 3875089076611619200030823

theorem tailTrace_7546709 : CollatzResearch.WordTrace tailWord_7546709 prefixEnd_7546709 3875089076611619200030823 := by
  unfold tailWord_7546709
  simp only [CollatzResearch.WordTrace]
  refine ⟨275251090016569643129707181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183500726677713095419804787 275251090016569643129707181)
  ·
    refine ⟨103219158756213616173640193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275251090016569643129707181 103219158756213616173640193)
    ·
      refine ⟨77414369067160212130230145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103219158756213616173640193 77414369067160212130230145)
      ·
        refine ⟨58060776800370159097672609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77414369067160212130230145 58060776800370159097672609)
        ·
          refine ⟨43545582600277619323254457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58060776800370159097672609 43545582600277619323254457)
          ·
            refine ⟨32659186950208214492440843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43545582600277619323254457 32659186950208214492440843)
            ·
              refine ⟨48988780425312321738661265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32659186950208214492440843 48988780425312321738661265)
              ·
                refine ⟨36741585318984241303995949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48988780425312321738661265 36741585318984241303995949)
                ·
                  refine ⟨13778094494619090488998481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36741585318984241303995949 13778094494619090488998481)
                  ·
                    refine ⟨10333570870964317866748861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13778094494619090488998481 10333570870964317866748861)
                    ·
                      refine ⟨3875089076611619200030823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333570870964317866748861 3875089076611619200030823)
                      ·
                        rfl

theorem cell23_7546709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7546709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546709 prefixEnd_7546709 := by exact prefixLift 7546709
  have htrace : WordTrace (prefixWord ++ tailWord_7546709) baseStart_7546709 baseEnd_7546709 := by
    simpa [prefixWord, tailWord_7546709, baseEnd_7546709] using wordTrace_append hprefix tailTrace_7546709
  have hstable : (prefixWord ++ tailWord_7546709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546709).length < 2 ^ (prefixWord ++ tailWord_7546709).sum := by decide
  have hdescent : baseEnd_7546709 < baseStart_7546709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546716 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7546716 : Nat := 118140960795 + 7546716 * 2 ^ 59
def prefixEnd_7546716 : Nat := 4983230072969 + 3 ^ 40 * 7546716 * 2
def baseEnd_7546716 : Nat := 1291697556992066890881097

theorem tailTrace_7546716 : CollatzResearch.WordTrace tailWord_7546716 prefixEnd_7546716 1291697556992066890881097 := by
  unfold tailWord_7546716
  simp only [CollatzResearch.WordTrace]
  refine ⟨137625672663772141662606001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183500896885029522216808001 137625672663772141662606001)
  ·
    refine ⟨103219254497829106246954501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137625672663772141662606001 103219254497829106246954501)
    ·
      refine ⟨19353610218342957421303969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103219254497829106246954501 19353610218342957421303969)
      ·
        refine ⟨14515207663757218065977977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19353610218342957421303969 14515207663757218065977977)
        ·
          refine ⟨10886405747817913549483483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14515207663757218065977977 10886405747817913549483483)
          ·
            refine ⟨16329608621726870324225225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886405747817913549483483 16329608621726870324225225)
            ·
              refine ⟨12247206466295152743168919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16329608621726870324225225 12247206466295152743168919)
              ·
                refine ⟨18370809699442729114753379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12247206466295152743168919 18370809699442729114753379)
                ·
                  refine ⟨27556214549164093672130069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18370809699442729114753379 27556214549164093672130069)
                  ·
                    refine ⟨1291697556992066890881097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27556214549164093672130069 1291697556992066890881097)
                    ·
                      rfl

theorem cell23_7546716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7546716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546716 prefixEnd_7546716 := by exact prefixLift 7546716
  have htrace : WordTrace (prefixWord ++ tailWord_7546716) baseStart_7546716 baseEnd_7546716 := by
    simpa [prefixWord, tailWord_7546716, baseEnd_7546716] using wordTrace_append hprefix tailTrace_7546716
  have hstable : (prefixWord ++ tailWord_7546716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546716).length < 2 ^ (prefixWord ++ tailWord_7546716).sum := by decide
  have hdescent : baseEnd_7546716 < baseStart_7546716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546719 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_7546719 : Nat := 118140960795 + 7546719 * 2 ^ 59
def prefixEnd_7546719 : Nat := 4983230072969 + 3 ^ 40 * 7546719 * 2
def baseEnd_7546719 : Nat := 3875094211418164160905777

theorem tailTrace_7546719 : CollatzResearch.WordTrace tailWord_7546719 prefixEnd_7546719 3875094211418164160905777 := by
  unfold tailWord_7546719
  simp only [CollatzResearch.WordTrace]
  refine ⟨275251454746533414837571211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183500969831022276558380807 275251454746533414837571211)
  ·
    refine ⟨412877182119800122256356817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275251454746533414837571211 412877182119800122256356817)
    ·
      refine ⟨309657886589850091692267613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412877182119800122256356817 309657886589850091692267613)
      ·
        refine ⟨116121707471193784384600355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309657886589850091692267613 116121707471193784384600355)
        ·
          refine ⟨174182561206790676576900533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116121707471193784384600355 174182561206790676576900533)
          ·
            refine ⟨16329615113136625929084425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174182561206790676576900533 16329615113136625929084425)
            ·
              refine ⟨12247211334852469446813319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16329615113136625929084425 12247211334852469446813319)
              ·
                refine ⟨18370817002278704170219979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12247211334852469446813319 18370817002278704170219979)
                ·
                  refine ⟨27556225503418056255329969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18370817002278704170219979 27556225503418056255329969)
                  ·
                    refine ⟨20667169127563542191497477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27556225503418056255329969 20667169127563542191497477)
                    ·
                      refine ⟨3875094211418164160905777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20667169127563542191497477 3875094211418164160905777)
                      ·
                        rfl

theorem cell23_7546719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_7546719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546719 prefixEnd_7546719 := by exact prefixLift 7546719
  have htrace : WordTrace (prefixWord ++ tailWord_7546719) baseStart_7546719 baseEnd_7546719 := by
    simpa [prefixWord, tailWord_7546719, baseEnd_7546719] using wordTrace_append hprefix tailTrace_7546719
  have hstable : (prefixWord ++ tailWord_7546719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546719).length < 2 ^ (prefixWord ++ tailWord_7546719).sum := by decide
  have hdescent : baseEnd_7546719 < baseStart_7546719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546723 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 3, 2, 2]
def baseStart_7546723 : Nat := 118140960795 + 7546723 * 2 ^ 59
def prefixEnd_7546723 : Nat := 4983230072969 + 3 ^ 40 * 7546723 * 2
def baseEnd_7546723 : Nat := 3875096265340782145255759

theorem tailTrace_7546723 : CollatzResearch.WordTrace tailWord_7546723 prefixEnd_7546723 3875096265340782145255759 := by
  unfold tailWord_7546723
  simp only [CollatzResearch.WordTrace]
  refine ⟨275251600638518923520716823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183501067092345949013811215 275251600638518923520716823)
  ·
    refine ⟨412877400957778385281075235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275251600638518923520716823 412877400957778385281075235)
    ·
      refine ⟨619316101436667577921612853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412877400957778385281075235 619316101436667577921612853)
      ·
        refine ⟨58060884509687585430151205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 619316101436667577921612853 58060884509687585430151205)
        ·
          refine ⟨10886415845566422268153351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58060884509687585430151205 10886415845566422268153351)
          ·
            refine ⟨16329623768349633402230027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886415845566422268153351 16329623768349633402230027)
            ·
              refine ⟨24494435652524450103345041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16329623768349633402230027 24494435652524450103345041)
              ·
                refine ⟨18370826739393337577508781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24494435652524450103345041 18370826739393337577508781)
                ·
                  refine ⟨6889060027272501591565793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18370826739393337577508781 6889060027272501591565793)
                  ·
                    refine ⟨5166795020454376193674345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6889060027272501591565793 5166795020454376193674345)
                    ·
                      refine ⟨3875096265340782145255759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166795020454376193674345 3875096265340782145255759)
                      ·
                        rfl

theorem cell23_7546723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_7546723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546723 prefixEnd_7546723 := by exact prefixLift 7546723
  have htrace : WordTrace (prefixWord ++ tailWord_7546723) baseStart_7546723 baseEnd_7546723 := by
    simpa [prefixWord, tailWord_7546723, baseEnd_7546723] using wordTrace_append hprefix tailTrace_7546723
  have hstable : (prefixWord ++ tailWord_7546723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546723).length < 2 ^ (prefixWord ++ tailWord_7546723).sum := by decide
  have hdescent : baseEnd_7546723 < baseStart_7546723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546739 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 3]
def baseStart_7546739 : Nat := 118140960795 + 7546739 * 2 ^ 59
def prefixEnd_7546739 : Nat := 4983230072969 + 3 ^ 40 * 7546739 * 2
def baseEnd_7546739 : Nat := 3875104481031254082655685

theorem tailTrace_7546739 : CollatzResearch.WordTrace tailWord_7546739 prefixEnd_7546739 3875104481031254082655685 := by
  unfold tailWord_7546739
  simp only [CollatzResearch.WordTrace]
  refine ⟨275252184206460958253299271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183501456137640638835532847 275252184206460958253299271)
  ·
    refine ⟨412878276309691437379948907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275252184206460958253299271 412878276309691437379948907)
    ·
      refine ⟨619317414464537156069923361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412878276309691437379948907 619317414464537156069923361)
      ·
        refine ⟨464488060848402867052442521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619317414464537156069923361 464488060848402867052442521)
        ·
          refine ⟨348366045636302150289331891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464488060848402867052442521 348366045636302150289331891)
          ·
            refine ⟨522549068454453225433997837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348366045636302150289331891 522549068454453225433997837)
            ·
              refine ⟨195955900670419959537749189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522549068454453225433997837 195955900670419959537749189)
              ·
                refine ⟨36741731375703742413327973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195955900670419959537749189 36741731375703742413327973)
                ·
                  refine ⟨6889074632944451702498995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36741731375703742413327973 6889074632944451702498995)
                  ·
                    refine ⟨10333611949416677553748493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6889074632944451702498995 10333611949416677553748493)
                    ·
                      refine ⟨3875104481031254082655685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333611949416677553748493 3875104481031254082655685)
                      ·
                        rfl

theorem cell23_7546739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_7546739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546739 prefixEnd_7546739 := by exact prefixLift 7546739
  have htrace : WordTrace (prefixWord ++ tailWord_7546739) baseStart_7546739 baseEnd_7546739 := by
    simpa [prefixWord, tailWord_7546739, baseEnd_7546739] using wordTrace_append hprefix tailTrace_7546739
  have hstable : (prefixWord ++ tailWord_7546739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546739).length < 2 ^ (prefixWord ++ tailWord_7546739).sum := by decide
  have hdescent : baseEnd_7546739 < baseStart_7546739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546750 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7546750 : Nat := 118140960795 + 7546750 * 2 ^ 59
def prefixEnd_7546750 : Nat := 4983230072969 + 3 ^ 40 * 7546750 * 2
def baseEnd_7546750 : Nat := 1291703376439484513206045

theorem tailTrace_7546750 : CollatzResearch.WordTrace tailWord_7546750 prefixEnd_7546750 1291703376439484513206045 := by
  unfold tailWord_7546750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406573176177638391493713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183501723606280738087966469 34406573176177638391493713)
  ·
    refine ⟨25804929882133228793620285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34406573176177638391493713 25804929882133228793620285)
    ·
      refine ⟨9676848705799960797607607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25804929882133228793620285 9676848705799960797607607)
      ·
        refine ⟨14515273058699941196411411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676848705799960797607607 14515273058699941196411411)
        ·
          refine ⟨21772909588049911794617117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515273058699941196411411 21772909588049911794617117)
          ·
            refine ⟨8164841095518716922981419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21772909588049911794617117 8164841095518716922981419)
            ·
              refine ⟨12247261643278075384472129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164841095518716922981419 12247261643278075384472129)
              ·
                refine ⟨9185446232458556538354097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12247261643278075384472129 9185446232458556538354097)
                ·
                  refine ⟨6889084674343917403765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185446232458556538354097 6889084674343917403765573)
                  ·
                    refine ⟨1291703376439484513206045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889084674343917403765573 1291703376439484513206045)
                    ·
                      rfl

theorem cell23_7546750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7546750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546750 prefixEnd_7546750 := by exact prefixLift 7546750
  have htrace : WordTrace (prefixWord ++ tailWord_7546750) baseStart_7546750 baseEnd_7546750 := by
    simpa [prefixWord, tailWord_7546750, baseEnd_7546750] using wordTrace_append hprefix tailTrace_7546750
  have hstable : (prefixWord ++ tailWord_7546750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546750).length < 2 ^ (prefixWord ++ tailWord_7546750).sum := by decide
  have hdescent : baseEnd_7546750 < baseStart_7546750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546773 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_7546773 : Nat := 118140960795 + 7546773 * 2 ^ 59
def prefixEnd_7546773 : Nat := 4983230072969 + 3 ^ 40 * 7546773 * 2
def baseEnd_7546773 : Nat := 3875121939373506949630529

theorem tailTrace_7546773 : CollatzResearch.WordTrace tailWord_7546773 prefixEnd_7546773 3875121939373506949630529 := by
  unfold tailWord_7546773
  simp only [CollatzResearch.WordTrace]
  refine ⟨275253424288337782060036973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183502282858891854706691315 275253424288337782060036973)
  ·
    refine ⟨103220034108126668272513865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275253424288337782060036973 103220034108126668272513865)
    ·
      refine ⟨77415025581095001204385399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103220034108126668272513865 77415025581095001204385399)
      ·
        refine ⟨116122538371642501806578099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77415025581095001204385399 116122538371642501806578099)
        ·
          refine ⟨174183807557463752709867149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116122538371642501806578099 174183807557463752709867149)
          ·
            refine ⟨65318927834048907266200181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174183807557463752709867149 65318927834048907266200181)
            ·
              refine ⟨6123649484442085056206267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65318927834048907266200181 6123649484442085056206267)
              ·
                refine ⟨9185474226663127584309401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6123649484442085056206267 9185474226663127584309401)
                ·
                  refine ⟨6889105669997345688232051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185474226663127584309401 6889105669997345688232051)
                  ·
                    refine ⟨10333658504996018532348077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6889105669997345688232051 10333658504996018532348077)
                    ·
                      refine ⟨3875121939373506949630529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333658504996018532348077 3875121939373506949630529)
                      ·
                        rfl

theorem cell23_7546773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_7546773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546773 prefixEnd_7546773 := by exact prefixLift 7546773
  have htrace : WordTrace (prefixWord ++ tailWord_7546773) baseStart_7546773 baseEnd_7546773 := by
    simpa [prefixWord, tailWord_7546773, baseEnd_7546773] using wordTrace_append hprefix tailTrace_7546773
  have hstable : (prefixWord ++ tailWord_7546773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546773).length < 2 ^ (prefixWord ++ tailWord_7546773).sum := by decide
  have hdescent : baseEnd_7546773 < baseStart_7546773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546802 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_7546802 : Nat := 118140960795 + 7546802 * 2 ^ 59
def prefixEnd_7546802 : Nat := 4983230072969 + 3 ^ 40 * 7546802 * 2
def baseEnd_7546802 : Nat := 430570758923609704018655

theorem tailTrace_7546802 : CollatzResearch.WordTrace tailWord_7546802 prefixEnd_7546802 430570758923609704018655 := by
  unfold tailWord_7546802
  simp only [CollatzResearch.WordTrace]
  refine ⟨68813620501308180003210665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183502988003488480008561773 68813620501308180003210665)
  ·
    refine ⟨51610215375981135002407999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68813620501308180003210665 51610215375981135002407999)
    ·
      refine ⟨77415323063971702503611999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51610215375981135002407999 77415323063971702503611999)
      ·
        refine ⟨116122984595957553755417999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77415323063971702503611999 116122984595957553755417999)
        ·
          refine ⟨174184476893936330633126999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116122984595957553755417999 174184476893936330633126999)
          ·
            refine ⟨261276715340904495949690499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174184476893936330633126999 261276715340904495949690499)
            ·
              refine ⟨391915073011356743924535749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261276715340904495949690499 391915073011356743924535749)
              ·
                refine ⟨73484076189629389485850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391915073011356743924535749 73484076189629389485850453)
                ·
                  refine ⟨430570758923609704018655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73484076189629389485850453 430570758923609704018655)
                  ·
                    rfl

theorem cell23_7546802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_7546802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546802 prefixEnd_7546802 := by exact prefixLift 7546802
  have htrace : WordTrace (prefixWord ++ tailWord_7546802) baseStart_7546802 baseEnd_7546802 := by
    simpa [prefixWord, tailWord_7546802, baseEnd_7546802] using wordTrace_append hprefix tailTrace_7546802
  have hstable : (prefixWord ++ tailWord_7546802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546802).length < 2 ^ (prefixWord ++ tailWord_7546802).sum := by decide
  have hdescent : baseEnd_7546802 < baseStart_7546802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546813 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7546813 : Nat := 118140960795 + 7546813 * 2 ^ 59
def prefixEnd_7546813 : Nat := 4983230072969 + 3 ^ 40 * 7546813 * 2
def baseEnd_7546813 : Nat := 3875142478599686793130345

theorem tailTrace_7546813 : CollatzResearch.WordTrace tailWord_7546813 prefixEnd_7546813 3875142478599686793130345 := by
  unfold tailWord_7546813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275254883208192868891493093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183503255472128579260995395 275254883208192868891493093)
  ·
    refine ⟨51610290601536162917154955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275254883208192868891493093 51610290601536162917154955)
    ·
      refine ⟨77415435902304244375732433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51610290601536162917154955 77415435902304244375732433)
      ·
        refine ⟨58061576926728183281799325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77415435902304244375732433 58061576926728183281799325)
        ·
          refine ⟨21773091347523068730674747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58061576926728183281799325 21773091347523068730674747)
          ·
            refine ⟨32659637021284603096012121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21773091347523068730674747 32659637021284603096012121)
            ·
              refine ⟨24494727765963452322009091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32659637021284603096012121 24494727765963452322009091)
              ·
                refine ⟨36742091648945178483013637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24494727765963452322009091 36742091648945178483013637)
                ·
                  refine ⟨6889142184177220965565057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36742091648945178483013637 6889142184177220965565057)
                  ·
                    refine ⟨5166856638132915724173793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6889142184177220965565057 5166856638132915724173793)
                    ·
                      refine ⟨3875142478599686793130345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5166856638132915724173793 3875142478599686793130345)
                      ·
                        rfl

theorem cell23_7546813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7546813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546813 prefixEnd_7546813 := by exact prefixLift 7546813
  have htrace : WordTrace (prefixWord ++ tailWord_7546813) baseStart_7546813 baseEnd_7546813 := by
    simpa [prefixWord, tailWord_7546813, baseEnd_7546813] using wordTrace_append hprefix tailTrace_7546813
  have hstable : (prefixWord ++ tailWord_7546813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546813).length < 2 ^ (prefixWord ++ tailWord_7546813).sum := by decide
  have hdescent : baseEnd_7546813 < baseStart_7546813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546832 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_7546832 : Nat := 118140960795 + 7546832 * 2 ^ 59
def prefixEnd_7546832 : Nat := 4983230072969 + 3 ^ 40 * 7546832 * 2
def baseEnd_7546832 : Nat := 1291717411577374072930919

theorem tailTrace_7546832 : CollatzResearch.WordTrace tailWord_7546832 prefixEnd_7546832 1291717411577374072930919 := by
  unfold tailWord_7546832
  simp only [CollatzResearch.WordTrace]
  refine ⟨137627788097562017568217375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183503717463416023424289833 137627788097562017568217375)
  ·
    refine ⟨206441682146343026352326063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137627788097562017568217375 206441682146343026352326063)
    ·
      refine ⟨309662523219514539528489095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206441682146343026352326063 309662523219514539528489095)
      ·
        refine ⟨464493784829271809292733643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309662523219514539528489095 464493784829271809292733643)
        ·
          refine ⟨696740677243907713939100465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464493784829271809292733643 696740677243907713939100465)
          ·
            refine ⟨522555507932930785454325349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696740677243907713939100465 522555507932930785454325349)
            ·
              refine ⟨97979157737424522272686003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522555507932930785454325349 97979157737424522272686003)
              ·
                refine ⟨146968736606136783409029005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97979157737424522272686003 146968736606136783409029005)
                ·
                  refine ⟨55113276227301293778385877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146968736606136783409029005 55113276227301293778385877)
                  ·
                    refine ⟨1291717411577374072930919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55113276227301293778385877 1291717411577374072930919)
                    ·
                      rfl

theorem cell23_7546832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_7546832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546832 prefixEnd_7546832 := by exact prefixLift 7546832
  have htrace : WordTrace (prefixWord ++ tailWord_7546832) baseStart_7546832 baseEnd_7546832 := by
    simpa [prefixWord, tailWord_7546832, baseEnd_7546832] using wordTrace_append hprefix tailTrace_7546832
  have hstable : (prefixWord ++ tailWord_7546832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546832).length < 2 ^ (prefixWord ++ tailWord_7546832).sum := by decide
  have hdescent : baseEnd_7546832 < baseStart_7546832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546849 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7546849 : Nat := 118140960795 + 7546849 * 2 ^ 59
def prefixEnd_7546849 : Nat := 4983230072969 + 3 ^ 40 * 7546849 * 2
def baseEnd_7546849 : Nat := 1291720321301082884093393

theorem tailTrace_7546849 : CollatzResearch.WordTrace tailWord_7546849 prefixEnd_7546849 1291720321301082884093393 := by
  unfold tailWord_7546849
  simp only [CollatzResearch.WordTrace]
  refine ⟨275256196236062447039803601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183504130824041631359869067 275256196236062447039803601)
  ·
    refine ⟨206442147177046835279852701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275256196236062447039803601 206442147177046835279852701)
    ·
      refine ⟨77415805191392563229944763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206442147177046835279852701 77415805191392563229944763)
      ·
        refine ⟨116123707787088844844917145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77415805191392563229944763 116123707787088844844917145)
        ·
          refine ⟨87092780840316633633687859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116123707787088844844917145 87092780840316633633687859)
          ·
            refine ⟨130639171260474950450531789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87092780840316633633687859 130639171260474950450531789)
            ·
              refine ⟨48989689222678106418949421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130639171260474950450531789 48989689222678106418949421)
              ·
                refine ⟨18371133458504289907106033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48989689222678106418949421 18371133458504289907106033)
                ·
                  refine ⟨13778350093878217430329525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18371133458504289907106033 13778350093878217430329525)
                  ·
                    refine ⟨1291720321301082884093393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13778350093878217430329525 1291720321301082884093393)
                    ·
                      rfl

theorem cell23_7546849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7546849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546849 prefixEnd_7546849 := by exact prefixLift 7546849
  have htrace : WordTrace (prefixWord ++ tailWord_7546849) baseStart_7546849 baseEnd_7546849 := by
    simpa [prefixWord, tailWord_7546849, baseEnd_7546849] using wordTrace_append hprefix tailTrace_7546849
  have hstable : (prefixWord ++ tailWord_7546849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546849).length < 2 ^ (prefixWord ++ tailWord_7546849).sum := by decide
  have hdescent : baseEnd_7546849 < baseStart_7546849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546879 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 7, 4]
def baseStart_7546879 : Nat := 118140960795 + 7546879 * 2 ^ 59
def prefixEnd_7546879 : Nat := 4983230072969 + 3 ^ 40 * 7546879 * 2
def baseEnd_7546879 : Nat := 1291725456107627844968347

theorem tailTrace_7546879 : CollatzResearch.WordTrace tailWord_7546879 prefixEnd_7546879 1291725456107627844968347 := by
  unfold tailWord_7546879
  simp only [CollatzResearch.WordTrace]
  refine ⟨275257290425953762163395691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183504860283969174775597127 275257290425953762163395691)
  ·
    refine ⟨412885935638930643245093537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275257290425953762163395691 412885935638930643245093537)
    ·
      refine ⟨309664451729197982433820153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412885935638930643245093537 309664451729197982433820153)
      ·
        refine ⟨232248338796898486825365115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309664451729197982433820153 232248338796898486825365115)
        ·
          refine ⟨348372508195347730238047673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232248338796898486825365115 348372508195347730238047673)
          ·
            refine ⟨261279381146510797678535755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348372508195347730238047673 261279381146510797678535755)
            ·
              refine ⟨391919071719766196517803633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261279381146510797678535755 391919071719766196517803633)
              ·
                refine ⟨293939303789824647388352725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391919071719766196517803633 293939303789824647388352725)
                ·
                  refine ⟨6889202432574015173164517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293939303789824647388352725 6889202432574015173164517)
                  ·
                    refine ⟨1291725456107627844968347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889202432574015173164517 1291725456107627844968347)
                    ·
                      rfl

theorem cell23_7546879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_7546879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546879 prefixEnd_7546879 := by exact prefixLift 7546879
  have htrace : WordTrace (prefixWord ++ tailWord_7546879) baseStart_7546879 baseEnd_7546879 := by
    simpa [prefixWord, tailWord_7546879, baseEnd_7546879] using wordTrace_append hprefix tailTrace_7546879
  have hstable : (prefixWord ++ tailWord_7546879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546879).length < 2 ^ (prefixWord ++ tailWord_7546879).sum := by decide
  have hdescent : baseEnd_7546879 < baseStart_7546879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546906 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_7546906 : Nat := 118140960795 + 7546906 * 2 ^ 59
def prefixEnd_7546906 : Nat := 4983230072969 + 3 ^ 40 * 7546906 * 2
def baseEnd_7546906 : Nat := 3875190232300554929267417

theorem tailTrace_7546906 : CollatzResearch.WordTrace tailWord_7546906 prefixEnd_7546906 3875190232300554929267417 := by
  unfold tailWord_7546906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68814568799213986443657143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183505516797903963849752381 68814568799213986443657143)
  ·
    refine ⟨103221853198820979665485715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68814568799213986443657143 103221853198820979665485715)
    ·
      refine ⟨154832779798231469498228573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103221853198820979665485715 154832779798231469498228573)
      ·
        refine ⟨58062292424336801061835715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154832779798231469498228573 58062292424336801061835715)
        ·
          refine ⟨87093438636505201592753573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58062292424336801061835715 87093438636505201592753573)
          ·
            refine ⟨16330019744344725298641295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87093438636505201592753573 16330019744344725298641295)
            ·
              refine ⟨24495029616517087947961943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330019744344725298641295 24495029616517087947961943)
              ·
                refine ⟨36742544424775631921942915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495029616517087947961943 36742544424775631921942915)
                ·
                  refine ⟨55113816637163447882914373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36742544424775631921942915 55113816637163447882914373)
                  ·
                    refine ⟨10333840619468146478046445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55113816637163447882914373 10333840619468146478046445)
                    ·
                      refine ⟨3875190232300554929267417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333840619468146478046445 3875190232300554929267417)
                      ·
                        rfl

theorem cell23_7546906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_7546906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546906 prefixEnd_7546906 := by exact prefixLift 7546906
  have htrace : WordTrace (prefixWord ++ tailWord_7546906) baseStart_7546906 baseEnd_7546906 := by
    simpa [prefixWord, tailWord_7546906, baseEnd_7546906] using wordTrace_append hprefix tailTrace_7546906
  have hstable : (prefixWord ++ tailWord_7546906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546906).length < 2 ^ (prefixWord ++ tailWord_7546906).sum := by decide
  have hdescent : baseEnd_7546906 < baseStart_7546906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546926 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_7546926 : Nat := 118140960795 + 7546926 * 2 ^ 59
def prefixEnd_7546926 : Nat := 4983230072969 + 3 ^ 40 * 7546926 * 2
def baseEnd_7546926 : Nat := 430577833545960539001925

theorem tailTrace_7546926 : CollatzResearch.WordTrace tailWord_7546926 prefixEnd_7546926 430577833545960539001925 := by
  unfold tailWord_7546926
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407375582097936148794579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183506003104522326126904421 34407375582097936148794579)
  ·
    refine ⟨51611063373146904223191869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34407375582097936148794579 51611063373146904223191869)
    ·
      refine ⟨19354148764930089083696951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51611063373146904223191869 19354148764930089083696951)
      ·
        refine ⟨29031223147395133625545427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19354148764930089083696951 29031223147395133625545427)
        ·
          refine ⟨43546834721092700438318141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29031223147395133625545427 43546834721092700438318141)
          ·
            refine ⟨16330063020409762664369303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43546834721092700438318141 16330063020409762664369303)
            ·
              refine ⟨24495094530614643996553955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330063020409762664369303 24495094530614643996553955)
              ·
                refine ⟨36742641795921965994830933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495094530614643996553955 36742641795921965994830933)
                ·
                  refine ⟨430577833545960539001925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36742641795921965994830933 430577833545960539001925)
                  ·
                    rfl

theorem cell23_7546926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_7546926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546926 prefixEnd_7546926 := by exact prefixLift 7546926
  have htrace : WordTrace (prefixWord ++ tailWord_7546926) baseStart_7546926 baseEnd_7546926 := by
    simpa [prefixWord, tailWord_7546926, baseEnd_7546926] using wordTrace_append hprefix tailTrace_7546926
  have hstable : (prefixWord ++ tailWord_7546926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546926).length < 2 ^ (prefixWord ++ tailWord_7546926).sum := by decide
  have hdescent : baseEnd_7546926 < baseStart_7546926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546929 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7546929 : Nat := 118140960795 + 7546929 * 2 ^ 59
def prefixEnd_7546929 : Nat := 4983230072969 + 3 ^ 40 * 7546929 * 2
def baseEnd_7546929 : Nat := 3875202042355608339279811

theorem tailTrace_7546929 : CollatzResearch.WordTrace tailWord_7546929 prefixEnd_7546929 3875202042355608339279811 := by
  unfold tailWord_7546929
  simp only [CollatzResearch.WordTrace]
  refine ⟨275259114075772620702715841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183506076050515080468477227 275259114075772620702715841)
  ·
    refine ⟨206444335556829465527036881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275259114075772620702715841 206444335556829465527036881)
    ·
      refine ⟨154833251667622099145277661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206444335556829465527036881 154833251667622099145277661)
      ·
        refine ⟨58062469375358287179479123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154833251667622099145277661 58062469375358287179479123)
        ·
          refine ⟨87093704063037430769218685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58062469375358287179479123 87093704063037430769218685)
          ·
            refine ⟨32660139023639036538457007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87093704063037430769218685 32660139023639036538457007)
            ·
              refine ⟨48990208535458554807685511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32660139023639036538457007 48990208535458554807685511)
              ·
                refine ⟨73485312803187832211528267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48990208535458554807685511 73485312803187832211528267)
                ·
                  refine ⟨110227969204781748317292401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73485312803187832211528267 110227969204781748317292401)
                  ·
                    refine ⟨82670976903586311237969301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110227969204781748317292401 82670976903586311237969301)
                    ·
                      refine ⟨3875202042355608339279811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82670976903586311237969301 3875202042355608339279811)
                      ·
                        rfl

theorem cell23_7546929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7546929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546929 prefixEnd_7546929 := by exact prefixLift 7546929
  have htrace : WordTrace (prefixWord ++ tailWord_7546929) baseStart_7546929 baseEnd_7546929 := by
    simpa [prefixWord, tailWord_7546929, baseEnd_7546929] using wordTrace_append hprefix tailTrace_7546929
  have hstable : (prefixWord ++ tailWord_7546929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546929).length < 2 ^ (prefixWord ++ tailWord_7546929).sum := by decide
  have hdescent : baseEnd_7546929 < baseStart_7546929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546956 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_7546956 : Nat := 118140960795 + 7546956 * 2 ^ 59
def prefixEnd_7546956 : Nat := 4983230072969 + 3 ^ 40 * 7546956 * 2
def baseEnd_7546956 : Nat := 1291738635444426577880729

theorem tailTrace_7546956 : CollatzResearch.WordTrace tailWord_7546956 prefixEnd_7546956 1291738635444426577880729 := by
  unfold tailWord_7546956
  simp only [CollatzResearch.WordTrace]
  refine ⟨137630049423337402156974361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183506732564449869542632481 137630049423337402156974361)
  ·
    refine ⟨103222537067503051617730771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137630049423337402156974361 103222537067503051617730771)
    ·
      refine ⟨154833805601254577426596157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103222537067503051617730771 154833805601254577426596157)
      ·
        refine ⟨58062677100470466534973559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154833805601254577426596157 58062677100470466534973559)
        ·
          refine ⟨87094015650705699802460339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58062677100470466534973559 87094015650705699802460339)
          ·
            refine ⟨130641023476058549703690509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87094015650705699802460339 130641023476058549703690509)
            ·
              refine ⟨48990383803521956138883941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130641023476058549703690509 48990383803521956138883941)
              ·
                refine ⟨9185696963160366776040739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48990383803521956138883941 9185696963160366776040739)
                ·
                  refine ⟨13778545444740550164061109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9185696963160366776040739 13778545444740550164061109)
                  ·
                    refine ⟨1291738635444426577880729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13778545444740550164061109 1291738635444426577880729)
                    ·
                      rfl

theorem cell23_7546956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_7546956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546956 prefixEnd_7546956 := by exact prefixLift 7546956
  have htrace : WordTrace (prefixWord ++ tailWord_7546956) baseStart_7546956 baseEnd_7546956 := by
    simpa [prefixWord, tailWord_7546956, baseEnd_7546956] using wordTrace_append hprefix tailTrace_7546956
  have hstable : (prefixWord ++ tailWord_7546956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546956).length < 2 ^ (prefixWord ++ tailWord_7546956).sum := by decide
  have hdescent : baseEnd_7546956 < baseStart_7546956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546969 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_7546969 : Nat := 118140960795 + 7546969 * 2 ^ 59
def prefixEnd_7546969 : Nat := 4983230072969 + 3 ^ 40 * 7546969 * 2
def baseEnd_7546969 : Nat := 1291740860527262727593209

theorem tailTrace_7546969 : CollatzResearch.WordTrace tailWord_7546969 prefixEnd_7546969 1291740860527262727593209 := by
  unfold tailWord_7546969
  simp only [CollatzResearch.WordTrace]
  refine ⟨275260572995627707534171961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183507048663751805022781307 275260572995627707534171961)
  ·
    refine ⟨206445429746720780650628971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275260572995627707534171961 206445429746720780650628971)
    ·
      refine ⟨309668144620081170975943457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206445429746720780650628971 309668144620081170975943457)
      ·
        refine ⟨232251108465060878231957593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309668144620081170975943457 232251108465060878231957593)
        ·
          refine ⟨174188331348795658673968195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232251108465060878231957593 174188331348795658673968195)
          ·
            refine ⟨261282497023193488010952293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174188331348795658673968195 261282497023193488010952293)
            ·
              refine ⟨48990468191848779002053555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261282497023193488010952293 48990468191848779002053555)
              ·
                refine ⟨73485702287773168503080333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48990468191848779002053555 73485702287773168503080333)
                ·
                  refine ⟨27557138357914938188655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73485702287773168503080333 27557138357914938188655125)
                  ·
                    refine ⟨1291740860527262727593209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27557138357914938188655125 1291740860527262727593209)
                    ·
                      rfl

theorem cell23_7546969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_7546969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546969 prefixEnd_7546969 := by exact prefixLift 7546969
  have htrace : WordTrace (prefixWord ++ tailWord_7546969) baseStart_7546969 baseEnd_7546969 := by
    simpa [prefixWord, tailWord_7546969, baseEnd_7546969] using wordTrace_append hprefix tailTrace_7546969
  have hstable : (prefixWord ++ tailWord_7546969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546969).length < 2 ^ (prefixWord ++ tailWord_7546969).sum := by decide
  have hdescent : baseEnd_7546969 < baseStart_7546969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7546999 : List Nat := [1, 1, 3, 1, 1, 5, 1, 10]
def baseStart_7546999 : Nat := 118140960795 + 7546999 * 2 ^ 59
def prefixEnd_7546999 : Nat := 4983230072969 + 3 ^ 40 * 7546999 * 2
def baseEnd_7546999 : Nat := 143527332814867520940907

theorem tailTrace_7546999 : CollatzResearch.WordTrace tailWord_7546999 prefixEnd_7546999 143527332814867520940907 := by
  unfold tailWord_7546999
  simp only [CollatzResearch.WordTrace]
  refine ⟨275261667185519022657764051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183507778123679348438509367 275261667185519022657764051)
  ·
    refine ⟨412892500778278533986646077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275261667185519022657764051 412892500778278533986646077)
    ·
      refine ⟨154834687791854450244992279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412892500778278533986646077 154834687791854450244992279)
      ·
        refine ⟨232252031687781675367488419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154834687791854450244992279 232252031687781675367488419)
        ·
          refine ⟨348378047531672513051232629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232252031687781675367488419 348378047531672513051232629)
          ·
            refine ⟨32660441956094298098553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348378047531672513051232629 32660441956094298098553059)
            ·
              refine ⟨48990662934141447147829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32660441956094298098553059 48990662934141447147829589)
              ·
                refine ⟨143527332814867520940907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48990662934141447147829589 143527332814867520940907)
                ·
                  rfl

theorem cell23_7546999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 10].length) (baseStart_7546999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7546999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7546999 prefixEnd_7546999 := by exact prefixLift 7546999
  have htrace : WordTrace (prefixWord ++ tailWord_7546999) baseStart_7546999 baseEnd_7546999 := by
    simpa [prefixWord, tailWord_7546999, baseEnd_7546999] using wordTrace_append hprefix tailTrace_7546999
  have hstable : (prefixWord ++ tailWord_7546999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7546999).length < 2 ^ (prefixWord ++ tailWord_7546999).sum := by decide
  have hdescent : baseEnd_7546999 < baseStart_7546999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7546999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547013 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_7547013 : Nat := 118140960795 + 7547013 * 2 ^ 59
def prefixEnd_7547013 : Nat := 4983230072969 + 3 ^ 40 * 7547013 * 2
def baseEnd_7547013 : Nat := 3875245174730586010629425

theorem tailTrace_7547013 : CollatzResearch.WordTrace tailWord_7547013 prefixEnd_7547013 3875245174730586010629425 := by
  unfold tailWord_7547013
  simp only [CollatzResearch.WordTrace]
  refine ⟨275262177807468303048773693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183508118538312202032515795 275262177807468303048773693)
  ·
    refine ⟨103223316677800613643290135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275262177807468303048773693 103223316677800613643290135)
    ·
      refine ⟨154834975016700920464935203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103223316677800613643290135 154834975016700920464935203)
      ·
        refine ⟨232252462525051380697402805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154834975016700920464935203 232252462525051380697402805)
        ·
          refine ⟨21773668361723566940381513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232252462525051380697402805 21773668361723566940381513)
          ·
            refine ⟨16330251271292675205286135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21773668361723566940381513 16330251271292675205286135)
            ·
              refine ⟨24495376906939012807929203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330251271292675205286135 24495376906939012807929203)
              ·
                refine ⟨36743065360408519211893805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495376906939012807929203 36743065360408519211893805)
                ·
                  refine ⟨13778649510153194704460177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36743065360408519211893805 13778649510153194704460177)
                  ·
                    refine ⟨10333987132614896028345133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13778649510153194704460177 10333987132614896028345133)
                    ·
                      refine ⟨3875245174730586010629425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10333987132614896028345133 3875245174730586010629425)
                      ·
                        rfl

theorem cell23_7547013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_7547013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547013 prefixEnd_7547013 := by exact prefixLift 7547013
  have htrace : WordTrace (prefixWord ++ tailWord_7547013) baseStart_7547013 baseEnd_7547013 := by
    simpa [prefixWord, tailWord_7547013, baseEnd_7547013] using wordTrace_append hprefix tailTrace_7547013
  have hstable : (prefixWord ++ tailWord_7547013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547013).length < 2 ^ (prefixWord ++ tailWord_7547013).sum := by decide
  have hdescent : baseEnd_7547013 < baseStart_7547013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547016 : List Nat := [2, 1, 3, 4, 1, 1, 2, 9]
def baseStart_7547016 : Nat := 118140960795 + 7547016 * 2 ^ 59
def prefixEnd_7547016 : Nat := 4983230072969 + 3 ^ 40 * 7547016 * 2
def baseEnd_7547016 : Nat := 143527656117501833292293

theorem tailTrace_7547016 : CollatzResearch.WordTrace tailWord_7547016 prefixEnd_7547016 143527656117501833292293 := by
  unfold tailWord_7547016
  simp only [CollatzResearch.WordTrace]
  refine ⟨137631143613228717280566451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183508191484304956374088601 137631143613228717280566451)
  ·
    refine ⟨206446715419843075920849677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137631143613228717280566451 206446715419843075920849677)
    ·
      refine ⟨77417518282441153470318629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206446715419843075920849677 77417518282441153470318629)
      ·
        refine ⟨14515784677957716275684743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77417518282441153470318629 14515784677957716275684743)
        ·
          refine ⟨21773677016936574413527115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515784677957716275684743 21773677016936574413527115)
          ·
            refine ⟨32660515525404861620290673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21773677016936574413527115 32660515525404861620290673)
            ·
              refine ⟨24495386644053646215218005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32660515525404861620290673 24495386644053646215218005)
              ·
                refine ⟨143527656117501833292293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24495386644053646215218005 143527656117501833292293)
                ·
                  rfl

theorem cell23_7547016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 9].length) (baseStart_7547016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547016 prefixEnd_7547016 := by exact prefixLift 7547016
  have htrace : WordTrace (prefixWord ++ tailWord_7547016) baseStart_7547016 baseEnd_7547016 := by
    simpa [prefixWord, tailWord_7547016, baseEnd_7547016] using wordTrace_append hprefix tailTrace_7547016
  have hstable : (prefixWord ++ tailWord_7547016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547016).length < 2 ^ (prefixWord ++ tailWord_7547016).sum := by decide
  have hdescent : baseEnd_7547016 < baseStart_7547016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547038 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7547038 : Nat := 118140960795 + 7547038 * 2 ^ 59
def prefixEnd_7547038 : Nat := 4983230072969 + 3 ^ 40 * 7547038 * 2
def baseEnd_7547038 : Nat := 3875258011746948412816811

theorem tailTrace_7547038 : CollatzResearch.WordTrace tailWord_7547038 prefixEnd_7547038 3875258011746948412816811 := by
  unfold tailWord_7547038
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407886204047216539804221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183508726421585154878955845 34407886204047216539804221)
  ·
    refine ⟨12902957326517706202426583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34407886204047216539804221 12902957326517706202426583)
    ·
      refine ⟨19354435989776559303639875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902957326517706202426583 19354435989776559303639875)
      ·
        refine ⟨29031653984664838955459813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19354435989776559303639875 29031653984664838955459813)
        ·
          refine ⟨5443435122124657304148715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29031653984664838955459813 5443435122124657304148715)
          ·
            refine ⟨8165152683186985956223073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443435122124657304148715 8165152683186985956223073)
            ·
              refine ⟨6123864512390239467167305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8165152683186985956223073 6123864512390239467167305)
              ·
                refine ⟨4592898384292679600375479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123864512390239467167305 4592898384292679600375479)
                ·
                  refine ⟨6889347576439019400563219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592898384292679600375479 6889347576439019400563219)
                  ·
                    refine ⟨10334021364658529100844829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6889347576439019400563219 10334021364658529100844829)
                    ·
                      refine ⟨3875258011746948412816811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10334021364658529100844829 3875258011746948412816811)
                      ·
                        rfl

theorem cell23_7547038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7547038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547038 prefixEnd_7547038 := by exact prefixLift 7547038
  have htrace : WordTrace (prefixWord ++ tailWord_7547038) baseStart_7547038 baseEnd_7547038 := by
    simpa [prefixWord, tailWord_7547038, baseEnd_7547038] using wordTrace_append hprefix tailTrace_7547038
  have hstable : (prefixWord ++ tailWord_7547038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547038).length < 2 ^ (prefixWord ++ tailWord_7547038).sum := by decide
  have hdescent : baseEnd_7547038 < baseStart_7547038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547044 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_7547044 : Nat := 118140960795 + 7547044 * 2 ^ 59
def prefixEnd_7547044 : Nat := 4983230072969 + 3 ^ 40 * 7547044 * 2
def baseEnd_7547044 : Nat := 3875261092630875389341783

theorem tailTrace_7547044 : CollatzResearch.WordTrace tailWord_7547044 prefixEnd_7547044 3875261092630875389341783 := by
  unfold tailWord_7547044
  simp only [CollatzResearch.WordTrace]
  refine ⟨137631654235177997671576093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183508872313570663562101457 137631654235177997671576093)
  ·
    refine ⟨51611870338191749126841035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137631654235177997671576093 51611870338191749126841035)
    ·
      refine ⟨77417805507287623690261553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51611870338191749126841035 77417805507287623690261553)
      ·
        refine ⟨58063354130465717767696165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77417805507287623690261553 58063354130465717767696165)
        ·
          refine ⟨10886878899462322081443031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58063354130465717767696165 10886878899462322081443031)
          ·
            refine ⟨16330318349193483122164547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886878899462322081443031 16330318349193483122164547)
            ·
              refine ⟨24495477523790224683246821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330318349193483122164547 24495477523790224683246821)
              ·
                refine ⟨4592902035710667128108779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24495477523790224683246821 4592902035710667128108779)
                ·
                  refine ⟨6889353053566000692163169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592902035710667128108779 6889353053566000692163169)
                  ·
                    refine ⟨5167014790174500519122377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6889353053566000692163169 5167014790174500519122377)
                    ·
                      refine ⟨3875261092630875389341783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167014790174500519122377 3875261092630875389341783)
                      ·
                        rfl

theorem cell23_7547044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_7547044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547044 prefixEnd_7547044 := by exact prefixLift 7547044
  have htrace : WordTrace (prefixWord ++ tailWord_7547044) baseStart_7547044 baseEnd_7547044 := by
    simpa [prefixWord, tailWord_7547044, baseEnd_7547044] using wordTrace_append hprefix tailTrace_7547044
  have hstable : (prefixWord ++ tailWord_7547044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547044).length < 2 ^ (prefixWord ++ tailWord_7547044).sum := by decide
  have hdescent : baseEnd_7547044 < baseStart_7547044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547050 : List Nat := [3, 1, 5, 1, 2, 2, 1, 8]
def baseStart_7547050 : Nat := 118140960795 + 7547050 * 2 ^ 59
def prefixEnd_7547050 : Nat := 4983230072969 + 3 ^ 40 * 7547050 * 2
def baseEnd_7547050 : Nat := 143528302722770457995065

theorem tailTrace_7547050 : CollatzResearch.WordTrace tailWord_7547050 prefixEnd_7547050 143528302722770457995065 := by
  unfold tailWord_7547050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68815881827083564591967651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183509018205556172245247069 68815881827083564591967651)
  ·
    refine ⟨103223822740625346887951477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68815881827083564591967651 103223822740625346887951477)
    ·
      refine ⟨9677233381933626270745451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103223822740625346887951477 9677233381933626270745451)
      ·
        refine ⟨14515850072900439406118177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9677233381933626270745451 14515850072900439406118177)
        ·
          refine ⟨10886887554675329554588633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14515850072900439406118177 10886887554675329554588633)
          ·
            refine ⟨8165165666006497165941475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10886887554675329554588633 8165165666006497165941475)
            ·
              refine ⟨12247748499009745748912213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165165666006497165941475 12247748499009745748912213)
              ·
                refine ⟨143528302722770457995065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12247748499009745748912213 143528302722770457995065)
                ·
                  rfl

theorem cell23_7547050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_7547050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547050 prefixEnd_7547050 := by exact prefixLift 7547050
  have htrace : WordTrace (prefixWord ++ tailWord_7547050) baseStart_7547050 baseEnd_7547050 := by
    simpa [prefixWord, tailWord_7547050, baseEnd_7547050] using wordTrace_append hprefix tailTrace_7547050
  have hstable : (prefixWord ++ tailWord_7547050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547050).length < 2 ^ (prefixWord ++ tailWord_7547050).sum := by decide
  have hdescent : baseEnd_7547050 < baseStart_7547050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547083 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 4, 2]
def baseStart_7547083 : Nat := 118140960795 + 7547083 * 2 ^ 59
def prefixEnd_7547083 : Nat := 4983230072969 + 3 ^ 40 * 7547083 * 2
def baseEnd_7547083 : Nat := 3875281118376400736754103

theorem tailTrace_7547083 : CollatzResearch.WordTrace tailWord_7547083 prefixEnd_7547083 3875281118376400736754103 := by
  unfold tailWord_7547083
  simp only [CollatzResearch.WordTrace]
  refine ⟨275264730917214705003821903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183509820611476470002547935 275264730917214705003821903)
  ·
    refine ⟨412897096375822057505732855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275264730917214705003821903 412897096375822057505732855)
    ·
      refine ⟨619345644563733086258599283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412897096375822057505732855 619345644563733086258599283)
      ·
        refine ⟨929018466845599629387898925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619345644563733086258599283 929018466845599629387898925)
        ·
          refine ⟨348381925067099861020462097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929018466845599629387898925 348381925067099861020462097)
          ·
            refine ⟨261286443800324895765346573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348381925067099861020462097 261286443800324895765346573)
            ·
              refine ⟨97982416425121835912004965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261286443800324895765346573 97982416425121835912004965)
              ·
                refine ⟨18371703079710344233500931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97982416425121835912004965 18371703079710344233500931)
                ·
                  refine ⟨27557554619565516350251397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18371703079710344233500931 27557554619565516350251397)
                  ·
                    refine ⟨5167041491168534315672137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27557554619565516350251397 5167041491168534315672137)
                    ·
                      refine ⟨3875281118376400736754103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167041491168534315672137 3875281118376400736754103)
                      ·
                        rfl

theorem cell23_7547083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4, 2].length) (baseStart_7547083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547083 prefixEnd_7547083 := by exact prefixLift 7547083
  have htrace : WordTrace (prefixWord ++ tailWord_7547083) baseStart_7547083 baseEnd_7547083 := by
    simpa [prefixWord, tailWord_7547083, baseEnd_7547083] using wordTrace_append hprefix tailTrace_7547083
  have hstable : (prefixWord ++ tailWord_7547083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547083).length < 2 ^ (prefixWord ++ tailWord_7547083).sum := by decide
  have hdescent : baseEnd_7547083 < baseStart_7547083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547094 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7547094 : Nat := 118140960795 + 7547094 * 2 ^ 59
def prefixEnd_7547094 : Nat := 4983230072969 + 3 ^ 40 * 7547094 * 2
def baseEnd_7547094 : Nat := 3875286766663600193716553

theorem tailTrace_7547094 : CollatzResearch.WordTrace tailWord_7547094 prefixEnd_7547094 3875286766663600193716553 := by
  unfold tailWord_7547094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17204070757510928367654521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183510088080116569254981557 17204070757510928367654521)
  ·
    refine ⟨12903053068133196275740891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17204070757510928367654521 12903053068133196275740891)
    ·
      refine ⟨19354579602199794413611337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12903053068133196275740891 19354579602199794413611337)
      ·
        refine ⟨14515934701649845810208503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19354579602199794413611337 14515934701649845810208503)
        ·
          refine ⟨21773902052474768715312755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515934701649845810208503 21773902052474768715312755)
          ·
            refine ⟨32660853078712153072969133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21773902052474768715312755 32660853078712153072969133)
            ·
              refine ⟨12247819904517057402363425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32660853078712153072969133 12247819904517057402363425)
              ·
                refine ⟨9185864928387793051772569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12247819904517057402363425 9185864928387793051772569)
                ·
                  refine ⟨6889398696290844788829427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185864928387793051772569 6889398696290844788829427)
                  ·
                    refine ⟨10334098044436267183244141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6889398696290844788829427 10334098044436267183244141)
                    ·
                      refine ⟨3875286766663600193716553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10334098044436267183244141 3875286766663600193716553)
                      ·
                        rfl

theorem cell23_7547094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7547094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547094 prefixEnd_7547094 := by exact prefixLift 7547094
  have htrace : WordTrace (prefixWord ++ tailWord_7547094) baseStart_7547094 baseEnd_7547094 := by
    simpa [prefixWord, tailWord_7547094, baseEnd_7547094] using wordTrace_append hprefix tailTrace_7547094
  have hstable : (prefixWord ++ tailWord_7547094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547094).length < 2 ^ (prefixWord ++ tailWord_7547094).sum := by decide
  have hdescent : baseEnd_7547094 < baseStart_7547094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547136 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_7547136 : Nat := 118140960795 + 7547136 * 2 ^ 59
def prefixEnd_7547136 : Nat := 4983230072969 + 3 ^ 40 * 7547136 * 2
def baseEnd_7547136 : Nat := 1291769444283696343130453

theorem tailTrace_7547136 : CollatzResearch.WordTrace tailWord_7547136 prefixEnd_7547136 1291769444283696343130453 := by
  unfold tailWord_7547136
  simp only [CollatzResearch.WordTrace]
  refine ⟨137633331993011347527750631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183511109324015130037000841 137633331993011347527750631)
  ·
    refine ⟨206449997989517021291625947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137633331993011347527750631 206449997989517021291625947)
    ·
      refine ⟨309674996984275531937438921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206449997989517021291625947 309674996984275531937438921)
      ·
        refine ⟨232256247738206648953079191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309674996984275531937438921 232256247738206648953079191)
        ·
          refine ⟨348384371607309973429618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232256247738206648953079191 348384371607309973429618787)
          ·
            refine ⟨522576557410964960144428181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348384371607309973429618787 522576557410964960144428181)
            ·
              refine ⟨24495776128638982506770071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 522576557410964960144428181 24495776128638982506770071)
              ·
                refine ⟨36743664192958473760155107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495776128638982506770071 36743664192958473760155107)
                ·
                  refine ⟨55115496289437710640232661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36743664192958473760155107 55115496289437710640232661)
                  ·
                    refine ⟨1291769444283696343130453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55115496289437710640232661 1291769444283696343130453)
                    ·
                      rfl

theorem cell23_7547136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_7547136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547136 prefixEnd_7547136 := by exact prefixLift 7547136
  have htrace : WordTrace (prefixWord ++ tailWord_7547136) baseStart_7547136 baseEnd_7547136 := by
    simpa [prefixWord, tailWord_7547136, baseEnd_7547136] using wordTrace_append hprefix tailTrace_7547136
  have hstable : (prefixWord ++ tailWord_7547136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547136).length < 2 ^ (prefixWord ++ tailWord_7547136).sum := by decide
  have hdescent : baseEnd_7547136 < baseStart_7547136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547153 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_7547153 : Nat := 118140960795 + 7547153 * 2 ^ 59
def prefixEnd_7547153 : Nat := 4983230072969 + 3 ^ 40 * 7547153 * 2
def baseEnd_7547153 : Nat := 1291772354007405154292927

theorem tailTrace_7547153 : CollatzResearch.WordTrace tailWord_7547153 prefixEnd_7547153 1291772354007405154292927 := by
  unfold tailWord_7547153
  simp only [CollatzResearch.WordTrace]
  refine ⟨275267284026961106958870113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183511522684640737972580075 275267284026961106958870113)
  ·
    refine ⟨206450463020220830219152585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275267284026961106958870113 206450463020220830219152585)
    ·
      refine ⟨154837847265165622664364439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206450463020220830219152585 154837847265165622664364439)
      ·
        refine ⟨232256770897748433996546659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154837847265165622664364439 232256770897748433996546659)
        ·
          refine ⟨348385156346622650994819989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232256770897748433996546659 348385156346622650994819989)
          ·
            refine ⟨16330554203747936765382187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348385156346622650994819989 16330554203747936765382187)
            ·
              refine ⟨24495831305621905148073281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330554203747936765382187 24495831305621905148073281)
              ·
                refine ⟨18371873479216428861054961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24495831305621905148073281 18371873479216428861054961)
                ·
                  refine ⟨13778905109412321645791221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18371873479216428861054961 13778905109412321645791221)
                  ·
                    refine ⟨1291772354007405154292927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13778905109412321645791221 1291772354007405154292927)
                    ·
                      rfl

theorem cell23_7547153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_7547153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547153 prefixEnd_7547153 := by exact prefixLift 7547153
  have htrace : WordTrace (prefixWord ++ tailWord_7547153) baseStart_7547153 baseEnd_7547153 := by
    simpa [prefixWord, tailWord_7547153, baseEnd_7547153] using wordTrace_append hprefix tailTrace_7547153
  have hstable : (prefixWord ++ tailWord_7547153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547153).length < 2 ^ (prefixWord ++ tailWord_7547153).sum := by decide
  have hdescent : baseEnd_7547153 < baseStart_7547153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547183 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 3, 4]
def baseStart_7547183 : Nat := 118140960795 + 7547183 * 2 ^ 59
def prefixEnd_7547183 : Nat := 4983230072969 + 3 ^ 40 * 7547183 * 2
def baseEnd_7547183 : Nat := 1291777488813950115167881

theorem tailTrace_7547183 : CollatzResearch.WordTrace tailWord_7547183 prefixEnd_7547183 1291777488813950115167881 := by
  unfold tailWord_7547183
  simp only [CollatzResearch.WordTrace]
  refine ⟨275268378216852422082462203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183512252144568281388308135 275268378216852422082462203)
  ·
    refine ⟨412902567325278633123693305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275268378216852422082462203 412902567325278633123693305)
    ·
      refine ⟨309676925493958974842769979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412902567325278633123693305 309676925493958974842769979)
      ·
        refine ⟨464515388240938462264154969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309676925493958974842769979 464515388240938462264154969)
        ·
          refine ⟨348386541180703846698116227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464515388240938462264154969 348386541180703846698116227)
          ·
            refine ⟨522579811771055770047174341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348386541180703846698116227 522579811771055770047174341)
            ·
              refine ⟨97983714707072956883845189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522579811771055770047174341 97983714707072956883845189)
              ·
                refine ⟨18371946507576179415720973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97983714707072956883845189 18371946507576179415720973)
                ·
                  refine ⟨6889479940341067280895365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18371946507576179415720973 6889479940341067280895365)
                  ·
                    refine ⟨1291777488813950115167881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889479940341067280895365 1291777488813950115167881)
                    ·
                      rfl

theorem cell23_7547183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_7547183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547183 prefixEnd_7547183 := by exact prefixLift 7547183
  have htrace : WordTrace (prefixWord ++ tailWord_7547183) baseStart_7547183 baseEnd_7547183 := by
    simpa [prefixWord, tailWord_7547183, baseEnd_7547183] using wordTrace_append hprefix tailTrace_7547183
  have hstable : (prefixWord ++ tailWord_7547183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547183).length < 2 ^ (prefixWord ++ tailWord_7547183).sum := by decide
  have hdescent : baseEnd_7547183 < baseStart_7547183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547217 : List Nat := [1, 2, 2, 1, 4, 3, 1, 4, 1, 4]
def baseStart_7547217 : Nat := 118140960795 + 7547217 * 2 ^ 59
def prefixEnd_7547217 : Nat := 4983230072969 + 3 ^ 40 * 7547217 * 2
def baseEnd_7547217 : Nat := 1291783308261367737492829

theorem tailTrace_7547217 : CollatzResearch.WordTrace tailWord_7547217 prefixEnd_7547217 1291783308261367737492829 := by
  unfold tailWord_7547217
  simp only [CollatzResearch.WordTrace]
  refine ⟨275269618298729245889199905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183513078865819497259466603 275269618298729245889199905)
  ·
    refine ⟨206452213724046934416899929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275269618298729245889199905 206452213724046934416899929)
    ·
      refine ⟨154839160293035200812674947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206452213724046934416899929 154839160293035200812674947)
      ·
        refine ⟨232258740439552801219012421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154839160293035200812674947 232258740439552801219012421)
        ·
          refine ⟨43548513832416150228564829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232258740439552801219012421 43548513832416150228564829)
          ·
            refine ⟨16330692687156056335711811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43548513832416150228564829 16330692687156056335711811)
            ·
              refine ⟨24496039030734084503567717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330692687156056335711811 24496039030734084503567717)
              ·
                refine ⟨4593007318262640844418947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24496039030734084503567717 4593007318262640844418947)
                ·
                  refine ⟨6889510977393961266628421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593007318262640844418947 6889510977393961266628421)
                  ·
                    refine ⟨1291783308261367737492829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889510977393961266628421 1291783308261367737492829)
                    ·
                      rfl

theorem cell23_7547217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_7547217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547217 prefixEnd_7547217 := by exact prefixLift 7547217
  have htrace : WordTrace (prefixWord ++ tailWord_7547217) baseStart_7547217 baseEnd_7547217 := by
    simpa [prefixWord, tailWord_7547217, baseEnd_7547217] using wordTrace_append hprefix tailTrace_7547217
  have hstable : (prefixWord ++ tailWord_7547217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547217).length < 2 ^ (prefixWord ++ tailWord_7547217).sum := by decide
  have hdescent : baseEnd_7547217 < baseStart_7547217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547244 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_7547244 : Nat := 118140960795 + 7547244 * 2 ^ 59
def prefixEnd_7547244 : Nat := 4983230072969 + 3 ^ 40 * 7547244 * 2
def baseEnd_7547244 : Nat := 3875363788761774606840863

theorem tailTrace_7547244 : CollatzResearch.WordTrace tailWord_7547244 prefixEnd_7547244 3875363788761774606840863 := by
  unfold tailWord_7547244
  simp only [CollatzResearch.WordTrace]
  refine ⟨137635301534815714750216393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183513735379754286333621857 137635301534815714750216393)
  ·
    refine ⟨103226476151111786062662295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137635301534815714750216393 103226476151111786062662295)
    ·
      refine ⟨154839714226667679093993443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103226476151111786062662295 154839714226667679093993443)
      ·
        refine ⟨232259571340001518640990165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154839714226667679093993443 232259571340001518640990165)
        ·
          refine ⟨5443583703281285593148207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 232259571340001518640990165 5443583703281285593148207)
          ·
            refine ⟨8165375554921928389722311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443583703281285593148207 8165375554921928389722311)
            ·
              refine ⟨12248063332382892584583467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165375554921928389722311 12248063332382892584583467)
              ·
                refine ⟨18372094998574338876875201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248063332382892584583467 18372094998574338876875201)
                ·
                  refine ⟨13779071248930754157656401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18372094998574338876875201 13779071248930754157656401)
                  ·
                    refine ⟨10334303436698065618242301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13779071248930754157656401 10334303436698065618242301)
                    ·
                      refine ⟨3875363788761774606840863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10334303436698065618242301 3875363788761774606840863)
                      ·
                        rfl

theorem cell23_7547244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_7547244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547244 prefixEnd_7547244 := by exact prefixLift 7547244
  have htrace : WordTrace (prefixWord ++ tailWord_7547244) baseStart_7547244 baseEnd_7547244 := by
    simpa [prefixWord, tailWord_7547244, baseEnd_7547244] using wordTrace_append hprefix tailTrace_7547244
  have hstable : (prefixWord ++ tailWord_7547244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547244).length < 2 ^ (prefixWord ++ tailWord_7547244).sum := by decide
  have hdescent : baseEnd_7547244 < baseStart_7547244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547290 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_7547290 : Nat := 118140960795 + 7547290 * 2 ^ 59
def prefixEnd_7547290 : Nat := 4983230072969 + 3 ^ 40 * 7547290 * 2
def baseEnd_7547290 : Nat := 1291795802957293808955217

theorem tailTrace_7547290 : CollatzResearch.WordTrace tailWord_7547290 prefixEnd_7547290 1291795802957293808955217 := by
  unfold tailWord_7547290
  simp only [CollatzResearch.WordTrace]
  refine ⟨68818070206866194839151831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183514853884976519571071549 68818070206866194839151831)
  ·
    refine ⟨103227105310299292258727747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68818070206866194839151831 103227105310299292258727747)
    ·
      refine ⟨154840657965448938388091621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103227105310299292258727747 154840657965448938388091621)
      ·
        refine ⟨29032623368521675947767179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154840657965448938388091621 29032623368521675947767179)
        ·
          refine ⟨43548935052782513921650769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29032623368521675947767179 43548935052782513921650769)
          ·
            refine ⟨32661701289586885441238077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43548935052782513921650769 32661701289586885441238077)
            ·
              refine ⟨12248137983595082040464279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32661701289586885441238077 12248137983595082040464279)
              ·
                refine ⟨18372206975392623060696419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248137983595082040464279 18372206975392623060696419)
                ·
                  refine ⟨27558310463088934591044629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18372206975392623060696419 27558310463088934591044629)
                  ·
                    refine ⟨1291795802957293808955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27558310463088934591044629 1291795802957293808955217)
                    ·
                      rfl

theorem cell23_7547290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_7547290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547290 prefixEnd_7547290 := by exact prefixLift 7547290
  have htrace : WordTrace (prefixWord ++ tailWord_7547290) baseStart_7547290 baseEnd_7547290 := by
    simpa [prefixWord, tailWord_7547290, baseEnd_7547290] using wordTrace_append hprefix tailTrace_7547290
  have hstable : (prefixWord ++ tailWord_7547290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547290).length < 2 ^ (prefixWord ++ tailWord_7547290).sum := by decide
  have hdescent : baseEnd_7547290 < baseStart_7547290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547294 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7547294 : Nat := 118140960795 + 7547294 * 2 ^ 59
def prefixEnd_7547294 : Nat := 4983230072969 + 3 ^ 40 * 7547294 * 2
def baseEnd_7547294 : Nat := 1291796487598166470405211

theorem tailTrace_7547294 : CollatzResearch.WordTrace tailWord_7547294 prefixEnd_7547294 1291796487598166470405211 := by
  unfold tailWord_7547294
  simp only [CollatzResearch.WordTrace]
  refine ⟨34409053339931286004969117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183514951146300192026501957 34409053339931286004969117)
  ·
    refine ⟨12903395002474232251863419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34409053339931286004969117 12903395002474232251863419)
    ·
      refine ⟨19355092503711348377795129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12903395002474232251863419 19355092503711348377795129)
      ·
        refine ⟨14516319377783511283346347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19355092503711348377795129 14516319377783511283346347)
        ·
          refine ⟨21774479066675266925019521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14516319377783511283346347 21774479066675266925019521)
          ·
            refine ⟨16330859300006450193764641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21774479066675266925019521 16330859300006450193764641)
            ·
              refine ⟨12248144475004837645323481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16330859300006450193764641 12248144475004837645323481)
              ·
                refine ⟨9186108356253628233992611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12248144475004837645323481 9186108356253628233992611)
                ·
                  refine ⟨13779162534380442350988917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9186108356253628233992611 13779162534380442350988917)
                  ·
                    refine ⟨1291796487598166470405211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13779162534380442350988917 1291796487598166470405211)
                    ·
                      rfl

theorem cell23_7547294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7547294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547294 prefixEnd_7547294 := by exact prefixLift 7547294
  have htrace : WordTrace (prefixWord ++ tailWord_7547294) baseStart_7547294 baseEnd_7547294 := by
    simpa [prefixWord, tailWord_7547294, baseEnd_7547294] using wordTrace_append hprefix tailTrace_7547294
  have hstable : (prefixWord ++ tailWord_7547294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547294).length < 2 ^ (prefixWord ++ tailWord_7547294).sum := by decide
  have hdescent : baseEnd_7547294 < baseStart_7547294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547300 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_7547300 : Nat := 118140960795 + 7547300 * 2 ^ 59
def prefixEnd_7547300 : Nat := 4983230072969 + 3 ^ 40 * 7547300 * 2
def baseEnd_7547300 : Nat := 3875392543678426387740605

theorem tailTrace_7547300 : CollatzResearch.WordTrace tailWord_7547300 prefixEnd_7547300 3875392543678426387740605 := by
  unfold tailWord_7547300
  simp only [CollatzResearch.WordTrace]
  refine ⟨137636322778714275532235677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183515097038285700709647569 137636322778714275532235677)
  ·
    refine ⟨51613621042017853324588379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137636322778714275532235677 51613621042017853324588379)
    ·
      refine ⟨77420431563026779986882569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51613621042017853324588379 77420431563026779986882569)
      ·
        refine ⟨58065323672270084990161927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77420431563026779986882569 58065323672270084990161927)
        ·
          refine ⟨87097985508405127485242891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58065323672270084990161927 87097985508405127485242891)
          ·
            refine ⟨130646978262607691227864337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87097985508405127485242891 130646978262607691227864337)
            ·
              refine ⟨97985233696955768420898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130646978262607691227864337 97985233696955768420898253)
              ·
                refine ⟨36744462636358413157836845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97985233696955768420898253 36744462636358413157836845)
                ·
                  refine ⟨13779173488634404934188817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36744462636358413157836845 13779173488634404934188817)
                  ·
                    refine ⟨10334380116475803700641613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13779173488634404934188817 10334380116475803700641613)
                    ·
                      refine ⟨3875392543678426387740605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10334380116475803700641613 3875392543678426387740605)
                      ·
                        rfl

theorem cell23_7547300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_7547300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547300 prefixEnd_7547300 := by exact prefixLift 7547300
  have htrace : WordTrace (prefixWord ++ tailWord_7547300) baseStart_7547300 baseEnd_7547300 := by
    simpa [prefixWord, tailWord_7547300, baseEnd_7547300] using wordTrace_append hprefix tailTrace_7547300
  have hstable : (prefixWord ++ tailWord_7547300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547300).length < 2 ^ (prefixWord ++ tailWord_7547300).sum := by decide
  have hdescent : baseEnd_7547300 < baseStart_7547300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547317 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7547317 : Nat := 118140960795 + 7547317 * 2 ^ 59
def prefixEnd_7547317 : Nat := 4983230072969 + 3 ^ 40 * 7547317 * 2
def baseEnd_7547317 : Nat := 3875401272849552821228027

theorem tailTrace_7547317 : CollatzResearch.WordTrace tailWord_7547317 prefixEnd_7547317 3875401272849552821228027 := by
  unfold tailWord_7547317
  simp only [CollatzResearch.WordTrace]
  refine ⟨275273265598366962967840205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183515510398911308645226803 275273265598366962967840205)
  ·
    refine ⟨103227474599387611112940077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275273265598366962967840205 103227474599387611112940077)
    ·
      refine ⟨38710302974770354167352529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103227474599387611112940077 38710302974770354167352529)
      ·
        refine ⟨29032727231077765625514397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38710302974770354167352529 29032727231077765625514397)
        ·
          refine ⟨10887272711654162109567899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29032727231077765625514397 10887272711654162109567899)
          ·
            refine ⟨16330909067481243164351849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10887272711654162109567899 16330909067481243164351849)
            ·
              refine ⟨12248181800610932373263887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16330909067481243164351849 12248181800610932373263887)
              ·
                refine ⟨18372272700916398559895831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248181800610932373263887 18372272700916398559895831)
                ·
                  refine ⟨27558409051374597839843747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18372272700916398559895831 27558409051374597839843747)
                  ·
                    refine ⟨41337613577061896759765621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27558409051374597839843747 41337613577061896759765621)
                    ·
                      refine ⟨3875401272849552821228027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41337613577061896759765621 3875401272849552821228027)
                      ·
                        rfl

theorem cell23_7547317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7547317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547317 prefixEnd_7547317 := by exact prefixLift 7547317
  have htrace : WordTrace (prefixWord ++ tailWord_7547317) baseStart_7547317 baseEnd_7547317 := by
    simpa [prefixWord, tailWord_7547317, baseEnd_7547317] using wordTrace_append hprefix tailTrace_7547317
  have hstable : (prefixWord ++ tailWord_7547317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547317).length < 2 ^ (prefixWord ++ tailWord_7547317).sum := by decide
  have hdescent : baseEnd_7547317 < baseStart_7547317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547398 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7547398 : Nat := 118140960795 + 7547398 * 2 ^ 59
def prefixEnd_7547398 : Nat := 4983230072969 + 3 ^ 40 * 7547398 * 2
def baseEnd_7547398 : Nat := 3875442864782567004315155

theorem tailTrace_7547398 : CollatzResearch.WordTrace tailWord_7547398 prefixEnd_7547398 3875442864782567004315155 := by
  unfold tailWord_7547398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602381872221047306298089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183517479940715675867692565 8602381872221047306298089)
  ·
    refine ⟨6451786404165785479723567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8602381872221047306298089 6451786404165785479723567)
    ·
      refine ⟨9677679606248678219585351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6451786404165785479723567 9677679606248678219585351)
      ·
        refine ⟨14516519409373017329378027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9677679606248678219585351 14516519409373017329378027)
        ·
          refine ⟨21774779114059525994067041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14516519409373017329378027 21774779114059525994067041)
          ·
            refine ⟨16331084335544644495550281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21774779114059525994067041 16331084335544644495550281)
            ·
              refine ⟨12248313251658483371662711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16331084335544644495550281 12248313251658483371662711)
              ·
                refine ⟨18372469877487725057494067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248313251658483371662711 18372469877487725057494067)
                ·
                  refine ⟨27558704816231587586241101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18372469877487725057494067 27558704816231587586241101)
                  ·
                    refine ⟨10334514306086845344840413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27558704816231587586241101 10334514306086845344840413)
                    ·
                      refine ⟨3875442864782567004315155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10334514306086845344840413 3875442864782567004315155)
                      ·
                        rfl

theorem cell23_7547398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7547398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547398 prefixEnd_7547398 := by exact prefixLift 7547398
  have htrace : WordTrace (prefixWord ++ tailWord_7547398) baseStart_7547398 baseEnd_7547398 := by
    simpa [prefixWord, tailWord_7547398, baseEnd_7547398] using wordTrace_append hprefix tailTrace_7547398
  have hstable : (prefixWord ++ tailWord_7547398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547398).length < 2 ^ (prefixWord ++ tailWord_7547398).sum := by decide
  have hdescent : baseEnd_7547398 < baseStart_7547398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547404 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_7547404 : Nat := 118140960795 + 7547404 * 2 ^ 59
def prefixEnd_7547404 : Nat := 4983230072969 + 3 ^ 40 * 7547404 * 2
def baseEnd_7547404 : Nat := 3875445945666493980840127

theorem tailTrace_7547404 : CollatzResearch.WordTrace tailWord_7547404 prefixEnd_7547404 3875445945666493980840127 := by
  unfold tailWord_7547404
  simp only [CollatzResearch.WordTrace]
  refine ⟨137638219374525888413128633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183517625832701184550838177 137638219374525888413128633)
  ·
    refine ⟨103228664530894416309846475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137638219374525888413128633 103228664530894416309846475)
    ·
      refine ⟨154842996796341624464769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103228664530894416309846475 154842996796341624464769713)
      ·
        refine ⟨116132247597256218348577285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154842996796341624464769713 116132247597256218348577285)
        ·
          refine ⟨21774796424485540940358241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116132247597256218348577285 21774796424485540940358241)
          ·
            refine ⟨16331097318364155705268681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21774796424485540940358241 16331097318364155705268681)
            ·
              refine ⟨12248322988773116778951511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16331097318364155705268681 12248322988773116778951511)
              ·
                refine ⟨18372484483159675168427267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248322988773116778951511 18372484483159675168427267)
                ·
                  refine ⟨27558726724739512752640901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18372484483159675168427267 27558726724739512752640901)
                  ·
                    refine ⟨5167261260888658641120169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27558726724739512752640901 5167261260888658641120169)
                    ·
                      refine ⟨3875445945666493980840127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167261260888658641120169 3875445945666493980840127)
                      ·
                        rfl

theorem cell23_7547404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_7547404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547404 prefixEnd_7547404 := by exact prefixLift 7547404
  have htrace : WordTrace (prefixWord ++ tailWord_7547404) baseStart_7547404 baseEnd_7547404 := by
    simpa [prefixWord, tailWord_7547404, baseEnd_7547404] using wordTrace_append hprefix tailTrace_7547404
  have hstable : (prefixWord ++ tailWord_7547404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547404).length < 2 ^ (prefixWord ++ tailWord_7547404).sum := by decide
  have hdescent : baseEnd_7547404 < baseStart_7547404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547427 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 5]
def baseStart_7547427 : Nat := 118140960795 + 7547427 * 2 ^ 59
def prefixEnd_7547427 : Nat := 4983230072969 + 3 ^ 40 * 7547427 * 2
def baseEnd_7547427 : Nat := 430606417302394154539169

theorem tailTrace_7547427 : CollatzResearch.WordTrace tailWord_7547427 prefixEnd_7547427 430606417302394154539169 := by
  unfold tailWord_7547427
  simp only [CollatzResearch.WordTrace]
  refine ⟨275277277627968451754344535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183518185085312301169563023 275277277627968451754344535)
  ·
    refine ⟨412915916441952677631516803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275277277627968451754344535 412915916441952677631516803)
    ·
      refine ⟨619373874662929016447275205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412915916441952677631516803 619373874662929016447275205)
      ·
        refine ⟨116132601499299190583864101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619373874662929016447275205 116132601499299190583864101)
        ·
          refine ⟨21774862781118598234474519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116132601499299190583864101 21774862781118598234474519)
          ·
            refine ⟨32662294171677897351711779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21774862781118598234474519 32662294171677897351711779)
            ·
              refine ⟨48993441257516846027567669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32662294171677897351711779 48993441257516846027567669)
              ·
                refine ⟨4593135117892204315084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48993441257516846027567669 4593135117892204315084469)
                ·
                  refine ⟨430606417302394154539169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593135117892204315084469 430606417302394154539169)
                  ·
                    rfl

theorem cell23_7547427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 5].length) (baseStart_7547427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547427 prefixEnd_7547427 := by exact prefixLift 7547427
  have htrace : WordTrace (prefixWord ++ tailWord_7547427) baseStart_7547427 baseEnd_7547427 := by
    simpa [prefixWord, tailWord_7547427, baseEnd_7547427] using wordTrace_append hprefix tailTrace_7547427
  have hstable : (prefixWord ++ tailWord_7547427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547427).length < 2 ^ (prefixWord ++ tailWord_7547427).sum := by decide
  have hdescent : baseEnd_7547427 < baseStart_7547427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547440 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_7547440 : Nat := 118140960795 + 7547440 * 2 ^ 59
def prefixEnd_7547440 : Nat := 4983230072969 + 3 ^ 40 * 7547440 * 2
def baseEnd_7547440 : Nat := 1291821476990018613329987

theorem tailTrace_7547440 : CollatzResearch.WordTrace tailWord_7547440 prefixEnd_7547440 1291821476990018613329987 := by
  unfold tailWord_7547440
  simp only [CollatzResearch.WordTrace]
  refine ⟨137638875888460677487283887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183518501184614236649711849 137638875888460677487283887)
  ·
    refine ⟨206458313832691016230925831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137638875888460677487283887 206458313832691016230925831)
    ·
      refine ⟨309687470749036524346388747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206458313832691016230925831 309687470749036524346388747)
      ·
        refine ⟨464531206123554786519583121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309687470749036524346388747 464531206123554786519583121)
        ·
          refine ⟨348398404592666089889687341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464531206123554786519583121 348398404592666089889687341)
          ·
            refine ⟨130649401722249783708632753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348398404592666089889687341 130649401722249783708632753)
            ·
              refine ⟨97987051291687337781474565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130649401722249783708632753 97987051291687337781474565)
              ·
                refine ⟨18372572117191375834026481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97987051291687337781474565 18372572117191375834026481)
                ·
                  refine ⟨13779429087893531875519861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18372572117191375834026481 13779429087893531875519861)
                  ·
                    refine ⟨1291821476990018613329987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13779429087893531875519861 1291821476990018613329987)
                    ·
                      rfl

theorem cell23_7547440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_7547440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547440 prefixEnd_7547440 := by exact prefixLift 7547440
  have htrace : WordTrace (prefixWord ++ tailWord_7547440) baseStart_7547440 baseEnd_7547440 := by
    simpa [prefixWord, tailWord_7547440, baseEnd_7547440] using wordTrace_append hprefix tailTrace_7547440
  have hstable : (prefixWord ++ tailWord_7547440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547440).length < 2 ^ (prefixWord ++ tailWord_7547440).sum := by decide
  have hdescent : baseEnd_7547440 < baseStart_7547440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547477 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7547477 : Nat := 118140960795 + 7547477 * 2 ^ 59
def prefixEnd_7547477 : Nat := 4983230072969 + 3 ^ 40 * 7547477 * 2
def baseEnd_7547477 : Nat := 3875483429754272195227291

theorem tailTrace_7547477 : CollatzResearch.WordTrace tailWord_7547477 prefixEnd_7547477 3875483429754272195227291 := by
  unfold tailWord_7547477
  simp only [CollatzResearch.WordTrace]
  refine ⟨275279101277787310293664685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183519400851858206862443123 275279101277787310293664685)
  ·
    refine ⟨103229662979170241360124257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275279101277787310293664685 103229662979170241360124257)
    ·
      refine ⟨77422247234377681020093193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103229662979170241360124257 77422247234377681020093193)
      ·
        refine ⟨58066685425783260765069895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77422247234377681020093193 58066685425783260765069895)
        ·
          refine ⟨87100028138674891147604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58066685425783260765069895 87100028138674891147604843)
          ·
            refine ⟨130650042208012336721407265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87100028138674891147604843 130650042208012336721407265)
            ·
              refine ⟨97987531656009252541055449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130650042208012336721407265 97987531656009252541055449)
              ·
                refine ⟨73490648742006939405791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97987531656009252541055449 73490648742006939405791587)
                ·
                  refine ⟨110235973113010409108687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73490648742006939405791587 110235973113010409108687381)
                  ·
                    refine ⟨5167311239672362926969721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110235973113010409108687381 5167311239672362926969721)
                    ·
                      refine ⟨3875483429754272195227291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167311239672362926969721 3875483429754272195227291)
                      ·
                        rfl

theorem cell23_7547477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7547477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547477 prefixEnd_7547477 := by exact prefixLift 7547477
  have htrace : WordTrace (prefixWord ++ tailWord_7547477) baseStart_7547477 baseEnd_7547477 := by
    simpa [prefixWord, tailWord_7547477, baseEnd_7547477] using wordTrace_append hprefix tailTrace_7547477
  have hstable : (prefixWord ++ tailWord_7547477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547477).length < 2 ^ (prefixWord ++ tailWord_7547477).sum := by decide
  have hdescent : baseEnd_7547477 < baseStart_7547477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547500 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 8]
def baseStart_7547500 : Nat := 118140960795 + 7547500 * 2 ^ 59
def prefixEnd_7547500 : Nat := 4983230072969 + 3 ^ 40 * 7547500 * 2
def baseEnd_7547500 : Nat := 430610582201036178359965

theorem tailTrace_7547500 : CollatzResearch.WordTrace tailWord_7547500 prefixEnd_7547500 430610582201036178359965 := by
  unfold tailWord_7547500
  simp only [CollatzResearch.WordTrace]
  refine ⟨137639970078351992610875977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183519960104469323481167969 137639970078351992610875977)
  ·
    refine ⟨103229977558763994458156983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137639970078351992610875977 103229977558763994458156983)
    ·
      refine ⟨154844966338145991687235475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103229977558763994458156983 154844966338145991687235475)
      ·
        refine ⟨232267449507218987530853213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154844966338145991687235475 232267449507218987530853213)
        ·
          refine ⟨87100293565207120324069955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232267449507218987530853213 87100293565207120324069955)
          ·
            refine ⟨130650440347810680486104933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87100293565207120324069955 130650440347810680486104933)
            ·
              refine ⟨24496957565214502591144675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130650440347810680486104933 24496957565214502591144675)
              ·
                refine ⟨36745436347821753886717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24496957565214502591144675 36745436347821753886717013)
                ·
                  refine ⟨430610582201036178359965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36745436347821753886717013 430610582201036178359965)
                  ·
                    rfl

theorem cell23_7547500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_7547500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547500 prefixEnd_7547500 := by exact prefixLift 7547500
  have htrace : WordTrace (prefixWord ++ tailWord_7547500) baseStart_7547500 baseEnd_7547500 := by
    simpa [prefixWord, tailWord_7547500, baseEnd_7547500] using wordTrace_append hprefix tailTrace_7547500
  have hstable : (prefixWord ++ tailWord_7547500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547500).length < 2 ^ (prefixWord ++ tailWord_7547500).sum := by decide
  have hdescent : baseEnd_7547500 < baseStart_7547500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547537 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_7547537 : Nat := 118140960795 + 7547537 * 2 ^ 59
def prefixEnd_7547537 : Nat := 4983230072969 + 3 ^ 40 * 7547537 * 2
def baseEnd_7547537 : Nat := 3875514238593541960477015

theorem tailTrace_7547537 : CollatzResearch.WordTrace tailWord_7547537 prefixEnd_7547537 3875514238593541960477015 := by
  unfold tailWord_7547537
  simp only [CollatzResearch.WordTrace]
  refine ⟨275281289657569940540848865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183520859771713293693899243 275281289657569940540848865)
  ·
    refine ⟨206460967243177455405636649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275281289657569940540848865 206460967243177455405636649)
    ·
      refine ⟨154845725432383091554227487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206460967243177455405636649 154845725432383091554227487)
      ·
        refine ⟨232268588148574637331341231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154845725432383091554227487 232268588148574637331341231)
        ·
          refine ⟨348402882222861955997011847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232268588148574637331341231 348402882222861955997011847)
          ·
            refine ⟨522604323334292933995517771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348402882222861955997011847 522604323334292933995517771)
            ·
              refine ⟨783906485001439400993276657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522604323334292933995517771 783906485001439400993276657)
              ·
                refine ⟨587929863751079550744957493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783906485001439400993276657 587929863751079550744957493)
                ·
                  refine ⟨55118424726663707882339765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587929863751079550744957493 55118424726663707882339765)
                  ·
                    refine ⟨5167352318124722613969353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55118424726663707882339765 5167352318124722613969353)
                    ·
                      refine ⟨3875514238593541960477015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167352318124722613969353 3875514238593541960477015)
                      ·
                        rfl

theorem cell23_7547537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_7547537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547537 prefixEnd_7547537 := by exact prefixLift 7547537
  have htrace : WordTrace (prefixWord ++ tailWord_7547537) baseStart_7547537 baseEnd_7547537 := by
    simpa [prefixWord, tailWord_7547537, baseEnd_7547537] using wordTrace_append hprefix tailTrace_7547537
  have hstable : (prefixWord ++ tailWord_7547537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547537).length < 2 ^ (prefixWord ++ tailWord_7547537).sum := by decide
  have hdescent : baseEnd_7547537 < baseStart_7547537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
