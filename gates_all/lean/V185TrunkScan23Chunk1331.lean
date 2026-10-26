import V185TrunkScan23Chunk1330

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7883243 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_7883243 : Nat := 118140960795 + 7883243 * 2 ^ 59
def prefixEnd_7883243 : Nat := 4983230072969 + 3 ^ 40 * 7883243 * 2
def baseEnd_7883243 : Nat := 4047892775191805509208131

theorem tailTrace_7883243 : CollatzResearch.WordTrace tailWord_7883243 prefixEnd_7883243 4047892775191805509208131 := by
  unfold tailWord_7883243
  simp only [CollatzResearch.WordTrace]
  refine ⟨287525493379364436561054383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191683662252909624374036255 287525493379364436561054383)
  ·
    refine ⟨431288240069046654841581575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287525493379364436561054383 431288240069046654841581575)
    ·
      refine ⟨646932360103569982262372363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431288240069046654841581575 646932360103569982262372363)
      ·
        refine ⟨970398540155354973393558545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646932360103569982262372363 970398540155354973393558545)
        ·
          refine ⟨727798905116516230045168909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970398540155354973393558545 727798905116516230045168909)
          ·
            refine ⟨272924589418693586266938341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727798905116516230045168909 272924589418693586266938341)
            ·
              refine ⟨51173360516005047425050939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272924589418693586266938341 51173360516005047425050939)
              ·
                refine ⟨76760040774007571137576409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51173360516005047425050939 76760040774007571137576409)
                ·
                  refine ⟨57570030580505678353182307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76760040774007571137576409 57570030580505678353182307)
                  ·
                    refine ⟨86355045870758517529773461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57570030580505678353182307 86355045870758517529773461)
                    ·
                      refine ⟨4047892775191805509208131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86355045870758517529773461 4047892775191805509208131)
                      ·
                        rfl

theorem cell23_7883243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_7883243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883243 prefixEnd_7883243 := by exact prefixLift 7883243
  have htrace : WordTrace (prefixWord ++ tailWord_7883243) baseStart_7883243 baseEnd_7883243 := by
    simpa [prefixWord, tailWord_7883243, baseEnd_7883243] using wordTrace_append hprefix tailTrace_7883243
  have hstable : (prefixWord ++ tailWord_7883243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883243).length < 2 ^ (prefixWord ++ tailWord_7883243).sum := by decide
  have hdescent : baseEnd_7883243 < baseStart_7883243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883273 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_7883273 : Nat := 118140960795 + 7883273 * 2 ^ 59
def prefixEnd_7883273 : Nat := 4983230072969 + 3 ^ 40 * 7883273 * 2
def baseEnd_7883273 : Nat := 4047908179611440391832993

theorem tailTrace_7883273 : CollatzResearch.WordTrace tailWord_7883273 prefixEnd_7883273 4047908179611440391832993 := by
  unfold tailWord_7883273
  simp only [CollatzResearch.WordTrace]
  refine ⟨287526587569255751684646473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191684391712837167789764315 287526587569255751684646473)
  ·
    refine ⟨215644940676941813763484855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287526587569255751684646473 215644940676941813763484855)
    ·
      refine ⟨323467411015412720645227283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215644940676941813763484855 323467411015412720645227283)
      ·
        refine ⟨485201116523119080967840925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323467411015412720645227283 485201116523119080967840925)
        ·
          refine ⟨181950418696169655362940347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485201116523119080967840925 181950418696169655362940347)
          ·
            refine ⟨272925628044254483044410521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181950418696169655362940347 272925628044254483044410521)
            ·
              refine ⟨204694221033190862283307891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272925628044254483044410521 204694221033190862283307891)
              ·
                refine ⟨307041331549786293424961837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204694221033190862283307891 307041331549786293424961837)
                ·
                  refine ⟨115140499331169860034360689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307041331549786293424961837 115140499331169860034360689)
                  ·
                    refine ⟨86355374498377395025770517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115140499331169860034360689 86355374498377395025770517)
                    ·
                      refine ⟨4047908179611440391832993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86355374498377395025770517 4047908179611440391832993)
                      ·
                        rfl

theorem cell23_7883273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_7883273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883273 prefixEnd_7883273 := by exact prefixLift 7883273
  have htrace : WordTrace (prefixWord ++ tailWord_7883273) baseStart_7883273 baseEnd_7883273 := by
    simpa [prefixWord, tailWord_7883273, baseEnd_7883273] using wordTrace_append hprefix tailTrace_7883273
  have hstable : (prefixWord ++ tailWord_7883273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883273).length < 2 ^ (prefixWord ++ tailWord_7883273).sum := by decide
  have hdescent : baseEnd_7883273 < baseStart_7883273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883284 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7883284 : Nat := 118140960795 + 7883284 * 2 ^ 59
def prefixEnd_7883284 : Nat := 4983230072969 + 3 ^ 40 * 7883284 * 2
def baseEnd_7883284 : Nat := 4047913827898639848795443

theorem tailTrace_7883284 : CollatzResearch.WordTrace tailWord_7883284 prefixEnd_7883284 4047913827898639848795443 := by
  unfold tailWord_7883284
  simp only [CollatzResearch.WordTrace]
  refine ⟨143763494386107950281648453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191684659181477267042197937 143763494386107950281648453)
  ·
    refine ⟨26955655197395240677809085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143763494386107950281648453 26955655197395240677809085)
    ·
      refine ⟨10108370699023215254178407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26955655197395240677809085 10108370699023215254178407)
      ·
        refine ⟨15162556048534822881267611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108370699023215254178407 15162556048534822881267611)
        ·
          refine ⟨22743834072802234321901417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162556048534822881267611 22743834072802234321901417)
          ·
            refine ⟨17057875554601675741426063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22743834072802234321901417 17057875554601675741426063)
            ·
              refine ⟨25586813331902513612139095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057875554601675741426063 25586813331902513612139095)
              ·
                refine ⟨38380219997853770418208643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25586813331902513612139095 38380219997853770418208643)
                ·
                  refine ⟨57570329996780655627312965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38380219997853770418208643 57570329996780655627312965)
                  ·
                    refine ⟨10794436874396372930121181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57570329996780655627312965 10794436874396372930121181)
                    ·
                      refine ⟨4047913827898639848795443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794436874396372930121181 4047913827898639848795443)
                      ·
                        rfl

theorem cell23_7883284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7883284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883284 prefixEnd_7883284 := by exact prefixLift 7883284
  have htrace : WordTrace (prefixWord ++ tailWord_7883284) baseStart_7883284 baseEnd_7883284 := by
    simpa [prefixWord, tailWord_7883284, baseEnd_7883284] using wordTrace_append hprefix tailTrace_7883284
  have hstable : (prefixWord ++ tailWord_7883284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883284).length < 2 ^ (prefixWord ++ tailWord_7883284).sum := by decide
  have hdescent : baseEnd_7883284 < baseStart_7883284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883297 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7883297 : Nat := 118140960795 + 7883297 * 2 ^ 59
def prefixEnd_7883297 : Nat := 4983230072969 + 3 ^ 40 * 7883297 * 2
def baseEnd_7883297 : Nat := 4047920503147148297932883

theorem tailTrace_7883297 : CollatzResearch.WordTrace tailWord_7883297 prefixEnd_7883297 4047920503147148297932883 := by
  unfold tailWord_7883297
  simp only [CollatzResearch.WordTrace]
  refine ⟨287527462921168803783520145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191684975280779202522346763 287527462921168803783520145)
  ·
    refine ⟨215645597190876602837640109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287527462921168803783520145 215645597190876602837640109)
    ·
      refine ⟨80867098946578726064115041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215645597190876602837640109 80867098946578726064115041)
      ·
        refine ⟨60650324209934044548086281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80867098946578726064115041 60650324209934044548086281)
        ·
          refine ⟨45487743157450533411064711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60650324209934044548086281 45487743157450533411064711)
          ·
            refine ⟨68231614736175800116597067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45487743157450533411064711 68231614736175800116597067)
            ·
              refine ⟨102347422104263700174895601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68231614736175800116597067 102347422104263700174895601)
              ·
                refine ⟨76760566578197775131171701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102347422104263700174895601 76760566578197775131171701)
                ·
                  refine ⟨7196303116706041418547347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76760566578197775131171701 7196303116706041418547347)
                  ·
                    refine ⟨10794454675059062127821021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196303116706041418547347 10794454675059062127821021)
                    ·
                      refine ⟨4047920503147148297932883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794454675059062127821021 4047920503147148297932883)
                      ·
                        rfl

theorem cell23_7883297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7883297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883297 prefixEnd_7883297 := by exact prefixLift 7883297
  have htrace : WordTrace (prefixWord ++ tailWord_7883297) baseStart_7883297 baseEnd_7883297 := by
    simpa [prefixWord, tailWord_7883297, baseEnd_7883297] using wordTrace_append hprefix tailTrace_7883297
  have hstable : (prefixWord ++ tailWord_7883297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883297).length < 2 ^ (prefixWord ++ tailWord_7883297).sum := by decide
  have hdescent : baseEnd_7883297 < baseStart_7883297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883304 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 6]
def baseStart_7883304 : Nat := 118140960795 + 7883304 * 2 ^ 59
def prefixEnd_7883304 : Nat := 4983230072969 + 3 ^ 40 * 7883304 * 2
def baseEnd_7883304 : Nat := 449769344167969974505039

theorem tailTrace_7883304 : CollatzResearch.WordTrace tailWord_7883304 prefixEnd_7883304 449769344167969974505039 := by
  unfold tailWord_7883304
  simp only [CollatzResearch.WordTrace]
  refine ⟨143763859116071721989512483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191685145488095629319349977 143763859116071721989512483)
  ·
    refine ⟨215645788674107582984268725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143763859116071721989512483 215645788674107582984268725)
    ·
      refine ⟨20216792688197585904775193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215645788674107582984268725 20216792688197585904775193)
      ·
        refine ⟨15162594516148189428581395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216792688197585904775193 15162594516148189428581395)
        ·
          refine ⟨22743891774222284142872093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162594516148189428581395 22743891774222284142872093)
          ·
            refine ⟨8528959415333356553577035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22743891774222284142872093 8528959415333356553577035)
            ·
              refine ⟨12793439123000034830365553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8528959415333356553577035 12793439123000034830365553)
              ·
                refine ⟨9595079342250026122774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12793439123000034830365553 9595079342250026122774165)
                ·
                  refine ⟨449769344167969974505039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9595079342250026122774165 449769344167969974505039)
                  ·
                    rfl

theorem cell23_7883304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_7883304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883304 prefixEnd_7883304 := by exact prefixLift 7883304
  have htrace : WordTrace (prefixWord ++ tailWord_7883304) baseStart_7883304 baseEnd_7883304 := by
    simpa [prefixWord, tailWord_7883304, baseEnd_7883304] using wordTrace_append hprefix tailTrace_7883304
  have hstable : (prefixWord ++ tailWord_7883304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883304).length < 2 ^ (prefixWord ++ tailWord_7883304).sum := by decide
  have hdescent : baseEnd_7883304 < baseStart_7883304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883307 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 2, 3, 2]
def baseStart_7883307 : Nat := 118140960795 + 7883307 * 2 ^ 59
def prefixEnd_7883307 : Nat := 4983230072969 + 3 ^ 40 * 7883307 * 2
def baseEnd_7883307 : Nat := 4047925637953693258807837

theorem tailTrace_7883307 : CollatzResearch.WordTrace tailWord_7883307 prefixEnd_7883307 4047925637953693258807837 := by
  unfold tailWord_7883307
  simp only [CollatzResearch.WordTrace]
  refine ⟨287527827651132575491384175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191685218434088383660922783 287527827651132575491384175)
  ·
    refine ⟨431291741476698863237076263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287527827651132575491384175 431291741476698863237076263)
    ·
      refine ⟨646937612215048294855614395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431291741476698863237076263 646937612215048294855614395)
      ·
        refine ⟨970406418322572442283421593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646937612215048294855614395 970406418322572442283421593)
        ·
          refine ⟨727804813741929331712566195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970406418322572442283421593 727804813741929331712566195)
          ·
            refine ⟨1091707220612893997568849293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727804813741929331712566195 1091707220612893997568849293)
            ·
              refine ⟨409390207729835249088318485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091707220612893997568849293 409390207729835249088318485)
              ·
                refine ⟨19190165987336027301014929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409390207729835249088318485 19190165987336027301014929)
                ·
                  refine ⟨14392624490502020475761197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19190165987336027301014929 14392624490502020475761197)
                  ·
                    refine ⟨5397234183938257678410449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14392624490502020475761197 5397234183938257678410449)
                    ·
                      refine ⟨4047925637953693258807837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397234183938257678410449 4047925637953693258807837)
                      ·
                        rfl

theorem cell23_7883307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3, 2].length) (baseStart_7883307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883307 prefixEnd_7883307 := by exact prefixLift 7883307
  have htrace : WordTrace (prefixWord ++ tailWord_7883307) baseStart_7883307 baseEnd_7883307 := by
    simpa [prefixWord, tailWord_7883307, baseEnd_7883307] using wordTrace_append hprefix tailTrace_7883307
  have hstable : (prefixWord ++ tailWord_7883307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883307).length < 2 ^ (prefixWord ++ tailWord_7883307).sum := by decide
  have hdescent : baseEnd_7883307 < baseStart_7883307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883340 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_7883340 : Nat := 118140960795 + 7883340 * 2 ^ 59
def prefixEnd_7883340 : Nat := 4983230072969 + 3 ^ 40 * 7883340 * 2
def baseEnd_7883340 : Nat := 4047942582815291629695185

theorem tailTrace_7883340 : CollatzResearch.WordTrace tailWord_7883340 prefixEnd_7883340 4047942582815291629695185 := by
  unfold tailWord_7883340
  simp only [CollatzResearch.WordTrace]
  refine ⟨143764515630006511063667737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191686020840008681418223649 143764515630006511063667737)
  ·
    refine ⟨107823386722504883297750803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143764515630006511063667737 107823386722504883297750803)
    ·
      refine ⟨161735080083757324946626205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107823386722504883297750803 161735080083757324946626205)
      ·
        refine ⟨60650655031408996854984827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161735080083757324946626205 60650655031408996854984827)
        ·
          refine ⟨90975982547113495282477241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60650655031408996854984827 90975982547113495282477241)
          ·
            refine ⟨68231986910335121461857931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90975982547113495282477241 68231986910335121461857931)
            ·
              refine ⟨102347980365502682192786897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68231986910335121461857931 102347980365502682192786897)
              ·
                refine ⟨76760985274127011644590173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102347980365502682192786897 76760985274127011644590173)
                ·
                  refine ⟨28785369477797629366721315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76760985274127011644590173 28785369477797629366721315)
                  ·
                    refine ⟨43178054216696444050081973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28785369477797629366721315 43178054216696444050081973)
                    ·
                      refine ⟨4047942582815291629695185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43178054216696444050081973 4047942582815291629695185)
                      ·
                        rfl

theorem cell23_7883340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_7883340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883340 prefixEnd_7883340 := by exact prefixLift 7883340
  have htrace : WordTrace (prefixWord ++ tailWord_7883340) baseStart_7883340 baseEnd_7883340 := by
    simpa [prefixWord, tailWord_7883340, baseEnd_7883340] using wordTrace_append hprefix tailTrace_7883340
  have hstable : (prefixWord ++ tailWord_7883340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883340).length < 2 ^ (prefixWord ++ tailWord_7883340).sum := by decide
  have hdescent : baseEnd_7883340 < baseStart_7883340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883348 : List Nat := [2, 4, 1, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_7883348 : Nat := 118140960795 + 7883348 * 2 ^ 59
def prefixEnd_7883348 : Nat := 4983230072969 + 3 ^ 40 * 7883348 * 2
def baseEnd_7883348 : Nat := 4047946690660527598395149

theorem tailTrace_7883348 : CollatzResearch.WordTrace tailWord_7883348 prefixEnd_7883348 4047946690660527598395149 := by
  unfold tailWord_7883348
  simp only [CollatzResearch.WordTrace]
  refine ⟨143764661521992019746813349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191686215362656026329084465 143764661521992019746813349)
  ·
    refine ⟨26955874035373503702527503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143764661521992019746813349 26955874035373503702527503)
    ·
      refine ⟨40433811053060255553791255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26955874035373503702527503 40433811053060255553791255)
      ·
        refine ⟨60650716579590383330686883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40433811053060255553791255 60650716579590383330686883)
        ·
          refine ⟨90976074869385574996030325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60650716579590383330686883 90976074869385574996030325)
          ·
            refine ⟨8529007019004897655877843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90976074869385574996030325 8529007019004897655877843)
            ·
              refine ⟨12793510528507346483816765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529007019004897655877843 12793510528507346483816765)
              ·
                refine ⟨4797566448190254931431287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793510528507346483816765 4797566448190254931431287)
                ·
                  refine ⟨7196349672285382397146931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797566448190254931431287 7196349672285382397146931)
                  ·
                    refine ⟨10794524508428073595720397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196349672285382397146931 10794524508428073595720397)
                    ·
                      refine ⟨4047946690660527598395149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794524508428073595720397 4047946690660527598395149)
                      ·
                        rfl

theorem cell23_7883348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_7883348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883348 prefixEnd_7883348 := by exact prefixLift 7883348
  have htrace : WordTrace (prefixWord ++ tailWord_7883348) baseStart_7883348 baseEnd_7883348 := by
    simpa [prefixWord, tailWord_7883348, baseEnd_7883348] using wordTrace_append hprefix tailTrace_7883348
  have hstable : (prefixWord ++ tailWord_7883348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883348).length < 2 ^ (prefixWord ++ tailWord_7883348).sum := by decide
  have hdescent : baseEnd_7883348 < baseStart_7883348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883381 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7883381 : Nat := 118140960795 + 7883381 * 2 ^ 59
def prefixEnd_7883381 : Nat := 4983230072969 + 3 ^ 40 * 7883381 * 2
def baseEnd_7883381 : Nat := 1349321211840708656427499

theorem tailTrace_7883381 : CollatzResearch.WordTrace tailWord_7883381 prefixEnd_7883381 1349321211840708656427499 := by
  unfold tailWord_7883381
  simp only [CollatzResearch.WordTrace]
  refine ⟨287530526652864486129577997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191687017768576324086385331 287530526652864486129577997)
  ·
    refine ⟨107823947494824182298591749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287530526652864486129577997 107823947494824182298591749)
    ·
      refine ⟨20216990155279534180985953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107823947494824182298591749 20216990155279534180985953)
      ·
        refine ⟨15162742616459650635739465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216990155279534180985953 15162742616459650635739465)
        ·
          refine ⟨11372056962344737976804599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15162742616459650635739465 11372056962344737976804599)
          ·
            refine ⟨17058085443517106965206899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372056962344737976804599 17058085443517106965206899)
            ·
              refine ⟨25587128165275660447810349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17058085443517106965206899 25587128165275660447810349)
              ·
                refine ⟨9595173061978372667928881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25587128165275660447810349 9595173061978372667928881)
                ·
                  refine ⟨7196379796483779500946661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595173061978372667928881 7196379796483779500946661)
                  ·
                    refine ⟨1349321211840708656427499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7196379796483779500946661 1349321211840708656427499)
                    ·
                      rfl

theorem cell23_7883381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7883381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883381 prefixEnd_7883381 := by exact prefixLift 7883381
  have htrace : WordTrace (prefixWord ++ tailWord_7883381) baseStart_7883381 baseEnd_7883381 := by
    simpa [prefixWord, tailWord_7883381, baseEnd_7883381] using wordTrace_append hprefix tailTrace_7883381
  have hstable : (prefixWord ++ tailWord_7883381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883381).length < 2 ^ (prefixWord ++ tailWord_7883381).sum := by decide
  have hdescent : baseEnd_7883381 < baseStart_7883381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883387 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 3]
def baseStart_7883387 : Nat := 118140960795 + 7883387 * 2 ^ 59
def prefixEnd_7883387 : Nat := 4983230072969 + 3 ^ 40 * 7883387 * 2
def baseEnd_7883387 : Nat := 4047966716406052945807469

theorem tailTrace_7883387 : CollatzResearch.WordTrace tailWord_7883387 prefixEnd_7883387 4047966716406052945807469 := by
  unfold tailWord_7883387
  simp only [CollatzResearch.WordTrace]
  refine ⟨287530745490842749154296415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191687163660561832769530943 287530745490842749154296415)
  ·
    refine ⟨431296118236264123731444623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287530745490842749154296415 431296118236264123731444623)
    ·
      refine ⟨646944177354396185597166935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431296118236264123731444623 646944177354396185597166935)
      ·
        refine ⟨970416266031594278395750403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646944177354396185597166935 970416266031594278395750403)
        ·
          refine ⟨1455624399047391417593625605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970416266031594278395750403 1455624399047391417593625605)
          ·
            refine ⟨272929574821385890798804801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1455624399047391417593625605 272929574821385890798804801)
            ·
              refine ⟨204697181116039418099103601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272929574821385890798804801 204697181116039418099103601)
              ·
                refine ⟨153522885837029563574327701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204697181116039418099103601 153522885837029563574327701)
                ·
                  refine ⟨7196385273610760792546611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153522885837029563574327701 7196385273610760792546611)
                  ·
                    refine ⟨10794577910416141188819917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196385273610760792546611 10794577910416141188819917)
                    ·
                      refine ⟨4047966716406052945807469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794577910416141188819917 4047966716406052945807469)
                      ·
                        rfl

theorem cell23_7883387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 3].length) (baseStart_7883387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883387 prefixEnd_7883387 := by exact prefixLift 7883387
  have htrace : WordTrace (prefixWord ++ tailWord_7883387) baseStart_7883387 baseEnd_7883387 := by
    simpa [prefixWord, tailWord_7883387, baseEnd_7883387] using wordTrace_append hprefix tailTrace_7883387
  have hstable : (prefixWord ++ tailWord_7883387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883387).length < 2 ^ (prefixWord ++ tailWord_7883387).sum := by decide
  have hdescent : baseEnd_7883387 < baseStart_7883387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883437 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7883437 : Nat := 118140960795 + 7883437 * 2 ^ 59
def prefixEnd_7883437 : Nat := 4983230072969 + 3 ^ 40 * 7883437 * 2
def baseEnd_7883437 : Nat := 1349330796812925916727413

theorem tailTrace_7883437 : CollatzResearch.WordTrace tailWord_7883437 prefixEnd_7883437 1349330796812925916727413 := by
  unfold tailWord_7883437
  simp only [CollatzResearch.WordTrace]
  refine ⟨287532569140661607693616565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191688379427107738462411043 287532569140661607693616565)
  ·
    refine ⟨26956178356937025721276553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287532569140661607693616565 26956178356937025721276553)
    ·
      refine ⟨20217133767702769290957415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956178356937025721276553 20217133767702769290957415)
      ·
        refine ⟨30325700651554153936436123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217133767702769290957415 30325700651554153936436123)
        ·
          refine ⟨45488550977331230904654185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30325700651554153936436123 45488550977331230904654185)
          ·
            refine ⟨34116413232998423178490639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45488550977331230904654185 34116413232998423178490639)
            ·
              refine ⟨51174619849497634767735959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34116413232998423178490639 51174619849497634767735959)
              ·
                refine ⟨76761929774246452151603939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51174619849497634767735959 76761929774246452151603939)
                ·
                  refine ⟨115142894661369678227405909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76761929774246452151603939 115142894661369678227405909)
                  ·
                    refine ⟨1349330796812925916727413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115142894661369678227405909 1349330796812925916727413)
                    ·
                      rfl

theorem cell23_7883437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7883437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883437 prefixEnd_7883437 := by exact prefixLift 7883437
  have htrace : WordTrace (prefixWord ++ tailWord_7883437) baseStart_7883437 baseEnd_7883437 := by
    simpa [prefixWord, tailWord_7883437, baseEnd_7883437] using wordTrace_append hprefix tailTrace_7883437
  have hstable : (prefixWord ++ tailWord_7883437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883437).length < 2 ^ (prefixWord ++ tailWord_7883437).sum := by decide
  have hdescent : baseEnd_7883437 < baseStart_7883437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883438 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7883438 : Nat := 118140960795 + 7883438 * 2 ^ 59
def prefixEnd_7883438 : Nat := 4983230072969 + 3 ^ 40 * 7883438 * 2
def baseEnd_7883438 : Nat := 4047992903919432246269735

theorem tailTrace_7883438 : CollatzResearch.WordTrace tailWord_7883438 prefixEnd_7883438 4047992903919432246269735 := by
  unfold tailWord_7883438
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941575701707248108050371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191688403742438656576268645 35941575701707248108050371)
  ·
    refine ⟨53912363552560872162075557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35941575701707248108050371 53912363552560872162075557)
    ·
      refine ⟨10108568166105163530389167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53912363552560872162075557 10108568166105163530389167)
      ·
        refine ⟨15162852249157745295583751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108568166105163530389167 15162852249157745295583751)
        ·
          refine ⟨22744278373736617943375627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162852249157745295583751 22744278373736617943375627)
          ·
            refine ⟨34116417560604926915063441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22744278373736617943375627 34116417560604926915063441)
            ·
              refine ⟨25587313170453695186297581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34116417560604926915063441 25587313170453695186297581)
              ·
                refine ⟨9595242438920135694861593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25587313170453695186297581 9595242438920135694861593)
                ·
                  refine ⟨7196431829190101771146195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9595242438920135694861593 7196431829190101771146195)
                  ·
                    refine ⟨10794647743785152656719293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7196431829190101771146195 10794647743785152656719293)
                    ·
                      refine ⟨4047992903919432246269735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794647743785152656719293 4047992903919432246269735)
                      ·
                        rfl

theorem cell23_7883438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7883438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883438 prefixEnd_7883438 := by exact prefixLift 7883438
  have htrace : WordTrace (prefixWord ++ tailWord_7883438) baseStart_7883438 baseEnd_7883438 := by
    simpa [prefixWord, tailWord_7883438, baseEnd_7883438] using wordTrace_append hprefix tailTrace_7883438
  have hstable : (prefixWord ++ tailWord_7883438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883438).length < 2 ^ (prefixWord ++ tailWord_7883438).sum := by decide
  have hdescent : baseEnd_7883438 < baseStart_7883438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883484 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 7]
def baseStart_7883484 : Nat := 118140960795 + 7883484 * 2 ^ 59
def prefixEnd_7883484 : Nat := 4983230072969 + 3 ^ 40 * 7883484 * 2
def baseEnd_7883484 : Nat := 449779613781059896254947

theorem tailTrace_7883484 : CollatzResearch.WordTrace tailWord_7883484 prefixEnd_7883484 449779613781059896254947 := by
  unfold tailWord_7883484
  simp only [CollatzResearch.WordTrace]
  refine ⟨143767141685745667360288753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191689522247660889813718337 143767141685745667360288753)
  ·
    refine ⟨107825356264309250520216565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143767141685745667360288753 107825356264309250520216565)
    ·
      refine ⟨10108627149778992236270303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107825356264309250520216565 10108627149778992236270303)
      ·
        refine ⟨15162940724668488354405455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108627149778992236270303 15162940724668488354405455)
        ·
          refine ⟨22744411087002732531608183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162940724668488354405455 22744411087002732531608183)
          ·
            refine ⟨34116616630504098797412275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22744411087002732531608183 34116616630504098797412275)
            ·
              refine ⟨51174924945756148196118413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34116616630504098797412275 51174924945756148196118413)
              ·
                refine ⟨19190596854658555573544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51174924945756148196118413 19190596854658555573544405)
                ·
                  refine ⟨449779613781059896254947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19190596854658555573544405 449779613781059896254947)
                  ·
                    rfl

theorem cell23_7883484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_7883484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883484 prefixEnd_7883484 := by exact prefixLift 7883484
  have htrace : WordTrace (prefixWord ++ tailWord_7883484) baseStart_7883484 baseEnd_7883484 := by
    simpa [prefixWord, tailWord_7883484, baseEnd_7883484] using wordTrace_append hprefix tailTrace_7883484
  have hstable : (prefixWord ++ tailWord_7883484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883484).length < 2 ^ (prefixWord ++ tailWord_7883484).sum := by decide
  have hdescent : baseEnd_7883484 < baseStart_7883484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883517 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_7883517 : Nat := 118140960795 + 7883517 * 2 ^ 59
def prefixEnd_7883517 : Nat := 4983230072969 + 3 ^ 40 * 7883517 * 2
def baseEnd_7883517 : Nat := 4048033468891137437181871

theorem tailTrace_7883517 : CollatzResearch.WordTrace tailWord_7883517 prefixEnd_7883517 4048033468891137437181871 := by
  unfold tailWord_7883517
  simp only [CollatzResearch.WordTrace]
  refine ⟨287535486980371781356528805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191690324653581187571019203 287535486980371781356528805)
  ·
    refine ⟨53912903808819709004349151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287535486980371781356528805 53912903808819709004349151)
    ·
      refine ⟨80869355713229563506523727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53912903808819709004349151 80869355713229563506523727)
      ·
        refine ⟨121304033569844345259785591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80869355713229563506523727 121304033569844345259785591)
        ·
          refine ⟨181956050354766517889678387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121304033569844345259785591 181956050354766517889678387)
          ·
            refine ⟨272934075532149776834517581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181956050354766517889678387 272934075532149776834517581)
            ·
              refine ⟨102350278324556166312944093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272934075532149776834517581 102350278324556166312944093)
              ·
                refine ⟨38381354371708562367354035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102350278324556166312944093 38381354371708562367354035)
                ·
                  refine ⟨57572031557562843551031053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38381354371708562367354035 57572031557562843551031053)
                  ·
                    refine ⟨21589511834086066331636645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57572031557562843551031053 21589511834086066331636645)
                    ·
                      refine ⟨4048033468891137437181871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21589511834086066331636645 4048033468891137437181871)
                      ·
                        rfl

theorem cell23_7883517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_7883517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883517 prefixEnd_7883517 := by exact prefixLift 7883517
  have htrace : WordTrace (prefixWord ++ tailWord_7883517) baseStart_7883517 baseEnd_7883517 := by
    simpa [prefixWord, tailWord_7883517, baseEnd_7883517] using wordTrace_append hprefix tailTrace_7883517
  have hstable : (prefixWord ++ tailWord_7883517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883517).length < 2 ^ (prefixWord ++ tailWord_7883517).sum := by decide
  have hdescent : baseEnd_7883517 < baseStart_7883517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883518 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7883518 : Nat := 118140960795 + 7883518 * 2 ^ 59
def prefixEnd_7883518 : Nat := 4983230072969 + 3 ^ 40 * 7883518 * 2
def baseEnd_7883518 : Nat := 449781553596865770363263

theorem tailTrace_7883518 : CollatzResearch.WordTrace tailWord_7883518 prefixEnd_7883518 449781553596865770363263 := by
  unfold tailWord_7883518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35941940431671019815914401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191690348968912105684876805 35941940431671019815914401)
  ·
    refine ⟨26956455323753264861935801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35941940431671019815914401 26956455323753264861935801)
    ·
      refine ⟨20217341492814948646451851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26956455323753264861935801 20217341492814948646451851)
      ·
        refine ⟨30326012239222422969677777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217341492814948646451851 30326012239222422969677777)
        ·
          refine ⟨22744509179416817227258333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30326012239222422969677777 22744509179416817227258333)
          ·
            refine ⟨8529190942281306460221875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22744509179416817227258333 8529190942281306460221875)
            ·
              refine ⟨12793786413421959690332813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529190942281306460221875 12793786413421959690332813)
              ·
                refine ⟨4797669905033234883874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12793786413421959690332813 4797669905033234883874805)
                ·
                  refine ⟨449781553596865770363263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797669905033234883874805 449781553596865770363263)
                  ·
                    rfl

theorem cell23_7883518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7883518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883518 prefixEnd_7883518 := by exact prefixLift 7883518
  have htrace : WordTrace (prefixWord ++ tailWord_7883518) baseStart_7883518 baseEnd_7883518 := by
    simpa [prefixWord, tailWord_7883518, baseEnd_7883518] using wordTrace_append hprefix tailTrace_7883518
  have hstable : (prefixWord ++ tailWord_7883518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883518).length < 2 ^ (prefixWord ++ tailWord_7883518).sum := by decide
  have hdescent : baseEnd_7883518 < baseStart_7883518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883571 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3]
def baseStart_7883571 : Nat := 118140960795 + 7883571 * 2 ^ 59
def prefixEnd_7883571 : Nat := 4983230072969 + 3 ^ 40 * 7883571 * 2
def baseEnd_7883571 : Nat := 4048061196846480225906623

theorem tailTrace_7883571 : CollatzResearch.WordTrace tailWord_7883571 prefixEnd_7883571 4048061196846480225906623 := by
  unfold tailWord_7883571
  simp only [CollatzResearch.WordTrace]
  refine ⟨287537456522176148578994567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191691637681450765719329711 287537456522176148578994567)
  ·
    refine ⟨431306184783264222868491851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287537456522176148578994567 431306184783264222868491851)
    ·
      refine ⟨646959277174896334302737777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431306184783264222868491851 646959277174896334302737777)
      ·
        refine ⟨485219457881172250727053333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646959277174896334302737777 485219457881172250727053333)
        ·
          refine ⟨22744662088179949252830625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485219457881172250727053333 22744662088179949252830625)
          ·
            refine ⟨17058496566134961939622969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22744662088179949252830625 17058496566134961939622969)
            ·
              refine ⟨12793872424601221454717227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17058496566134961939622969 12793872424601221454717227)
              ·
                refine ⟨19190808636901832182075841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12793872424601221454717227 19190808636901832182075841)
                ·
                  refine ⟨14393106477676374136556881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19190808636901832182075841 14393106477676374136556881)
                  ·
                    refine ⟨10794829858257280602417661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14393106477676374136556881 10794829858257280602417661)
                    ·
                      refine ⟨4048061196846480225906623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10794829858257280602417661 4048061196846480225906623)
                      ·
                        rfl

theorem cell23_7883571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_7883571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883571 prefixEnd_7883571 := by exact prefixLift 7883571
  have htrace : WordTrace (prefixWord ++ tailWord_7883571) baseStart_7883571 baseEnd_7883571 := by
    simpa [prefixWord, tailWord_7883571, baseEnd_7883571] using wordTrace_append hprefix tailTrace_7883571
  have hstable : (prefixWord ++ tailWord_7883571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883571).length < 2 ^ (prefixWord ++ tailWord_7883571).sum := by decide
  have hdescent : baseEnd_7883571 < baseStart_7883571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883634 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_7883634 : Nat := 118140960795 + 7883634 * 2 ^ 59
def prefixEnd_7883634 : Nat := 4983230072969 + 3 ^ 40 * 7883634 * 2
def baseEnd_7883634 : Nat := 1349364515375904493139611

theorem tailTrace_7883634 : CollatzResearch.WordTrace tailWord_7883634 prefixEnd_7883634 1349364515375904493139611 := by
  unfold tailWord_7883634
  simp only [CollatzResearch.WordTrace]
  refine ⟨71884938580236977584634489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191693169547298606892358637 71884938580236977584634489)
  ·
    refine ⟨53913703935177733188475867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71884938580236977584634489 53913703935177733188475867)
    ·
      refine ⟨80870555902766599782713801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53913703935177733188475867 80870555902766599782713801)
      ·
        refine ⟨60652916927074949837035351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80870555902766599782713801 60652916927074949837035351)
        ·
          refine ⟨90979375390612424755553027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60652916927074949837035351 90979375390612424755553027)
          ·
            refine ⟨136469063085918637133329541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90979375390612424755553027 136469063085918637133329541)
            ·
              refine ⟨25587949328609744462499289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136469063085918637133329541 25587949328609744462499289)
              ·
                refine ⟨19190961996457308346874467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25587949328609744462499289 19190961996457308346874467)
                ·
                  refine ⟨28786442994685962520311701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19190961996457308346874467 28786442994685962520311701)
                  ·
                    refine ⟨1349364515375904493139611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28786442994685962520311701 1349364515375904493139611)
                    ·
                      rfl

theorem cell23_7883634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_7883634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883634 prefixEnd_7883634 := by exact prefixLift 7883634
  have htrace : WordTrace (prefixWord ++ tailWord_7883634) baseStart_7883634 baseEnd_7883634 := by
    simpa [prefixWord, tailWord_7883634, baseEnd_7883634] using wordTrace_append hprefix tailTrace_7883634
  have hstable : (prefixWord ++ tailWord_7883634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883634).length < 2 ^ (prefixWord ++ tailWord_7883634).sum := by decide
  have hdescent : baseEnd_7883634 < baseStart_7883634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883638 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_7883638 : Nat := 118140960795 + 7883638 * 2 ^ 59
def prefixEnd_7883638 : Nat := 4983230072969 + 3 ^ 40 * 7883638 * 2
def baseEnd_7883638 : Nat := 1349365200016777154589605

theorem tailTrace_7883638 : CollatzResearch.WordTrace tailWord_7883638 prefixEnd_7883638 1349365200016777154589605 := by
  unfold tailWord_7883638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971243763308338688855223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191693266808622279347789045 17971243763308338688855223)
  ·
    refine ⟨26956865644962508033282835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17971243763308338688855223 26956865644962508033282835)
    ·
      refine ⟨40435298467443762049924253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26956865644962508033282835 40435298467443762049924253)
      ·
        refine ⟨15163236925291410768721595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40435298467443762049924253 15163236925291410768721595)
        ·
          refine ⟨22744855387937116153082393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163236925291410768721595 22744855387937116153082393)
          ·
            refine ⟨17058641540952837114811795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22744855387937116153082393 17058641540952837114811795)
            ·
              refine ⟨25587962311429255672217693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17058641540952837114811795 25587962311429255672217693)
              ·
                refine ⟨9595485866785970877081635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25587962311429255672217693 9595485866785970877081635)
                ·
                  refine ⟨14393228800178956315622453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595485866785970877081635 14393228800178956315622453)
                  ·
                    refine ⟨1349365200016777154589605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14393228800178956315622453 1349365200016777154589605)
                    ·
                      rfl

theorem cell23_7883638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_7883638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883638 prefixEnd_7883638 := by exact prefixLift 7883638
  have htrace : WordTrace (prefixWord ++ tailWord_7883638) baseStart_7883638 baseEnd_7883638 := by
    simpa [prefixWord, tailWord_7883638, baseEnd_7883638] using wordTrace_append hprefix tailTrace_7883638
  have hstable : (prefixWord ++ tailWord_7883638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883638).length < 2 ^ (prefixWord ++ tailWord_7883638).sum := by decide
  have hdescent : baseEnd_7883638 < baseStart_7883638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883641 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_7883641 : Nat := 118140960795 + 7883641 * 2 ^ 59
def prefixEnd_7883641 : Nat := 4983230072969 + 3 ^ 40 * 7883641 * 2
def baseEnd_7883641 : Nat := 4048097140492294952031301

theorem tailTrace_7883641 : CollatzResearch.WordTrace tailWord_7883641 prefixEnd_7883641 4048097140492294952031301 := by
  unfold tailWord_7883641
  simp only [CollatzResearch.WordTrace]
  refine ⟨287540009631922550534042777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191693339754615033689361851 287540009631922550534042777)
  ·
    refine ⟨215655007223941912900532083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287540009631922550534042777 215655007223941912900532083)
    ·
      refine ⟨323482510835912869350798125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215655007223941912900532083 323482510835912869350798125)
      ·
        refine ⟨121305941563467326006549297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323482510835912869350798125 121305941563467326006549297)
        ·
          refine ⟨90979456172600494504911973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121305941563467326006549297 90979456172600494504911973)
          ·
            refine ⟨17058648032362592719670995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90979456172600494504911973 17058648032362592719670995)
            ·
              refine ⟨25587972048543889079506493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17058648032362592719670995 25587972048543889079506493)
              ·
                refine ⟨9595489518203958404814935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25587972048543889079506493 9595489518203958404814935)
                ·
                  refine ⟨14393234277305937607222403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595489518203958404814935 14393234277305937607222403)
                  ·
                    refine ⟨21589851415958906410833605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14393234277305937607222403 21589851415958906410833605)
                    ·
                      refine ⟨4048097140492294952031301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21589851415958906410833605 4048097140492294952031301)
                      ·
                        rfl

theorem cell23_7883641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_7883641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883641 prefixEnd_7883641 := by exact prefixLift 7883641
  have htrace : WordTrace (prefixWord ++ tailWord_7883641) baseStart_7883641 baseEnd_7883641 := by
    simpa [prefixWord, tailWord_7883641, baseEnd_7883641] using wordTrace_append hprefix tailTrace_7883641
  have hstable : (prefixWord ++ tailWord_7883641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883641).length < 2 ^ (prefixWord ++ tailWord_7883641).sum := by decide
  have hdescent : baseEnd_7883641 < baseStart_7883641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_7883667 : Nat := 118140960795 + 7883667 * 2 ^ 59
def prefixEnd_7883667 : Nat := 4983230072969 + 3 ^ 40 * 7883667 * 2
def baseEnd_7883667 : Nat := 4048110490989311850306181

theorem tailTrace_7883667 : CollatzResearch.WordTrace tailWord_7883667 prefixEnd_7883667 4048110490989311850306181 := by
  unfold tailWord_7883667
  simp only [CollatzResearch.WordTrace]
  refine ⟨287540957929828356974489255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191693971953218904649659503 287540957929828356974489255)
  ·
    refine ⟨431311436894742535461733883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287540957929828356974489255 431311436894742535461733883)
    ·
      refine ⟨646967155342113803192600825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431311436894742535461733883 646967155342113803192600825)
      ·
        refine ⟨485225366506585352394450619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646967155342113803192600825 485225366506585352394450619)
        ·
          refine ⟨727838049759878028591675929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485225366506585352394450619 727838049759878028591675929)
          ·
            refine ⟨545878537319908521443756947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727838049759878028591675929 545878537319908521443756947)
            ·
              refine ⟨818817805979862782165635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545878537319908521443756947 818817805979862782165635421)
              ·
                refine ⟨307056677242448543312113283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818817805979862782165635421 307056677242448543312113283)
                ·
                  refine ⟨460585015863672814968169925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307056677242448543312113283 460585015863672814968169925)
                  ·
                    refine ⟨86359690474438652806531861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460585015863672814968169925 86359690474438652806531861)
                    ·
                      refine ⟨4048110490989311850306181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86359690474438652806531861 4048110490989311850306181)
                      ·
                        rfl

theorem cell23_7883667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_7883667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883667 prefixEnd_7883667 := by exact prefixLift 7883667
  have htrace : WordTrace (prefixWord ++ tailWord_7883667) baseStart_7883667 baseEnd_7883667 := by
    simpa [prefixWord, tailWord_7883667, baseEnd_7883667] using wordTrace_append hprefix tailTrace_7883667
  have hstable : (prefixWord ++ tailWord_7883667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883667).length < 2 ^ (prefixWord ++ tailWord_7883667).sum := by decide
  have hdescent : baseEnd_7883667 < baseStart_7883667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883681 : List Nat := [1, 2, 3, 4, 1, 1, 4, 7]
def baseStart_7883681 : Nat := 118140960795 + 7883681 * 2 ^ 59
def prefixEnd_7883681 : Nat := 4983230072969 + 3 ^ 40 * 7883681 * 2
def baseEnd_7883681 : Nat := 149930284434017585019671

theorem tailTrace_7883681 : CollatzResearch.WordTrace tailWord_7883681 prefixEnd_7883681 149930284434017585019671 := by
  unfold tailWord_7883681
  simp only [CollatzResearch.WordTrace]
  refine ⟨287541468551777637365498897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191694312367851758243665931 287541468551777637365498897)
  ·
    refine ⟨215656101413833228024124173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287541468551777637365498897 215656101413833228024124173)
    ·
      refine ⟨80871038030187460509046565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215656101413833228024124173 80871038030187460509046565)
      ·
        refine ⟨15163319630660148845446231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80871038030187460509046565 15163319630660148845446231)
        ·
          refine ⟨22744979445990223268169347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163319630660148845446231 22744979445990223268169347)
          ·
            refine ⟨34117469168985334902254021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22744979445990223268169347 34117469168985334902254021)
            ·
              refine ⟨6397025469184750294172629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34117469168985334902254021 6397025469184750294172629)
              ·
                refine ⟨149930284434017585019671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6397025469184750294172629 149930284434017585019671)
                ·
                  rfl

theorem cell23_7883681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 7].length) (baseStart_7883681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883681 prefixEnd_7883681 := by exact prefixLift 7883681
  have htrace : WordTrace (prefixWord ++ tailWord_7883681) baseStart_7883681 baseEnd_7883681 := by
    simpa [prefixWord, tailWord_7883681, baseEnd_7883681] using wordTrace_append hprefix tailTrace_7883681
  have hstable : (prefixWord ++ tailWord_7883681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883681).length < 2 ^ (prefixWord ++ tailWord_7883681).sum := by decide
  have hdescent : baseEnd_7883681 < baseStart_7883681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883709 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7883709 : Nat := 118140960795 + 7883709 * 2 ^ 59
def prefixEnd_7883709 : Nat := 4983230072969 + 3 ^ 40 * 7883709 * 2
def baseEnd_7883709 : Nat := 4048132057176800685980989

theorem tailTrace_7883709 : CollatzResearch.WordTrace tailWord_7883709 prefixEnd_7883709 4048132057176800685980989 := by
  unfold tailWord_7883709
  simp only [CollatzResearch.WordTrace]
  refine ⟨287542489795676198147518181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191694993197117465431678787 287542489795676198147518181)
  ·
    refine ⟨53914216836689287152659659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287542489795676198147518181 53914216836689287152659659)
    ·
      refine ⟨80871325255033930728989489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53914216836689287152659659 80871325255033930728989489)
      ·
        refine ⟨60653493941275448046742117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80871325255033930728989489 60653493941275448046742117)
        ·
          refine ⟨11372530113989146508764147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60653493941275448046742117 11372530113989146508764147)
          ·
            refine ⟨17058795170983719763146221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372530113989146508764147 17058795170983719763146221)
            ·
              refine ⟨6397048189118894911179833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17058795170983719763146221 6397048189118894911179833)
              ·
                refine ⟨4797786141839171183384875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397048189118894911179833 4797786141839171183384875)
                ·
                  refine ⟨7196679212758756775077313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797786141839171183384875 7196679212758756775077313)
                  ·
                    refine ⟨5397509409569067581307985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196679212758756775077313 5397509409569067581307985)
                    ·
                      refine ⟨4048132057176800685980989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397509409569067581307985 4048132057176800685980989)
                      ·
                        rfl

theorem cell23_7883709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7883709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883709 prefixEnd_7883709 := by exact prefixLift 7883709
  have htrace : WordTrace (prefixWord ++ tailWord_7883709) baseStart_7883709 baseEnd_7883709 := by
    simpa [prefixWord, tailWord_7883709, baseEnd_7883709] using wordTrace_append hprefix tailTrace_7883709
  have hstable : (prefixWord ++ tailWord_7883709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883709).length < 2 ^ (prefixWord ++ tailWord_7883709).sum := by decide
  have hdescent : baseEnd_7883709 < baseStart_7883709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883724 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_7883724 : Nat := 118140960795 + 7883724 * 2 ^ 59
def prefixEnd_7883724 : Nat := 4983230072969 + 3 ^ 40 * 7883724 * 2
def baseEnd_7883724 : Nat := 1349379919795539375764473

theorem tailTrace_7883724 : CollatzResearch.WordTrace tailWord_7883724 prefixEnd_7883724 1349379919795539375764473 := by
  unfold tailWord_7883724
  simp only [CollatzResearch.WordTrace]
  refine ⟨143771518445310927854657113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191695357927081237139542817 143771518445310927854657113)
  ·
    refine ⟨107828638833983195890992835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143771518445310927854657113 107828638833983195890992835)
    ·
      refine ⟨161742958250974793836489253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107828638833983195890992835 161742958250974793836489253)
      ·
        refine ⟨30326804672057773844341735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161742958250974793836489253 30326804672057773844341735)
        ·
          refine ⟨45490207008086660766512603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30326804672057773844341735 45490207008086660766512603)
          ·
            refine ⟨68235310512129991149768905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45490207008086660766512603 68235310512129991149768905)
            ·
              refine ⟨51176482884097493362326679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68235310512129991149768905 51176482884097493362326679)
              ·
                refine ⟨76764724326146240043490019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51176482884097493362326679 76764724326146240043490019)
                ·
                  refine ⟨115147086489219360065235029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76764724326146240043490019 115147086489219360065235029)
                  ·
                    refine ⟨1349379919795539375764473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115147086489219360065235029 1349379919795539375764473)
                    ·
                      rfl

theorem cell23_7883724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_7883724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883724 prefixEnd_7883724 := by exact prefixLift 7883724
  have htrace : WordTrace (prefixWord ++ tailWord_7883724) baseStart_7883724 baseEnd_7883724 := by
    simpa [prefixWord, tailWord_7883724, baseEnd_7883724] using wordTrace_append hprefix tailTrace_7883724
  have hstable : (prefixWord ++ tailWord_7883724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883724).length < 2 ^ (prefixWord ++ tailWord_7883724).sum := by decide
  have hdescent : baseEnd_7883724 < baseStart_7883724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883744 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_7883744 : Nat := 118140960795 + 7883744 * 2 ^ 59
def prefixEnd_7883744 : Nat := 4983230072969 + 3 ^ 40 * 7883744 * 2
def baseEnd_7883744 : Nat := 4048150028999708049043327

theorem tailTrace_7883744 : CollatzResearch.WordTrace tailWord_7883744 prefixEnd_7883744 4048150028999708049043327 := by
  unfold tailWord_7883744
  simp only [CollatzResearch.WordTrace]
  refine ⟨143771883175274699562521143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191695844233699599416694857 143771883175274699562521143)
  ·
    refine ⟨215657824762912049343781715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143771883175274699562521143 215657824762912049343781715)
    ·
      refine ⟨323486737144368074015672573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215657824762912049343781715 323486737144368074015672573)
      ·
        refine ⟨121307526429138027755877215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323486737144368074015672573 121307526429138027755877215)
        ·
          refine ⟨181961289643707041633815823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121307526429138027755877215 181961289643707041633815823)
          ·
            refine ⟨272941934465560562450723735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181961289643707041633815823 272941934465560562450723735)
            ·
              refine ⟨409412901698340843676085603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272941934465560562450723735 409412901698340843676085603)
              ·
                refine ⟨614119352547511265514128405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409412901698340843676085603 614119352547511265514128405)
                ·
                  refine ⟨28786844650664590570974769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 614119352547511265514128405 28786844650664590570974769)
                  ·
                    refine ⟨21590133487998442928231077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28786844650664590570974769 21590133487998442928231077)
                    ·
                      refine ⟨4048150028999708049043327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21590133487998442928231077 4048150028999708049043327)
                      ·
                        rfl

theorem cell23_7883744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_7883744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883744 prefixEnd_7883744 := by exact prefixLift 7883744
  have htrace : WordTrace (prefixWord ++ tailWord_7883744) baseStart_7883744 baseEnd_7883744 := by
    simpa [prefixWord, tailWord_7883744, baseEnd_7883744] using wordTrace_append hprefix tailTrace_7883744
  have hstable : (prefixWord ++ tailWord_7883744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883744).length < 2 ^ (prefixWord ++ tailWord_7883744).sum := by decide
  have hdescent : baseEnd_7883744 < baseStart_7883744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883748 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_7883748 : Nat := 118140960795 + 7883748 * 2 ^ 59
def prefixEnd_7883748 : Nat := 4983230072969 + 3 ^ 40 * 7883748 * 2
def baseEnd_7883748 : Nat := 4048152082922326033393309

theorem tailTrace_7883748 : CollatzResearch.WordTrace tailWord_7883748 prefixEnd_7883748 4048152082922326033393309 := by
  unfold tailWord_7883748
  simp only [CollatzResearch.WordTrace]
  refine ⟨143771956121267453904093949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191695941495023271872125265 143771956121267453904093949)
  ·
    refine ⟨53914483545475295214035231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143771956121267453904093949 53914483545475295214035231)
    ·
      refine ⟨80871725318212942821052847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53914483545475295214035231 80871725318212942821052847)
      ·
        refine ⟨121307587977319414231579271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80871725318212942821052847 121307587977319414231579271)
        ·
          refine ⟨181961381965979121347368907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121307587977319414231579271 181961381965979121347368907)
          ·
            refine ⟨272942072948968682021053361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181961381965979121347368907 272942072948968682021053361)
            ·
              refine ⟨204706554711726511515790021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272942072948968682021053361 204706554711726511515790021)
              ·
                refine ⟨38382479008448720909210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204706554711726511515790021 38382479008448720909210629)
                ·
                  refine ⟨7196714814084135170476993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38382479008448720909210629 7196714814084135170476993)
                  ·
                    refine ⟨5397536110563101377857745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7196714814084135170476993 5397536110563101377857745)
                    ·
                      refine ⟨4048152082922326033393309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397536110563101377857745 4048152082922326033393309)
                      ·
                        rfl

theorem cell23_7883748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_7883748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883748 prefixEnd_7883748 := by exact prefixLift 7883748
  have htrace : WordTrace (prefixWord ++ tailWord_7883748) baseStart_7883748 baseEnd_7883748 := by
    simpa [prefixWord, tailWord_7883748, baseEnd_7883748] using wordTrace_append hprefix tailTrace_7883748
  have hstable : (prefixWord ++ tailWord_7883748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883748).length < 2 ^ (prefixWord ++ tailWord_7883748).sum := by decide
  have hdescent : baseEnd_7883748 < baseStart_7883748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883751 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7883751 : Nat := 118140960795 + 7883751 * 2 ^ 59
def prefixEnd_7883751 : Nat := 4983230072969 + 3 ^ 40 * 7883751 * 2
def baseEnd_7883751 : Nat := 4048153623364289521655795

theorem tailTrace_7883751 : CollatzResearch.WordTrace tailWord_7883751 prefixEnd_7883751 4048153623364289521655795 := by
  unfold tailWord_7883751
  simp only [CollatzResearch.WordTrace]
  refine ⟨287544021661524039320547107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191696014441016026213698071 287544021661524039320547107)
  ·
    refine ⟨431316032492286058980820661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287544021661524039320547107 431316032492286058980820661)
    ·
      refine ⟨40435878046151818029451937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 431316032492286058980820661 40435878046151818029451937)
      ·
        refine ⟨30326908534613863522088953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40435878046151818029451937 30326908534613863522088953)
        ·
          refine ⟨22745181400960397641566715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30326908534613863522088953 22745181400960397641566715)
          ·
            refine ⟨34117772101440596462350073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22745181400960397641566715 34117772101440596462350073)
            ·
              refine ⟨25588329076080447346762555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34117772101440596462350073 25588329076080447346762555)
              ·
                refine ⟨38382493614120671020143833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588329076080447346762555 38382493614120671020143833)
                ·
                  refine ⟨28786870210590503265107875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38382493614120671020143833 28786870210590503265107875)
                  ·
                    refine ⟨43180305315885754897661813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28786870210590503265107875 43180305315885754897661813)
                    ·
                      refine ⟨4048153623364289521655795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43180305315885754897661813 4048153623364289521655795)
                      ·
                        rfl

theorem cell23_7883751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7883751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883751 prefixEnd_7883751 := by exact prefixLift 7883751
  have htrace : WordTrace (prefixWord ++ tailWord_7883751) baseStart_7883751 baseEnd_7883751 := by
    simpa [prefixWord, tailWord_7883751, baseEnd_7883751] using wordTrace_append hprefix tailTrace_7883751
  have hstable : (prefixWord ++ tailWord_7883751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883751).length < 2 ^ (prefixWord ++ tailWord_7883751).sum := by decide
  have hdescent : baseEnd_7883751 < baseStart_7883751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883781 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_7883781 : Nat := 118140960795 + 7883781 * 2 ^ 59
def prefixEnd_7883781 : Nat := 4983230072969 + 3 ^ 40 * 7883781 * 2
def baseEnd_7883781 : Nat := 4048169027783924404280657

theorem tailTrace_7883781 : CollatzResearch.WordTrace tailWord_7883781 prefixEnd_7883781 4048169027783924404280657 := by
  unfold tailWord_7883781
  simp only [CollatzResearch.WordTrace]
  refine ⟨287545115851415354444139197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191696743900943569629426131 287545115851415354444139197)
  ·
    refine ⟨107829418444280757916552199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287545115851415354444139197 107829418444280757916552199)
    ·
      refine ⟨161744127666421136874828299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107829418444280757916552199 161744127666421136874828299)
      ·
        refine ⟨242616191499631705312242449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161744127666421136874828299 242616191499631705312242449)
        ·
          refine ⟨181962143624723778984181837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242616191499631705312242449 181962143624723778984181837)
          ·
            refine ⟨68235803859271417119068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181962143624723778984181837 68235803859271417119068189)
            ·
              refine ⟨25588426447226781419650571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68235803859271417119068189 25588426447226781419650571)
              ·
                refine ⟨38382639670840172129475857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588426447226781419650571 38382639670840172129475857)
                ·
                  refine ⟨28786979753130129097106893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38382639670840172129475857 28786979753130129097106893)
                  ·
                    refine ⟨10795117407423798411415085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28786979753130129097106893 10795117407423798411415085)
                    ·
                      refine ⟨4048169027783924404280657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10795117407423798411415085 4048169027783924404280657)
                      ·
                        rfl

theorem cell23_7883781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_7883781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883781 prefixEnd_7883781 := by exact prefixLift 7883781
  have htrace : WordTrace (prefixWord ++ tailWord_7883781) baseStart_7883781 baseEnd_7883781 := by
    simpa [prefixWord, tailWord_7883781, baseEnd_7883781] using wordTrace_append hprefix tailTrace_7883781
  have hstable : (prefixWord ++ tailWord_7883781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883781).length < 2 ^ (prefixWord ++ tailWord_7883781).sum := by decide
  have hdescent : baseEnd_7883781 < baseStart_7883781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883801 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_7883801 : Nat := 118140960795 + 7883801 * 2 ^ 59
def prefixEnd_7883801 : Nat := 4983230072969 + 3 ^ 40 * 7883801 * 2
def baseEnd_7883801 : Nat := 1349393099132338108676855

theorem tailTrace_7883801 : CollatzResearch.WordTrace tailWord_7883801 prefixEnd_7883801 1349393099132338108676855 := by
  unfold tailWord_7883801
  simp only [CollatzResearch.WordTrace]
  refine ⟨287545845311342897859867257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191697230207561931906578171 287545845311342897859867257)
  ·
    refine ⟨215659383983507173394900443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287545845311342897859867257 215659383983507173394900443)
    ·
      refine ⟨323489075975260760092350665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215659383983507173394900443 323489075975260760092350665)
      ·
        refine ⟨242616806981445570069262999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323489075975260760092350665 242616806981445570069262999)
        ·
          refine ⟨363925210472168355103894499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242616806981445570069262999 363925210472168355103894499)
          ·
            refine ⟨545887815708252532655841749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363925210472168355103894499 545887815708252532655841749)
            ·
              refine ⟨12794245680662168734121291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 545887815708252532655841749 12794245680662168734121291)
              ·
                refine ⟨19191368520993253101181937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12794245680662168734121291 19191368520993253101181937)
                ·
                  refine ⟨14393526390744939825886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19191368520993253101181937 14393526390744939825886453)
                  ·
                    refine ⟨1349393099132338108676855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14393526390744939825886453 1349393099132338108676855)
                    ·
                      rfl

theorem cell23_7883801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_7883801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883801 prefixEnd_7883801 := by exact prefixLift 7883801
  have htrace : WordTrace (prefixWord ++ tailWord_7883801) baseStart_7883801 baseEnd_7883801 := by
    simpa [prefixWord, tailWord_7883801, baseEnd_7883801] using wordTrace_append hprefix tailTrace_7883801
  have hstable : (prefixWord ++ tailWord_7883801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883801).length < 2 ^ (prefixWord ++ tailWord_7883801).sum := by decide
  have hdescent : baseEnd_7883801 < baseStart_7883801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883805 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 5]
def baseStart_7883805 : Nat := 118140960795 + 7883805 * 2 ^ 59
def prefixEnd_7883805 : Nat := 4983230072969 + 3 ^ 40 * 7883805 * 2
def baseEnd_7883805 : Nat := 449797927924403590042283

theorem tailTrace_7883805 : CollatzResearch.WordTrace tailWord_7883805 prefixEnd_7883805 449797927924403590042283 := by
  unfold tailWord_7883805
  simp only [CollatzResearch.WordTrace]
  refine ⟨287545991203328406543012869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191697327468885604362008579 287545991203328406543012869)
  ·
    refine ⟨53914873350624076226814913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287545991203328406543012869 53914873350624076226814913)
    ·
      refine ⟨40436155012968057170111185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53914873350624076226814913 40436155012968057170111185)
      ·
        refine ⟨30327116259726042877583389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40436155012968057170111185 30327116259726042877583389)
        ·
          refine ⟨11372668597397266079093771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30327116259726042877583389 11372668597397266079093771)
          ·
            refine ⟨17059002896095899118640657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372668597397266079093771 17059002896095899118640657)
            ·
              refine ⟨12794252172071924338980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17059002896095899118640657 12794252172071924338980493)
              ·
                refine ⟨4797844564526971627117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12794252172071924338980493 4797844564526971627117685)
                ·
                  refine ⟨449797927924403590042283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797844564526971627117685 449797927924403590042283)
                  ·
                    rfl

theorem cell23_7883805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_7883805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883805 prefixEnd_7883805 := by exact prefixLift 7883805
  have htrace : WordTrace (prefixWord ++ tailWord_7883805) baseStart_7883805 baseEnd_7883805 := by
    simpa [prefixWord, tailWord_7883805, baseEnd_7883805] using wordTrace_append hprefix tailTrace_7883805
  have hstable : (prefixWord ++ tailWord_7883805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883805).length < 2 ^ (prefixWord ++ tailWord_7883805).sum := by decide
  have hdescent : baseEnd_7883805 < baseStart_7883805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883838 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7883838 : Nat := 118140960795 + 7883838 * 2 ^ 59
def prefixEnd_7883838 : Nat := 4983230072969 + 3 ^ 40 * 7883838 * 2
def baseEnd_7883838 : Nat := 4048198296181230681267895

theorem tailTrace_7883838 : CollatzResearch.WordTrace tailWord_7883838 prefixEnd_7883838 4048198296181230681267895 := by
  unfold tailWord_7883838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35943399351526106647370521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191698129874805902119309445 35943399351526106647370521)
  ·
    refine ⟨26957549513644579985527891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35943399351526106647370521 26957549513644579985527891)
    ·
      refine ⟨40436324270466869978291837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26957549513644579985527891 40436324270466869978291837)
      ·
        refine ⟨15163621601425076241859439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40436324270466869978291837 15163621601425076241859439)
        ·
          refine ⟨22745432402137614362789159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163621601425076241859439 22745432402137614362789159)
          ·
            refine ⟨34118148603206421544183739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22745432402137614362789159 34118148603206421544183739)
            ·
              refine ⟨51177222904809632316275609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34118148603206421544183739 51177222904809632316275609)
              ·
                refine ⟨38382917178607224237206707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51177222904809632316275609 38382917178607224237206707)
                ·
                  refine ⟨57574375767910836355810061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38382917178607224237206707 57574375767910836355810061)
                  ·
                    refine ⟨21590390912966563633428773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57574375767910836355810061 21590390912966563633428773)
                    ·
                      refine ⟨4048198296181230681267895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21590390912966563633428773 4048198296181230681267895)
                      ·
                        rfl

theorem cell23_7883838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7883838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883838 prefixEnd_7883838 := by exact prefixLift 7883838
  have htrace : WordTrace (prefixWord ++ tailWord_7883838) baseStart_7883838 baseEnd_7883838 := by
    simpa [prefixWord, tailWord_7883838, baseEnd_7883838] using wordTrace_append hprefix tailTrace_7883838
  have hstable : (prefixWord ++ tailWord_7883838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883838).length < 2 ^ (prefixWord ++ tailWord_7883838).sum := by decide
  have hdescent : baseEnd_7883838 < baseStart_7883838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883858 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_7883858 : Nat := 118140960795 + 7883858 * 2 ^ 59
def prefixEnd_7883858 : Nat := 4983230072969 + 3 ^ 40 * 7883858 * 2
def baseEnd_7883858 : Nat := 4048208565794320603017803

theorem tailTrace_7883858 : CollatzResearch.WordTrace tailWord_7883858 prefixEnd_7883858 4048208565794320603017803 := by
  unfold tailWord_7883858
  simp only [CollatzResearch.WordTrace]
  refine ⟨71886981068034099148673057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191698616181424264396461485 71886981068034099148673057)
  ·
    refine ⟨53915235801025574361504793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71886981068034099148673057 53915235801025574361504793)
    ·
      refine ⟨40436426850769180771128595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53915235801025574361504793 40436426850769180771128595)
      ·
        refine ⟨60654640276153771156692893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40436426850769180771128595 60654640276153771156692893)
        ·
          refine ⟨22745490103557664183759835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60654640276153771156692893 22745490103557664183759835)
          ·
            refine ⟨34118235155336496275639753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22745490103557664183759835 34118235155336496275639753)
            ·
              refine ⟨25588676366502372206729815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34118235155336496275639753 25588676366502372206729815)
              ·
                refine ⟨38383014549753558310094723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588676366502372206729815 38383014549753558310094723)
                ·
                  refine ⟨57574521824630337465142085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38383014549753558310094723 57574521824630337465142085)
                  ·
                    refine ⟨10795222842118188274714141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57574521824630337465142085 10795222842118188274714141)
                    ·
                      refine ⟨4048208565794320603017803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10795222842118188274714141 4048208565794320603017803)
                      ·
                        rfl

theorem cell23_7883858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_7883858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883858 prefixEnd_7883858 := by exact prefixLift 7883858
  have htrace : WordTrace (prefixWord ++ tailWord_7883858) baseStart_7883858 baseEnd_7883858 := by
    simpa [prefixWord, tailWord_7883858, baseEnd_7883858] using wordTrace_append hprefix tailTrace_7883858
  have hstable : (prefixWord ++ tailWord_7883858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883858).length < 2 ^ (prefixWord ++ tailWord_7883858).sum := by decide
  have hdescent : baseEnd_7883858 < baseStart_7883858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883908 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7883908 : Nat := 118140960795 + 7883908 * 2 ^ 59
def prefixEnd_7883908 : Nat := 4983230072969 + 3 ^ 40 * 7883908 * 2
def baseEnd_7883908 : Nat := 1349411413275681802464191

theorem tailTrace_7883908 : CollatzResearch.WordTrace tailWord_7883908 prefixEnd_7883908 1349411413275681802464191 := by
  unfold tailWord_7883908
  simp only [CollatzResearch.WordTrace]
  refine ⟨143774873960977627567006189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191699831947970170089341585 143774873960977627567006189)
  ·
    refine ⟨53915577735366610337627321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143774873960977627567006189 53915577735366610337627321)
    ·
      refine ⟨40436683301524957753220491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53915577735366610337627321 40436683301524957753220491)
      ·
        refine ⟨60655024952287436629830737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40436683301524957753220491 60655024952287436629830737)
        ·
          refine ⟨45491268714215577472373053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60655024952287436629830737 45491268714215577472373053)
          ·
            refine ⟨17059225767830841552139895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45491268714215577472373053 17059225767830841552139895)
            ·
              refine ⟨25588838651746262328209843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059225767830841552139895 25588838651746262328209843)
              ·
                refine ⟨38383257977619393492314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25588838651746262328209843 38383257977619393492314765)
                ·
                  refine ⟨14393721741607272559618037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38383257977619393492314765 14393721741607272559618037)
                  ·
                    refine ⟨1349411413275681802464191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14393721741607272559618037 1349411413275681802464191)
                    ·
                      rfl

theorem cell23_7883908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7883908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883908 prefixEnd_7883908 := by exact prefixLift 7883908
  have htrace : WordTrace (prefixWord ++ tailWord_7883908) baseStart_7883908 baseEnd_7883908 := by
    simpa [prefixWord, tailWord_7883908, baseEnd_7883908] using wordTrace_append hprefix tailTrace_7883908
  have hstable : (prefixWord ++ tailWord_7883908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883908).length < 2 ^ (prefixWord ++ tailWord_7883908).sum := by decide
  have hdescent : baseEnd_7883908 < baseStart_7883908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883951 : List Nat := [1, 1, 2, 1, 2, 3, 5, 8]
def baseStart_7883951 : Nat := 118140960795 + 7883951 * 2 ^ 59
def prefixEnd_7883951 : Nat := 4983230072969 + 3 ^ 40 * 7883951 * 2
def baseEnd_7883951 : Nat := 149935419240562545894625

theorem tailTrace_7883951 : CollatzResearch.WordTrace tailWord_7883951 prefixEnd_7883951 149935419240562545894625 := by
  unfold tailWord_7883951
  simp only [CollatzResearch.WordTrace]
  refine ⟨287551316260799473477827707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191700877507199648985218471 287551316260799473477827707)
  ·
    refine ⟨431326974391199210216741561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287551316260799473477827707 431326974391199210216741561)
    ·
      refine ⟨323495230793399407662556171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431326974391199210216741561 323495230793399407662556171)
      ·
        refine ⟨485242846190099111493834257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323495230793399407662556171 485242846190099111493834257)
        ·
          refine ⟨363932134642574333620375693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485242846190099111493834257 363932134642574333620375693)
          ·
            refine ⟨136474550490965375107640885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363932134642574333620375693 136474550490965375107640885)
            ·
              refine ⟨12794489108528003916341333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136474550490965375107640885 12794489108528003916341333)
              ·
                refine ⟨149935419240562545894625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12794489108528003916341333 149935419240562545894625)
                ·
                  rfl

theorem cell23_7883951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 8].length) (baseStart_7883951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883951 prefixEnd_7883951 := by exact prefixLift 7883951
  have htrace : WordTrace (prefixWord ++ tailWord_7883951) baseStart_7883951 baseEnd_7883951 := by
    simpa [prefixWord, tailWord_7883951, baseEnd_7883951] using wordTrace_append hprefix tailTrace_7883951
  have hstable : (prefixWord ++ tailWord_7883951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883951).length < 2 ^ (prefixWord ++ tailWord_7883951).sum := by decide
  have hdescent : baseEnd_7883951 < baseStart_7883951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7883982 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_7883982 : Nat := 118140960795 + 7883982 * 2 ^ 59
def prefixEnd_7883982 : Nat := 4983230072969 + 3 ^ 40 * 7883982 * 2
def baseEnd_7883982 : Nat := 4048272237395478117867233

theorem tailTrace_7883982 : CollatzResearch.WordTrace tailWord_7883982 prefixEnd_7883982 4048272237395478117867233 := by
  unfold tailWord_7883982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35944055865460895721525775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191701631282458110514804133 35944055865460895721525775)
  ·
    refine ⟨53916083798191343582288663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35944055865460895721525775 53916083798191343582288663)
    ·
      refine ⟨80874125697287015373432995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53916083798191343582288663 80874125697287015373432995)
      ·
        refine ⟨121311188545930523060149493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80874125697287015373432995 121311188545930523060149493)
        ·
          refine ⟨11372923926180986536889015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121311188545930523060149493 11372923926180986536889015)
          ·
            refine ⟨17059385889271479805333523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372923926180986536889015 17059385889271479805333523)
            ·
              refine ⟨25589078833907219708000285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059385889271479805333523 25589078833907219708000285)
              ·
                refine ⟨9595904562715207390500107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25589078833907219708000285 9595904562715207390500107)
                ·
                  refine ⟨14393856844072811085750161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9595904562715207390500107 14393856844072811085750161)
                  ·
                    refine ⟨10795392633054608314312621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14393856844072811085750161 10795392633054608314312621)
                    ·
                      refine ⟨4048272237395478117867233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10795392633054608314312621 4048272237395478117867233)
                      ·
                        rfl

theorem cell23_7883982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_7883982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7883982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7883982 prefixEnd_7883982 := by exact prefixLift 7883982
  have htrace : WordTrace (prefixWord ++ tailWord_7883982) baseStart_7883982 baseEnd_7883982 := by
    simpa [prefixWord, tailWord_7883982, baseEnd_7883982] using wordTrace_append hprefix tailTrace_7883982
  have hstable : (prefixWord ++ tailWord_7883982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7883982).length < 2 ^ (prefixWord ++ tailWord_7883982).sum := by decide
  have hdescent : baseEnd_7883982 < baseStart_7883982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7883982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884069 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_7884069 : Nat := 118140960795 + 7884069 * 2 ^ 59
def prefixEnd_7884069 : Nat := 4983230072969 + 3 ^ 40 * 7884069 * 2
def baseEnd_7884069 : Nat := 4048316910212419277479333

theorem tailTrace_7884069 : CollatzResearch.WordTrace tailWord_7884069 prefixEnd_7884069 4048316910212419277479333 := by
  unfold tailWord_7884069
  simp only [CollatzResearch.WordTrace]
  refine ⟨287555620074371979630623261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191703746716247986420415507 287555620074371979630623261)
  ·
    refine ⟨107833357527889492361483723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287555620074371979630623261 107833357527889492361483723)
    ·
      refine ⟨161750036291834238542225585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107833357527889492361483723 161750036291834238542225585)
      ·
        refine ⟨121312527218875678906669189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161750036291834238542225585 121312527218875678906669189)
        ·
          refine ⟨22746098853539189795000473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121312527218875678906669189 22746098853539189795000473)
          ·
            refine ⟨17059574140154392346250355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22746098853539189795000473 17059574140154392346250355)
            ·
              refine ⟨25589361210231588519375533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059574140154392346250355 25589361210231588519375533)
              ·
                refine ⟨9596010453836845694765825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25589361210231588519375533 9596010453836845694765825)
                ·
                  refine ⟨7197007840377634271074369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596010453836845694765825 7197007840377634271074369)
                  ·
                    refine ⟨5397755880283225703305777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197007840377634271074369 5397755880283225703305777)
                    ·
                      refine ⟨4048316910212419277479333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397755880283225703305777 4048316910212419277479333)
                      ·
                        rfl

theorem cell23_7884069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_7884069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884069 prefixEnd_7884069 := by exact prefixLift 7884069
  have htrace : WordTrace (prefixWord ++ tailWord_7884069) baseStart_7884069 baseEnd_7884069 := by
    simpa [prefixWord, tailWord_7884069, baseEnd_7884069] using wordTrace_append hprefix tailTrace_7884069
  have hstable : (prefixWord ++ tailWord_7884069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884069).length < 2 ^ (prefixWord ++ tailWord_7884069).sum := by decide
  have hdescent : baseEnd_7884069 < baseStart_7884069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884086 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7884086 : Nat := 118140960795 + 7884086 * 2 ^ 59
def prefixEnd_7884086 : Nat := 4983230072969 + 3 ^ 40 * 7884086 * 2
def baseEnd_7884086 : Nat := 4048325639383545710966755

theorem tailTrace_7884086 : CollatzResearch.WordTrace tailWord_7884086 prefixEnd_7884086 4048325639383545710966755 := by
  unfold tailWord_7884086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972265007206899470874507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191704160076873594355994741 17972265007206899470874507)
  ·
    refine ⟨26958397510810349206311761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17972265007206899470874507 26958397510810349206311761)
    ·
      refine ⟨20218798133107761904733821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26958397510810349206311761 20218798133107761904733821)
      ·
        refine ⟨7582049299915410714275183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20218798133107761904733821 7582049299915410714275183)
        ·
          refine ⟨11373073949873116071412775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582049299915410714275183 11373073949873116071412775)
          ·
            refine ⟨17059610924809674107119163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373073949873116071412775 17059610924809674107119163)
            ·
              refine ⟨25589416387214511160678745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17059610924809674107119163 25589416387214511160678745)
              ·
                refine ⟨19192062290410883370509059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25589416387214511160678745 19192062290410883370509059)
                ·
                  refine ⟨28788093435616325055763589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19192062290410883370509059 28788093435616325055763589)
                  ·
                    refine ⟨5397767519178060947955673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28788093435616325055763589 5397767519178060947955673)
                    ·
                      refine ⟨4048325639383545710966755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397767519178060947955673 4048325639383545710966755)
                      ·
                        rfl

theorem cell23_7884086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7884086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884086 prefixEnd_7884086 := by exact prefixLift 7884086
  have htrace : WordTrace (prefixWord ++ tailWord_7884086) baseStart_7884086 baseEnd_7884086 := by
    simpa [prefixWord, tailWord_7884086, baseEnd_7884086] using wordTrace_append hprefix tailTrace_7884086
  have hstable : (prefixWord ++ tailWord_7884086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884086).length < 2 ^ (prefixWord ++ tailWord_7884086).sum := by decide
  have hdescent : baseEnd_7884086 < baseStart_7884086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884165 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 6]
def baseStart_7884165 : Nat := 118140960795 + 7884165 * 2 ^ 59
def prefixEnd_7884165 : Nat := 4983230072969 + 3 ^ 40 * 7884165 * 2
def baseEnd_7884165 : Nat := 449818467150583433542099

theorem tailTrace_7884165 : CollatzResearch.WordTrace tailWord_7884165 prefixEnd_7884165 449818467150583433542099 := by
  unfold tailWord_7884165
  simp only [CollatzResearch.WordTrace]
  refine ⟨287559121482024188026117949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191706080988016125350745299 287559121482024188026117949)
  ·
    refine ⟨107834670555759070509794231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287559121482024188026117949 107834670555759070509794231)
    ·
      refine ⟨161752005833638605764691347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107834670555759070509794231 161752005833638605764691347)
      ·
        refine ⟨242628008750457908647037021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161752005833638605764691347 242628008750457908647037021)
        ·
          refine ⟨90985503281421715742638883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242628008750457908647037021 90985503281421715742638883)
          ·
            refine ⟨136478254922132573613958325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90985503281421715742638883 136478254922132573613958325)
            ·
              refine ⟨12794836398949928776308593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136478254922132573613958325 12794836398949928776308593)
              ·
                refine ⟨9596127299212446582231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12794836398949928776308593 9596127299212446582231445)
                ·
                  refine ⟨449818467150583433542099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9596127299212446582231445 449818467150583433542099)
                  ·
                    rfl

theorem cell23_7884165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_7884165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884165 prefixEnd_7884165 := by exact prefixLift 7884165
  have htrace : WordTrace (prefixWord ++ tailWord_7884165) baseStart_7884165 baseEnd_7884165 := by
    simpa [prefixWord, tailWord_7884165, baseEnd_7884165] using wordTrace_append hprefix tailTrace_7884165
  have hstable : (prefixWord ++ tailWord_7884165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884165).length < 2 ^ (prefixWord ++ tailWord_7884165).sum := by decide
  have hdescent : baseEnd_7884165 < baseStart_7884165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884192 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_7884192 : Nat := 118140960795 + 7884192 * 2 ^ 59
def prefixEnd_7884192 : Nat := 4983230072969 + 3 ^ 40 * 7884192 * 2
def baseEnd_7884192 : Nat := 4048380068332922296241267

theorem tailTrace_7884192 : CollatzResearch.WordTrace tailWord_7884192 prefixEnd_7884192 4048380068332922296241267 := by
  unfold tailWord_7884192
  simp only [CollatzResearch.WordTrace]
  refine ⟨143780053126463185818675415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191706737501950914424900553 143780053126463185818675415)
  ·
    refine ⟨215670079689694778728013123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143780053126463185818675415 215670079689694778728013123)
    ·
      refine ⟨323505119534542168092019685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215670079689694778728013123 323505119534542168092019685)
      ·
        refine ⟨60657209912726656517253691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323505119534542168092019685 60657209912726656517253691)
        ·
          refine ⟨90985814869089984775880537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60657209912726656517253691 90985814869089984775880537)
          ·
            refine ⟨68239361151817488581910403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90985814869089984775880537 68239361151817488581910403)
            ·
              refine ⟨102359041727726232872865605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68239361151817488581910403 102359041727726232872865605)
              ·
                refine ⟨19192320323948668663662301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102359041727726232872865605 19192320323948668663662301)
                ·
                  refine ⟨7197120121480750748873363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19192320323948668663662301 7197120121480750748873363)
                  ·
                    refine ⟨10795680182221126123310045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197120121480750748873363 10795680182221126123310045)
                    ·
                      refine ⟨4048380068332922296241267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10795680182221126123310045 4048380068332922296241267)
                      ·
                        rfl

theorem cell23_7884192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_7884192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884192 prefixEnd_7884192 := by exact prefixLift 7884192
  have htrace : WordTrace (prefixWord ++ tailWord_7884192) baseStart_7884192 baseEnd_7884192 := by
    simpa [prefixWord, tailWord_7884192, baseEnd_7884192] using wordTrace_append hprefix tailTrace_7884192
  have hstable : (prefixWord ++ tailWord_7884192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884192).length < 2 ^ (prefixWord ++ tailWord_7884192).sum := by decide
  have hdescent : baseEnd_7884192 < baseStart_7884192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884235 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_7884235 : Nat := 118140960795 + 7884235 * 2 ^ 59
def prefixEnd_7884235 : Nat := 4983230072969 + 3 ^ 40 * 7884235 * 2
def baseEnd_7884235 : Nat := 4048402148001065628003569

theorem tailTrace_7884235 : CollatzResearch.WordTrace tailWord_7884235 prefixEnd_7884235 4048402148001065628003569 := by
  unfold tailWord_7884235
  simp only [CollatzResearch.WordTrace]
  refine ⟨287561674591770589981166159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191707783061180393320777439 287561674591770589981166159)
  ·
    refine ⟨431342511887655884971749239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287561674591770589981166159 431342511887655884971749239)
    ·
      refine ⟨647013767831483827457623859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431342511887655884971749239 647013767831483827457623859)
      ·
        refine ⟨970520651747225741186435789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647013767831483827457623859 970520651747225741186435789)
        ·
          refine ⟨363945244405209652944913421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 970520651747225741186435789 363945244405209652944913421)
          ·
            refine ⟨136479466651953619854342533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363945244405209652944913421 136479466651953619854342533)
            ·
              refine ⟨25589899997241303722689225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136479466651953619854342533 25589899997241303722689225)
              ·
                refine ⟨19192424997930977792016919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25589899997241303722689225 19192424997930977792016919)
                ·
                  refine ⟨28788637496896466688025379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19192424997930977792016919 28788637496896466688025379)
                  ·
                    refine ⟨43182956245344700032038069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28788637496896466688025379 43182956245344700032038069)
                    ·
                      refine ⟨4048402148001065628003569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43182956245344700032038069 4048402148001065628003569)
                      ·
                        rfl

theorem cell23_7884235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_7884235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884235 prefixEnd_7884235 := by exact prefixLift 7884235
  have htrace : WordTrace (prefixWord ++ tailWord_7884235) baseStart_7884235 baseEnd_7884235 := by
    simpa [prefixWord, tailWord_7884235, baseEnd_7884235] using wordTrace_append hprefix tailTrace_7884235
  have hstable : (prefixWord ++ tailWord_7884235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884235).length < 2 ^ (prefixWord ++ tailWord_7884235).sum := by decide
  have hdescent : baseEnd_7884235 < baseStart_7884235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884245 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7884245 : Nat := 118140960795 + 7884245 * 2 ^ 59
def prefixEnd_7884245 : Nat := 4983230072969 + 3 ^ 40 * 7884245 * 2
def baseEnd_7884245 : Nat := 4048407282807610588878523

theorem tailTrace_7884245 : CollatzResearch.WordTrace tailWord_7884245 prefixEnd_7884245 4048407282807610588878523 := by
  unfold tailWord_7884245
  simp only [CollatzResearch.WordTrace]
  refine ⟨287562039321734361689030189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191708026214489574459353459 287562039321734361689030189)
  ·
    refine ⟨107835764745650385633386321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287562039321734361689030189 107835764745650385633386321)
    ·
      refine ⟨80876823559237789225039741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107835764745650385633386321 80876823559237789225039741)
      ·
        refine ⟨30328808834714170959389903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80876823559237789225039741 30328808834714170959389903)
        ·
          refine ⟨45493213252071256439084855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30328808834714170959389903 45493213252071256439084855)
          ·
            refine ⟨68239819878106884658627283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45493213252071256439084855 68239819878106884658627283)
            ·
              refine ⟨102359729817160326987940925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68239819878106884658627283 102359729817160326987940925)
              ·
                refine ⟨38384898681435122620477847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102359729817160326987940925 38384898681435122620477847)
                ·
                  refine ⟨57577348022152683930716771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38384898681435122620477847 57577348022152683930716771)
                  ·
                    refine ⟨86366022033229025896075157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57577348022152683930716771 86366022033229025896075157)
                    ·
                      refine ⟨4048407282807610588878523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86366022033229025896075157 4048407282807610588878523)
                      ·
                        rfl

theorem cell23_7884245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7884245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884245 prefixEnd_7884245 := by exact prefixLift 7884245
  have htrace : WordTrace (prefixWord ++ tailWord_7884245) baseStart_7884245 baseEnd_7884245 := by
    simpa [prefixWord, tailWord_7884245, baseEnd_7884245] using wordTrace_append hprefix tailTrace_7884245
  have hstable : (prefixWord ++ tailWord_7884245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884245).length < 2 ^ (prefixWord ++ tailWord_7884245).sum := by decide
  have hdescent : baseEnd_7884245 < baseStart_7884245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884246 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7884246 : Nat := 118140960795 + 7884246 * 2 ^ 59
def prefixEnd_7884246 : Nat := 4983230072969 + 3 ^ 40 * 7884246 * 2
def baseEnd_7884246 : Nat := 1349469265429421694988673

theorem tailTrace_7884246 : CollatzResearch.WordTrace tailWord_7884246 prefixEnd_7884246 1349469265429421694988673 := by
  unfold tailWord_7884246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972629737170671178738537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191708050529820492573211061 17972629737170671178738537)
  ·
    refine ⟨13479472302878003384053903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17972629737170671178738537 13479472302878003384053903)
    ·
      refine ⟨20219208454317005076080855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479472302878003384053903 20219208454317005076080855)
      ·
        refine ⟨30328812681475507614121283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20219208454317005076080855 30328812681475507614121283)
        ·
          refine ⟨45493219022213261421181925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30328812681475507614121283 45493219022213261421181925)
          ·
            refine ⟨8529978566664986516471611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45493219022213261421181925 8529978566664986516471611)
            ·
              refine ⟨12794967849997479774707417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529978566664986516471611 12794967849997479774707417)
              ·
                refine ⟨9596225887498109831030563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12794967849997479774707417 9596225887498109831030563)
                ·
                  refine ⟨14394338831247164746545845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596225887498109831030563 14394338831247164746545845)
                  ·
                    refine ⟨1349469265429421694988673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14394338831247164746545845 1349469265429421694988673)
                    ·
                      rfl

theorem cell23_7884246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7884246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884246 prefixEnd_7884246 := by exact prefixLift 7884246
  have htrace : WordTrace (prefixWord ++ tailWord_7884246) baseStart_7884246 baseEnd_7884246 := by
    simpa [prefixWord, tailWord_7884246, baseEnd_7884246] using wordTrace_append hprefix tailTrace_7884246
  have hstable : (prefixWord ++ tailWord_7884246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884246).length < 2 ^ (prefixWord ++ tailWord_7884246).sum := by decide
  have hdescent : baseEnd_7884246 < baseStart_7884246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884249 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_7884249 : Nat := 118140960795 + 7884249 * 2 ^ 59
def prefixEnd_7884249 : Nat := 4983230072969 + 3 ^ 40 * 7884249 * 2
def baseEnd_7884249 : Nat := 4048409336730228573228505

theorem tailTrace_7884249 : CollatzResearch.WordTrace tailWord_7884249 prefixEnd_7884249 4048409336730228573228505 := by
  unfold tailWord_7884249
  simp only [CollatzResearch.WordTrace]
  refine ⟨287562185213719870372175801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191708123475813246914783867 287562185213719870372175801)
  ·
    refine ⟨215671638910289902779131851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287562185213719870372175801 215671638910289902779131851)
    ·
      refine ⟨323507458365434854168697777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215671638910289902779131851 323507458365434854168697777)
      ·
        refine ⟨242630593774076140626523333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323507458365434854168697777 242630593774076140626523333)
        ·
          refine ⟨45493236332639276367473125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242630593774076140626523333 45493236332639276367473125)
          ·
            refine ⟨8529981812369864318901211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45493236332639276367473125 8529981812369864318901211)
            ·
              refine ⟨12794972718554796478351817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529981812369864318901211 12794972718554796478351817)
              ·
                refine ⟨9596229538916097358763863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12794972718554796478351817 9596229538916097358763863)
                ·
                  refine ⟨14394344308374146038145795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596229538916097358763863 14394344308374146038145795)
                  ·
                    refine ⟨21591516462561219057218693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14394344308374146038145795 21591516462561219057218693)
                    ·
                      refine ⟨4048409336730228573228505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21591516462561219057218693 4048409336730228573228505)
                      ·
                        rfl

theorem cell23_7884249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_7884249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884249 prefixEnd_7884249 := by exact prefixLift 7884249
  have htrace : WordTrace (prefixWord ++ tailWord_7884249) baseStart_7884249 baseEnd_7884249 := by
    simpa [prefixWord, tailWord_7884249, baseEnd_7884249] using wordTrace_append hprefix tailTrace_7884249
  have hstable : (prefixWord ++ tailWord_7884249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884249).length < 2 ^ (prefixWord ++ tailWord_7884249).sum := by decide
  have hdescent : baseEnd_7884249 < baseStart_7884249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884266 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_7884266 : Nat := 118140960795 + 7884266 * 2 ^ 59
def prefixEnd_7884266 : Nat := 4983230072969 + 3 ^ 40 * 7884266 * 2
def baseEnd_7884266 : Nat := 4048418065901355006715927

theorem tailTrace_7884266 : CollatzResearch.WordTrace tailWord_7884266 prefixEnd_7884266 4048418065901355006715927 := by
  unfold tailWord_7884266
  simp only [CollatzResearch.WordTrace]
  refine ⟨71890701313664570568886163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191708536836438854850363101 71890701313664570568886163)
  ·
    refine ⟨107836051970496855853329245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71890701313664570568886163 107836051970496855853329245)
    ·
      refine ⟨40438519488936320944998467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107836051970496855853329245 40438519488936320944998467)
      ·
        refine ⟨60657779233404481417497701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40438519488936320944998467 60657779233404481417497701)
        ·
          refine ⟨11373333606263340265780819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60657779233404481417497701 11373333606263340265780819)
          ·
            refine ⟨17060000409395010398671229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373333606263340265780819 17060000409395010398671229)
            ·
              refine ⟨6397500153523128899501711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17060000409395010398671229 6397500153523128899501711)
              ·
                refine ⟨9596250230284693349252567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397500153523128899501711 9596250230284693349252567)
                ·
                  refine ⟨14394375345427040023878851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596250230284693349252567 14394375345427040023878851)
                  ·
                    refine ⟨21591563018140560035818277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14394375345427040023878851 21591563018140560035818277)
                    ·
                      refine ⟨4048418065901355006715927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21591563018140560035818277 4048418065901355006715927)
                      ·
                        rfl

theorem cell23_7884266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_7884266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884266 prefixEnd_7884266 := by exact prefixLift 7884266
  have htrace : WordTrace (prefixWord ++ tailWord_7884266) baseStart_7884266 baseEnd_7884266 := by
    simpa [prefixWord, tailWord_7884266, baseEnd_7884266] using wordTrace_append hprefix tailTrace_7884266
  have hstable : (prefixWord ++ tailWord_7884266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884266).length < 2 ^ (prefixWord ++ tailWord_7884266).sum := by decide
  have hdescent : baseEnd_7884266 < baseStart_7884266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884285 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7884285 : Nat := 118140960795 + 7884285 * 2 ^ 59
def prefixEnd_7884285 : Nat := 4983230072969 + 3 ^ 40 * 7884285 * 2
def baseEnd_7884285 : Nat := 1349475940677930144126113

theorem tailTrace_7884285 : CollatzResearch.WordTrace tailWord_7884285 prefixEnd_7884285 1349475940677930144126113 := by
  unfold tailWord_7884285
  simp only [CollatzResearch.WordTrace]
  refine ⟨287563498241589448520486309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191708998827726299013657539 287563498241589448520486309)
  ·
    refine ⟨53918155920298021597591183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287563498241589448520486309 53918155920298021597591183)
    ·
      refine ⟨80877233880447032396386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53918155920298021597591183 80877233880447032396386775)
      ·
        refine ⟨121315850820670548594580163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80877233880447032396386775 121315850820670548594580163)
        ·
          refine ⟨181973776231005822891870245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121315850820670548594580163 181973776231005822891870245)
          ·
            refine ⟨34120083043313591792225671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181973776231005822891870245 34120083043313591792225671)
            ·
              refine ⟨51180124564970387688338507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34120083043313591792225671 51180124564970387688338507)
              ·
                refine ⟨76770186847455581532507761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51180124564970387688338507 76770186847455581532507761)
                ·
                  refine ⟨57577640135591686149380821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76770186847455581532507761 57577640135591686149380821)
                  ·
                    refine ⟨1349475940677930144126113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57577640135591686149380821 1349475940677930144126113)
                    ·
                      rfl

theorem cell23_7884285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7884285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884285 prefixEnd_7884285 := by exact prefixLift 7884285
  have htrace : WordTrace (prefixWord ++ tailWord_7884285) baseStart_7884285 baseEnd_7884285 := by
    simpa [prefixWord, tailWord_7884285, baseEnd_7884285] using wordTrace_append hprefix tailTrace_7884285
  have hstable : (prefixWord ++ tailWord_7884285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884285).length < 2 ^ (prefixWord ++ tailWord_7884285).sum := by decide
  have hdescent : baseEnd_7884285 < baseStart_7884285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884289 : List Nat := [1, 2, 4, 1, 5, 1, 1, 8]
def baseStart_7884289 : Nat := 118140960795 + 7884289 * 2 ^ 59
def prefixEnd_7884289 : Nat := 4983230072969 + 3 ^ 40 * 7884289 * 2
def baseEnd_7884289 : Nat := 149941847257644756175123

theorem tailTrace_7884289 : CollatzResearch.WordTrace tailWord_7884289 prefixEnd_7884289 149941847257644756175123 := by
  unfold tailWord_7884289
  simp only [CollatzResearch.WordTrace]
  refine ⟨287563644133574957203631921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191709096089049971469087947 287563644133574957203631921)
  ·
    refine ⟨215672733100181217902723941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287563644133574957203631921 215672733100181217902723941)
    ·
      refine ⟨40438637456283978356760739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215672733100181217902723941 40438637456283978356760739)
      ·
        refine ⟨60657956184425967535141109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40438637456283978356760739 60657956184425967535141109)
        ·
          refine ⟨5686683392289934456419479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60657956184425967535141109 5686683392289934456419479)
          ·
            refine ⟨8530025088434901684629219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686683392289934456419479 8530025088434901684629219)
            ·
              refine ⟨12795037632652352526943829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530025088434901684629219 12795037632652352526943829)
              ·
                refine ⟨149941847257644756175123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12795037632652352526943829 149941847257644756175123)
                ·
                  rfl

theorem cell23_7884289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 8].length) (baseStart_7884289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884289 prefixEnd_7884289 := by exact prefixLift 7884289
  have htrace : WordTrace (prefixWord ++ tailWord_7884289) baseStart_7884289 baseEnd_7884289 := by
    simpa [prefixWord, tailWord_7884289, baseEnd_7884289] using wordTrace_append hprefix tailTrace_7884289
  have hstable : (prefixWord ++ tailWord_7884289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884289).length < 2 ^ (prefixWord ++ tailWord_7884289).sum := by decide
  have hdescent : baseEnd_7884289 < baseStart_7884289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884299 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3]
def baseStart_7884299 : Nat := 118140960795 + 7884299 * 2 ^ 59
def prefixEnd_7884299 : Nat := 4983230072969 + 3 ^ 40 * 7884299 * 2
def baseEnd_7884299 : Nat := 4048435010762953377603275

theorem tailTrace_7884299 : CollatzResearch.WordTrace tailWord_7884299 prefixEnd_7884299 4048435010762953377603275 := by
  unfold tailWord_7884299
  simp only [CollatzResearch.WordTrace]
  refine ⟨287564008863538728911495951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191709339242359152607663967 287564008863538728911495951)
  ·
    refine ⟨431346013295308093367243927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287564008863538728911495951 431346013295308093367243927)
    ·
      refine ⟨647019019942962140050865891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431346013295308093367243927 647019019942962140050865891)
      ·
        refine ⟨970528529914443210076298837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647019019942962140050865891 970528529914443210076298837)
        ·
          refine ⟨11373381209934881368081627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 970528529914443210076298837 11373381209934881368081627)
          ·
            refine ⟨17060071814902322052122441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373381209934881368081627 17060071814902322052122441)
            ·
              refine ⟨12795053861176741539091831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17060071814902322052122441 12795053861176741539091831)
              ·
                refine ⟨19192580791765112308637747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795053861176741539091831 19192580791765112308637747)
                ·
                  refine ⟨28788871187647668462956621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19192580791765112308637747 28788871187647668462956621)
                  ·
                    refine ⟨10795826695367875673608733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28788871187647668462956621 10795826695367875673608733)
                    ·
                      refine ⟨4048435010762953377603275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10795826695367875673608733 4048435010762953377603275)
                      ·
                        rfl

theorem cell23_7884299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].length) (baseStart_7884299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884299 prefixEnd_7884299 := by exact prefixLift 7884299
  have htrace : WordTrace (prefixWord ++ tailWord_7884299) baseStart_7884299 baseEnd_7884299 := by
    simpa [prefixWord, tailWord_7884299, baseEnd_7884299] using wordTrace_append hprefix tailTrace_7884299
  have hstable : (prefixWord ++ tailWord_7884299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884299).length < 2 ^ (prefixWord ++ tailWord_7884299).sum := by decide
  have hdescent : baseEnd_7884299 < baseStart_7884299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884305 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_7884305 : Nat := 118140960795 + 7884305 * 2 ^ 59
def prefixEnd_7884305 : Nat := 4983230072969 + 3 ^ 40 * 7884305 * 2
def baseEnd_7884305 : Nat := 4048438091646880354128247

theorem tailTrace_7884305 : CollatzResearch.WordTrace tailWord_7884305 prefixEnd_7884305 4048438091646880354128247 := by
  unfold tailWord_7884305
  simp only [CollatzResearch.WordTrace]
  refine ⟨287564227701516991936214369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191709485134344661290809579 287564227701516991936214369)
  ·
    refine ⟨215673170776137743952160777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287564227701516991936214369 215673170776137743952160777)
    ·
      refine ⟨161754878082103307964120583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215673170776137743952160777 161754878082103307964120583)
      ·
        refine ⟨242632317123154961946180875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161754878082103307964120583 242632317123154961946180875)
        ·
          refine ⟨363948475684732442919271313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242632317123154961946180875 363948475684732442919271313)
          ·
            refine ⟨272961356763549332189453485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363948475684732442919271313 272961356763549332189453485)
            ·
              refine ⟨102360508786330999571045057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272961356763549332189453485 102360508786330999571045057)
              ·
                refine ⟨76770381589748249678283793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102360508786330999571045057 76770381589748249678283793)
                ·
                  refine ⟨57577786192311187258712845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76770381589748249678283793 57577786192311187258712845)
                  ·
                    refine ⟨21591669822116695222017317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57577786192311187258712845 21591669822116695222017317)
                    ·
                      refine ⟨4048438091646880354128247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21591669822116695222017317 4048438091646880354128247)
                      ·
                        rfl

theorem cell23_7884305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_7884305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884305 prefixEnd_7884305 := by exact prefixLift 7884305
  have htrace : WordTrace (prefixWord ++ tailWord_7884305) baseStart_7884305 baseEnd_7884305 := by
    simpa [prefixWord, tailWord_7884305, baseEnd_7884305] using wordTrace_append hprefix tailTrace_7884305
  have hstable : (prefixWord ++ tailWord_7884305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884305).length < 2 ^ (prefixWord ++ tailWord_7884305).sum := by decide
  have hdescent : baseEnd_7884305 < baseStart_7884305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884309 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_7884309 : Nat := 118140960795 + 7884309 * 2 ^ 59
def prefixEnd_7884309 : Nat := 4983230072969 + 3 ^ 40 * 7884309 * 2
def baseEnd_7884309 : Nat := 4048440145569498338478229

theorem tailTrace_7884309 : CollatzResearch.WordTrace tailWord_7884309 prefixEnd_7884309 4048440145569498338478229 := by
  unfold tailWord_7884309
  simp only [CollatzResearch.WordTrace]
  refine ⟨287564373593502500619359981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191709582395668333746239987 287564373593502500619359981)
  ·
    refine ⟨107836640097563437732259993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287564373593502500619359981 107836640097563437732259993)
    ·
      refine ⟨80877480073172578299194995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107836640097563437732259993 80877480073172578299194995)
      ·
        refine ⟨121316220109758867448792493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80877480073172578299194995 121316220109758867448792493)
        ·
          refine ⟨45493582541159575293297185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121316220109758867448792493 45493582541159575293297185)
          ·
            refine ⟨34120186905869681469972889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45493582541159575293297185 34120186905869681469972889)
            ·
              refine ⟨25590140179402261102479667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34120186905869681469972889 25590140179402261102479667)
              ·
                refine ⟨38385210269103391653719501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25590140179402261102479667 38385210269103391653719501)
                ·
                  refine ⟨14394453850913771870144813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38385210269103391653719501 14394453850913771870144813)
                  ·
                    refine ⟨5397920194092664451304305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14394453850913771870144813 5397920194092664451304305)
                    ·
                      refine ⟨4048440145569498338478229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5397920194092664451304305 4048440145569498338478229)
                      ·
                        rfl

theorem cell23_7884309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_7884309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884309 prefixEnd_7884309 := by exact prefixLift 7884309
  have htrace : WordTrace (prefixWord ++ tailWord_7884309) baseStart_7884309 baseEnd_7884309 := by
    simpa [prefixWord, tailWord_7884309, baseEnd_7884309] using wordTrace_append hprefix tailTrace_7884309
  have hstable : (prefixWord ++ tailWord_7884309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884309).length < 2 ^ (prefixWord ++ tailWord_7884309).sum := by decide
  have hdescent : baseEnd_7884309 < baseStart_7884309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884325 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_7884325 : Nat := 118140960795 + 7884325 * 2 ^ 59
def prefixEnd_7884325 : Nat := 4983230072969 + 3 ^ 40 * 7884325 * 2
def baseEnd_7884325 : Nat := 4048448361259970275878155

theorem tailTrace_7884325 : CollatzResearch.WordTrace tailWord_7884325 prefixEnd_7884325 4048448361259970275878155 := by
  unfold tailWord_7884325
  simp only [CollatzResearch.WordTrace]
  refine ⟨287564957161444535351942429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191709971440963023567961619 287564957161444535351942429)
  ·
    refine ⟨107836858935541700756978411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287564957161444535351942429 107836858935541700756978411)
    ·
      refine ⟨161755288403312551135467617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107836858935541700756978411 161755288403312551135467617)
      ·
        refine ⟨121316466302484413351600713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161755288403312551135467617 121316466302484413351600713)
        ·
          refine ⟨90987349726863310013700535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121316466302484413351600713 90987349726863310013700535)
          ·
            refine ⟨136481024590294965020550803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90987349726863310013700535 136481024590294965020550803)
            ·
              refine ⟨204721536885442447530826205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136481024590294965020550803 204721536885442447530826205)
              ·
                refine ⟨76770576332040917824059827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204721536885442447530826205 76770576332040917824059827)
                ·
                  refine ⟨115155864498061376736089741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76770576332040917824059827 115155864498061376736089741)
                  ·
                    refine ⟨43183449186773016276033653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115155864498061376736089741 43183449186773016276033653)
                    ·
                      refine ⟨4048448361259970275878155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43183449186773016276033653 4048448361259970275878155)
                      ·
                        rfl

theorem cell23_7884325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_7884325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884325 prefixEnd_7884325 := by exact prefixLift 7884325
  have htrace : WordTrace (prefixWord ++ tailWord_7884325) baseStart_7884325 baseEnd_7884325 := by
    simpa [prefixWord, tailWord_7884325, baseEnd_7884325] using wordTrace_append hprefix tailTrace_7884325
  have hstable : (prefixWord ++ tailWord_7884325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884325).length < 2 ^ (prefixWord ++ tailWord_7884325).sum := by decide
  have hdescent : baseEnd_7884325 < baseStart_7884325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884402 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_7884402 : Nat := 118140960795 + 7884402 * 2 ^ 59
def prefixEnd_7884402 : Nat := 4983230072969 + 3 ^ 40 * 7884402 * 2
def baseEnd_7884402 : Nat := 4048487899270366474615301

theorem tailTrace_7884402 : CollatzResearch.WordTrace tailWord_7884402 prefixEnd_7884402 4048487899270366474615301 := by
  unfold tailWord_7884402
  simp only [CollatzResearch.WordTrace]
  refine ⟨71891941395541394375623865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191711843721443718334996973 71891941395541394375623865)
  ·
    refine ⟨53918956046656045781717899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71891941395541394375623865 53918956046656045781717899)
    ·
      refine ⟨80878434069984068672576849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53918956046656045781717899 80878434069984068672576849)
      ·
        refine ⟨60658825552488051504432637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80878434069984068672576849 60658825552488051504432637)
        ·
          refine ⟨22747059582183019314162239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60658825552488051504432637 22747059582183019314162239)
          ·
            refine ⟨34120589373274528971243359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22747059582183019314162239 34120589373274528971243359)
            ·
              refine ⟨51180884059911793456865039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34120589373274528971243359 51180884059911793456865039)
              ·
                refine ⟨76771326089867690185297559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51180884059911793456865039 76771326089867690185297559)
                ·
                  refine ⟨115156989134801535277946339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76771326089867690185297559 115156989134801535277946339)
                  ·
                    refine ⟨172735483702202302916919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115156989134801535277946339 172735483702202302916919509)
                    ·
                      refine ⟨4048487899270366474615301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172735483702202302916919509 4048487899270366474615301)
                      ·
                        rfl

theorem cell23_7884402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_7884402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884402 prefixEnd_7884402 := by exact prefixLift 7884402
  have htrace : WordTrace (prefixWord ++ tailWord_7884402) baseStart_7884402 baseEnd_7884402 := by
    simpa [prefixWord, tailWord_7884402, baseEnd_7884402] using wordTrace_append hprefix tailTrace_7884402
  have hstable : (prefixWord ++ tailWord_7884402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884402).length < 2 ^ (prefixWord ++ tailWord_7884402).sum := by decide
  have hdescent : baseEnd_7884402 < baseStart_7884402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884412 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_7884412 : Nat := 118140960795 + 7884412 * 2 ^ 59
def prefixEnd_7884412 : Nat := 4983230072969 + 3 ^ 40 * 7884412 * 2
def baseEnd_7884412 : Nat := 4048493034076911435490255

theorem tailTrace_7884412 : CollatzResearch.WordTrace tailWord_7884412 prefixEnd_7884412 4048493034076911435490255 := by
  unfold tailWord_7884412
  simp only [CollatzResearch.WordTrace]
  refine ⟨143784065156064674605179745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191712086874752899473572993 143784065156064674605179745)
  ·
    refine ⟨107838048867048505953884809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143784065156064674605179745 107838048867048505953884809)
    ·
      refine ⟨80878536650286379465413607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107838048867048505953884809 80878536650286379465413607)
      ·
        refine ⟨121317804975429569198120411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80878536650286379465413607 121317804975429569198120411)
        ·
          refine ⟨181976707463144353797180617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121317804975429569198120411 181976707463144353797180617)
          ·
            refine ⟨136482530597358265347885463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181976707463144353797180617 136482530597358265347885463)
            ·
              refine ⟨204723795896037398021828195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136482530597358265347885463 204723795896037398021828195)
              ·
                refine ⟨307085693844056097032742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204723795896037398021828195 307085693844056097032742293)
                ·
                  refine ⟨14394641898940129548409795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307085693844056097032742293 14394641898940129548409795)
                  ·
                    refine ⟨21591962848410194322614693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14394641898940129548409795 21591962848410194322614693)
                    ·
                      refine ⟨4048493034076911435490255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21591962848410194322614693 4048493034076911435490255)
                      ·
                        rfl

theorem cell23_7884412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_7884412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884412 prefixEnd_7884412 := by exact prefixLift 7884412
  have htrace : WordTrace (prefixWord ++ tailWord_7884412) baseStart_7884412 baseEnd_7884412 := by
    simpa [prefixWord, tailWord_7884412, baseEnd_7884412] using wordTrace_append hprefix tailTrace_7884412
  have hstable : (prefixWord ++ tailWord_7884412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884412).length < 2 ^ (prefixWord ++ tailWord_7884412).sum := by decide
  have hdescent : baseEnd_7884412 < baseStart_7884412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884415 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_7884415 : Nat := 118140960795 + 7884415 * 2 ^ 59
def prefixEnd_7884415 : Nat := 4983230072969 + 3 ^ 40 * 7884415 * 2
def baseEnd_7884415 : Nat := 4048494574518874923752741

theorem tailTrace_7884415 : CollatzResearch.WordTrace tailWord_7884415 prefixEnd_7884415 4048494574518874923752741 := by
  unfold tailWord_7884415
  simp only [CollatzResearch.WordTrace]
  refine ⟨287568239731118480722718699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191712159820745653815145799 287568239731118480722718699)
  ·
    refine ⟨431352359596677721084078049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287568239731118480722718699 431352359596677721084078049)
    ·
      refine ⟨323514269697508290813058537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431352359596677721084078049 323514269697508290813058537)
      ·
        refine ⟨242635702273131218109793903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323514269697508290813058537 242635702273131218109793903)
        ·
          refine ⟨363953553409696827164690855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242635702273131218109793903 363953553409696827164690855)
          ·
            refine ⟨545930330114545240747036283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363953553409696827164690855 545930330114545240747036283)
            ·
              refine ⟨818895495171817861120554425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545930330114545240747036283 818895495171817861120554425)
              ·
                refine ⟨614171621378863395840415819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818895495171817861120554425 614171621378863395840415819)
                ·
                  refine ⟨921257432068295093760623729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614171621378863395840415819 921257432068295093760623729)
                  ·
                    refine ⟨690943074051221320320467797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921257432068295093760623729 690943074051221320320467797)
                    ·
                      refine ⟨4048494574518874923752741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 690943074051221320320467797 4048494574518874923752741)
                      ·
                        rfl

theorem cell23_7884415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_7884415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884415 prefixEnd_7884415 := by exact prefixLift 7884415
  have htrace : WordTrace (prefixWord ++ tailWord_7884415) baseStart_7884415 baseEnd_7884415 := by
    simpa [prefixWord, tailWord_7884415, baseEnd_7884415] using wordTrace_append hprefix tailTrace_7884415
  have hstable : (prefixWord ++ tailWord_7884415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884415).length < 2 ^ (prefixWord ++ tailWord_7884415).sum := by decide
  have hdescent : baseEnd_7884415 < baseStart_7884415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884432 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_7884432 : Nat := 118140960795 + 7884432 * 2 ^ 59
def prefixEnd_7884432 : Nat := 4983230072969 + 3 ^ 40 * 7884432 * 2
def baseEnd_7884432 : Nat := 4048503303690001357240163

theorem tailTrace_7884432 : CollatzResearch.WordTrace tailWord_7884432 prefixEnd_7884432 4048503303690001357240163 := by
  unfold tailWord_7884432
  simp only [CollatzResearch.WordTrace]
  refine ⟨143784429886028446313043775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191712573181371261750725033 143784429886028446313043775)
  ·
    refine ⟨215676644829042669469565663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143784429886028446313043775 215676644829042669469565663)
    ·
      refine ⟨323514967243564004204348495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215676644829042669469565663 323514967243564004204348495)
      ·
        refine ⟨485272450865346006306522743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323514967243564004204348495 485272450865346006306522743)
        ·
          refine ⟨727908676298019009459784115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485272450865346006306522743 727908676298019009459784115)
          ·
            refine ⟨1091863014447028514189676173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727908676298019009459784115 1091863014447028514189676173)
            ·
              refine ⟨409448630417635692821128565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091863014447028514189676173 409448630417635692821128565)
              ·
                refine ⟨38385809101653346201980803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409448630417635692821128565 38385809101653346201980803)
                ·
                  refine ⟨57578713652480019302971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38385809101653346201980803 57578713652480019302971205)
                  ·
                    refine ⟨10796008809840003619307101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57578713652480019302971205 10796008809840003619307101)
                    ·
                      refine ⟨4048503303690001357240163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796008809840003619307101 4048503303690001357240163)
                      ·
                        rfl

theorem cell23_7884432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_7884432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884432 prefixEnd_7884432 := by exact prefixLift 7884432
  have htrace : WordTrace (prefixWord ++ tailWord_7884432) baseStart_7884432 baseEnd_7884432 := by
    simpa [prefixWord, tailWord_7884432, baseEnd_7884432] using wordTrace_append hprefix tailTrace_7884432
  have hstable : (prefixWord ++ tailWord_7884432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884432).length < 2 ^ (prefixWord ++ tailWord_7884432).sum := by decide
  have hdescent : baseEnd_7884432 < baseStart_7884432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884446 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7884446 : Nat := 118140960795 + 7884446 * 2 ^ 59
def prefixEnd_7884446 : Nat := 4983230072969 + 3 ^ 40 * 7884446 * 2
def baseEnd_7884446 : Nat := 4048510492419164302465099

theorem tailTrace_7884446 : CollatzResearch.WordTrace tailWord_7884446 prefixEnd_7884446 4048510492419164302465099 := by
  unfold tailWord_7884446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946171299250771627137149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191712913596004115344731461 35946171299250771627137149)
  ·
    refine ⟨13479814237219039360176431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35946171299250771627137149 13479814237219039360176431)
    ·
      refine ⟨20219721355828559040264647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479814237219039360176431 20219721355828559040264647)
      ·
        refine ⟨30329582033742838560396971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20219721355828559040264647 30329582033742838560396971)
        ·
          refine ⟨45494373050614257840595457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30329582033742838560396971 45494373050614257840595457)
          ·
            refine ⟨34120779787960693380446593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45494373050614257840595457 34120779787960693380446593)
            ·
              refine ⟨25590584840970520035334945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34120779787960693380446593 25590584840970520035334945)
              ·
                refine ⟨19192938630727890026501209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25590584840970520035334945 19192938630727890026501209)
                ·
                  refine ⟨14394703973045917519875907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19192938630727890026501209 14394703973045917519875907)
                  ·
                    refine ⟨21592055959568876279813861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14394703973045917519875907 21592055959568876279813861)
                    ·
                      refine ⟨4048510492419164302465099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21592055959568876279813861 4048510492419164302465099)
                      ·
                        rfl

theorem cell23_7884446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7884446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884446 prefixEnd_7884446 := by exact prefixLift 7884446
  have htrace : WordTrace (prefixWord ++ tailWord_7884446) baseStart_7884446 baseEnd_7884446 := by
    simpa [prefixWord, tailWord_7884446, baseEnd_7884446] using wordTrace_append hprefix tailTrace_7884446
  have hstable : (prefixWord ++ tailWord_7884446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884446).length < 2 ^ (prefixWord ++ tailWord_7884446).sum := by decide
  have hdescent : baseEnd_7884446 < baseStart_7884446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884512 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_7884512 : Nat := 118140960795 + 7884512 * 2 ^ 59
def prefixEnd_7884512 : Nat := 4983230072969 + 3 ^ 40 * 7884512 * 2
def baseEnd_7884512 : Nat := 1349514794047453681413265

theorem tailTrace_7884512 : CollatzResearch.WordTrace tailWord_7884512 prefixEnd_7884512 1349514794047453681413265 := by
  unfold tailWord_7884512
  simp only [CollatzResearch.WordTrace]
  refine ⟨143785888805883533144499895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191714518407844710859333193 143785888805883533144499895)
  ·
    refine ⟨215678833208825299716749843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143785888805883533144499895 215678833208825299716749843)
    ·
      refine ⟨323518249813237949575124765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215678833208825299716749843 323518249813237949575124765)
      ·
        refine ⟨121319343679964231090671787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323518249813237949575124765 121319343679964231090671787)
        ·
          refine ⟨181979015519946346636007681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121319343679964231090671787 181979015519946346636007681)
          ·
            refine ⟨136484261639959759977005761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181979015519946346636007681 136484261639959759977005761)
            ·
              refine ⟨102363196229969819982754321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136484261639959759977005761 102363196229969819982754321)
              ·
                refine ⟨76772397172477364987065741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102363196229969819982754321 76772397172477364987065741)
                ·
                  refine ⟨28789648939679011870149653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76772397172477364987065741 28789648939679011870149653)
                  ·
                    refine ⟨1349514794047453681413265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28789648939679011870149653 1349514794047453681413265)
                    ·
                      rfl

theorem cell23_7884512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_7884512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884512 prefixEnd_7884512 := by exact prefixLift 7884512
  have htrace : WordTrace (prefixWord ++ tailWord_7884512) baseStart_7884512 baseEnd_7884512 := by
    simpa [prefixWord, tailWord_7884512, baseEnd_7884512] using wordTrace_append hprefix tailTrace_7884512
  have hstable : (prefixWord ++ tailWord_7884512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884512).length < 2 ^ (prefixWord ++ tailWord_7884512).sum := by decide
  have hdescent : baseEnd_7884512 < baseStart_7884512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884513 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_7884513 : Nat := 118140960795 + 7884513 * 2 ^ 59
def prefixEnd_7884513 : Nat := 4983230072969 + 3 ^ 40 * 7884513 * 2
def baseEnd_7884513 : Nat := 4048544895623015540327291

theorem tailTrace_7884513 : CollatzResearch.WordTrace tailWord_7884513 prefixEnd_7884513 4048544895623015540327291 := by
  unfold tailWord_7884513
  simp only [CollatzResearch.WordTrace]
  refine ⟨287571814084763443459786193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191714542723175628973190795 287571814084763443459786193)
  ·
    refine ⟨215678860563572582594839645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287571814084763443459786193 215678860563572582594839645)
    ·
      refine ⟨80879572711339718473064867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215678860563572582594839645 80879572711339718473064867)
      ·
        refine ⟨121319359067009577709597301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80879572711339718473064867 121319359067009577709597301)
        ·
          refine ⟨11373689912532147910274747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121319359067009577709597301 11373689912532147910274747)
          ·
            refine ⟨17060534868798221865412121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373689912532147910274747 17060534868798221865412121)
            ·
              refine ⟨12795401151598666399059091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17060534868798221865412121 12795401151598666399059091)
              ·
                refine ⟨19193101727397999598588637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795401151598666399059091 19193101727397999598588637)
                ·
                  refine ⟨7197413147774249849470739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19193101727397999598588637 7197413147774249849470739)
                  ·
                    refine ⟨10796119721661374774206109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197413147774249849470739 10796119721661374774206109)
                    ·
                      refine ⟨4048544895623015540327291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796119721661374774206109 4048544895623015540327291)
                      ·
                        rfl

theorem cell23_7884513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_7884513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884513 prefixEnd_7884513 := by exact prefixLift 7884513
  have htrace : WordTrace (prefixWord ++ tailWord_7884513) baseStart_7884513 baseEnd_7884513 := by
    simpa [prefixWord, tailWord_7884513, baseEnd_7884513] using wordTrace_append hprefix tailTrace_7884513
  have hstable : (prefixWord ++ tailWord_7884513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884513).length < 2 ^ (prefixWord ++ tailWord_7884513).sum := by decide
  have hdescent : baseEnd_7884513 < baseStart_7884513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884529 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_7884529 : Nat := 118140960795 + 7884529 * 2 ^ 59
def prefixEnd_7884529 : Nat := 4983230072969 + 3 ^ 40 * 7884529 * 2
def baseEnd_7884529 : Nat := 1349517703771162492575739

theorem tailTrace_7884529 : CollatzResearch.WordTrace tailWord_7884529 prefixEnd_7884529 1349517703771162492575739 := by
  unfold tailWord_7884529
  simp only [CollatzResearch.WordTrace]
  refine ⟨287572397652705478192368641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191714931768470318794912427 287572397652705478192368641)
  ·
    refine ⟨215679298239529108644276481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287572397652705478192368641 215679298239529108644276481)
    ·
      refine ⟨161759473679646831483207361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215679298239529108644276481 161759473679646831483207361)
      ·
        refine ⟨121319605259735123612405521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161759473679646831483207361 121319605259735123612405521)
        ·
          refine ⟨90989703944801342709304141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121319605259735123612405521 90989703944801342709304141)
          ·
            refine ⟨34121138979300503515989053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90989703944801342709304141 34121138979300503515989053)
            ·
              refine ⟨12795427117237688818495895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34121138979300503515989053 12795427117237688818495895)
              ·
                refine ⟨19193140675856533227743843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795427117237688818495895 19193140675856533227743843)
                ·
                  refine ⟨28789711013784799841615765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19193140675856533227743843 28789711013784799841615765)
                  ·
                    refine ⟨1349517703771162492575739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28789711013784799841615765 1349517703771162492575739)
                    ·
                      rfl

theorem cell23_7884529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_7884529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884529 prefixEnd_7884529 := by exact prefixLift 7884529
  have htrace : WordTrace (prefixWord ++ tailWord_7884529) baseStart_7884529 baseEnd_7884529 := by
    simpa [prefixWord, tailWord_7884529, baseEnd_7884529] using wordTrace_append hprefix tailTrace_7884529
  have hstable : (prefixWord ++ tailWord_7884529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884529).length < 2 ^ (prefixWord ++ tailWord_7884529).sum := by decide
  have hdescent : baseEnd_7884529 < baseStart_7884529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884536 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_7884536 : Nat := 118140960795 + 7884536 * 2 ^ 59
def prefixEnd_7884536 : Nat := 4983230072969 + 3 ^ 40 * 7884536 * 2
def baseEnd_7884536 : Nat := 4048556705678068950339685

theorem tailTrace_7884536 : CollatzResearch.WordTrace tailWord_7884536 prefixEnd_7884536 4048556705678068950339685 := by
  unfold tailWord_7884536
  simp only [CollatzResearch.WordTrace]
  refine ⟨143786326481840059193936731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191715101975786745591915641 143786326481840059193936731)
  ·
    refine ⟨215679489722760088790905097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143786326481840059193936731 215679489722760088790905097)
    ·
      refine ⟨161759617292070066593178823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215679489722760088790905097 161759617292070066593178823)
      ·
        refine ⟨242639425938105099889768235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161759617292070066593178823 242639425938105099889768235)
        ·
          refine ⟨363959138907157649834652353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242639425938105099889768235 363959138907157649834652353)
          ·
            refine ⟨272969354180368237375989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363959138907157649834652353 272969354180368237375989265)
            ·
              refine ⟨204727015635276178031991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272969354180368237375989265 204727015635276178031991949)
              ·
                refine ⟨76772630863228566761996981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204727015635276178031991949 76772630863228566761996981)
                ·
                  refine ⟨7197434143427678133937217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76772630863228566761996981 7197434143427678133937217)
                  ·
                    refine ⟨5398075607570758600452913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197434143427678133937217 5398075607570758600452913)
                    ·
                      refine ⟨4048556705678068950339685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398075607570758600452913 4048556705678068950339685)
                      ·
                        rfl

theorem cell23_7884536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_7884536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884536 prefixEnd_7884536 := by exact prefixLift 7884536
  have htrace : WordTrace (prefixWord ++ tailWord_7884536) baseStart_7884536 baseEnd_7884536 := by
    simpa [prefixWord, tailWord_7884536, baseEnd_7884536] using wordTrace_append hprefix tailTrace_7884536
  have hstable : (prefixWord ++ tailWord_7884536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884536).length < 2 ^ (prefixWord ++ tailWord_7884536).sum := by decide
  have hdescent : baseEnd_7884536 < baseStart_7884536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884546 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_7884546 : Nat := 118140960795 + 7884546 * 2 ^ 59
def prefixEnd_7884546 : Nat := 4983230072969 + 3 ^ 40 * 7884546 * 2
def baseEnd_7884546 : Nat := 1349520613494871303738213

theorem tailTrace_7884546 : CollatzResearch.WordTrace tailWord_7884546 prefixEnd_7884546 1349520613494871303738213 := by
  unfold tailWord_7884546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71893254423410972523934373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191715345129095926730491661 71893254423410972523934373)
  ·
    refine ⟨13479985204389557348237695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71893254423410972523934373 13479985204389557348237695)
    ·
      refine ⟨20219977806584336022356543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479985204389557348237695 20219977806584336022356543)
      ·
        refine ⟨30329966709876504033534815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20219977806584336022356543 30329966709876504033534815)
        ·
          refine ⟨45494950064814756050302223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30329966709876504033534815 45494950064814756050302223)
          ·
            refine ⟨68242425097222134075453335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45494950064814756050302223 68242425097222134075453335)
            ·
              refine ⟨102363637645833201113180003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68242425097222134075453335 102363637645833201113180003)
              ·
                refine ⟨153545456468749801669770005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102363637645833201113180003 153545456468749801669770005)
                ·
                  refine ⟨7197443271972646953270469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153545456468749801669770005 7197443271972646953270469)
                  ·
                    refine ⟨1349520613494871303738213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197443271972646953270469 1349520613494871303738213)
                    ·
                      rfl

theorem cell23_7884546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_7884546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884546 prefixEnd_7884546 := by exact prefixLift 7884546
  have htrace : WordTrace (prefixWord ++ tailWord_7884546) baseStart_7884546 baseEnd_7884546 := by
    simpa [prefixWord, tailWord_7884546, baseEnd_7884546] using wordTrace_append hprefix tailTrace_7884546
  have hstable : (prefixWord ++ tailWord_7884546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884546).length < 2 ^ (prefixWord ++ tailWord_7884546).sum := by decide
  have hdescent : baseEnd_7884546 < baseStart_7884546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884556 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_7884556 : Nat := 118140960795 + 7884556 * 2 ^ 59
def prefixEnd_7884556 : Nat := 4983230072969 + 3 ^ 40 * 7884556 * 2
def baseEnd_7884556 : Nat := 4048566975291158872089593

theorem tailTrace_7884556 : CollatzResearch.WordTrace tailWord_7884556 prefixEnd_7884556 4048566975291158872089593 := by
  unfold tailWord_7884556
  simp only [CollatzResearch.WordTrace]
  refine ⟨143786691211803830901800761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191715588282405107869067681 143786691211803830901800761)
  ·
    refine ⟨107840018408852873176350571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143786691211803830901800761 107840018408852873176350571)
    ·
      refine ⟨161760027613279309764525857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107840018408852873176350571 161760027613279309764525857)
      ·
        refine ⟨121320020709959482323394393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161760027613279309764525857 121320020709959482323394393)
        ·
          refine ⟨90990015532469611742545795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121320020709959482323394393 90990015532469611742545795)
          ·
            refine ⟨136485023298704417613818693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90990015532469611742545795 136485023298704417613818693)
            ·
              refine ⟨25590941868507078302591005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136485023298704417613818693 25590941868507078302591005)
              ·
                refine ⟨9596603200690154363471627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25590941868507078302591005 9596603200690154363471627)
                ·
                  refine ⟨14394904801035231545207441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596603200690154363471627 14394904801035231545207441)
                  ·
                    refine ⟨10796178600776423658905581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14394904801035231545207441 10796178600776423658905581)
                    ·
                      refine ⟨4048566975291158872089593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796178600776423658905581 4048566975291158872089593)
                      ·
                        rfl

theorem cell23_7884556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_7884556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884556 prefixEnd_7884556 := by exact prefixLift 7884556
  have htrace : WordTrace (prefixWord ++ tailWord_7884556) baseStart_7884556 baseEnd_7884556 := by
    simpa [prefixWord, tailWord_7884556, baseEnd_7884556] using wordTrace_append hprefix tailTrace_7884556
  have hstable : (prefixWord ++ tailWord_7884556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884556).length < 2 ^ (prefixWord ++ tailWord_7884556).sum := by decide
  have hdescent : baseEnd_7884556 < baseStart_7884556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884564 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7884564 : Nat := 118140960795 + 7884564 * 2 ^ 59
def prefixEnd_7884564 : Nat := 4983230072969 + 3 ^ 40 * 7884564 * 2
def baseEnd_7884564 : Nat := 4048571083136394840789557

theorem tailTrace_7884564 : CollatzResearch.WordTrace tailWord_7884564 prefixEnd_7884564 4048571083136394840789557 := by
  unfold tailWord_7884564
  simp only [CollatzResearch.WordTrace]
  refine ⟨143786837103789339584946373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191715782805052452779928497 143786837103789339584946373)
  ·
    refine ⟨26960031956960501172177445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143786837103789339584946373 26960031956960501172177445)
    ·
      refine ⟨5055005991930093969783271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26960031956960501172177445 5055005991930093969783271)
      ·
        refine ⟨7582508987895140954674907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055005991930093969783271 7582508987895140954674907)
        ·
          refine ⟨11373763481842711432012361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582508987895140954674907 11373763481842711432012361)
          ·
            refine ⟨8530322611382033574009271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11373763481842711432012361 8530322611382033574009271)
            ·
              refine ⟨12795483917073050361013907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530322611382033574009271 12795483917073050361013907)
              ·
                refine ⟨19193225875609575541520861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795483917073050361013907 19193225875609575541520861)
                ·
                  refine ⟨7197459703353590828070323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19193225875609575541520861 7197459703353590828070323)
                  ·
                    refine ⟨10796189555030386242105485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197459703353590828070323 10796189555030386242105485)
                    ·
                      refine ⟨4048571083136394840789557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796189555030386242105485 4048571083136394840789557)
                      ·
                        rfl

theorem cell23_7884564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7884564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884564 prefixEnd_7884564 := by exact prefixLift 7884564
  have htrace : WordTrace (prefixWord ++ tailWord_7884564) baseStart_7884564 baseEnd_7884564 := by
    simpa [prefixWord, tailWord_7884564, baseEnd_7884564] using wordTrace_append hprefix tailTrace_7884564
  have hstable : (prefixWord ++ tailWord_7884564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884564).length < 2 ^ (prefixWord ++ tailWord_7884564).sum := by decide
  have hdescent : baseEnd_7884564 < baseStart_7884564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884570 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_7884570 : Nat := 118140960795 + 7884570 * 2 ^ 59
def prefixEnd_7884570 : Nat := 4983230072969 + 3 ^ 40 * 7884570 * 2
def baseEnd_7884570 : Nat := 4048574164020321817314529

theorem tailTrace_7884570 : CollatzResearch.WordTrace tailWord_7884570 prefixEnd_7884570 4048574164020321817314529 := by
  unfold tailWord_7884570
  simp only [CollatzResearch.WordTrace]
  refine ⟨71893473261389235548652791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191715928697037961463074109 71893473261389235548652791)
  ·
    refine ⟨107840209892083853322979187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71893473261389235548652791 107840209892083853322979187)
    ·
      refine ⟨161760314838125779984468781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107840209892083853322979187 161760314838125779984468781)
      ·
        refine ⟨60660118064297167494175793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161760314838125779984468781 60660118064297167494175793)
        ·
          refine ⟨45495088548222875620631845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60660118064297167494175793 45495088548222875620631845)
          ·
            refine ⟨8530329102791789178868471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45495088548222875620631845 8530329102791789178868471)
            ·
              refine ⟨12795493654187683768302707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8530329102791789178868471 12795493654187683768302707)
              ·
                refine ⟨19193240481281525652454061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12795493654187683768302707 19193240481281525652454061)
                ·
                  refine ⟨7197465180480572119670273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19193240481281525652454061 7197465180480572119670273)
                  ·
                    refine ⟨5398098885360429089752705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197465180480572119670273 5398098885360429089752705)
                    ·
                      refine ⟨4048574164020321817314529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398098885360429089752705 4048574164020321817314529)
                      ·
                        rfl

theorem cell23_7884570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_7884570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884570 prefixEnd_7884570 := by exact prefixLift 7884570
  have htrace : WordTrace (prefixWord ++ tailWord_7884570) baseStart_7884570 baseEnd_7884570 := by
    simpa [prefixWord, tailWord_7884570, baseEnd_7884570] using wordTrace_append hprefix tailTrace_7884570
  have hstable : (prefixWord ++ tailWord_7884570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884570).length < 2 ^ (prefixWord ++ tailWord_7884570).sum := by decide
  have hdescent : baseEnd_7884570 < baseStart_7884570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884580 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_7884580 : Nat := 118140960795 + 7884580 * 2 ^ 59
def prefixEnd_7884580 : Nat := 4983230072969 + 3 ^ 40 * 7884580 * 2
def baseEnd_7884580 : Nat := 1349526432942288926063161

theorem tailTrace_7884580 : CollatzResearch.WordTrace tailWord_7884580 prefixEnd_7884580 1349526432942288926063161 := by
  unfold tailWord_7884580
  simp only [CollatzResearch.WordTrace]
  refine ⟨143787128887760356951237597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191716171850347142601650129 143787128887760356951237597)
  ·
    refine ⟨53920173332910133856714099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143787128887760356951237597 53920173332910133856714099)
    ·
      refine ⟨80880259999365200785071149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53920173332910133856714099 80880259999365200785071149)
      ·
        refine ⟨30330097499761950294401681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80880259999365200785071149 30330097499761950294401681)
        ·
          refine ⟨22747573124821462720801261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30330097499761950294401681 22747573124821462720801261)
          ·
            refine ⟨8530339921808048520300473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22747573124821462720801261 8530339921808048520300473)
            ·
              refine ⟨6397754941356036390225355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530339921808048520300473 6397754941356036390225355)
              ·
                refine ⟨9596632412034054585338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6397754941356036390225355 9596632412034054585338033)
                ·
                  refine ⟨7197474309025540939003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596632412034054585338033 7197474309025540939003525)
                  ·
                    refine ⟨1349526432942288926063161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197474309025540939003525 1349526432942288926063161)
                    ·
                      rfl

theorem cell23_7884580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_7884580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884580 prefixEnd_7884580 := by exact prefixLift 7884580
  have htrace : WordTrace (prefixWord ++ tailWord_7884580) baseStart_7884580 baseEnd_7884580 := by
    simpa [prefixWord, tailWord_7884580, baseEnd_7884580] using wordTrace_append hprefix tailTrace_7884580
  have hstable : (prefixWord ++ tailWord_7884580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884580).length < 2 ^ (prefixWord ++ tailWord_7884580).sum := by decide
  have hdescent : baseEnd_7884580 < baseStart_7884580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_7884592 : Nat := 118140960795 + 7884592 * 2 ^ 59
def prefixEnd_7884592 : Nat := 4983230072969 + 3 ^ 40 * 7884592 * 2
def baseEnd_7884592 : Nat := 4048585460594720731239427

theorem tailTrace_7884592 : CollatzResearch.WordTrace tailWord_7884592 prefixEnd_7884592 4048585460594720731239427 := by
  unfold tailWord_7884592
  simp only [CollatzResearch.WordTrace]
  refine ⟨143787347725738619975956015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191716463634318159967941353 143787347725738619975956015)
  ·
    refine ⟨215681021588607929963934023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143787347725738619975956015 215681021588607929963934023)
    ·
      refine ⟨323521532382911894945901035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215681021588607929963934023 323521532382911894945901035)
      ·
        refine ⟨485282298574367842418851553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323521532382911894945901035 485282298574367842418851553)
        ·
          refine ⟨363961723930775881814138665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485282298574367842418851553 363961723930775881814138665)
          ·
            refine ⟨272971292948081911360603999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363961723930775881814138665 272971292948081911360603999)
            ·
              refine ⟨409456939422122867040905999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272971292948081911360603999 409456939422122867040905999)
              ·
                refine ⟨614185409133184300561358999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409456939422122867040905999 614185409133184300561358999)
                ·
                  refine ⟨921278113699776450842038499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614185409133184300561358999 921278113699776450842038499)
                  ·
                    refine ⟨1381917170549664676263057749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921278113699776450842038499 1381917170549664676263057749)
                    ·
                      refine ⟨4048585460594720731239427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1381917170549664676263057749 4048585460594720731239427)
                      ·
                        rfl

theorem cell23_7884592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_7884592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884592 prefixEnd_7884592 := by exact prefixLift 7884592
  have htrace : WordTrace (prefixWord ++ tailWord_7884592) baseStart_7884592 baseEnd_7884592 := by
    simpa [prefixWord, tailWord_7884592, baseEnd_7884592] using wordTrace_append hprefix tailTrace_7884592
  have hstable : (prefixWord ++ tailWord_7884592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884592).length < 2 ^ (prefixWord ++ tailWord_7884592).sum := by decide
  have hdescent : baseEnd_7884592 < baseStart_7884592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884620 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_7884620 : Nat := 118140960795 + 7884620 * 2 ^ 59
def prefixEnd_7884620 : Nat := 4983230072969 + 3 ^ 40 * 7884620 * 2
def baseEnd_7884620 : Nat := 4048599838053046621689299

theorem tailTrace_7884620 : CollatzResearch.WordTrace tailWord_7884620 prefixEnd_7884620 4048599838053046621689299 := by
  unfold tailWord_7884620
  simp only [CollatzResearch.WordTrace]
  refine ⟨143787858347687900366965657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191717144463583867155954209 143787858347687900366965657)
  ·
    refine ⟨107840893760765925275224243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143787858347687900366965657 107840893760765925275224243)
    ·
      refine ⟨161761340641148887912836365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107840893760765925275224243 161761340641148887912836365)
      ·
        refine ⟨60660502740430832967313637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161761340641148887912836365 60660502740430832967313637)
        ·
          refine ⟨11373844263830781181371307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60660502740430832967313637 11373844263830781181371307)
          ·
            refine ⟨17060766395746171772056961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11373844263830781181371307 17060766395746171772056961)
            ·
              refine ⟨12795574796809628829042721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17060766395746171772056961 12795574796809628829042721)
              ·
                refine ⟨9596681097607221621782041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12795574796809628829042721 9596681097607221621782041)
                ·
                  refine ⟨7197510823205416216336531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596681097607221621782041 7197510823205416216336531)
                  ·
                    refine ⟨10796266234808124324504797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197510823205416216336531 10796266234808124324504797)
                    ·
                      refine ⟨4048599838053046621689299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796266234808124324504797 4048599838053046621689299)
                      ·
                        rfl

theorem cell23_7884620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_7884620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884620 prefixEnd_7884620 := by exact prefixLift 7884620
  have htrace : WordTrace (prefixWord ++ tailWord_7884620) baseStart_7884620 baseEnd_7884620 := by
    simpa [prefixWord, tailWord_7884620, baseEnd_7884620] using wordTrace_append hprefix tailTrace_7884620
  have hstable : (prefixWord ++ tailWord_7884620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884620).length < 2 ^ (prefixWord ++ tailWord_7884620).sum := by decide
  have hdescent : baseEnd_7884620 < baseStart_7884620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884621 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7884621 : Nat := 118140960795 + 7884621 * 2 ^ 59
def prefixEnd_7884621 : Nat := 4983230072969 + 3 ^ 40 * 7884621 * 2
def baseEnd_7884621 : Nat := 4048600351533701117776795

theorem tailTrace_7884621 : CollatzResearch.WordTrace tailWord_7884621 prefixEnd_7884621 4048600351533701117776795 := by
  unfold tailWord_7884621
  simp only [CollatzResearch.WordTrace]
  refine ⟨287575753168372177904717717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191717168778914785269811811 287575753168372177904717717)
  ·
    refine ⟨13480113429767445839283643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287575753168372177904717717 13480113429767445839283643)
    ·
      refine ⟨20220170144651168758925465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13480113429767445839283643 20220170144651168758925465)
      ·
        refine ⟨15165127608488376569194099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20220170144651168758925465 15165127608488376569194099)
        ·
          refine ⟨22747691412732564853791149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15165127608488376569194099 22747691412732564853791149)
          ·
            refine ⟨8530384279774711820171681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22747691412732564853791149 8530384279774711820171681)
            ·
              refine ⟨6397788209831033865128761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530384279774711820171681 6397788209831033865128761)
              ·
                refine ⟨4798341157373275398846571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6397788209831033865128761 4798341157373275398846571)
                ·
                  refine ⟨7197511736059913098269857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798341157373275398846571 7197511736059913098269857)
                  ·
                    refine ⟨5398133802044934823702393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7197511736059913098269857 5398133802044934823702393)
                    ·
                      refine ⟨4048600351533701117776795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398133802044934823702393 4048600351533701117776795)
                      ·
                        rfl

theorem cell23_7884621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7884621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884621 prefixEnd_7884621 := by exact prefixLift 7884621
  have htrace : WordTrace (prefixWord ++ tailWord_7884621) baseStart_7884621 baseEnd_7884621 := by
    simpa [prefixWord, tailWord_7884621, baseEnd_7884621] using wordTrace_append hprefix tailTrace_7884621
  have hstable : (prefixWord ++ tailWord_7884621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884621).length < 2 ^ (prefixWord ++ tailWord_7884621).sum := by decide
  have hdescent : baseEnd_7884621 < baseStart_7884621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884639 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_7884639 : Nat := 118140960795 + 7884639 * 2 ^ 59
def prefixEnd_7884639 : Nat := 4983230072969 + 3 ^ 40 * 7884639 * 2
def baseEnd_7884639 : Nat := 4048609594185482047351711

theorem tailTrace_7884639 : CollatzResearch.WordTrace tailWord_7884639 prefixEnd_7884639 4048609594185482047351711 := by
  unfold tailWord_7884639
  simp only [CollatzResearch.WordTrace]
  refine ⟨287576409682306966978872971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191717606454871311319248647 287576409682306966978872971)
  ·
    refine ⟨431364614523460450468309457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287576409682306966978872971 431364614523460450468309457)
    ·
      refine ⟨323523460892595337851232093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431364614523460450468309457 323523460892595337851232093)
      ·
        refine ⟨121321297834723251694212035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323523460892595337851232093 121321297834723251694212035)
        ·
          refine ⟨181981946752084877541318053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121321297834723251694212035 181981946752084877541318053)
          ·
            refine ⟨34121615016015914538997135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181981946752084877541318053 34121615016015914538997135)
            ·
              refine ⟨51182422524023871808495703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34121615016015914538997135 51182422524023871808495703)
              ·
                refine ⟨76773633786035807712743555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51182422524023871808495703 76773633786035807712743555)
                ·
                  refine ⟨115160450679053711569115333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76773633786035807712743555 115160450679053711569115333)
                  ·
                    refine ⟨21592584502322570919209125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115160450679053711569115333 21592584502322570919209125)
                    ·
                      refine ⟨4048609594185482047351711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21592584502322570919209125 4048609594185482047351711)
                      ·
                        rfl

theorem cell23_7884639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_7884639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884639 prefixEnd_7884639 := by exact prefixLift 7884639
  have htrace : WordTrace (prefixWord ++ tailWord_7884639) baseStart_7884639 baseEnd_7884639 := by
    simpa [prefixWord, tailWord_7884639, baseEnd_7884639] using wordTrace_append hprefix tailTrace_7884639
  have hstable : (prefixWord ++ tailWord_7884639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884639).length < 2 ^ (prefixWord ++ tailWord_7884639).sum := by decide
  have hdescent : baseEnd_7884639 < baseStart_7884639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884659 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3]
def baseStart_7884659 : Nat := 118140960795 + 7884659 * 2 ^ 59
def prefixEnd_7884659 : Nat := 4983230072969 + 3 ^ 40 * 7884659 * 2
def baseEnd_7884659 : Nat := 4048619863798571969101619

theorem tailTrace_7884659 : CollatzResearch.WordTrace tailWord_7884659 prefixEnd_7884659 4048619863798571969101619 := by
  unfold tailWord_7884659
  simp only [CollatzResearch.WordTrace]
  refine ⟨287577139142234510394601031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191718092761489673596400687 287577139142234510394601031)
  ·
    refine ⟨431365708713351765591901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287577139142234510394601031 431365708713351765591901547)
    ·
      refine ⟨647048563070027648387852321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431365708713351765591901547 647048563070027648387852321)
      ·
        refine ⟨485286422302520736290889241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647048563070027648387852321 485286422302520736290889241)
        ·
          refine ⟨363964816726890552218166931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485286422302520736290889241 363964816726890552218166931)
          ·
            refine ⟨545947225090335828327250397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363964816726890552218166931 545947225090335828327250397)
            ·
              refine ⟨204730209408875935622718899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545947225090335828327250397 204730209408875935622718899)
              ·
                refine ⟨307095314113313903434078349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204730209408875935622718899 307095314113313903434078349)
                ·
                  refine ⟨115160742792492713787779381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307095314113313903434078349 115160742792492713787779381)
                  ·
                    refine ⟨10796319636796191917604317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115160742792492713787779381 10796319636796191917604317)
                    ·
                      refine ⟨4048619863798571969101619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796319636796191917604317 4048619863798571969101619)
                      ·
                        rfl

theorem cell23_7884659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_7884659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884659 prefixEnd_7884659 := by exact prefixLift 7884659
  have htrace : WordTrace (prefixWord ++ tailWord_7884659) baseStart_7884659 baseEnd_7884659 := by
    simpa [prefixWord, tailWord_7884659, baseEnd_7884659] using wordTrace_append hprefix tailTrace_7884659
  have hstable : (prefixWord ++ tailWord_7884659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884659).length < 2 ^ (prefixWord ++ tailWord_7884659).sum := by decide
  have hdescent : baseEnd_7884659 < baseStart_7884659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884666 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_7884666 : Nat := 118140960795 + 7884666 * 2 ^ 59
def prefixEnd_7884666 : Nat := 4983230072969 + 3 ^ 40 * 7884666 * 2
def baseEnd_7884666 : Nat := 449847050907017049079343

theorem tailTrace_7884666 : CollatzResearch.WordTrace tailWord_7884666 prefixEnd_7884666 449847050907017049079343 := by
  unfold tailWord_7884666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71894348613302287647526463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191718262968806100393403901 71894348613302287647526463)
  ·
    refine ⟨107841522919953431471289695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71894348613302287647526463 107841522919953431471289695)
    ·
      refine ⟨161762284379930147206934543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107841522919953431471289695 161762284379930147206934543)
      ·
        refine ⟨242643426569895220810401815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161762284379930147206934543 242643426569895220810401815)
        ·
          refine ⟨363965139854842831215602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242643426569895220810401815 363965139854842831215602723)
          ·
            refine ⟨545947709782264246823404085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363965139854842831215602723 545947709782264246823404085)
            ·
              refine ⟨51182597792087273139694133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 545947709782264246823404085 51182597792087273139694133)
              ·
                refine ⟨4798368543008181856846325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51182597792087273139694133 4798368543008181856846325)
                ·
                  refine ⟨449847050907017049079343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798368543008181856846325 449847050907017049079343)
                  ·
                    rfl

theorem cell23_7884666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_7884666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884666 prefixEnd_7884666 := by exact prefixLift 7884666
  have htrace : WordTrace (prefixWord ++ tailWord_7884666) baseStart_7884666 baseEnd_7884666 := by
    simpa [prefixWord, tailWord_7884666, baseEnd_7884666] using wordTrace_append hprefix tailTrace_7884666
  have hstable : (prefixWord ++ tailWord_7884666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884666).length < 2 ^ (prefixWord ++ tailWord_7884666).sum := by decide
  have hdescent : baseEnd_7884666 < baseStart_7884666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884676 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7884676 : Nat := 118140960795 + 7884676 * 2 ^ 59
def prefixEnd_7884676 : Nat := 4983230072969 + 3 ^ 40 * 7884676 * 2
def baseEnd_7884676 : Nat := 4048628592969698402589041

theorem tailTrace_7884676 : CollatzResearch.WordTrace tailWord_7884676 prefixEnd_7884676 4048628592969698402589041 := by
  unfold tailWord_7884676
  simp only [CollatzResearch.WordTrace]
  refine ⟨143788879591586461148984941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191718506122115281531979921 143788879591586461148984941)
  ·
    refine ⟨53920829846844922930869353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143788879591586461148984941 53920829846844922930869353)
    ·
      refine ⟨40440622385133692198152015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53920829846844922930869353 40440622385133692198152015)
      ·
        refine ⟨60660933577700538297228023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40440622385133692198152015 60660933577700538297228023)
        ·
          refine ⟨90991400366550807445842035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60660933577700538297228023 90991400366550807445842035)
          ·
            refine ⟨136487100549826211168763053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90991400366550807445842035 136487100549826211168763053)
            ·
              refine ⟨51182662706184829188286145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136487100549826211168763053 51182662706184829188286145)
              ·
                refine ⟨38386997029638621891214609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51182662706184829188286145 38386997029638621891214609)
                ·
                  refine ⟨28790247772228966418410957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38386997029638621891214609 28790247772228966418410957)
                  ·
                    refine ⟨10796342914585862406904109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28790247772228966418410957 10796342914585862406904109)
                    ·
                      refine ⟨4048628592969698402589041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796342914585862406904109 4048628592969698402589041)
                      ·
                        rfl

theorem cell23_7884676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7884676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884676 prefixEnd_7884676 := by exact prefixLift 7884676
  have htrace : WordTrace (prefixWord ++ tailWord_7884676) baseStart_7884676 baseEnd_7884676 := by
    simpa [prefixWord, tailWord_7884676, baseEnd_7884676] using wordTrace_append hprefix tailTrace_7884676
  have hstable : (prefixWord ++ tailWord_7884676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884676).length < 2 ^ (prefixWord ++ tailWord_7884676).sum := by decide
  have hdescent : baseEnd_7884676 < baseStart_7884676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884689 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_7884689 : Nat := 118140960795 + 7884689 * 2 ^ 59
def prefixEnd_7884689 : Nat := 4983230072969 + 3 ^ 40 * 7884689 * 2
def baseEnd_7884689 : Nat := 4048635268218206851726481

theorem tailTrace_7884689 : CollatzResearch.WordTrace tailWord_7884689 prefixEnd_7884689 4048635268218206851726481 := by
  unfold tailWord_7884689
  simp only [CollatzResearch.WordTrace]
  refine ⟨287578233332125825518193121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191718822221417217012128747 287578233332125825518193121)
  ·
    refine ⟨215683674999094369138644841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287578233332125825518193121 215683674999094369138644841)
    ·
      refine ⟨161762756249320776853983631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215683674999094369138644841 161762756249320776853983631)
      ·
        refine ⟨242644134373981165280975447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161762756249320776853983631 242644134373981165280975447)
        ·
          refine ⟨363966201560971747921463171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242644134373981165280975447 363966201560971747921463171)
          ·
            refine ⟨545949302341457621882194757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363966201560971747921463171 545949302341457621882194757)
            ·
              refine ⟨102365494189023304102911517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545949302341457621882194757 102365494189023304102911517)
              ·
                refine ⟨38387060320883739038591819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102365494189023304102911517 38387060320883739038591819)
                ·
                  refine ⟨57580590481325608557887729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38387060320883739038591819 57580590481325608557887729)
                  ·
                    refine ⟨43185442860994206418415797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57580590481325608557887729 43185442860994206418415797)
                    ·
                      refine ⟨4048635268218206851726481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43185442860994206418415797 4048635268218206851726481)
                      ·
                        rfl

theorem cell23_7884689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_7884689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884689 prefixEnd_7884689 := by exact prefixLift 7884689
  have htrace : WordTrace (prefixWord ++ tailWord_7884689) baseStart_7884689 baseEnd_7884689 := by
    simpa [prefixWord, tailWord_7884689, baseEnd_7884689] using wordTrace_append hprefix tailTrace_7884689
  have hstable : (prefixWord ++ tailWord_7884689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884689).length < 2 ^ (prefixWord ++ tailWord_7884689).sum := by decide
  have hdescent : baseEnd_7884689 < baseStart_7884689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884733 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7884733 : Nat := 118140960795 + 7884733 * 2 ^ 59
def prefixEnd_7884733 : Nat := 4983230072969 + 3 ^ 40 * 7884733 * 2
def baseEnd_7884733 : Nat := 4048657861367004679576279

theorem tailTrace_7884733 : CollatzResearch.WordTrace tailWord_7884733 prefixEnd_7884733 4048657861367004679576279 := by
  unfold tailWord_7884733
  simp only [CollatzResearch.WordTrace]
  refine ⟨287579838143966421032794853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191719892095977614021863235 287579838143966421032794853)
  ·
    refine ⟨53921219651993703943649035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287579838143966421032794853 53921219651993703943649035)
    ·
      refine ⟨80881829477990555915473553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53921219651993703943649035 80881829477990555915473553)
      ·
        refine ⟨60661372108492916936605165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80881829477990555915473553 60661372108492916936605165)
        ·
          refine ⟨22748014540684843851226937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60661372108492916936605165 22748014540684843851226937)
          ·
            refine ⟨17061010905513632888420203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22748014540684843851226937 17061010905513632888420203)
            ·
              refine ⟨25591516358270449332630305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17061010905513632888420203 25591516358270449332630305)
              ·
                refine ⟨19193637268702836999472729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25591516358270449332630305 19193637268702836999472729)
                ·
                  refine ⟨14395227951527127749604547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19193637268702836999472729 14395227951527127749604547)
                  ·
                    refine ⟨21592841927290691624406821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14395227951527127749604547 21592841927290691624406821)
                    ·
                      refine ⟨4048657861367004679576279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21592841927290691624406821 4048657861367004679576279)
                      ·
                        rfl

theorem cell23_7884733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7884733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884733 prefixEnd_7884733 := by exact prefixLift 7884733
  have htrace : WordTrace (prefixWord ++ tailWord_7884733) baseStart_7884733 baseEnd_7884733 := by
    simpa [prefixWord, tailWord_7884733, baseEnd_7884733] using wordTrace_append hprefix tailTrace_7884733
  have hstable : (prefixWord ++ tailWord_7884733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884733).length < 2 ^ (prefixWord ++ tailWord_7884733).sum := by decide
  have hdescent : baseEnd_7884733 < baseStart_7884733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884779 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_7884779 : Nat := 118140960795 + 7884779 * 2 ^ 59
def prefixEnd_7884779 : Nat := 4983230072969 + 3 ^ 40 * 7884779 * 2
def baseEnd_7884779 : Nat := 4048681481477111499601067

theorem tailTrace_7884779 : CollatzResearch.WordTrace tailWord_7884779 prefixEnd_7884779 4048681481477111499601067 := by
  unfold tailWord_7884779
  simp only [CollatzResearch.WordTrace]
  refine ⟨287581515901799770888969391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191721010601199847259312927 287581515901799770888969391)
  ·
    refine ⟨431372273852699656333454087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287581515901799770888969391 431372273852699656333454087)
    ·
      refine ⟨647058410779049484500181131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431372273852699656333454087 647058410779049484500181131)
      ·
        refine ⟨970587616168574226750271697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647058410779049484500181131 970587616168574226750271697)
        ·
          refine ⟨727940712126430670062703773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970587616168574226750271697 727940712126430670062703773)
          ·
            refine ⟨272977767047411501273513915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727940712126430670062703773 272977767047411501273513915)
            ·
              refine ⟨409466650571117251910270873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272977767047411501273513915 409466650571117251910270873)
              ·
                refine ⟨307099987928337938932703155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409466650571117251910270873 307099987928337938932703155)
                ·
                  refine ⟨460649981892506908399054733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307099987928337938932703155 460649981892506908399054733)
                  ·
                    refine ⟨172743743209690090649645525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 460649981892506908399054733 172743743209690090649645525)
                    ·
                      refine ⟨4048681481477111499601067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172743743209690090649645525 4048681481477111499601067)
                      ·
                        rfl

theorem cell23_7884779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_7884779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884779 prefixEnd_7884779 := by exact prefixLift 7884779
  have htrace : WordTrace (prefixWord ++ tailWord_7884779) baseStart_7884779 baseEnd_7884779 := by
    simpa [prefixWord, tailWord_7884779, baseEnd_7884779] using wordTrace_append hprefix tailTrace_7884779
  have hstable : (prefixWord ++ tailWord_7884779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884779).length < 2 ^ (prefixWord ++ tailWord_7884779).sum := by decide
  have hdescent : baseEnd_7884779 < baseStart_7884779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884790 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_7884790 : Nat := 118140960795 + 7884790 * 2 ^ 59
def prefixEnd_7884790 : Nat := 4983230072969 + 3 ^ 40 * 7884790 * 2
def baseEnd_7884790 : Nat := 449854125529367884062613

theorem tailTrace_7884790 : CollatzResearch.WordTrace tailWord_7884790 prefixEnd_7884790 449854125529367884062613 := by
  unfold tailWord_7884790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17973869819047494985476239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191721278069839946511746549 17973869819047494985476239)
  ·
    refine ⟨26960804728571242478214359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17973869819047494985476239 26960804728571242478214359)
    ·
      refine ⟨40441207092856863717321539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26960804728571242478214359 40441207092856863717321539)
      ·
        refine ⟨60661810639285295575982309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40441207092856863717321539 60661810639285295575982309)
        ·
          refine ⟨11374089494865992920496683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60661810639285295575982309 11374089494865992920496683)
          ·
            refine ⟨17061134242298989380745025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374089494865992920496683 17061134242298989380745025)
            ·
              refine ⟨12795850681724242035558769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061134242298989380745025 12795850681724242035558769)
              ·
                refine ⟨9596888011293181526669077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12795850681724242035558769 9596888011293181526669077)
                ·
                  refine ⟨449854125529367884062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9596888011293181526669077 449854125529367884062613)
                  ·
                    rfl

theorem cell23_7884790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_7884790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884790 prefixEnd_7884790 := by exact prefixLift 7884790
  have htrace : WordTrace (prefixWord ++ tailWord_7884790) baseStart_7884790 baseEnd_7884790 := by
    simpa [prefixWord, tailWord_7884790, baseEnd_7884790] using wordTrace_append hprefix tailTrace_7884790
  have hstable : (prefixWord ++ tailWord_7884790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884790).length < 2 ^ (prefixWord ++ tailWord_7884790).sum := by decide
  have hdescent : baseEnd_7884790 < baseStart_7884790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884850 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_7884850 : Nat := 118140960795 + 7884850 * 2 ^ 59
def prefixEnd_7884850 : Nat := 4983230072969 + 3 ^ 40 * 7884850 * 2
def baseEnd_7884850 : Nat := 1349572646201193573937747

theorem tailTrace_7884850 : CollatzResearch.WordTrace tailWord_7884850 prefixEnd_7884850 1349572646201193573937747 := by
  unfold tailWord_7884850
  simp only [CollatzResearch.WordTrace]
  refine ⟨71896026371135637503701001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191722736989695033343202669 71896026371135637503701001)
  ·
    refine ⟨53922019778351728127775751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71896026371135637503701001 53922019778351728127775751)
    ·
      refine ⟨80883029667527592191663627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53922019778351728127775751 80883029667527592191663627)
      ·
        refine ⟨121324544501291388287495441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80883029667527592191663627 121324544501291388287495441)
        ·
          refine ⟨90993408375968541215621581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121324544501291388287495441 90993408375968541215621581)
          ·
            refine ⟨34122528140988202955858093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90993408375968541215621581 34122528140988202955858093)
            ·
              refine ⟨12795948052870576108446785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34122528140988202955858093 12795948052870576108446785)
              ·
                refine ⟨9596961039652932081335089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12795948052870576108446785 9596961039652932081335089)
                ·
                  refine ⟨7197720779739699061001317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9596961039652932081335089 7197720779739699061001317)
                  ·
                    refine ⟨1349572646201193573937747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197720779739699061001317 1349572646201193573937747)
                    ·
                      rfl

theorem cell23_7884850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_7884850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884850 prefixEnd_7884850 := by exact prefixLift 7884850
  have htrace : WordTrace (prefixWord ++ tailWord_7884850) baseStart_7884850 baseEnd_7884850 := by
    simpa [prefixWord, tailWord_7884850, baseEnd_7884850] using wordTrace_append hprefix tailTrace_7884850
  have hstable : (prefixWord ++ tailWord_7884850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884850).length < 2 ^ (prefixWord ++ tailWord_7884850).sum := by decide
  have hdescent : baseEnd_7884850 < baseStart_7884850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884870 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_7884870 : Nat := 118140960795 + 7884870 * 2 ^ 59
def prefixEnd_7884870 : Nat := 4983230072969 + 3 ^ 40 * 7884870 * 2
def baseEnd_7884870 : Nat := 4048728208216670643563149

theorem tailTrace_7884870 : CollatzResearch.WordTrace tailWord_7884870 prefixEnd_7884870 4048728208216670643563149 := by
  unfold tailWord_7884870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987026092014690419704127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191723223296313395620354709 8987026092014690419704127)
  ·
    refine ⟨13480539138022035629556191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987026092014690419704127 13480539138022035629556191)
    ·
      refine ⟨20220808707033053444334287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13480539138022035629556191 20220808707033053444334287)
      ·
        refine ⟨30331213060549580166501431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20220808707033053444334287 30331213060549580166501431)
        ·
          refine ⟨45496819590824370249752147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30331213060549580166501431 45496819590824370249752147)
          ·
            refine ⟨68245229386236555374628221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45496819590824370249752147 68245229386236555374628221)
            ·
              refine ⟨25591961019838708265485583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68245229386236555374628221 25591961019838708265485583)
              ·
                refine ⟨38387941529758062398228375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25591961019838708265485583 38387941529758062398228375)
                ·
                  refine ⟨57581912294637093597342563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38387941529758062398228375 57581912294637093597342563)
                  ·
                    refine ⟨86372868441955640396013845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57581912294637093597342563 86372868441955640396013845)
                    ·
                      refine ⟨4048728208216670643563149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86372868441955640396013845 4048728208216670643563149)
                      ·
                        rfl

theorem cell23_7884870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_7884870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884870 prefixEnd_7884870 := by exact prefixLift 7884870
  have htrace : WordTrace (prefixWord ++ tailWord_7884870) baseStart_7884870 baseEnd_7884870 := by
    simpa [prefixWord, tailWord_7884870, baseEnd_7884870] using wordTrace_append hprefix tailTrace_7884870
  have hstable : (prefixWord ++ tailWord_7884870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884870).length < 2 ^ (prefixWord ++ tailWord_7884870).sum := by decide
  have hdescent : baseEnd_7884870 < baseStart_7884870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884876 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_7884876 : Nat := 118140960795 + 7884876 * 2 ^ 59
def prefixEnd_7884876 : Nat := 4983230072969 + 3 ^ 40 * 7884876 * 2
def baseEnd_7884876 : Nat := 1349577096366865873362707

theorem tailTrace_7884876 : CollatzResearch.WordTrace tailWord_7884876 prefixEnd_7884876 1349577096366865873362707 := by
  unfold tailWord_7884876
  simp only [CollatzResearch.WordTrace]
  refine ⟨143792526891224178227625241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191723369188298904303500321 143792526891224178227625241)
  ·
    refine ⟨107844395168418133670718931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143792526891224178227625241 107844395168418133670718931)
    ·
      refine ⟨161766592752627200506078397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107844395168418133670718931 161766592752627200506078397)
      ·
        refine ⟨60662472282235200189779399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161766592752627200506078397 60662472282235200189779399)
        ·
          refine ⟨90993708423352800284669099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60662472282235200189779399 90993708423352800284669099)
          ·
            refine ⟨136490562635029200427003649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90993708423352800284669099 136490562635029200427003649)
            ·
              refine ⟨102367921976271900320252737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136490562635029200427003649 102367921976271900320252737)
              ·
                refine ⟨76775941482203925240189553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102367921976271900320252737 76775941482203925240189553)
                ·
                  refine ⟨57581956111652943930142165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76775941482203925240189553 57581956111652943930142165)
                  ·
                    refine ⟨1349577096366865873362707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57581956111652943930142165 1349577096366865873362707)
                    ·
                      rfl

theorem cell23_7884876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_7884876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884876 prefixEnd_7884876 := by exact prefixLift 7884876
  have htrace : WordTrace (prefixWord ++ tailWord_7884876) baseStart_7884876 baseEnd_7884876 := by
    simpa [prefixWord, tailWord_7884876, baseEnd_7884876] using wordTrace_append hprefix tailTrace_7884876
  have hstable : (prefixWord ++ tailWord_7884876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884876).length < 2 ^ (prefixWord ++ tailWord_7884876).sum := by decide
  have hdescent : baseEnd_7884876 < baseStart_7884876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884877 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_7884877 : Nat := 118140960795 + 7884877 * 2 ^ 59
def prefixEnd_7884877 : Nat := 4983230072969 + 3 ^ 40 * 7884877 * 2
def baseEnd_7884877 : Nat := 4048731802581252116175617

theorem tailTrace_7884877 : CollatzResearch.WordTrace tailWord_7884877 prefixEnd_7884877 4048731802581252116175617 := by
  unfold tailWord_7884877
  simp only [CollatzResearch.WordTrace]
  refine ⟨287585090255444733626036885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191723393503629822417357923 287585090255444733626036885)
  ·
    refine ⟨13480551105723971888720479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287585090255444733626036885 13480551105723971888720479)
    ·
      refine ⟨20220826658585957833080719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13480551105723971888720479 20220826658585957833080719)
      ·
        refine ⟨30331239987878936749621079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20220826658585957833080719 30331239987878936749621079)
        ·
          refine ⟨45496859981818405124431619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30331239987878936749621079 45496859981818405124431619)
          ·
            refine ⟨68245289972727607686647429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45496859981818405124431619 68245289972727607686647429)
            ·
              refine ⟨12795991869886426441246393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68245289972727607686647429 12795991869886426441246393)
              ·
                refine ⟨9596993902414819830934795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12795991869886426441246393 9596993902414819830934795)
                ·
                  refine ⟨14395490853622229746402193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9596993902414819830934795 14395490853622229746402193)
                  ·
                    refine ⟨10796618140216672309801645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14395490853622229746402193 10796618140216672309801645)
                    ·
                      refine ⟨4048731802581252116175617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796618140216672309801645 4048731802581252116175617)
                      ·
                        rfl

theorem cell23_7884877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_7884877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884877 prefixEnd_7884877 := by exact prefixLift 7884877
  have htrace : WordTrace (prefixWord ++ tailWord_7884877) baseStart_7884877 baseEnd_7884877 := by
    simpa [prefixWord, tailWord_7884877, baseEnd_7884877] using wordTrace_append hprefix tailTrace_7884877
  have hstable : (prefixWord ++ tailWord_7884877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884877).length < 2 ^ (prefixWord ++ tailWord_7884877).sum := by decide
  have hdescent : baseEnd_7884877 < baseStart_7884877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884894 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7884894 : Nat := 118140960795 + 7884894 * 2 ^ 59
def prefixEnd_7884894 : Nat := 4983230072969 + 3 ^ 40 * 7884894 * 2
def baseEnd_7884894 : Nat := 4048740531752378549663039

theorem tailTrace_7884894 : CollatzResearch.WordTrace tailWord_7884894 prefixEnd_7884894 4048740531752378549663039 := by
  unfold tailWord_7884894
  simp only [CollatzResearch.WordTrace]
  refine ⟨35948213787047893191175717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191723806864255430352937157 35948213787047893191175717)
  ·
    refine ⟨6740290085071479973345447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35948213787047893191175717 6740290085071479973345447)
    ·
      refine ⟨10110435127607219960018171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740290085071479973345447 10110435127607219960018171)
      ·
        refine ⟨15165652691410829940027257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110435127607219960018171 15165652691410829940027257)
        ·
          refine ⟨11374239518558122455020443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15165652691410829940027257 11374239518558122455020443)
          ·
            refine ⟨17061359277837183682530665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374239518558122455020443 17061359277837183682530665)
            ·
              refine ⟨12796019458377887761897999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061359277837183682530665 12796019458377887761897999)
              ·
                refine ⟨19194029187566831642846999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796019458377887761897999 19194029187566831642846999)
                ·
                  refine ⟨28791043781350247464270499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19194029187566831642846999 28791043781350247464270499)
                  ·
                    refine ⟨43186565672025371196405749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28791043781350247464270499 43186565672025371196405749)
                    ·
                      refine ⟨4048740531752378549663039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43186565672025371196405749 4048740531752378549663039)
                      ·
                        rfl

theorem cell23_7884894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7884894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884894 prefixEnd_7884894 := by exact prefixLift 7884894
  have htrace : WordTrace (prefixWord ++ tailWord_7884894) baseStart_7884894 baseEnd_7884894 := by
    simpa [prefixWord, tailWord_7884894, baseEnd_7884894] using wordTrace_append hprefix tailTrace_7884894
  have hstable : (prefixWord ++ tailWord_7884894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884894).length < 2 ^ (prefixWord ++ tailWord_7884894).sum := by decide
  have hdescent : baseEnd_7884894 < baseStart_7884894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884924 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_7884924 : Nat := 118140960795 + 7884924 * 2 ^ 59
def prefixEnd_7884924 : Nat := 4983230072969 + 3 ^ 40 * 7884924 * 2
def baseEnd_7884924 : Nat := 4048755936172013432287901

theorem tailTrace_7884924 : CollatzResearch.WordTrace tailWord_7884924 prefixEnd_7884924 4048755936172013432287901 := by
  unfold tailWord_7884924
  simp only [CollatzResearch.WordTrace]
  refine ⟨143793402243137230326498913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191724536324182973768665217 143793402243137230326498913)
  ·
    refine ⟨107845051682352922744874185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143793402243137230326498913 107845051682352922744874185)
    ·
      refine ⟨80883788761764692058655639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107845051682352922744874185 80883788761764692058655639)
      ·
        refine ⟨121325683142647038087983459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80883788761764692058655639 121325683142647038087983459)
        ·
          refine ⟨181988524713970557131975189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121325683142647038087983459 181988524713970557131975189)
          ·
            refine ⟨8530712095967369865561337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181988524713970557131975189 8530712095967369865561337)
            ·
              refine ⟨6398034071975527399171003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530712095967369865561337 6398034071975527399171003)
              ·
                refine ⟨9597051107963291098756505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398034071975527399171003 9597051107963291098756505)
                ·
                  refine ⟨7197788330972468324067379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597051107963291098756505 7197788330972468324067379)
                  ·
                    refine ⟨10796682496458702486101069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7197788330972468324067379 10796682496458702486101069)
                    ·
                      refine ⟨4048755936172013432287901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10796682496458702486101069 4048755936172013432287901)
                      ·
                        rfl

theorem cell23_7884924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_7884924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884924 prefixEnd_7884924 := by exact prefixLift 7884924
  have htrace : WordTrace (prefixWord ++ tailWord_7884924) baseStart_7884924 baseEnd_7884924 := by
    simpa [prefixWord, tailWord_7884924, baseEnd_7884924] using wordTrace_append hprefix tailTrace_7884924
  have hstable : (prefixWord ++ tailWord_7884924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884924).length < 2 ^ (prefixWord ++ tailWord_7884924).sum := by decide
  have hdescent : baseEnd_7884924 < baseStart_7884924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7884933 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_7884933 : Nat := 118140960795 + 7884933 * 2 ^ 59
def prefixEnd_7884933 : Nat := 4983230072969 + 3 ^ 40 * 7884933 * 2
def baseEnd_7884933 : Nat := 4048760557497903897075359

theorem tailTrace_7884933 : CollatzResearch.WordTrace tailWord_7884933 prefixEnd_7884933 4048760557497903897075359 := by
  unfold tailWord_7884933
  simp only [CollatzResearch.WordTrace]
  refine ⟨287587132743241855190075453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191724755162161236793383635 287587132743241855190075453)
  ·
    refine ⟨107845174778715695696278295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287587132743241855190075453 107845174778715695696278295)
    ·
      refine ⟨161767762168073543544417443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107845174778715695696278295 161767762168073543544417443)
      ·
        refine ⟨242651643252110315316626165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161767762168073543544417443 242651643252110315316626165)
        ·
          refine ⟨22748591554885342060933703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242651643252110315316626165 22748591554885342060933703)
          ·
            refine ⟨34122887332328013091400555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22748591554885342060933703 34122887332328013091400555)
            ·
              refine ⟨51184330998492019637100833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34122887332328013091400555 51184330998492019637100833)
              ·
                refine ⟨38388248248869014727825625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51184330998492019637100833 38388248248869014727825625)
                ·
                  refine ⟨28791186186651761045869219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38388248248869014727825625 28791186186651761045869219)
                  ·
                    refine ⟨43186779279977641568803829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28791186186651761045869219 43186779279977641568803829)
                    ·
                      refine ⟨4048760557497903897075359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43186779279977641568803829 4048760557497903897075359)
                      ·
                        rfl

theorem cell23_7884933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_7884933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7884933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7884933 prefixEnd_7884933 := by exact prefixLift 7884933
  have htrace : WordTrace (prefixWord ++ tailWord_7884933) baseStart_7884933 baseEnd_7884933 := by
    simpa [prefixWord, tailWord_7884933, baseEnd_7884933] using wordTrace_append hprefix tailTrace_7884933
  have hstable : (prefixWord ++ tailWord_7884933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7884933).length < 2 ^ (prefixWord ++ tailWord_7884933).sum := by decide
  have hdescent : baseEnd_7884933 < baseStart_7884933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7884933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885003 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_7885003 : Nat := 118140960795 + 7885003 * 2 ^ 59
def prefixEnd_7885003 : Nat := 4983230072969 + 3 ^ 40 * 7885003 * 2
def baseEnd_7885003 : Nat := 4048796501143718623200037

theorem tailTrace_7885003 : CollatzResearch.WordTrace tailWord_7885003 prefixEnd_7885003 4048796501143718623200037 := by
  unfold tailWord_7885003
  simp only [CollatzResearch.WordTrace]
  refine ⟨287589685852988257145123663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191726457235325504763415775 287589685852988257145123663)
  ·
    refine ⟨431384528779482385717685495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287589685852988257145123663 431384528779482385717685495)
    ·
      refine ⟨647076793169223578576528243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431384528779482385717685495 647076793169223578576528243)
      ·
        refine ⟨970615189753835367864792365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647076793169223578576528243 970615189753835367864792365)
        ·
          refine ⟨363980696157688262949297137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 970615189753835367864792365 363980696157688262949297137)
          ·
            refine ⟨272985522118266197211972853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363980696157688262949297137 272985522118266197211972853)
            ·
              refine ⟨25592392698587455988622455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 272985522118266197211972853 25592392698587455988622455)
              ·
                refine ⟨38388589047881183982933683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25592392698587455988622455 38388589047881183982933683)
                ·
                  refine ⟨57582883571821775974400525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38388589047881183982933683 57582883571821775974400525)
                  ·
                    refine ⟨21593581339433165990400197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57582883571821775974400525 21593581339433165990400197)
                    ·
                      refine ⟨4048796501143718623200037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21593581339433165990400197 4048796501143718623200037)
                      ·
                        rfl

theorem cell23_7885003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_7885003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885003 prefixEnd_7885003 := by exact prefixLift 7885003
  have htrace : WordTrace (prefixWord ++ tailWord_7885003) baseStart_7885003 baseEnd_7885003 := by
    simpa [prefixWord, tailWord_7885003, baseEnd_7885003] using wordTrace_append hprefix tailTrace_7885003
  have hstable : (prefixWord ++ tailWord_7885003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885003).length < 2 ^ (prefixWord ++ tailWord_7885003).sum := by decide
  have hdescent : baseEnd_7885003 < baseStart_7885003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885004 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 5]
def baseStart_7885004 : Nat := 118140960795 + 7885004 * 2 ^ 59
def prefixEnd_7885004 : Nat := 4983230072969 + 3 ^ 40 * 7885004 * 2
def baseEnd_7885004 : Nat := 449866334958263679920837

theorem tailTrace_7885004 : CollatzResearch.WordTrace tailWord_7885004 prefixEnd_7885004 449866334958263679920837 := by
  unfold tailWord_7885004
  simp only [CollatzResearch.WordTrace]
  refine ⟨143794861162992317157955033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191726481550656422877273377 143794861162992317157955033)
  ·
    refine ⟨107846145872244237868466275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143794861162992317157955033 107846145872244237868466275)
    ·
      refine ⟨161769218808366356802699413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107846145872244237868466275 161769218808366356802699413)
      ·
        refine ⟨7582932131642172975126535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161769218808366356802699413 7582932131642172975126535)
        ·
          refine ⟨11374398197463259462689803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582932131642172975126535 11374398197463259462689803)
          ·
            refine ⟨17061597296194889194034705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374398197463259462689803 17061597296194889194034705)
            ·
              refine ⟨12796197972146166895526029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061597296194889194034705 12796197972146166895526029)
              ·
                refine ⟨4798574239554812585822261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12796197972146166895526029 4798574239554812585822261)
                ·
                  refine ⟨449866334958263679920837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798574239554812585822261 449866334958263679920837)
                  ·
                    rfl

theorem cell23_7885004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_7885004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885004 prefixEnd_7885004 := by exact prefixLift 7885004
  have htrace : WordTrace (prefixWord ++ tailWord_7885004) baseStart_7885004 baseEnd_7885004 := by
    simpa [prefixWord, tailWord_7885004, baseEnd_7885004] using wordTrace_append hprefix tailTrace_7885004
  have hstable : (prefixWord ++ tailWord_7885004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885004).length < 2 ^ (prefixWord ++ tailWord_7885004).sum := by decide
  have hdescent : baseEnd_7885004 < baseStart_7885004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885064 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 1, 4]
def baseStart_7885064 : Nat := 118140960795 + 7885064 * 2 ^ 59
def prefixEnd_7885064 : Nat := 4983230072969 + 3 ^ 40 * 7885064 * 2
def baseEnd_7885064 : Nat := 1349609274487880961512419

theorem tailTrace_7885064 : CollatzResearch.WordTrace tailWord_7885064 prefixEnd_7885064 1349609274487880961512419 := by
  unfold tailWord_7885064
  simp only [CollatzResearch.WordTrace]
  refine ⟨143795955352883632281547123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191727940470511509708729497 143795955352883632281547123)
  ·
    refine ⟨215693933029325448422320685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143795955352883632281547123 215693933029325448422320685)
    ·
      refine ⟨80885224885997043158370257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215693933029325448422320685 80885224885997043158370257)
      ·
        refine ⟨60663918664497782368777693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80885224885997043158370257 60663918664497782368777693)
        ·
          refine ⟨22748969499186668388291635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60663918664497782368777693 22748969499186668388291635)
          ·
            refine ⟨34123454248780002582437453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22748969499186668388291635 34123454248780002582437453)
            ·
              refine ⟨12796295343292500968414045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34123454248780002582437453 12796295343292500968414045)
              ·
                refine ⟨4798610753734687863155267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12796295343292500968414045 4798610753734687863155267)
                ·
                  refine ⟨7197916130602031794732901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798610753734687863155267 7197916130602031794732901)
                  ·
                    refine ⟨1349609274487880961512419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197916130602031794732901 1349609274487880961512419)
                    ·
                      rfl

theorem cell23_7885064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_7885064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885064 prefixEnd_7885064 := by exact prefixLift 7885064
  have htrace : WordTrace (prefixWord ++ tailWord_7885064) baseStart_7885064 baseEnd_7885064 := by
    simpa [prefixWord, tailWord_7885064, baseEnd_7885064] using wordTrace_append hprefix tailTrace_7885064
  have hstable : (prefixWord ++ tailWord_7885064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885064).length < 2 ^ (prefixWord ++ tailWord_7885064).sum := by decide
  have hdescent : baseEnd_7885064 < baseStart_7885064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885114 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_7885114 : Nat := 118140960795 + 7885114 * 2 ^ 59
def prefixEnd_7885114 : Nat := 4983230072969 + 3 ^ 40 * 7885114 * 2
def baseEnd_7885114 : Nat := 4048853497496367688912027

theorem tailTrace_7885114 : CollatzResearch.WordTrace tailWord_7885114 prefixEnd_7885114 4048853497496367688912027 := by
  unfold tailWord_7885114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71898433588896530775603599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191729156237057415401609597 71898433588896530775603599)
  ·
    refine ⟨107847650383344796163405399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71898433588896530775603599 107847650383344796163405399)
    ·
      refine ⟨161771475575017194245108099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107847650383344796163405399 161771475575017194245108099)
      ·
        refine ⟨242657213362525791367662149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161771475575017194245108099 242657213362525791367662149)
        ·
          refine ⟨45498227505473585881436653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242657213362525791367662149 45498227505473585881436653)
          ·
            refine ⟨17061835314552594705538745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45498227505473585881436653 17061835314552594705538745)
            ·
              refine ⟨12796376485914446029154059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061835314552594705538745 12796376485914446029154059)
              ·
                refine ⟨19194564728871669043731089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796376485914446029154059 19194564728871669043731089)
                ·
                  refine ⟨14395923546653751782798317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19194564728871669043731089 14395923546653751782798317)
                  ·
                    refine ⟨5398471329995156918549369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14395923546653751782798317 5398471329995156918549369)
                    ·
                      refine ⟨4048853497496367688912027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398471329995156918549369 4048853497496367688912027)
                      ·
                        rfl

theorem cell23_7885114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_7885114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885114 prefixEnd_7885114 := by exact prefixLift 7885114
  have htrace : WordTrace (prefixWord ++ tailWord_7885114) baseStart_7885114 baseEnd_7885114 := by
    simpa [prefixWord, tailWord_7885114, baseEnd_7885114] using wordTrace_append hprefix tailTrace_7885114
  have hstable : (prefixWord ++ tailWord_7885114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885114).length < 2 ^ (prefixWord ++ tailWord_7885114).sum := by decide
  have hdescent : baseEnd_7885114 < baseStart_7885114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885120 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_7885120 : Nat := 118140960795 + 7885120 * 2 ^ 59
def prefixEnd_7885120 : Nat := 4983230072969 + 3 ^ 40 * 7885120 * 2
def baseEnd_7885120 : Nat := 1349618859460098221812333

theorem tailTrace_7885120 : CollatzResearch.WordTrace tailWord_7885120 prefixEnd_7885120 1349618859460098221812333 := by
  unfold tailWord_7885120
  simp only [CollatzResearch.WordTrace]
  refine ⟨143796976596782193063566407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191729302129042924084755209 143796976596782193063566407)
  ·
    refine ⟨215695464895173289595349611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143796976596782193063566407 215695464895173289595349611)
    ·
      refine ⟨323543197342759934393024417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215695464895173289595349611 323543197342759934393024417)
      ·
        refine ⟨242657398007069950794768313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323543197342759934393024417 242657398007069950794768313)
        ·
          refine ⟨181993048505302463096076235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242657398007069950794768313 181993048505302463096076235)
          ·
            refine ⟨272989572757953694644114353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181993048505302463096076235 272989572757953694644114353)
            ·
              refine ⟨204742179568465270983085765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272989572757953694644114353 204742179568465270983085765)
              ·
                refine ⟨38389158669087238309328581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204742179568465270983085765 38389158669087238309328581)
                ·
                  refine ⟨7197967250453857182999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38389158669087238309328581 7197967250453857182999109)
                  ·
                    refine ⟨1349618859460098221812333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197967250453857182999109 1349618859460098221812333)
                    ·
                      rfl

theorem cell23_7885120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_7885120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885120 prefixEnd_7885120 := by exact prefixLift 7885120
  have htrace : WordTrace (prefixWord ++ tailWord_7885120) baseStart_7885120 baseEnd_7885120 := by
    simpa [prefixWord, tailWord_7885120, baseEnd_7885120] using wordTrace_append hprefix tailTrace_7885120
  have hstable : (prefixWord ++ tailWord_7885120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885120).length < 2 ^ (prefixWord ++ tailWord_7885120).sum := by decide
  have hdescent : baseEnd_7885120 < baseStart_7885120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885137 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_7885137 : Nat := 118140960795 + 7885137 * 2 ^ 59
def prefixEnd_7885137 : Nat := 4983230072969 + 3 ^ 40 * 7885137 * 2
def baseEnd_7885137 : Nat := 1349621769183807032974807

theorem tailTrace_7885137 : CollatzResearch.WordTrace tailWord_7885137 prefixEnd_7885137 1349621769183807032974807 := by
  unfold tailWord_7885137
  simp only [CollatzResearch.WordTrace]
  refine ⟨287594573234502798030501665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191729715489668532020334443 287594573234502798030501665)
  ·
    refine ⟨215695929925877098522876249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287594573234502798030501665 215695929925877098522876249)
    ·
      refine ⟨161771947444407823892157187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215695929925877098522876249 161771947444407823892157187)
      ·
        refine ⟨242657921166611735838235781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161771947444407823892157187 242657921166611735838235781)
        ·
          refine ⟨45498360218739700469669209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242657921166611735838235781 45498360218739700469669209)
          ·
            refine ⟨34123770164054775352251907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45498360218739700469669209 34123770164054775352251907)
            ·
              refine ⟨51185655246082163028377861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34123770164054775352251907 51185655246082163028377861)
              ·
                refine ⟨9597310358640405567820849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51185655246082163028377861 9597310358640405567820849)
                ·
                  refine ⟨7197982768980304175865637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597310358640405567820849 7197982768980304175865637)
                  ·
                    refine ⟨1349621769183807032974807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197982768980304175865637 1349621769183807032974807)
                    ·
                      rfl

theorem cell23_7885137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_7885137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885137 prefixEnd_7885137 := by exact prefixLift 7885137
  have htrace : WordTrace (prefixWord ++ tailWord_7885137) baseStart_7885137 baseEnd_7885137 := by
    simpa [prefixWord, tailWord_7885137, baseEnd_7885137] using wordTrace_append hprefix tailTrace_7885137
  have hstable : (prefixWord ++ tailWord_7885137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885137).length < 2 ^ (prefixWord ++ tailWord_7885137).sum := by decide
  have hdescent : baseEnd_7885137 < baseStart_7885137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885154 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7885154 : Nat := 118140960795 + 7885154 * 2 ^ 59
def prefixEnd_7885154 : Nat := 4983230072969 + 3 ^ 40 * 7885154 * 2
def baseEnd_7885154 : Nat := 1349624678907515844137281

theorem tailTrace_7885154 : CollatzResearch.WordTrace tailWord_7885154 prefixEnd_7885154 1349624678907515844137281 := by
  unfold tailWord_7885154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71898798318860302483467629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191730128850294139955913677 71898798318860302483467629)
  ·
    refine ⟨26962049369572613431300361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71898798318860302483467629 26962049369572613431300361)
    ·
      refine ⟨20221537027179460073475271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26962049369572613431300361 20221537027179460073475271)
      ·
        refine ⟨30332305540769190110212907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20221537027179460073475271 30332305540769190110212907)
        ·
          refine ⟨45498458311153785165319361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30332305540769190110212907 45498458311153785165319361)
          ·
            refine ⟨34123843733365338873989521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45498458311153785165319361 34123843733365338873989521)
            ·
              refine ⟨25592882800024004155492141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34123843733365338873989521 25592882800024004155492141)
              ·
                refine ⟨9597331050009001558309553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25592882800024004155492141 9597331050009001558309553)
                ·
                  refine ⟨7197998287506751168732165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597331050009001558309553 7197998287506751168732165)
                  ·
                    refine ⟨1349624678907515844137281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7197998287506751168732165 1349624678907515844137281)
                    ·
                      rfl

theorem cell23_7885154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7885154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885154 prefixEnd_7885154 := by exact prefixLift 7885154
  have htrace : WordTrace (prefixWord ++ tailWord_7885154) baseStart_7885154 baseEnd_7885154 := by
    simpa [prefixWord, tailWord_7885154, baseEnd_7885154] using wordTrace_append hprefix tailTrace_7885154
  have hstable : (prefixWord ++ tailWord_7885154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885154).length < 2 ^ (prefixWord ++ tailWord_7885154).sum := by decide
  have hdescent : baseEnd_7885154 < baseStart_7885154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885157 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_7885157 : Nat := 118140960795 + 7885157 * 2 ^ 59
def prefixEnd_7885157 : Nat := 4983230072969 + 3 ^ 40 * 7885157 * 2
def baseEnd_7885157 : Nat := 4048875577164511020674329

theorem tailTrace_7885157 : CollatzResearch.WordTrace tailWord_7885157 prefixEnd_7885157 4048875577164511020674329 := by
  unfold tailWord_7885157
  simp only [CollatzResearch.WordTrace]
  refine ⟨287595302694430341446229725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191730201796286894297486483 287595302694430341446229725)
  ·
    refine ⟨107848238510411378042336147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287595302694430341446229725 107848238510411378042336147)
    ·
      refine ⟨161772357765617067063504221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107848238510411378042336147 161772357765617067063504221)
      ·
        refine ⟨60664634162106400148814083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161772357765617067063504221 60664634162106400148814083)
        ·
          refine ⟨90996951243159600223221125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60664634162106400148814083 90996951243159600223221125)
          ·
            refine ⟨17061928358092425041853961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90996951243159600223221125 17061928358092425041853961)
            ·
              refine ⟨12796446268569318781390471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17061928358092425041853961 12796446268569318781390471)
              ·
                refine ⟨19194669402853978172085707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796446268569318781390471 19194669402853978172085707)
                ·
                  refine ⟨28792004104280967258128561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19194669402853978172085707 28792004104280967258128561)
                  ·
                    refine ⟨21594003078210725443596421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28792004104280967258128561 21594003078210725443596421)
                    ·
                      refine ⟨4048875577164511020674329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21594003078210725443596421 4048875577164511020674329)
                      ·
                        rfl

theorem cell23_7885157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_7885157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885157 prefixEnd_7885157 := by exact prefixLift 7885157
  have htrace : WordTrace (prefixWord ++ tailWord_7885157) baseStart_7885157 baseEnd_7885157 := by
    simpa [prefixWord, tailWord_7885157, baseEnd_7885157] using wordTrace_append hprefix tailTrace_7885157
  have hstable : (prefixWord ++ tailWord_7885157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885157).length < 2 ^ (prefixWord ++ tailWord_7885157).sum := by decide
  have hdescent : baseEnd_7885157 < baseStart_7885157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885177 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_7885177 : Nat := 118140960795 + 7885177 * 2 ^ 59
def prefixEnd_7885177 : Nat := 4983230072969 + 3 ^ 40 * 7885177 * 2
def baseEnd_7885177 : Nat := 4048885846777600942424237

theorem tailTrace_7885177 : CollatzResearch.WordTrace tailWord_7885177 prefixEnd_7885177 4048885846777600942424237 := by
  unfold tailWord_7885177
  simp only [CollatzResearch.WordTrace]
  refine ⟨287596032154357884861957785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191730688102905256574638523 287596032154357884861957785)
  ·
    refine ⟨215697024115768413646468339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287596032154357884861957785 215697024115768413646468339)
    ·
      refine ⟨323545536173652620469702509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215697024115768413646468339 323545536173652620469702509)
      ·
        refine ⟨121329576065119732676138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323545536173652620469702509 121329576065119732676138441)
        ·
          refine ⟨90997182048839799507103831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121329576065119732676138441 90997182048839799507103831)
          ·
            refine ⟨136495773073259699260655747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90997182048839799507103831 136495773073259699260655747)
            ·
              refine ⟨204743659609889548890983621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136495773073259699260655747 204743659609889548890983621)
              ·
                refine ⟨38389436176854290417059429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204743659609889548890983621 38389436176854290417059429)
                ·
                  refine ⟨7198019283160179453198643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38389436176854290417059429 7198019283160179453198643)
                  ·
                    refine ⟨10797028924740269179797965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198019283160179453198643 10797028924740269179797965)
                    ·
                      refine ⟨4048885846777600942424237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797028924740269179797965 4048885846777600942424237)
                      ·
                        rfl

theorem cell23_7885177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_7885177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885177 prefixEnd_7885177 := by exact prefixLift 7885177
  have htrace : WordTrace (prefixWord ++ tailWord_7885177) baseStart_7885177 baseEnd_7885177 := by
    simpa [prefixWord, tailWord_7885177, baseEnd_7885177] using wordTrace_append hprefix tailTrace_7885177
  have hstable : (prefixWord ++ tailWord_7885177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885177).length < 2 ^ (prefixWord ++ tailWord_7885177).sum := by decide
  have hdescent : baseEnd_7885177 < baseStart_7885177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885181 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_7885181 : Nat := 118140960795 + 7885181 * 2 ^ 59
def prefixEnd_7885181 : Nat := 4983230072969 + 3 ^ 40 * 7885181 * 2
def baseEnd_7885181 : Nat := 4048887900700218926774219

theorem tailTrace_7885181 : CollatzResearch.WordTrace tailWord_7885181 prefixEnd_7885181 4048887900700218926774219 := by
  unfold tailWord_7885181
  simp only [CollatzResearch.WordTrace]
  refine ⟨287596178046343393545103397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191730785364228929030068931 287596178046343393545103397)
  ·
    refine ⟨53924283383689386289706887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287596178046343393545103397 53924283383689386289706887)
    ·
      refine ⟨80886425075534079434560331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53924283383689386289706887 80886425075534079434560331)
      ·
        refine ⟨121329637613301119151840497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80886425075534079434560331 121329637613301119151840497)
        ·
          refine ⟨90997228209975839363880373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121329637613301119151840497 90997228209975839363880373)
          ·
            refine ⟨8530990144685234940363785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90997228209975839363880373 8530990144685234940363785)
            ·
              refine ⟨6398242608513926205272839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8530990144685234940363785 6398242608513926205272839)
              ·
                refine ⟨9597363912770889307909259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398242608513926205272839 9597363912770889307909259)
                ·
                  refine ⟨14396045869156333961863889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9597363912770889307909259 14396045869156333961863889)
                  ·
                    refine ⟨10797034401867250471397917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14396045869156333961863889 10797034401867250471397917)
                    ·
                      refine ⟨4048887900700218926774219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797034401867250471397917 4048887900700218926774219)
                      ·
                        rfl

theorem cell23_7885181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_7885181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885181 prefixEnd_7885181 := by exact prefixLift 7885181
  have htrace : WordTrace (prefixWord ++ tailWord_7885181) baseStart_7885181 baseEnd_7885181 := by
    simpa [prefixWord, tailWord_7885181, baseEnd_7885181] using wordTrace_append hprefix tailTrace_7885181
  have hstable : (prefixWord ++ tailWord_7885181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885181).length < 2 ^ (prefixWord ++ tailWord_7885181).sum := by decide
  have hdescent : baseEnd_7885181 < baseStart_7885181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885234 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_7885234 : Nat := 118140960795 + 7885234 * 2 ^ 59
def prefixEnd_7885234 : Nat := 4983230072969 + 3 ^ 40 * 7885234 * 2
def baseEnd_7885234 : Nat := 4048915115174907219411475

theorem tailTrace_7885234 : CollatzResearch.WordTrace tailWord_7885234 prefixEnd_7885234 4048915115174907219411475 := by
  unfold tailWord_7885234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71899527778787845899195689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191732074076767589064521837 71899527778787845899195689)
  ·
    refine ⟨53924645834090884424396767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71899527778787845899195689 53924645834090884424396767)
    ·
      refine ⟨80886968751136326636595151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53924645834090884424396767 80886968751136326636595151)
      ·
        refine ⟨121330453126704489954892727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80886968751136326636595151 121330453126704489954892727)
        ·
          refine ⟨181995679690056734932339091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121330453126704489954892727 181995679690056734932339091)
          ·
            refine ⟨272993519535085102398508637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181995679690056734932339091 272993519535085102398508637)
            ·
              refine ⟨102372569825656913399440739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272993519535085102398508637 102372569825656913399440739)
              ·
                refine ⟨153558854738485370099161109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102372569825656913399440739 153558854738485370099161109)
                ·
                  refine ⟨7198071315866501723398177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153558854738485370099161109 7198071315866501723398177)
                  ·
                    refine ⟨5398553486899876292548633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198071315866501723398177 5398553486899876292548633)
                    ·
                      refine ⟨4048915115174907219411475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398553486899876292548633 4048915115174907219411475)
                      ·
                        rfl

theorem cell23_7885234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_7885234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885234 prefixEnd_7885234 := by exact prefixLift 7885234
  have htrace : WordTrace (prefixWord ++ tailWord_7885234) baseStart_7885234 baseEnd_7885234 := by
    simpa [prefixWord, tailWord_7885234, baseEnd_7885234] using wordTrace_append hprefix tailTrace_7885234
  have hstable : (prefixWord ++ tailWord_7885234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885234).length < 2 ^ (prefixWord ++ tailWord_7885234).sum := by decide
  have hdescent : baseEnd_7885234 < baseStart_7885234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885257 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 5]
def baseStart_7885257 : Nat := 118140960795 + 7885257 * 2 ^ 59
def prefixEnd_7885257 : Nat := 4983230072969 + 3 ^ 40 * 7885257 * 2
def baseEnd_7885257 : Nat := 449880769469995625491541

theorem tailTrace_7885257 : CollatzResearch.WordTrace tailWord_7885257 prefixEnd_7885257 449880769469995625491541 := by
  unfold tailWord_7885257
  simp only [CollatzResearch.WordTrace]
  refine ⟨287598949994068058524870025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191732633329378705683246683 287598949994068058524870025)
  ·
    refine ⟨215699212495551043893652519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287598949994068058524870025 215699212495551043893652519)
    ·
      refine ⟨323548818743326565840478779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215699212495551043893652519 323548818743326565840478779)
      ·
        refine ⟨485323228114989848760718169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323548818743326565840478779 485323228114989848760718169)
        ·
          refine ⟨363992421086242386570538627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485323228114989848760718169 363992421086242386570538627)
          ·
            refine ⟨545988631629363579855807941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363992421086242386570538627 545988631629363579855807941)
            ·
              refine ⟨102372868430505671222963989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 545988631629363579855807941 102372868430505671222963989)
              ·
                refine ⟨4798728207679953338576437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102372868430505671222963989 4798728207679953338576437)
                ·
                  refine ⟨449880769469995625491541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798728207679953338576437 449880769469995625491541)
                  ·
                    rfl

theorem cell23_7885257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 5].length) (baseStart_7885257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885257 prefixEnd_7885257 := by exact prefixLift 7885257
  have htrace : WordTrace (prefixWord ++ tailWord_7885257) baseStart_7885257 baseEnd_7885257 := by
    simpa [prefixWord, tailWord_7885257, baseEnd_7885257] using wordTrace_append hprefix tailTrace_7885257
  have hstable : (prefixWord ++ tailWord_7885257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885257).length < 2 ^ (prefixWord ++ tailWord_7885257).sum := by decide
  have hdescent : baseEnd_7885257 < baseStart_7885257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885268 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7885268 : Nat := 118140960795 + 7885268 * 2 ^ 59
def prefixEnd_7885268 : Nat := 4983230072969 + 3 ^ 40 * 7885268 * 2
def baseEnd_7885268 : Nat := 4048932573517160086386319

theorem tailTrace_7885268 : CollatzResearch.WordTrace tailWord_7885268 prefixEnd_7885268 4048932573517160086386319 := by
  unfold tailWord_7885268
  simp only [CollatzResearch.WordTrace]
  refine ⟨143799675598514103701760229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191732900798018804935680305 143799675598514103701760229)
  ·
    refine ⟨26962439174721394444080043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143799675598514103701760229 26962439174721394444080043)
    ·
      refine ⟨40443658762082091666120065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26962439174721394444080043 40443658762082091666120065)
      ·
        refine ⟨30332744071561568749590049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40443658762082091666120065 30332744071561568749590049)
        ·
          refine ⟨22749558053671176562192537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30332744071561568749590049 22749558053671176562192537)
          ·
            refine ⟨17062168540253382421644403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22749558053671176562192537 17062168540253382421644403)
            ·
              refine ⟨25593252810380073632466605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17062168540253382421644403 25593252810380073632466605)
              ·
                refine ⟨9597469803892527612174977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25593252810380073632466605 9597469803892527612174977)
                ·
                  refine ⟨7198102352919395709131233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597469803892527612174977 7198102352919395709131233)
                  ·
                    refine ⟨5398576764689546781848425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198102352919395709131233 5398576764689546781848425)
                    ·
                      refine ⟨4048932573517160086386319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398576764689546781848425 4048932573517160086386319)
                      ·
                        rfl

theorem cell23_7885268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7885268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885268 prefixEnd_7885268 := by exact prefixLift 7885268
  have htrace : WordTrace (prefixWord ++ tailWord_7885268) baseStart_7885268 baseEnd_7885268 := by
    simpa [prefixWord, tailWord_7885268, baseEnd_7885268] using wordTrace_append hprefix tailTrace_7885268
  have hstable : (prefixWord ++ tailWord_7885268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885268).length < 2 ^ (prefixWord ++ tailWord_7885268).sum := by decide
  have hdescent : baseEnd_7885268 < baseStart_7885268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885280 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_7885280 : Nat := 118140960795 + 7885280 * 2 ^ 59
def prefixEnd_7885280 : Nat := 4983230072969 + 3 ^ 40 * 7885280 * 2
def baseEnd_7885280 : Nat := 4048938735285014039436263

theorem tailTrace_7885280 : CollatzResearch.WordTrace tailWord_7885280 prefixEnd_7885280 4048938735285014039436263 := by
  unfold tailWord_7885280
  simp only [CollatzResearch.WordTrace]
  refine ⟨143799894436492366726478647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191733192581989822301971529 143799894436492366726478647)
  ·
    refine ⟨215699841654738550089717971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143799894436492366726478647 215699841654738550089717971)
    ·
      refine ⟨323549762482107825134576957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215699841654738550089717971 323549762482107825134576957)
      ·
        refine ⟨121331160930790434425466359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323549762482107825134576957 121331160930790434425466359)
        ·
          refine ⟨181996741396185651638199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121331160930790434425466359 181996741396185651638199539)
          ·
            refine ⟨272995112094278477457299309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181996741396185651638199539 272995112094278477457299309)
            ·
              refine ⟨102373167035354429046487241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272995112094278477457299309 102373167035354429046487241)
              ·
                refine ⟨76779875276515821784865431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102373167035354429046487241 76779875276515821784865431)
                ·
                  refine ⟨115169812914773732677298147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76779875276515821784865431 115169812914773732677298147)
                  ·
                    refine ⟨172754719372160599015947221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115169812914773732677298147 172754719372160599015947221)
                    ·
                      refine ⟨4048938735285014039436263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 172754719372160599015947221 4048938735285014039436263)
                      ·
                        rfl

theorem cell23_7885280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_7885280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885280 prefixEnd_7885280 := by exact prefixLift 7885280
  have htrace : WordTrace (prefixWord ++ tailWord_7885280) baseStart_7885280 baseEnd_7885280 := by
    simpa [prefixWord, tailWord_7885280, baseEnd_7885280] using wordTrace_append hprefix tailTrace_7885280
  have hstable : (prefixWord ++ tailWord_7885280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885280).length < 2 ^ (prefixWord ++ tailWord_7885280).sum := by decide
  have hdescent : baseEnd_7885280 < baseStart_7885280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885318 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7885318 : Nat := 118140960795 + 7885318 * 2 ^ 59
def prefixEnd_7885318 : Nat := 4983230072969 + 3 ^ 40 * 7885318 * 2
def baseEnd_7885318 : Nat := 4048958247549884890761089

theorem tailTrace_7885318 : CollatzResearch.WordTrace tailWord_7885318 prefixEnd_7885318 4048958247549884890761089 := by
  unfold tailWord_7885318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987536713963970810713769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191734116564564710628560405 8987536713963970810713769)
  ·
    refine ⟨6740652535472978108035327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8987536713963970810713769 6740652535472978108035327)
    ·
      refine ⟨10110978803209467162052991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740652535472978108035327 10110978803209467162052991)
      ·
        refine ⟨15166468204814200743079487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110978803209467162052991 15166468204814200743079487)
        ·
          refine ⟨22749702307221301114619231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15166468204814200743079487 22749702307221301114619231)
          ·
            refine ⟨34124553460831951671928847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22749702307221301114619231 34124553460831951671928847)
            ·
              refine ⟨51186830191247927507893271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34124553460831951671928847 51186830191247927507893271)
              ·
                refine ⟨76780245286871891261839907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51186830191247927507893271 76780245286871891261839907)
                ·
                  refine ⟨115170367930307836892759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76780245286871891261839907 115170367930307836892759861)
                  ·
                    refine ⟨10797221993466359708696237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115170367930307836892759861 10797221993466359708696237)
                    ·
                      refine ⟨4048958247549884890761089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797221993466359708696237 4048958247549884890761089)
                      ·
                        rfl

theorem cell23_7885318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7885318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885318 prefixEnd_7885318 := by exact prefixLift 7885318
  have htrace : WordTrace (prefixWord ++ tailWord_7885318) baseStart_7885318 baseEnd_7885318 := by
    simpa [prefixWord, tailWord_7885318, baseEnd_7885318] using wordTrace_append hprefix tailTrace_7885318
  have hstable : (prefixWord ++ tailWord_7885318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885318).length < 2 ^ (prefixWord ++ tailWord_7885318).sum := by decide
  have hdescent : baseEnd_7885318 < baseStart_7885318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885324 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_7885324 : Nat := 118140960795 + 7885324 * 2 ^ 59
def prefixEnd_7885324 : Nat := 4983230072969 + 3 ^ 40 * 7885324 * 2
def baseEnd_7885324 : Nat := 4048961328433811867286061

theorem tailTrace_7885324 : CollatzResearch.WordTrace tailWord_7885324 prefixEnd_7885324 4048961328433811867286061 := by
  unfold tailWord_7885324
  simp only [CollatzResearch.WordTrace]
  refine ⟨143800696842412664483779513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191734262456550219311706017 143800696842412664483779513)
  ·
    refine ⟨107850522631809498362834635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143800696842412664483779513 107850522631809498362834635)
    ·
      refine ⟨161775783947714247544251953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107850522631809498362834635 161775783947714247544251953)
      ·
        refine ⟨121331837960785685658188965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161775783947714247544251953 121331837960785685658188965)
        ·
          refine ⟨22749719617647316060910431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121331837960785685658188965 22749719617647316060910431)
          ·
            refine ⟨34124579426470974091365647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22749719617647316060910431 34124579426470974091365647)
            ·
              refine ⟨51186869139706461137048471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34124579426470974091365647 51186869139706461137048471)
              ·
                refine ⟨76780303709559691705572707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51186869139706461137048471 76780303709559691705572707)
                ·
                  refine ⟨115170455564339537558359061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76780303709559691705572707 115170455564339537558359061)
                  ·
                    refine ⟨5398615104578415823048081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115170455564339537558359061 5398615104578415823048081)
                    ·
                      refine ⟨4048961328433811867286061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398615104578415823048081 4048961328433811867286061)
                      ·
                        rfl

theorem cell23_7885324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_7885324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885324 prefixEnd_7885324 := by exact prefixLift 7885324
  have htrace : WordTrace (prefixWord ++ tailWord_7885324) baseStart_7885324 baseEnd_7885324 := by
    simpa [prefixWord, tailWord_7885324, baseEnd_7885324] using wordTrace_append hprefix tailTrace_7885324
  have hstable : (prefixWord ++ tailWord_7885324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885324).length < 2 ^ (prefixWord ++ tailWord_7885324).sum := by decide
  have hdescent : baseEnd_7885324 < baseStart_7885324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_7885327 : Nat := 118140960795 + 7885327 * 2 ^ 59
def prefixEnd_7885327 : Nat := 4983230072969 + 3 ^ 40 * 7885327 * 2
def baseEnd_7885327 : Nat := 4048962868875775355548547

theorem tailTrace_7885327 : CollatzResearch.WordTrace tailWord_7885327 prefixEnd_7885327 4048962868875775355548547 := by
  unfold tailWord_7885327
  simp only [CollatzResearch.WordTrace]
  refine ⟨287601503103814460479918235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191734335402542973653278823 287601503103814460479918235)
  ·
    refine ⟨431402254655721690719877353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287601503103814460479918235 431402254655721690719877353)
    ·
      refine ⟨323551690991791268039908015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431402254655721690719877353 323551690991791268039908015)
      ·
        refine ⟨485327536487686902059862023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323551690991791268039908015 485327536487686902059862023)
        ·
          refine ⟨727991304731530353089793035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485327536487686902059862023 727991304731530353089793035)
          ·
            refine ⟨1091986957097295529634689553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727991304731530353089793035 1091986957097295529634689553)
            ·
              refine ⟨818990217822971647226017165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091986957097295529634689553 818990217822971647226017165)
              ·
                refine ⟨307121331683614367709756437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818990217822971647226017165 307121331683614367709756437)
                ·
                  refine ⟨14396312422669423486394833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307121331683614367709756437 14396312422669423486394833)
                  ·
                    refine ⟨10797234317002067614796125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14396312422669423486394833 10797234317002067614796125)
                    ·
                      refine ⟨4048962868875775355548547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797234317002067614796125 4048962868875775355548547)
                      ·
                        rfl

theorem cell23_7885327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_7885327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885327 prefixEnd_7885327 := by exact prefixLift 7885327
  have htrace : WordTrace (prefixWord ++ tailWord_7885327) baseStart_7885327 baseEnd_7885327 := by
    simpa [prefixWord, tailWord_7885327, baseEnd_7885327] using wordTrace_append hprefix tailTrace_7885327
  have hstable : (prefixWord ++ tailWord_7885327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885327).length < 2 ^ (prefixWord ++ tailWord_7885327).sum := by decide
  have hdescent : baseEnd_7885327 < baseStart_7885327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885341 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_7885341 : Nat := 118140960795 + 7885341 * 2 ^ 59
def prefixEnd_7885341 : Nat := 4983230072969 + 3 ^ 40 * 7885341 * 2
def baseEnd_7885341 : Nat := 4048970057604938300773483

theorem tailTrace_7885341 : CollatzResearch.WordTrace tailWord_7885341 prefixEnd_7885341 4048970057604938300773483 := by
  unfold tailWord_7885341
  simp only [CollatzResearch.WordTrace]
  refine ⟨287602013725763740870927877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191734675817175827247285251 287602013725763740870927877)
  ·
    refine ⟨53925377573580701413298977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287602013725763740870927877 53925377573580701413298977)
    ·
      refine ⟨40444033180185526059974233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53925377573580701413298977 40444033180185526059974233)
      ·
        refine ⟨30333024885139144544980675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40444033180185526059974233 30333024885139144544980675)
        ·
          refine ⟨45499537327708716817471013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30333024885139144544980675 45499537327708716817471013)
          ·
            refine ⟨8531163248945384403275815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45499537327708716817471013 8531163248945384403275815)
            ·
              refine ⟨12796744873418076604913723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531163248945384403275815 12796744873418076604913723)
              ·
                refine ⟨19195117310127114907370585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12796744873418076604913723 19195117310127114907370585)
                ·
                  refine ⟨14396337982595336180527939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19195117310127114907370585 14396337982595336180527939)
                  ·
                    refine ⟨21594506973893004270791909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14396337982595336180527939 21594506973893004270791909)
                    ·
                      refine ⟨4048970057604938300773483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21594506973893004270791909 4048970057604938300773483)
                      ·
                        rfl

theorem cell23_7885341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_7885341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885341 prefixEnd_7885341 := by exact prefixLift 7885341
  have htrace : WordTrace (prefixWord ++ tailWord_7885341) baseStart_7885341 baseEnd_7885341 := by
    simpa [prefixWord, tailWord_7885341, baseEnd_7885341] using wordTrace_append hprefix tailTrace_7885341
  have hstable : (prefixWord ++ tailWord_7885341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885341).length < 2 ^ (prefixWord ++ tailWord_7885341).sum := by decide
  have hdescent : baseEnd_7885341 < baseStart_7885341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885407 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 6]
def baseStart_7885407 : Nat := 118140960795 + 7885407 * 2 ^ 59
def prefixEnd_7885407 : Nat := 4983230072969 + 3 ^ 40 * 7885407 * 2
def baseEnd_7885407 : Nat := 1349667982442711680849393

theorem tailTrace_7885407 : CollatzResearch.WordTrace tailWord_7885407 prefixEnd_7885407 1349667982442711680849393 := by
  unfold tailWord_7885407
  simp only [CollatzResearch.WordTrace]
  refine ⟨287604420943524634142830475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191736280629016422761886983 287604420943524634142830475)
  ·
    refine ⟨431406631415286951214245713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287604420943524634142830475 431406631415286951214245713)
    ·
      refine ⟨323554973561465213410684285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431406631415286951214245713 323554973561465213410684285)
      ·
        refine ⟨121333115085549455029006607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323554973561465213410684285 121333115085549455029006607)
        ·
          refine ⟨181999672628324182543509911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121333115085549455029006607 181999672628324182543509911)
          ·
            refine ⟨272999508942486273815264867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181999672628324182543509911 272999508942486273815264867)
            ·
              refine ⟨409499263413729410722897301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272999508942486273815264867 409499263413729410722897301)
              ·
                refine ⟨19195277972518566127635811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409499263413729410722897301 19195277972518566127635811)
                ·
                  refine ⟨28792916958777849191453717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19195277972518566127635811 28792916958777849191453717)
                  ·
                    refine ⟨1349667982442711680849393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28792916958777849191453717 1349667982442711680849393)
                    ·
                      rfl

theorem cell23_7885407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_7885407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885407 prefixEnd_7885407 := by exact prefixLift 7885407
  have htrace : WordTrace (prefixWord ++ tailWord_7885407) baseStart_7885407 baseEnd_7885407 := by
    simpa [prefixWord, tailWord_7885407, baseEnd_7885407] using wordTrace_append hprefix tailTrace_7885407
  have hstable : (prefixWord ++ tailWord_7885407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885407).length < 2 ^ (prefixWord ++ tailWord_7885407).sum := by decide
  have hdescent : baseEnd_7885407 < baseStart_7885407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885408 : List Nat := [2, 1, 1, 3, 2, 1, 5, 3, 1, 1, 3]
def baseStart_7885408 : Nat := 118140960795 + 7885408 * 2 ^ 59
def prefixEnd_7885408 : Nat := 4983230072969 + 3 ^ 40 * 7885408 * 2
def baseEnd_7885408 : Nat := 4049004460808789538635675

theorem tailTrace_7885408 : CollatzResearch.WordTrace tailWord_7885408 prefixEnd_7885408 4049004460808789538635675 := by
  unfold tailWord_7885408
  simp only [CollatzResearch.WordTrace]
  refine ⟨143802228708260505656808439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191736304944347340875744585 143802228708260505656808439)
  ·
    refine ⟨215703343062390758485212659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143802228708260505656808439 215703343062390758485212659)
    ·
      refine ⟨323555014593586137727818989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215703343062390758485212659 323555014593586137727818989)
      ·
        refine ⟨121333130472594801647932121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323555014593586137727818989 121333130472594801647932121)
        ·
          refine ⟨90999847854446101235949091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121333130472594801647932121 90999847854446101235949091)
          ·
            refine ⟨136499771781669151853923637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90999847854446101235949091 136499771781669151853923637)
            ·
              refine ⟨12796853604531482986305341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136499771781669151853923637 12796853604531482986305341)
              ·
                refine ⟨4798820101699306119864503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12796853604531482986305341 4798820101699306119864503)
                ·
                  refine ⟨7198230152548959179796755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798820101699306119864503 7198230152548959179796755)
                  ·
                    refine ⟨10797345228823438769695133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198230152548959179796755 10797345228823438769695133)
                    ·
                      refine ⟨4049004460808789538635675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797345228823438769695133 4049004460808789538635675)
                      ·
                        rfl

theorem cell23_7885408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_7885408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885408 prefixEnd_7885408 := by exact prefixLift 7885408
  have htrace : WordTrace (prefixWord ++ tailWord_7885408) baseStart_7885408 baseEnd_7885408 := by
    simpa [prefixWord, tailWord_7885408, baseEnd_7885408] using wordTrace_append hprefix tailTrace_7885408
  have hstable : (prefixWord ++ tailWord_7885408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885408).length < 2 ^ (prefixWord ++ tailWord_7885408).sum := by decide
  have hdescent : baseEnd_7885408 < baseStart_7885408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885427 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_7885427 : Nat := 118140960795 + 7885427 * 2 ^ 59
def prefixEnd_7885427 : Nat := 4983230072969 + 3 ^ 40 * 7885427 * 2
def baseEnd_7885427 : Nat := 4049014216941224964298087

theorem tailTrace_7885427 : CollatzResearch.WordTrace tailWord_7885427 prefixEnd_7885427 4049014216941224964298087 := by
  unfold tailWord_7885427
  simp only [CollatzResearch.WordTrace]
  refine ⟨287605150403452177558558535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191736766935634785039039023 287605150403452177558558535)
  ·
    refine ⟨431407725605178266337837803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287605150403452177558558535 431407725605178266337837803)
    ·
      refine ⟨647111588407767399506756705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431407725605178266337837803 647111588407767399506756705)
      ·
        refine ⟨485333691305825549630067529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647111588407767399506756705 485333691305825549630067529)
        ·
          refine ⟨364000268479369162222550647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485333691305825549630067529 364000268479369162222550647)
          ·
            refine ⟨546000402719053743333825971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364000268479369162222550647 546000402719053743333825971)
            ·
              refine ⟨819000604078580615000738957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546000402719053743333825971 819000604078580615000738957)
              ·
                refine ⟨307125226529467730625277109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819000604078580615000738957 307125226529467730625277109)
                ·
                  refine ⟨28792989987137599746119729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307125226529467730625277109 28792989987137599746119729)
                  ·
                    refine ⟨21594742490353199809589797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28792989987137599746119729 21594742490353199809589797)
                    ·
                      refine ⟨4049014216941224964298087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21594742490353199809589797 4049014216941224964298087)
                      ·
                        rfl

theorem cell23_7885427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_7885427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885427 prefixEnd_7885427 := by exact prefixLift 7885427
  have htrace : WordTrace (prefixWord ++ tailWord_7885427) baseStart_7885427 baseEnd_7885427 := by
    simpa [prefixWord, tailWord_7885427, baseEnd_7885427] using wordTrace_append hprefix tailTrace_7885427
  have hstable : (prefixWord ++ tailWord_7885427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885427).length < 2 ^ (prefixWord ++ tailWord_7885427).sum := by decide
  have hdescent : baseEnd_7885427 < baseStart_7885427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885441 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_7885441 : Nat := 118140960795 + 7885441 * 2 ^ 59
def prefixEnd_7885441 : Nat := 4983230072969 + 3 ^ 40 * 7885441 * 2
def baseEnd_7885441 : Nat := 1349673801890129303174341

theorem tailTrace_7885441 : CollatzResearch.WordTrace tailWord_7885441 prefixEnd_7885441 1349673801890129303174341 := by
  unfold tailWord_7885441
  simp only [CollatzResearch.WordTrace]
  refine ⟨287605661025401457949568177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191737107350267638633045451 287605661025401457949568177)
  ·
    refine ⟨215704245769051093462176133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287605661025401457949568177 215704245769051093462176133)
    ·
      refine ⟨40444546081697080024158025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215704245769051093462176133 40444546081697080024158025)
      ·
        refine ⟨30333409561272810018118519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40444546081697080024158025 30333409561272810018118519)
        ·
          refine ⟨45500114341909215027177779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30333409561272810018118519 45500114341909215027177779)
          ·
            refine ⟨68250171512863822540766669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45500114341909215027177779 68250171512863822540766669)
            ·
              refine ⟨25593814317323933452787501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68250171512863822540766669 25593814317323933452787501)
              ·
                refine ⟨9597680368996475044795313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25593814317323933452787501 9597680368996475044795313)
                ·
                  refine ⟨7198260276747356283596485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597680368996475044795313 7198260276747356283596485)
                  ·
                    refine ⟨1349673801890129303174341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198260276747356283596485 1349673801890129303174341)
                    ·
                      rfl

theorem cell23_7885441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_7885441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885441 prefixEnd_7885441 := by exact prefixLift 7885441
  have htrace : WordTrace (prefixWord ++ tailWord_7885441) baseStart_7885441 baseEnd_7885441 := by
    simpa [prefixWord, tailWord_7885441, baseEnd_7885441] using wordTrace_append hprefix tailTrace_7885441
  have hstable : (prefixWord ++ tailWord_7885441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885441).length < 2 ^ (prefixWord ++ tailWord_7885441).sum := by decide
  have hdescent : baseEnd_7885441 < baseStart_7885441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885444 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7885444 : Nat := 118140960795 + 7885444 * 2 ^ 59
def prefixEnd_7885444 : Nat := 4983230072969 + 3 ^ 40 * 7885444 * 2
def baseEnd_7885444 : Nat := 4049022946112351397785509

theorem tailTrace_7885444 : CollatzResearch.WordTrace tailWord_7885444 prefixEnd_7885444 4049022946112351397785509 := by
  unfold tailWord_7885444
  simp only [CollatzResearch.WordTrace]
  refine ⟨143802885222195294730963693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191737180296260392974618257 143802885222195294730963693)
  ·
    refine ⟨53926081958323235524111385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143802885222195294730963693 53926081958323235524111385)
    ·
      refine ⟨40444561468742426643083539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53926081958323235524111385 40444561468742426643083539)
      ·
        refine ⟨60666842203113639964625309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40444561468742426643083539 60666842203113639964625309)
        ·
          refine ⟨22750065826167614986734491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60666842203113639964625309 22750065826167614986734491)
          ·
            refine ⟨34125098739251422480101737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22750065826167614986734491 34125098739251422480101737)
            ·
              refine ⟨25593824054438566860076303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34125098739251422480101737 25593824054438566860076303)
              ·
                refine ⟨38390736081657850290114455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25593824054438566860076303 38390736081657850290114455)
                ·
                  refine ⟨57586104122486775435171683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38390736081657850290114455 57586104122486775435171683)
                  ·
                    refine ⟨86379156183730163152757525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57586104122486775435171683 86379156183730163152757525)
                    ·
                      refine ⟨4049022946112351397785509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86379156183730163152757525 4049022946112351397785509)
                      ·
                        rfl

theorem cell23_7885444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7885444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885444 prefixEnd_7885444 := by exact prefixLift 7885444
  have htrace : WordTrace (prefixWord ++ tailWord_7885444) baseStart_7885444 baseEnd_7885444 := by
    simpa [prefixWord, tailWord_7885444, baseEnd_7885444] using wordTrace_append hprefix tailTrace_7885444
  have hstable : (prefixWord ++ tailWord_7885444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885444).length < 2 ^ (prefixWord ++ tailWord_7885444).sum := by decide
  have hdescent : baseEnd_7885444 < baseStart_7885444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885481 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_7885481 : Nat := 118140960795 + 7885481 * 2 ^ 59
def prefixEnd_7885481 : Nat := 4983230072969 + 3 ^ 40 * 7885481 * 2
def baseEnd_7885481 : Nat := 4049041944896567753022839

theorem tailTrace_7885481 : CollatzResearch.WordTrace tailWord_7885481 prefixEnd_7885481 4049041944896567753022839 := by
  unfold tailWord_7885481
  simp only [CollatzResearch.WordTrace]
  refine ⟨287607119945256544781024297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191738079963504363187349531 287607119945256544781024297)
  ·
    refine ⟨215705339958942408585768223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287607119945256544781024297 215705339958942408585768223)
    ·
      refine ⟨323558009938413612878652335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215705339958942408585768223 323558009938413612878652335)
      ·
        refine ⟨485337014907620419317978503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323558009938413612878652335 485337014907620419317978503)
        ·
          refine ⟨728005522361430628976967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485337014907620419317978503 728005522361430628976967755)
          ·
            refine ⟨1092008283542145943465451633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728005522361430628976967755 1092008283542145943465451633)
            ·
              refine ⟨819006212656609457599088725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092008283542145943465451633 819006212656609457599088725)
              ·
                refine ⟨9597729054569642081239321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 819006212656609457599088725 9597729054569642081239321)
                ·
                  refine ⟨7198296790927231560929491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597729054569642081239321 7198296790927231560929491)
                  ·
                    refine ⟨10797445186390847341394237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198296790927231560929491 10797445186390847341394237)
                    ·
                      refine ⟨4049041944896567753022839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797445186390847341394237 4049041944896567753022839)
                      ·
                        rfl

theorem cell23_7885481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_7885481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885481 prefixEnd_7885481 := by exact prefixLift 7885481
  have htrace : WordTrace (prefixWord ++ tailWord_7885481) baseStart_7885481 baseEnd_7885481 := by
    simpa [prefixWord, tailWord_7885481, baseEnd_7885481] using wordTrace_append hprefix tailTrace_7885481
  have hstable : (prefixWord ++ tailWord_7885481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885481).length < 2 ^ (prefixWord ++ tailWord_7885481).sum := by decide
  have hdescent : baseEnd_7885481 < baseStart_7885481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885491 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 3, 3, 2]
def baseStart_7885491 : Nat := 118140960795 + 7885491 * 2 ^ 59
def prefixEnd_7885491 : Nat := 4983230072969 + 3 ^ 40 * 7885491 * 2
def baseEnd_7885491 : Nat := 4049047079703112713897793

theorem tailTrace_7885491 : CollatzResearch.WordTrace tailWord_7885491 prefixEnd_7885491 4049047079703112713897793 := by
  unfold tailWord_7885491
  simp only [CollatzResearch.WordTrace]
  refine ⟨287607484675220316488888327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191738323116813544325925551 287607484675220316488888327)
  ·
    refine ⟨431411227012830474733332491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287607484675220316488888327 431411227012830474733332491)
    ·
      refine ⟨647116840519245712099998737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431411227012830474733332491 647116840519245712099998737)
      ·
        refine ⟨485337630389434284074999053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647116840519245712099998737 485337630389434284074999053)
        ·
          refine ⟨182001611396037856528124645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485337630389434284074999053 182001611396037856528124645)
          ·
            refine ⟨34125302136757098099023371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182001611396037856528124645 34125302136757098099023371)
            ·
              refine ⟨51187953205135647148535057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34125302136757098099023371 51187953205135647148535057)
              ·
                refine ⟨38390964903851735361401293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51187953205135647148535057 38390964903851735361401293)
                ·
                  refine ⟨14396611838944400760525485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38390964903851735361401293 14396611838944400760525485)
                  ·
                    refine ⟨5398729439604150285197057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14396611838944400760525485 5398729439604150285197057)
                    ·
                      refine ⟨4049047079703112713897793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398729439604150285197057 4049047079703112713897793)
                      ·
                        rfl

theorem cell23_7885491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3, 2].length) (baseStart_7885491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885491 prefixEnd_7885491 := by exact prefixLift 7885491
  have htrace : WordTrace (prefixWord ++ tailWord_7885491) baseStart_7885491 baseEnd_7885491 := by
    simpa [prefixWord, tailWord_7885491, baseEnd_7885491] using wordTrace_append hprefix tailTrace_7885491
  have hstable : (prefixWord ++ tailWord_7885491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885491).length < 2 ^ (prefixWord ++ tailWord_7885491).sum := by decide
  have hdescent : baseEnd_7885491 < baseStart_7885491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885508 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7885508 : Nat := 118140960795 + 7885508 * 2 ^ 59
def prefixEnd_7885508 : Nat := 4983230072969 + 3 ^ 40 * 7885508 * 2
def baseEnd_7885508 : Nat := 4049055808874239147385215

theorem tailTrace_7885508 : CollatzResearch.WordTrace tailWord_7885508 prefixEnd_7885508 4049055808874239147385215 := by
  unfold tailWord_7885508
  simp only [CollatzResearch.WordTrace]
  refine ⟨143804052358079364196128589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191738736477439152261504785 143804052358079364196128589)
  ·
    refine ⟨53926519634279761573548221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143804052358079364196128589 53926519634279761573548221)
    ·
      refine ⟨20222444862854910590080583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53926519634279761573548221 20222444862854910590080583)
      ·
        refine ⟨30333667294282365885120875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20222444862854910590080583 30333667294282365885120875)
        ·
          refine ⟨45500500941423548827681313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30333667294282365885120875 45500500941423548827681313)
          ·
            refine ⟨34125375706067661620760985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45500500941423548827681313 34125375706067661620760985)
            ·
              refine ⟨25594031779550746215570739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34125375706067661620760985 25594031779550746215570739)
              ·
                refine ⟨38391047669326119323356109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25594031779550746215570739 38391047669326119323356109)
                ·
                  refine ⟨14396642875997294746258541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38391047669326119323356109 14396642875997294746258541)
                  ·
                    refine ⟨5398741078498985529846953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14396642875997294746258541 5398741078498985529846953)
                    ·
                      refine ⟨4049055808874239147385215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398741078498985529846953 4049055808874239147385215)
                      ·
                        rfl

theorem cell23_7885508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7885508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885508 prefixEnd_7885508 := by exact prefixLift 7885508
  have htrace : WordTrace (prefixWord ++ tailWord_7885508) baseStart_7885508 baseEnd_7885508 := by
    simpa [prefixWord, tailWord_7885508, baseEnd_7885508] using wordTrace_append hprefix tailTrace_7885508
  have hstable : (prefixWord ++ tailWord_7885508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885508).length < 2 ^ (prefixWord ++ tailWord_7885508).sum := by decide
  have hdescent : baseEnd_7885508 < baseStart_7885508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885521 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_7885521 : Nat := 118140960795 + 7885521 * 2 ^ 59
def prefixEnd_7885521 : Nat := 4983230072969 + 3 ^ 40 * 7885521 * 2
def baseEnd_7885521 : Nat := 4049062484122747596522655

theorem tailTrace_7885521 : CollatzResearch.WordTrace tailWord_7885521 prefixEnd_7885521 4049062484122747596522655 := by
  unfold tailWord_7885521
  simp only [CollatzResearch.WordTrace]
  refine ⟨287608578865111631612480417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191739052576741087741653611 287608578865111631612480417)
  ·
    refine ⟨215706434148833723709360313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287608578865111631612480417 215706434148833723709360313)
    ·
      refine ⟨161779825611625292782020235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215706434148833723709360313 161779825611625292782020235)
      ·
        refine ⟨242669738417437939173030353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161779825611625292782020235 242669738417437939173030353)
        ·
          refine ⟨182002303813078454379772765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242669738417437939173030353 182002303813078454379772765)
          ·
            refine ⟨68250863929904420392414787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182002303813078454379772765 68250863929904420392414787)
            ·
              refine ⟨102376295894856630588622181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68250863929904420392414787 102376295894856630588622181)
              ·
                refine ⟨19195555480285618235366659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102376295894856630588622181 19195555480285618235366659)
                ·
                  refine ⟨28793333220428427353049989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19195555480285618235366659 28793333220428427353049989)
                  ·
                    refine ⟨5398749978830330128696873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28793333220428427353049989 5398749978830330128696873)
                    ·
                      refine ⟨4049062484122747596522655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398749978830330128696873 4049062484122747596522655)
                      ·
                        rfl

theorem cell23_7885521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_7885521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885521 prefixEnd_7885521 := by exact prefixLift 7885521
  have htrace : WordTrace (prefixWord ++ tailWord_7885521) baseStart_7885521 baseEnd_7885521 := by
    simpa [prefixWord, tailWord_7885521, baseEnd_7885521] using wordTrace_append hprefix tailTrace_7885521
  have hstable : (prefixWord ++ tailWord_7885521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885521).length < 2 ^ (prefixWord ++ tailWord_7885521).sum := by decide
  have hdescent : baseEnd_7885521 < baseStart_7885521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885532 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7885532 : Nat := 118140960795 + 7885532 * 2 ^ 59
def prefixEnd_7885532 : Nat := 4983230072969 + 3 ^ 40 * 7885532 * 2
def baseEnd_7885532 : Nat := 4049068132409947053485105

theorem tailTrace_7885532 : CollatzResearch.WordTrace tailWord_7885532 prefixEnd_7885532 4049068132409947053485105 := by
  unfold tailWord_7885532
  simp only [CollatzResearch.WordTrace]
  refine ⟨143804490034035890245565425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191739320045381186994087233 143804490034035890245565425)
  ·
    refine ⟨107853367525526917684174069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143804490034035890245565425 107853367525526917684174069)
    ·
      refine ⟨10111253205518148532891319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107853367525526917684174069 10111253205518148532891319)
      ·
        refine ⟨15166879808277222799336979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10111253205518148532891319 15166879808277222799336979)
        ·
          refine ⟨22750319712415834199005469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15166879808277222799336979 22750319712415834199005469)
          ·
            refine ⟨8531369892155937824627051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22750319712415834199005469 8531369892155937824627051)
            ·
              refine ⟨12797054838233906736940577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531369892155937824627051 12797054838233906736940577)
              ·
                refine ⟨9597791128675430052705433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12797054838233906736940577 9597791128675430052705433)
                ·
                  refine ⟨7198343346506572539529075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597791128675430052705433 7198343346506572539529075)
                  ·
                    refine ⟨10797515019759858809293613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198343346506572539529075 10797515019759858809293613)
                    ·
                      refine ⟨4049068132409947053485105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797515019759858809293613 4049068132409947053485105)
                      ·
                        rfl

theorem cell23_7885532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7885532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885532 prefixEnd_7885532 := by exact prefixLift 7885532
  have htrace : WordTrace (prefixWord ++ tailWord_7885532) baseStart_7885532 baseEnd_7885532 := by
    simpa [prefixWord, tailWord_7885532, baseEnd_7885532] using wordTrace_append hprefix tailTrace_7885532
  have hstable : (prefixWord ++ tailWord_7885532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885532).length < 2 ^ (prefixWord ++ tailWord_7885532).sum := by decide
  have hdescent : baseEnd_7885532 < baseStart_7885532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885655 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 1, 4]
def baseStart_7885655 : Nat := 118140960795 + 7885655 * 2 ^ 59
def prefixEnd_7885655 : Nat := 4983230072969 + 3 ^ 40 * 7885655 * 2
def baseEnd_7885655 : Nat := 1349710430176816690749013

theorem tailTrace_7885655 : CollatzResearch.WordTrace tailWord_7885655 prefixEnd_7885655 1349710430176816690749013 := by
  unfold tailWord_7885655
  simp only [CollatzResearch.WordTrace]
  refine ⟨287613466246626172497858419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191742310831084114998572279 287613466246626172497858419)
  ·
    refine ⟨431420199369939258746787629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287613466246626172497858419 431420199369939258746787629)
    ·
      refine ⟨161782574763727222030045361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431420199369939258746787629 161782574763727222030045361)
      ·
        refine ⟨121336931072795416522534021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161782574763727222030045361 121336931072795416522534021)
        ·
          refine ⟨22750674576149140597975129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121336931072795416522534021 22750674576149140597975129)
          ·
            refine ⟨17063005932111855448481347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22750674576149140597975129 17063005932111855448481347)
            ·
              refine ⟨25594508898167783172722021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17063005932111855448481347 25594508898167783172722021)
              ·
                refine ⟨4798970418406459344885379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25594508898167783172722021 4798970418406459344885379)
                ·
                  refine ⟨7198455627609689017328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798970418406459344885379 7198455627609689017328069)
                  ·
                    refine ⟨1349710430176816690749013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198455627609689017328069 1349710430176816690749013)
                    ·
                      rfl

theorem cell23_7885655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_7885655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885655 prefixEnd_7885655 := by exact prefixLift 7885655
  have htrace : WordTrace (prefixWord ++ tailWord_7885655) baseStart_7885655 baseEnd_7885655 := by
    simpa [prefixWord, tailWord_7885655, baseEnd_7885655] using wordTrace_append hprefix tailTrace_7885655
  have hstable : (prefixWord ++ tailWord_7885655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885655).length < 2 ^ (prefixWord ++ tailWord_7885655).sum := by decide
  have hdescent : baseEnd_7885655 < baseStart_7885655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885681 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_7885681 : Nat := 118140960795 + 7885681 * 2 ^ 59
def prefixEnd_7885681 : Nat := 4983230072969 + 3 ^ 40 * 7885681 * 2
def baseEnd_7885681 : Nat := 1349714880342488990173973

theorem tailTrace_7885681 : CollatzResearch.WordTrace tailWord_7885681 prefixEnd_7885681 1349714880342488990173973 := by
  unfold tailWord_7885681
  simp only [CollatzResearch.WordTrace]
  refine ⟨287614414544531978938304897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191742943029687985958869931 287614414544531978938304897)
  ·
    refine ⟨215710810908398984203728673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287614414544531978938304897 215710810908398984203728673)
    ·
      refine ⟨161783108181299238152796505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215710810908398984203728673 161783108181299238152796505)
      ·
        refine ⟨121337331135974428614597379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161783108181299238152796505 121337331135974428614597379)
        ·
          refine ⟨182005996703961642921896069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121337331135974428614597379 182005996703961642921896069)
          ·
            refine ⟨34126124381992808047855513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182005996703961642921896069 34126124381992808047855513)
            ·
              refine ⟨25594593286494606035891635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34126124381992808047855513 25594593286494606035891635)
              ·
                refine ⟨38391889929741909053837453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25594593286494606035891635 38391889929741909053837453)
                ·
                  refine ⟨14396958723653215895189045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38391889929741909053837453 14396958723653215895189045)
                  ·
                    refine ⟨1349714880342488990173973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14396958723653215895189045 1349714880342488990173973)
                    ·
                      rfl

theorem cell23_7885681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_7885681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885681 prefixEnd_7885681 := by exact prefixLift 7885681
  have htrace : WordTrace (prefixWord ++ tailWord_7885681) baseStart_7885681 baseEnd_7885681 := by
    simpa [prefixWord, tailWord_7885681, baseEnd_7885681] using wordTrace_append hprefix tailTrace_7885681
  have hstable : (prefixWord ++ tailWord_7885681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885681).length < 2 ^ (prefixWord ++ tailWord_7885681).sum := by decide
  have hdescent : baseEnd_7885681 < baseStart_7885681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885688 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_7885688 : Nat := 118140960795 + 7885688 * 2 ^ 59
def prefixEnd_7885688 : Nat := 4983230072969 + 3 ^ 40 * 7885688 * 2
def baseEnd_7885688 : Nat := 4049148235392048443134387

theorem tailTrace_7885688 : CollatzResearch.WordTrace tailWord_7885688 prefixEnd_7885688 4049148235392048443134387 := by
  unfold tailWord_7885688
  simp only [CollatzResearch.WordTrace]
  refine ⟨143807334927753309566904859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191743113237004412755873145 143807334927753309566904859)
  ·
    refine ⟨215711002391629964350357289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143807334927753309566904859 215711002391629964350357289)
    ·
      refine ⟨161783251793722473262767967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215711002391629964350357289 161783251793722473262767967)
      ·
        refine ⟨242674877690583709894151951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161783251793722473262767967 242674877690583709894151951)
        ·
          refine ⟨364012316535875564841227927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242674877690583709894151951 364012316535875564841227927)
          ·
            refine ⟨546018474803813347261841891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364012316535875564841227927 546018474803813347261841891)
            ·
              refine ⟨819027712205720020892762837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546018474803813347261841891 819027712205720020892762837)
              ·
                refine ⟨19195962004821562989674129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 819027712205720020892762837 19195962004821562989674129)
                ·
                  refine ⟨14396971503616172242255597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19195962004821562989674129 14396971503616172242255597)
                  ·
                    refine ⟨5398864313856064590845849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14396971503616172242255597 5398864313856064590845849)
                    ·
                      refine ⟨4049148235392048443134387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398864313856064590845849 4049148235392048443134387)
                      ·
                        rfl

theorem cell23_7885688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_7885688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885688 prefixEnd_7885688 := by exact prefixLift 7885688
  have htrace : WordTrace (prefixWord ++ tailWord_7885688) baseStart_7885688 baseEnd_7885688 := by
    simpa [prefixWord, tailWord_7885688, baseEnd_7885688] using wordTrace_append hprefix tailTrace_7885688
  have hstable : (prefixWord ++ tailWord_7885688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885688).length < 2 ^ (prefixWord ++ tailWord_7885688).sum := by decide
  have hdescent : baseEnd_7885688 < baseStart_7885688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885695 : List Nat := [1, 1, 2, 2, 1, 1, 5, 5, 1, 1, 3]
def baseStart_7885695 : Nat := 118140960795 + 7885695 * 2 ^ 59
def prefixEnd_7885695 : Nat := 4983230072969 + 3 ^ 40 * 7885695 * 2
def baseEnd_7885695 : Nat := 4049151829756629915746855

theorem tailTrace_7885695 : CollatzResearch.WordTrace tailWord_7885695 prefixEnd_7885695 4049151829756629915746855 := by
  unfold tailWord_7885695
  simp only [CollatzResearch.WordTrace]
  refine ⟨287614925166481259329314539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191743283444320839552876359 287614925166481259329314539)
  ·
    refine ⟨431422387749721888993971809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287614925166481259329314539 431422387749721888993971809)
    ·
      refine ⟨323566790812291416745478857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431422387749721888993971809 323566790812291416745478857)
      ·
        refine ⟨242675093109218562559109143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323566790812291416745478857 242675093109218562559109143)
        ·
          refine ⟨364012639663827843838663715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242675093109218562559109143 364012639663827843838663715)
          ·
            refine ⟨546018959495741765757995573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364012639663827843838663715 546018959495741765757995573)
            ·
              refine ⟨51189277452725790539812085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 546018959495741765757995573 51189277452725790539812085)
              ·
                refine ⟨4798994761193042863107383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51189277452725790539812085 4798994761193042863107383)
                ·
                  refine ⟨7198492141789564294661075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798994761193042863107383 7198492141789564294661075)
                  ·
                    refine ⟨10797738212684346441991613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7198492141789564294661075 10797738212684346441991613)
                    ·
                      refine ⟨4049151829756629915746855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10797738212684346441991613 4049151829756629915746855)
                      ·
                        rfl

theorem cell23_7885695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_7885695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885695 prefixEnd_7885695 := by exact prefixLift 7885695
  have htrace : WordTrace (prefixWord ++ tailWord_7885695) baseStart_7885695 baseEnd_7885695 := by
    simpa [prefixWord, tailWord_7885695, baseEnd_7885695] using wordTrace_append hprefix tailTrace_7885695
  have hstable : (prefixWord ++ tailWord_7885695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885695).length < 2 ^ (prefixWord ++ tailWord_7885695).sum := by decide
  have hdescent : baseEnd_7885695 < baseStart_7885695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885728 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_7885728 : Nat := 118140960795 + 7885728 * 2 ^ 59
def prefixEnd_7885728 : Nat := 4983230072969 + 3 ^ 40 * 7885728 * 2
def baseEnd_7885728 : Nat := 1349722924872742762211401

theorem tailTrace_7885728 : CollatzResearch.WordTrace tailWord_7885728 prefixEnd_7885728 1349722924872742762211401 := by
  unfold tailWord_7885728
  simp only [CollatzResearch.WordTrace]
  refine ⟨143808064387680852982632919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191744085850241137310177225 143808064387680852982632919)
  ·
    refine ⟨215712096581521279473949379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143808064387680852982632919 215712096581521279473949379)
    ·
      refine ⟨323568144872281919210924069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215712096581521279473949379 323568144872281919210924069)
      ·
        refine ⟨60669027163552859852048263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323568144872281919210924069 60669027163552859852048263)
        ·
          refine ⟨91003540745329289778072395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60669027163552859852048263 91003540745329289778072395)
          ·
            refine ⟨136505311117993934667108593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91003540745329289778072395 136505311117993934667108593)
            ·
              refine ⟨102378983338495451000331445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136505311117993934667108593 102378983338495451000331445)
              ·
                refine ⟨9598029687983948531281073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102378983338495451000331445 9598029687983948531281073)
                ·
                  refine ⟨7198522265987961398460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598029687983948531281073 7198522265987961398460805)
                  ·
                    refine ⟨1349722924872742762211401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198522265987961398460805 1349722924872742762211401)
                    ·
                      rfl

theorem cell23_7885728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_7885728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885728 prefixEnd_7885728 := by exact prefixLift 7885728
  have htrace : WordTrace (prefixWord ++ tailWord_7885728) baseStart_7885728 baseEnd_7885728 := by
    simpa [prefixWord, tailWord_7885728, baseEnd_7885728] using wordTrace_append hprefix tailTrace_7885728
  have hstable : (prefixWord ++ tailWord_7885728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885728).length < 2 ^ (prefixWord ++ tailWord_7885728).sum := by decide
  have hdescent : baseEnd_7885728 < baseStart_7885728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885795 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7885795 : Nat := 118140960795 + 7885795 * 2 ^ 59
def prefixEnd_7885795 : Nat := 4983230072969 + 3 ^ 40 * 7885795 * 2
def baseEnd_7885795 : Nat := 4049203177822079524496395

theorem tailTrace_7885795 : CollatzResearch.WordTrace tailWord_7885795 prefixEnd_7885795 4049203177822079524496395 := by
  unfold tailWord_7885795
  simp only [CollatzResearch.WordTrace]
  refine ⟨287618572466118976407954839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191745714977412650938636559 287618572466118976407954839)
  ·
    refine ⟨431427858699178464611932259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287618572466118976407954839 431427858699178464611932259)
    ·
      refine ⟨647141788048767696917898389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431427858699178464611932259 647141788048767696917898389)
      ·
        refine ⟨30334771314785985793026487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 647141788048767696917898389 30334771314785985793026487)
        ·
          refine ⟨45502156972178978689539731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30334771314785985793026487 45502156972178978689539731)
          ·
            refine ⟨68253235458268468034309597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45502156972178978689539731 68253235458268468034309597)
            ·
              refine ⟨25594963296850675512866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68253235458268468034309597 25594963296850675512866099)
              ·
                refine ⟨38392444945276013269299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25594963296850675512866099 38392444945276013269299149)
                ·
                  refine ⟨14397166854478504975987181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38392444945276013269299149 14397166854478504975987181)
                  ·
                    refine ⟨5398937570429439365995193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14397166854478504975987181 5398937570429439365995193)
                    ·
                      refine ⟨4049203177822079524496395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398937570429439365995193 4049203177822079524496395)
                      ·
                        rfl

theorem cell23_7885795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7885795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885795 prefixEnd_7885795 := by exact prefixLift 7885795
  have htrace : WordTrace (prefixWord ++ tailWord_7885795) baseStart_7885795 baseEnd_7885795 := by
    simpa [prefixWord, tailWord_7885795, baseEnd_7885795] using wordTrace_append hprefix tailTrace_7885795
  have hstable : (prefixWord ++ tailWord_7885795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885795).length < 2 ^ (prefixWord ++ tailWord_7885795).sum := by decide
  have hdescent : baseEnd_7885795 < baseStart_7885795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885821 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_7885821 : Nat := 118140960795 + 7885821 * 2 ^ 59
def prefixEnd_7885821 : Nat := 4983230072969 + 3 ^ 40 * 7885821 * 2
def baseEnd_7885821 : Nat := 4049216528319096422771275

theorem tailTrace_7885821 : CollatzResearch.WordTrace tailWord_7885821 prefixEnd_7885821 4049216528319096422771275 := by
  unfold tailWord_7885821
  simp only [CollatzResearch.WordTrace]
  refine ⟨287619520764024782848401317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191746347176016521898934211 287619520764024782848401317)
  ·
    refine ⟨53928660143254646784075247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287619520764024782848401317 53928660143254646784075247)
    ·
      refine ⟨80892990214881970176112871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53928660143254646784075247 80892990214881970176112871)
      ·
        refine ⟨121339485322322955264169307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80892990214881970176112871 121339485322322955264169307)
        ·
          refine ⟨182009227983484432896253961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121339485322322955264169307 182009227983484432896253961)
          ·
            refine ⟨136506920987613324672190471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182009227983484432896253961 136506920987613324672190471)
            ·
              refine ⟨204760381481419987008285707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136506920987613324672190471 204760381481419987008285707)
              ·
                refine ⟨307140572222129980512428561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204760381481419987008285707 307140572222129980512428561)
                ·
                  refine ⟨230355429166597485384321421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307140572222129980512428561 230355429166597485384321421)
                  ·
                    refine ⟨86383285937474057019120533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230355429166597485384321421 86383285937474057019120533)
                    ·
                      refine ⟨4049216528319096422771275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86383285937474057019120533 4049216528319096422771275)
                      ·
                        rfl

theorem cell23_7885821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_7885821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885821 prefixEnd_7885821 := by exact prefixLift 7885821
  have htrace : WordTrace (prefixWord ++ tailWord_7885821) baseStart_7885821 baseEnd_7885821 := by
    simpa [prefixWord, tailWord_7885821, baseEnd_7885821] using wordTrace_append hprefix tailTrace_7885821
  have hstable : (prefixWord ++ tailWord_7885821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885821).length < 2 ^ (prefixWord ++ tailWord_7885821).sum := by decide
  have hdescent : baseEnd_7885821 < baseStart_7885821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885838 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7885838 : Nat := 118140960795 + 7885838 * 2 ^ 59
def prefixEnd_7885838 : Nat := 4983230072969 + 3 ^ 40 * 7885838 * 2
def baseEnd_7885838 : Nat := 4049225257490222856258697

theorem tailTrace_7885838 : CollatzResearch.WordTrace tailWord_7885838 prefixEnd_7885838 4049225257490222856258697 := by
  unfold tailWord_7885838
  simp only [CollatzResearch.WordTrace]
  refine ⟨35952517600620399343971271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191746760536642129834513445 35952517600620399343971271)
  ·
    refine ⟨53928776400930599015956907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35952517600620399343971271 53928776400930599015956907)
    ·
      refine ⟨80893164601395898523935361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53928776400930599015956907 80893164601395898523935361)
      ·
        refine ⟨60669873451046923892951521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80893164601395898523935361 60669873451046923892951521)
        ·
          refine ⟨45502405088285192919713641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60669873451046923892951521 45502405088285192919713641)
          ·
            refine ⟨34126803816213894689785231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45502405088285192919713641 34126803816213894689785231)
            ·
              refine ⟨51190205724320842034677847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34126803816213894689785231 51190205724320842034677847)
              ·
                refine ⟨76785308586481263052016771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51190205724320842034677847 76785308586481263052016771)
                ·
                  refine ⟨115177962879721894578025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76785308586481263052016771 115177962879721894578025157)
                  ·
                    refine ⟨21595868039947855233379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115177962879721894578025157 21595868039947855233379717)
                    ·
                      refine ⟨4049225257490222856258697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21595868039947855233379717 4049225257490222856258697)
                      ·
                        rfl

theorem cell23_7885838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7885838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885838 prefixEnd_7885838 := by exact prefixLift 7885838
  have htrace : WordTrace (prefixWord ++ tailWord_7885838) baseStart_7885838 baseEnd_7885838 := by
    simpa [prefixWord, tailWord_7885838, baseEnd_7885838] using wordTrace_append hprefix tailTrace_7885838
  have hstable : (prefixWord ++ tailWord_7885838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885838).length < 2 ^ (prefixWord ++ tailWord_7885838).sum := by decide
  have hdescent : baseEnd_7885838 < baseStart_7885838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885848 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 7]
def baseStart_7885848 : Nat := 118140960795 + 7885848 * 2 ^ 59
def prefixEnd_7885848 : Nat := 4983230072969 + 3 ^ 40 * 7885848 * 2
def baseEnd_7885848 : Nat := 449914488032974201903739

theorem tailTrace_7885848 : CollatzResearch.WordTrace tailWord_7885848 prefixEnd_7885848 449914488032974201903739 := by
  unfold tailWord_7885848
  simp only [CollatzResearch.WordTrace]
  refine ⟨143810252767463483229817099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191747003689951310973089465 143810252767463483229817099)
  ·
    refine ⟨215715379151195224844725649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143810252767463483229817099 215715379151195224844725649)
    ·
      refine ⟨161786534363396418633544237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215715379151195224844725649 161786534363396418633544237)
      ·
        refine ⟨60669950386273656987579089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161786534363396418633544237 60669950386273656987579089)
        ·
          refine ⟨45502462789705242740684317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60669950386273656987579089 45502462789705242740684317)
          ·
            refine ⟨17063423546139466027756619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45502462789705242740684317 17063423546139466027756619)
            ·
              refine ⟨25595135319209199041634929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17063423546139466027756619 25595135319209199041634929)
              ·
                refine ⟨19196351489406899281226197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25595135319209199041634929 19196351489406899281226197)
                ·
                  refine ⟨449914488032974201903739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19196351489406899281226197 449914488032974201903739)
                  ·
                    rfl

theorem cell23_7885848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_7885848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885848 prefixEnd_7885848 := by exact prefixLift 7885848
  have htrace : WordTrace (prefixWord ++ tailWord_7885848) baseStart_7885848 baseEnd_7885848 := by
    simpa [prefixWord, tailWord_7885848, baseEnd_7885848] using wordTrace_append hprefix tailTrace_7885848
  have hstable : (prefixWord ++ tailWord_7885848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885848).length < 2 ^ (prefixWord ++ tailWord_7885848).sum := by decide
  have hdescent : baseEnd_7885848 < baseStart_7885848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885876 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7885876 : Nat := 118140960795 + 7885876 * 2 ^ 59
def prefixEnd_7885876 : Nat := 4983230072969 + 3 ^ 40 * 7885876 * 2
def baseEnd_7885876 : Nat := 4049244769755093707583523

theorem tailTrace_7885876 : CollatzResearch.WordTrace tailWord_7885876 prefixEnd_7885876 4049244769755093707583523 := by
  unfold tailWord_7885876
  simp only [CollatzResearch.WordTrace]
  refine ⟨143810763389412763620826741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191747684519217018161102321 143810763389412763620826741)
  ·
    refine ⟨13482259067757446589452507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143810763389412763620826741 13482259067757446589452507)
    ·
      refine ⟨20223388601636169884178761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13482259067757446589452507 20223388601636169884178761)
      ·
        refine ⟨15167541451227127413134071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20223388601636169884178761 15167541451227127413134071)
        ·
          refine ⟨22751312176840691119701107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15167541451227127413134071 22751312176840691119701107)
          ·
            refine ⟨34126968265261036679551661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22751312176840691119701107 34126968265261036679551661)
            ·
              refine ⟨12797613099472888754831873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34126968265261036679551661 12797613099472888754831873)
              ·
                refine ⟨9598209824604666566123905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12797613099472888754831873 9598209824604666566123905)
                ·
                  refine ⟨7198657368453499924592929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598209824604666566123905 7198657368453499924592929)
                  ·
                    refine ⟨5398993026340124943444697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198657368453499924592929 5398993026340124943444697)
                    ·
                      refine ⟨4049244769755093707583523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5398993026340124943444697 4049244769755093707583523)
                      ·
                        rfl

theorem cell23_7885876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7885876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885876 prefixEnd_7885876 := by exact prefixLift 7885876
  have htrace : WordTrace (prefixWord ++ tailWord_7885876) baseStart_7885876 baseEnd_7885876 := by
    simpa [prefixWord, tailWord_7885876, baseEnd_7885876] using wordTrace_append hprefix tailTrace_7885876
  have hstable : (prefixWord ++ tailWord_7885876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885876).length < 2 ^ (prefixWord ++ tailWord_7885876).sum := by decide
  have hdescent : baseEnd_7885876 < baseStart_7885876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885898 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_7885898 : Nat := 118140960795 + 7885898 * 2 ^ 59
def prefixEnd_7885898 : Nat := 4983230072969 + 3 ^ 40 * 7885898 * 2
def baseEnd_7885898 : Nat := 4049256066329492621508421

theorem tailTrace_7885898 : CollatzResearch.WordTrace tailWord_7885898 prefixEnd_7885898 4049256066329492621508421 := by
  unfold tailWord_7885898
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905582296186456249738587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191748219456497216665969565 71905582296186456249738587)
  ·
    refine ⟨107858373444279684374607881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71905582296186456249738587 107858373444279684374607881)
    ·
      refine ⟨80893780083209763280955911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107858373444279684374607881 80893780083209763280955911)
      ·
        refine ⟨121340670124814644921433867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80893780083209763280955911 121340670124814644921433867)
        ·
          refine ⟨182011005187221967382150801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121340670124814644921433867 182011005187221967382150801)
          ·
            refine ⟨136508253890416475536613101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182011005187221967382150801 136508253890416475536613101)
            ·
              refine ⟨51190595208906178326229913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136508253890416475536613101 51190595208906178326229913)
              ·
                refine ⟨38392946406679633744672435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51190595208906178326229913 38392946406679633744672435)
                ·
                  refine ⟨57589419610019450617008653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38392946406679633744672435 57589419610019450617008653)
                  ·
                    refine ⟨21596032353757293981378245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57589419610019450617008653 21596032353757293981378245)
                    ·
                      refine ⟨4049256066329492621508421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21596032353757293981378245 4049256066329492621508421)
                      ·
                        rfl

theorem cell23_7885898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_7885898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885898 prefixEnd_7885898 := by exact prefixLift 7885898
  have htrace : WordTrace (prefixWord ++ tailWord_7885898) baseStart_7885898 baseEnd_7885898 := by
    simpa [prefixWord, tailWord_7885898, baseEnd_7885898] using wordTrace_append hprefix tailTrace_7885898
  have hstable : (prefixWord ++ tailWord_7885898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885898).length < 2 ^ (prefixWord ++ tailWord_7885898).sum := by decide
  have hdescent : baseEnd_7885898 < baseStart_7885898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885935 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_7885935 : Nat := 118140960795 + 7885935 * 2 ^ 59
def prefixEnd_7885935 : Nat := 4983230072969 + 3 ^ 40 * 7885935 * 2
def baseEnd_7885935 : Nat := 4049275065113708976745751

theorem tailTrace_7885935 : CollatzResearch.WordTrace tailWord_7885935 prefixEnd_7885935 4049275065113708976745751 := by
  unfold tailWord_7885935
  simp only [CollatzResearch.WordTrace]
  refine ⟨287623678685611780318051259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191749119123741186878700839 287623678685611780318051259)
  ·
    refine ⟨431435518028417670477076889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287623678685611780318051259 431435518028417670477076889)
    ·
      refine ⟨323576638521313252857807667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431435518028417670477076889 323576638521313252857807667)
      ·
        refine ⟨485364957781969879286711501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323576638521313252857807667 485364957781969879286711501)
        ·
          refine ⟨182011859168238704732516813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485364957781969879286711501 182011859168238704732516813)
          ·
            refine ⟨68254447188089514274693805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182011859168238704732516813 68254447188089514274693805)
            ·
              refine ⟨25595417695533567853010177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68254447188089514274693805 25595417695533567853010177)
              ·
                refine ⟨19196563271650175889757633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25595417695533567853010177 19196563271650175889757633)
                ·
                  refine ⟨14397422453737631917318225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19196563271650175889757633 14397422453737631917318225)
                  ·
                    refine ⟨10798066840303223937988669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14397422453737631917318225 10798066840303223937988669)
                    ·
                      refine ⟨4049275065113708976745751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798066840303223937988669 4049275065113708976745751)
                      ·
                        rfl

theorem cell23_7885935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_7885935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885935 prefixEnd_7885935 := by exact prefixLift 7885935
  have htrace : WordTrace (prefixWord ++ tailWord_7885935) baseStart_7885935 baseEnd_7885935 := by
    simpa [prefixWord, tailWord_7885935, baseEnd_7885935] using wordTrace_append hprefix tailTrace_7885935
  have hstable : (prefixWord ++ tailWord_7885935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885935).length < 2 ^ (prefixWord ++ tailWord_7885935).sum := by decide
  have hdescent : baseEnd_7885935 < baseStart_7885935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7885938 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_7885938 : Nat := 118140960795 + 7885938 * 2 ^ 59
def prefixEnd_7885938 : Nat := 4983230072969 + 3 ^ 40 * 7885938 * 2
def baseEnd_7885938 : Nat := 449919622839519162778693

theorem tailTrace_7885938 : CollatzResearch.WordTrace tailWord_7885938 prefixEnd_7885938 449919622839519162778693 := by
  unfold tailWord_7885938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71905947026150227957602617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191749192069733941220273645 71905947026150227957602617)
  ·
    refine ⟨53929460269612670968201963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71905947026150227957602617 53929460269612670968201963)
    ·
      refine ⟨80894190404419006452302945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53929460269612670968201963 80894190404419006452302945)
      ·
        refine ⟨60670642803314254839227209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80894190404419006452302945 60670642803314254839227209)
        ·
          refine ⟨45502982102485691129420407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60670642803314254839227209 45502982102485691129420407)
          ·
            refine ⟨68254473153728536694130611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45502982102485691129420407 68254473153728536694130611)
            ·
              refine ⟨102381709730592805041195917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68254473153728536694130611 102381709730592805041195917)
              ·
                refine ⟨38393141148972301890448469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102381709730592805041195917 38393141148972301890448469)
                ·
                  refine ⟨449919622839519162778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38393141148972301890448469 449919622839519162778693)
                  ·
                    rfl

theorem cell23_7885938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_7885938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7885938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7885938 prefixEnd_7885938 := by exact prefixLift 7885938
  have htrace : WordTrace (prefixWord ++ tailWord_7885938) baseStart_7885938 baseEnd_7885938 := by
    simpa [prefixWord, tailWord_7885938, baseEnd_7885938] using wordTrace_append hprefix tailTrace_7885938
  have hstable : (prefixWord ++ tailWord_7885938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7885938).length < 2 ^ (prefixWord ++ tailWord_7885938).sum := by decide
  have hdescent : baseEnd_7885938 < baseStart_7885938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7885938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886049 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_7886049 : Nat := 118140960795 + 7886049 * 2 ^ 59
def prefixEnd_7886049 : Nat := 4983230072969 + 3 ^ 40 * 7886049 * 2
def baseEnd_7886049 : Nat := 1349777867302773843573409

theorem tailTrace_7886049 : CollatzResearch.WordTrace tailWord_7886049 prefixEnd_7886049 1349777867302773843573409 := by
  unfold tailWord_7886049
  simp only [CollatzResearch.WordTrace]
  refine ⟨287627836607198777787701201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191751891071465851858467467 287627836607198777787701201)
  ·
    refine ⟨215720877455399083340775901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287627836607198777787701201 215720877455399083340775901)
    ·
      refine ⟨80895329045774656252790963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215720877455399083340775901 80895329045774656252790963)
      ·
        refine ⟨121342993568661984379186445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80895329045774656252790963 121342993568661984379186445)
        ·
          refine ⟨45503622588248244142194917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121342993568661984379186445 45503622588248244142194917)
          ·
            refine ⟨8531929235296545776661547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45503622588248244142194917 8531929235296545776661547)
            ·
              refine ⟨12797893852944818664992321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8531929235296545776661547 12797893852944818664992321)
              ·
                refine ⟨9598420389708613998744241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12797893852944818664992321 9598420389708613998744241)
                ·
                  refine ⟨7198815292281460499058181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598420389708613998744241 7198815292281460499058181)
                  ·
                    refine ⟨1349777867302773843573409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198815292281460499058181 1349777867302773843573409)
                    ·
                      rfl

theorem cell23_7886049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_7886049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886049 prefixEnd_7886049 := by exact prefixLift 7886049
  have htrace : WordTrace (prefixWord ++ tailWord_7886049) baseStart_7886049 baseEnd_7886049 := by
    simpa [prefixWord, tailWord_7886049, baseEnd_7886049] using wordTrace_append hprefix tailTrace_7886049
  have hstable : (prefixWord ++ tailWord_7886049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886049).length < 2 ^ (prefixWord ++ tailWord_7886049).sum := by decide
  have hdescent : baseEnd_7886049 < baseStart_7886049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886056 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7886056 : Nat := 118140960795 + 7886056 * 2 ^ 59
def prefixEnd_7886056 : Nat := 4983230072969 + 3 ^ 40 * 7886056 * 2
def baseEnd_7886056 : Nat := 4049337196272903003332695

theorem tailTrace_7886056 : CollatzResearch.WordTrace tailWord_7886056 prefixEnd_7886056 4049337196272903003332695 := by
  unfold tailWord_7886056
  simp only [CollatzResearch.WordTrace]
  refine ⟨143814045959086708991603011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191752061278782278655470681 143814045959086708991603011)
  ·
    refine ⟨215721068938630063487404517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143814045959086708991603011 215721068938630063487404517)
    ·
      refine ⟨40447700425993136903888347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215721068938630063487404517 40447700425993136903888347)
      ·
        refine ⟨60671550638989705355832521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40447700425993136903888347 60671550638989705355832521)
        ·
          refine ⟨45503662979242279016874391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60671550638989705355832521 45503662979242279016874391)
          ·
            refine ⟨68255494468863418525311587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45503662979242279016874391 68255494468863418525311587)
            ·
              refine ⟨102383241703295127787967381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68255494468863418525311587 102383241703295127787967381)
              ·
                refine ⟨4799214454841959115060971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102383241703295127787967381 4799214454841959115060971)
                ·
                  refine ⟨7198821682262938672591457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799214454841959115060971 7198821682262938672591457)
                  ·
                    refine ⟨5399116261697204004443593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198821682262938672591457 5399116261697204004443593)
                    ·
                      refine ⟨4049337196272903003332695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399116261697204004443593 4049337196272903003332695)
                      ·
                        rfl

theorem cell23_7886056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7886056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886056 prefixEnd_7886056 := by exact prefixLift 7886056
  have htrace : WordTrace (prefixWord ++ tailWord_7886056) baseStart_7886056 baseEnd_7886056 := by
    simpa [prefixWord, tailWord_7886056, baseEnd_7886056] using wordTrace_append hprefix tailTrace_7886056
  have hstable : (prefixWord ++ tailWord_7886056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886056).length < 2 ^ (prefixWord ++ tailWord_7886056).sum := by decide
  have hdescent : baseEnd_7886056 < baseStart_7886056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886066 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_7886066 : Nat := 118140960795 + 7886066 * 2 ^ 59
def prefixEnd_7886066 : Nat := 4983230072969 + 3 ^ 40 * 7886066 * 2
def baseEnd_7886066 : Nat := 1349780777026482654735883

theorem tailTrace_7886066 : CollatzResearch.WordTrace tailWord_7886066 prefixEnd_7886066 1349780777026482654735883 := by
  unfold tailWord_7886066
  simp only [CollatzResearch.WordTrace]
  refine ⟨71907114162034297422767513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191752304432091459794046701 71907114162034297422767513)
  ·
    refine ⟨53930335621525723067075635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71907114162034297422767513 53930335621525723067075635)
    ·
      refine ⟨80895503432288584600613453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53930335621525723067075635 80895503432288584600613453)
      ·
        refine ⟨30335813787108219225230045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80895503432288584600613453 30335813787108219225230045)
        ·
          refine ⟨11375930170165582209461267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30335813787108219225230045 11375930170165582209461267)
          ·
            refine ⟨17063895255248373314191901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375930170165582209461267 17063895255248373314191901)
            ·
              refine ⟨6398960720718139992821963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17063895255248373314191901 6398960720718139992821963)
              ·
                refine ⟨9598441081077209989232945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398960720718139992821963 9598441081077209989232945)
                ·
                  refine ⟨7198830810807907491924709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598441081077209989232945 7198830810807907491924709)
                  ·
                    refine ⟨1349780777026482654735883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7198830810807907491924709 1349780777026482654735883)
                    ·
                      rfl

theorem cell23_7886066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_7886066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886066 prefixEnd_7886066 := by exact prefixLift 7886066
  have htrace : WordTrace (prefixWord ++ tailWord_7886066) baseStart_7886066 baseEnd_7886066 := by
    simpa [prefixWord, tailWord_7886066, baseEnd_7886066] using wordTrace_append hprefix tailTrace_7886066
  have hstable : (prefixWord ++ tailWord_7886066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886066).length < 2 ^ (prefixWord ++ tailWord_7886066).sum := by decide
  have hdescent : baseEnd_7886066 < baseStart_7886066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886132 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7886132 : Nat := 118140960795 + 7886132 * 2 ^ 59
def prefixEnd_7886132 : Nat := 4983230072969 + 3 ^ 40 * 7886132 * 2
def baseEnd_7886132 : Nat := 4049376220802644705982345

theorem tailTrace_7886132 : CollatzResearch.WordTrace tailWord_7886132 prefixEnd_7886132 4049376220802644705982345 := by
  unfold tailWord_7886132
  simp only [CollatzResearch.WordTrace]
  refine ⟨143815431932949041481486325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191753909243932055308648433 143815431932949041481486325)
  ·
    refine ⟨13482696743713972638889343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143815431932949041481486325 13482696743713972638889343)
    ·
      refine ⟨20224045115570958958334015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13482696743713972638889343 20224045115570958958334015)
      ·
        refine ⟨30336067673356438437501023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20224045115570958958334015 30336067673356438437501023)
        ·
          refine ⟨45504101510034657656251535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30336067673356438437501023 45504101510034657656251535)
          ·
            refine ⟨68256152265051986484377303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45504101510034657656251535 68256152265051986484377303)
            ·
              refine ⟨102384228397577979726565955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68256152265051986484377303 102384228397577979726565955)
              ·
                refine ⟨153576342596366969589848933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102384228397577979726565955 153576342596366969589848933)
                ·
                  refine ⟨28795564236818806798096675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153576342596366969589848933 28795564236818806798096675)
                  ·
                    refine ⟨43193346355228210197145013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28795564236818806798096675 43193346355228210197145013)
                    ·
                      refine ⟨4049376220802644705982345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43193346355228210197145013 4049376220802644705982345)
                      ·
                        rfl

theorem cell23_7886132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7886132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886132 prefixEnd_7886132 := by exact prefixLift 7886132
  have htrace : WordTrace (prefixWord ++ tailWord_7886132) baseStart_7886132 baseEnd_7886132 := by
    simpa [prefixWord, tailWord_7886132, baseEnd_7886132] using wordTrace_append hprefix tailTrace_7886132
  have hstable : (prefixWord ++ tailWord_7886132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886132).length < 2 ^ (prefixWord ++ tailWord_7886132).sum := by decide
  have hdescent : baseEnd_7886132 < baseStart_7886132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886152 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 5]
def baseStart_7886152 : Nat := 118140960795 + 7886152 * 2 ^ 59
def prefixEnd_7886152 : Nat := 4983230072969 + 3 ^ 40 * 7886152 * 2
def baseEnd_7886152 : Nat := 449931832268414958636917

theorem tailTrace_7886152 : CollatzResearch.WordTrace tailWord_7886152 prefixEnd_7886152 449931832268414958636917 := by
  unfold tailWord_7886152
  simp only [CollatzResearch.WordTrace]
  refine ⟨143815796662912813189350355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191754395550550417585800473 143815796662912813189350355)
  ·
    refine ⟨215723694994369219784025533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143815796662912813189350355 215723694994369219784025533)
    ·
      refine ⟨80896385622888457419009575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215723694994369219784025533 80896385622888457419009575)
      ·
        refine ⟨121344578434332686128514363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80896385622888457419009575 121344578434332686128514363)
        ·
          refine ⟨182016867651499029192771545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121344578434332686128514363 182016867651499029192771545)
          ·
            refine ⟨136512650738624271894578659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182016867651499029192771545 136512650738624271894578659)
            ·
              refine ⟨204768976107936407841867989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136512650738624271894578659 204768976107936407841867989)
              ·
                refine ⟨4799272877529759558793781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204768976107936407841867989 4799272877529759558793781)
                ·
                  refine ⟨449931832268414958636917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799272877529759558793781 449931832268414958636917)
                  ·
                    rfl

theorem cell23_7886152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 5].length) (baseStart_7886152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886152 prefixEnd_7886152 := by exact prefixLift 7886152
  have htrace : WordTrace (prefixWord ++ tailWord_7886152) baseStart_7886152 baseEnd_7886152 := by
    simpa [prefixWord, tailWord_7886152, baseEnd_7886152] using wordTrace_append hprefix tailTrace_7886152
  have hstable : (prefixWord ++ tailWord_7886152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886152).length < 2 ^ (prefixWord ++ tailWord_7886152).sum := by decide
  have hdescent : baseEnd_7886152 < baseStart_7886152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886162 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_7886162 : Nat := 118140960795 + 7886162 * 2 ^ 59
def prefixEnd_7886162 : Nat := 4983230072969 + 3 ^ 40 * 7886162 * 2
def baseEnd_7886162 : Nat := 4049391625222279588607207

theorem tailTrace_7886162 : CollatzResearch.WordTrace tailWord_7886162 prefixEnd_7886162 4049391625222279588607207 := by
  unfold tailWord_7886162
  simp only [CollatzResearch.WordTrace]
  refine ⟨71907989513947349521641185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191754638703859598724376493 71907989513947349521641185)
  ·
    refine ⟨53930992135460512141230889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71907989513947349521641185 53930992135460512141230889)
    ·
      refine ⟨40448244101595384105923167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53930992135460512141230889 40448244101595384105923167)
      ·
        refine ⟨60672366152393076158884751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40448244101595384105923167 60672366152393076158884751)
        ·
          refine ⟨91008549228589614238327127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60672366152393076158884751 91008549228589614238327127)
          ·
            refine ⟨136512823842884421357490691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91008549228589614238327127 136512823842884421357490691)
            ·
              refine ⟨204769235764326632036236037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136512823842884421357490691 204769235764326632036236037)
              ·
                refine ⟨38394231705811243506794257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204769235764326632036236037 38394231705811243506794257)
                ·
                  refine ⟨28795673779358432630095693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38394231705811243506794257 28795673779358432630095693)
                  ·
                    refine ⟨10798377667259412236285885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28795673779358432630095693 10798377667259412236285885)
                    ·
                      refine ⟨4049391625222279588607207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798377667259412236285885 4049391625222279588607207)
                      ·
                        rfl

theorem cell23_7886162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_7886162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886162 prefixEnd_7886162 := by exact prefixLift 7886162
  have htrace : WordTrace (prefixWord ++ tailWord_7886162) baseStart_7886162 baseEnd_7886162 := by
    simpa [prefixWord, tailWord_7886162, baseEnd_7886162] using wordTrace_append hprefix tailTrace_7886162
  have hstable : (prefixWord ++ tailWord_7886162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886162).length < 2 ^ (prefixWord ++ tailWord_7886162).sum := by decide
  have hdescent : baseEnd_7886162 < baseStart_7886162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886169 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 5]
def baseStart_7886169 : Nat := 118140960795 + 7886169 * 2 ^ 59
def prefixEnd_7886169 : Nat := 4983230072969 + 3 ^ 40 * 7886169 * 2
def baseEnd_7886169 : Nat := 449932802176317895691075

theorem tailTrace_7886169 : CollatzResearch.WordTrace tailWord_7886169 prefixEnd_7886169 449932802176317895691075 := by
  unfold tailWord_7886169
  simp only [CollatzResearch.WordTrace]
  refine ⟨287632213366764038282069561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191754808911176025521379707 287632213366764038282069561)
  ·
    refine ⟨215724160025073028711552171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287632213366764038282069561 215724160025073028711552171)
    ·
      refine ⟨323586240037609543067328257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215724160025073028711552171 323586240037609543067328257)
      ·
        refine ⟨242689680028207157300496193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323586240037609543067328257 242689680028207157300496193)
        ·
          refine ⟨182017260021155367975372145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242689680028207157300496193 182017260021155367975372145)
          ·
            refine ⟨136512945015866525981529109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182017260021155367975372145 136512945015866525981529109)
            ·
              refine ⟨6399044297618743405384177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136512945015866525981529109 6399044297618743405384177)
              ·
                refine ⟨4799283223214057554038133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399044297618743405384177 4799283223214057554038133)
                ·
                  refine ⟨449932802176317895691075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799283223214057554038133 449932802176317895691075)
                  ·
                    rfl

theorem cell23_7886169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 5].length) (baseStart_7886169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886169 prefixEnd_7886169 := by exact prefixLift 7886169
  have htrace : WordTrace (prefixWord ++ tailWord_7886169) baseStart_7886169 baseEnd_7886169 := by
    simpa [prefixWord, tailWord_7886169, baseEnd_7886169] using wordTrace_append hprefix tailTrace_7886169
  have hstable : (prefixWord ++ tailWord_7886169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886169).length < 2 ^ (prefixWord ++ tailWord_7886169).sum := by decide
  have hdescent : baseEnd_7886169 < baseStart_7886169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886225 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 8]
def baseStart_7886225 : Nat := 118140960795 + 7886225 * 2 ^ 59
def prefixEnd_7886225 : Nat := 4983230072969 + 3 ^ 40 * 7886225 * 2
def baseEnd_7886225 : Nat := 449935997167056982457713

theorem tailTrace_7886225 : CollatzResearch.WordTrace tailWord_7886225 prefixEnd_7886225 449935997167056982457713 := by
  unfold tailWord_7886225
  simp only [CollatzResearch.WordTrace]
  refine ⟨287634255854561159846108129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191756170569707439897405419 287634255854561159846108129)
  ·
    refine ⟨215725691890920869884581097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287634255854561159846108129 215725691890920869884581097)
    ·
      refine ⟨161794268918190652413435823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215725691890920869884581097 161794268918190652413435823)
      ·
        refine ⟨242691403377285978620153735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161794268918190652413435823 242691403377285978620153735)
        ·
          refine ⟨364037105065928967930230603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242691403377285978620153735 364037105065928967930230603)
          ·
            refine ⟨546055657598893451895345905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364037105065928967930230603 546055657598893451895345905)
            ·
              refine ⟨409541743199170088921509429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546055657598893451895345905 409541743199170088921509429)
              ·
                refine ⟨38394538424922195836391509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409541743199170088921509429 38394538424922195836391509)
                ·
                  refine ⟨449935997167056982457713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38394538424922195836391509 449935997167056982457713)
                  ·
                    rfl

theorem cell23_7886225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_7886225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886225 prefixEnd_7886225 := by exact prefixLift 7886225
  have htrace : WordTrace (prefixWord ++ tailWord_7886225) baseStart_7886225 baseEnd_7886225 := by
    simpa [prefixWord, tailWord_7886225, baseEnd_7886225] using wordTrace_append hprefix tailTrace_7886225
  have hstable : (prefixWord ++ tailWord_7886225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886225).length < 2 ^ (prefixWord ++ tailWord_7886225).sum := by decide
  have hdescent : baseEnd_7886225 < baseStart_7886225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886255 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 9]
def baseStart_7886255 : Nat := 118140960795 + 7886255 * 2 ^ 59
def prefixEnd_7886255 : Nat := 4983230072969 + 3 ^ 40 * 7886255 * 2
def baseEnd_7886255 : Nat := 1349813126307715908248093

theorem tailTrace_7886255 : CollatzResearch.WordTrace tailWord_7886255 prefixEnd_7886255 1349813126307715908248093 := by
  unfold tailWord_7886255
  simp only [CollatzResearch.WordTrace]
  refine ⟨287635350044452474969700219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191756900029634983313133479 287635350044452474969700219)
  ·
    refine ⟨431453025066678712454550329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287635350044452474969700219 431453025066678712454550329)
    ·
      refine ⟨323589768800009034340912747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431453025066678712454550329 323589768800009034340912747)
      ·
        refine ⟨485384653200013551511369121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323589768800009034340912747 485384653200013551511369121)
        ·
          refine ⟨364038489900010163633526841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485384653200013551511369121 364038489900010163633526841)
          ·
            refine ⟨273028867425007622725145131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364038489900010163633526841 273028867425007622725145131)
            ·
              refine ⟨409543301137511434087717697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273028867425007622725145131 409543301137511434087717697)
              ·
                refine ⟨307157475853133575565788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409543301137511434087717697 307157475853133575565788273)
                ·
                  refine ⟨230368106889850181674341205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307157475853133575565788273 230368106889850181674341205)
                  ·
                    refine ⟨1349813126307715908248093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230368106889850181674341205 1349813126307715908248093)
                    ·
                      rfl

theorem cell23_7886255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_7886255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886255 prefixEnd_7886255 := by exact prefixLift 7886255
  have htrace : WordTrace (prefixWord ++ tailWord_7886255) baseStart_7886255 baseEnd_7886255 := by
    simpa [prefixWord, tailWord_7886255, baseEnd_7886255] using wordTrace_append hprefix tailTrace_7886255
  have hstable : (prefixWord ++ tailWord_7886255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886255).length < 2 ^ (prefixWord ++ tailWord_7886255).sum := by decide
  have hdescent : baseEnd_7886255 < baseStart_7886255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886286 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_7886286 : Nat := 118140960795 + 7886286 * 2 ^ 59
def prefixEnd_7886286 : Nat := 4983230072969 + 3 ^ 40 * 7886286 * 2
def baseEnd_7886286 : Nat := 4049455296823437103456637

theorem tailTrace_7886286 : CollatzResearch.WordTrace tailWord_7886286 prefixEnd_7886286 4049455296823437103456637 := by
  unfold tailWord_7886286
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954560088417520908009839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191757653804893444842719141 35954560088417520908009839)
  ·
    refine ⟨53931840132626281362014759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35954560088417520908009839 53931840132626281362014759)
    ·
      refine ⟨80897760198939422043022139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53931840132626281362014759 80897760198939422043022139)
      ·
        refine ⟨121346640298409133064533209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80897760198939422043022139 121346640298409133064533209)
        ·
          refine ⟨91009980223806849798399907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121346640298409133064533209 91009980223806849798399907)
          ·
            refine ⟨136514970335710274697599861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91009980223806849798399907 136514970335710274697599861)
            ·
              refine ⟨12798278468972838252899987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136514970335710274697599861 12798278468972838252899987)
              ·
                refine ⟨19197417703459257379349981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798278468972838252899987 19197417703459257379349981)
                ·
                  refine ⟨7199031638797221517256243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19197417703459257379349981 7199031638797221517256243)
                  ·
                    refine ⟨10798547458195832275884365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199031638797221517256243 10798547458195832275884365)
                    ·
                      refine ⟨4049455296823437103456637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798547458195832275884365 4049455296823437103456637)
                      ·
                        rfl

theorem cell23_7886286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_7886286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886286 prefixEnd_7886286 := by exact prefixLift 7886286
  have htrace : WordTrace (prefixWord ++ tailWord_7886286) baseStart_7886286 baseEnd_7886286 := by
    simpa [prefixWord, tailWord_7886286, baseEnd_7886286] using wordTrace_append hprefix tailTrace_7886286
  have hstable : (prefixWord ++ tailWord_7886286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886286).length < 2 ^ (prefixWord ++ tailWord_7886286).sum := by decide
  have hdescent : baseEnd_7886286 < baseStart_7886286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886337 : List Nat := [1, 2, 4, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_7886337 : Nat := 118140960795 + 7886337 * 2 ^ 59
def prefixEnd_7886337 : Nat := 4983230072969 + 3 ^ 40 * 7886337 * 2
def baseEnd_7886337 : Nat := 4049481484336816403918903

theorem tailTrace_7886337 : CollatzResearch.WordTrace tailWord_7886337 prefixEnd_7886337 4049481484336816403918903 := by
  unfold tailWord_7886337
  simp only [CollatzResearch.WordTrace]
  refine ⟨287638340830155402974185265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191758893886770268649456843 287638340830155402974185265)
  ·
    refine ⟨215728755622616552230638949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287638340830155402974185265 215728755622616552230638949)
    ·
      refine ⟨40449141679240603543244803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215728755622616552230638949 40449141679240603543244803)
      ·
        refine ⟨60673712518860905314867205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40449141679240603543244803 60673712518860905314867205)
        ·
          refine ⟨11376321097286419746537601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60673712518860905314867205 11376321097286419746537601)
          ·
            refine ⟨8532240822964814809903201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376321097286419746537601 8532240822964814809903201)
            ·
              refine ⟨6399180617223611107427401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8532240822964814809903201 6399180617223611107427401)
              ·
                refine ⟨4799385462917708330570551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399180617223611107427401 4799385462917708330570551)
                ·
                  refine ⟨7199078194376562495855827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4799385462917708330570551 7199078194376562495855827)
                  ·
                    refine ⟨10798617291564843743783741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199078194376562495855827 10798617291564843743783741)
                    ·
                      refine ⟨4049481484336816403918903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798617291564843743783741 4049481484336816403918903)
                      ·
                        rfl

theorem cell23_7886337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_7886337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886337 prefixEnd_7886337 := by exact prefixLift 7886337
  have htrace : WordTrace (prefixWord ++ tailWord_7886337) baseStart_7886337 baseEnd_7886337 := by
    simpa [prefixWord, tailWord_7886337, baseEnd_7886337] using wordTrace_append hprefix tailTrace_7886337
  have hstable : (prefixWord ++ tailWord_7886337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886337).length < 2 ^ (prefixWord ++ tailWord_7886337).sum := by decide
  have hdescent : baseEnd_7886337 < baseStart_7886337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886362 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_7886362 : Nat := 118140960795 + 7886362 * 2 ^ 59
def prefixEnd_7886362 : Nat := 4983230072969 + 3 ^ 40 * 7886362 * 2
def baseEnd_7886362 : Nat := 1349831440451059602035429

theorem tailTrace_7886362 : CollatzResearch.WordTrace tailWord_7886362 prefixEnd_7886362 1349831440451059602035429 := by
  unfold tailWord_7886362
  simp only [CollatzResearch.WordTrace]
  refine ⟨71909813163766208060961335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191759501770043221495896893 71909813163766208060961335)
  ·
    refine ⟨107864719745649312091442003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71909813163766208060961335 107864719745649312091442003)
    ·
      refine ⟨161797079618473968137163005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107864719745649312091442003 161797079618473968137163005)
      ·
        refine ⟨60673904856927738051436127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161797079618473968137163005 60673904856927738051436127)
        ·
          refine ⟨91010857285391607077154191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60673904856927738051436127 91010857285391607077154191)
          ·
            refine ⟨136516285928087410615731287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91010857285391607077154191 136516285928087410615731287)
            ·
              refine ⟨204774428892131115923596931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136516285928087410615731287 204774428892131115923596931)
              ·
                refine ⟨307161643338196673885395397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204774428892131115923596931 307161643338196673885395397)
                ·
                  refine ⟨57592808125911876353511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307161643338196673885395397 57592808125911876353511637)
                  ·
                    refine ⟨1349831440451059602035429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57592808125911876353511637 1349831440451059602035429)
                    ·
                      rfl

theorem cell23_7886362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_7886362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886362 prefixEnd_7886362 := by exact prefixLift 7886362
  have htrace : WordTrace (prefixWord ++ tailWord_7886362) baseStart_7886362 baseEnd_7886362 := by
    simpa [prefixWord, tailWord_7886362, baseEnd_7886362] using wordTrace_append hprefix tailTrace_7886362
  have hstable : (prefixWord ++ tailWord_7886362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886362).length < 2 ^ (prefixWord ++ tailWord_7886362).sum := by decide
  have hdescent : baseEnd_7886362 < baseStart_7886362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886393 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7886393 : Nat := 118140960795 + 7886393 * 2 ^ 59
def prefixEnd_7886393 : Nat := 4983230072969 + 3 ^ 40 * 7886393 * 2
def baseEnd_7886393 : Nat := 4049510239253468184818645

theorem tailTrace_7886393 : CollatzResearch.WordTrace tailWord_7886393 prefixEnd_7886393 4049510239253468184818645 := by
  unfold tailWord_7886393
  simp only [CollatzResearch.WordTrace]
  refine ⟨287640383317952524538223833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191760255545301683025482555 287640383317952524538223833)
  ·
    refine ⟨215730287488464393403667875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287640383317952524538223833 215730287488464393403667875)
    ·
      refine ⟨323595431232696590105501813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215730287488464393403667875 323595431232696590105501813)
      ·
        refine ⟨30337071678065305322390795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 323595431232696590105501813 30337071678065305322390795)
        ·
          refine ⟨45505607517097957983586193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30337071678065305322390795 45505607517097957983586193)
          ·
            refine ⟨34129205637823468487689645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45505607517097957983586193 34129205637823468487689645)
            ·
              refine ⟨12798452114183800682883617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34129205637823468487689645 12798452114183800682883617)
              ·
                refine ⟨9598839085637850512162713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12798452114183800682883617 9598839085637850512162713)
                ·
                  refine ⟨7199129314228387884122035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9598839085637850512162713 7199129314228387884122035)
                  ·
                    refine ⟨10798693971342581826183053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199129314228387884122035 10798693971342581826183053)
                    ·
                      refine ⟨4049510239253468184818645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798693971342581826183053 4049510239253468184818645)
                      ·
                        rfl

theorem cell23_7886393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7886393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886393 prefixEnd_7886393 := by exact prefixLift 7886393
  have htrace : WordTrace (prefixWord ++ tailWord_7886393) baseStart_7886393 baseEnd_7886393 := by
    simpa [prefixWord, tailWord_7886393, baseEnd_7886393] using wordTrace_append hprefix tailTrace_7886393
  have hstable : (prefixWord ++ tailWord_7886393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886393).length < 2 ^ (prefixWord ++ tailWord_7886393).sum := by decide
  have hdescent : baseEnd_7886393 < baseStart_7886393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886449 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_7886449 : Nat := 118140960795 + 7886449 * 2 ^ 59
def prefixEnd_7886449 : Nat := 4983230072969 + 3 ^ 40 * 7886449 * 2
def baseEnd_7886449 : Nat := 4049538994170119965718387

theorem tailTrace_7886449 : CollatzResearch.WordTrace tailWord_7886449 prefixEnd_7886449 4049538994170119965718387 := by
  unfold tailWord_7886449
  simp only [CollatzResearch.WordTrace]
  refine ⟨287642425805749646102262401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191761617203833097401508267 287642425805749646102262401)
  ·
    refine ⟨215731819354312234576696801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287642425805749646102262401 215731819354312234576696801)
    ·
      refine ⟨161798864515734175932522601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215731819354312234576696801 161798864515734175932522601)
      ·
        refine ⟨121349148386800631949391951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161798864515734175932522601 121349148386800631949391951)
        ·
          refine ⟨182023722580200947924087927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121349148386800631949391951 182023722580200947924087927)
          ·
            refine ⟨273035583870301421886131891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182023722580200947924087927 273035583870301421886131891)
            ·
              refine ⟨409553375805452132829197837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273035583870301421886131891 409553375805452132829197837)
              ·
                refine ⟨153582515927044549810949189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409553375805452132829197837 153582515927044549810949189)
                ·
                  refine ⟨28796721736320853089552973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153582515927044549810949189 28796721736320853089552973)
                  ·
                    refine ⟨10798770651120319908582365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28796721736320853089552973 10798770651120319908582365)
                    ·
                      refine ⟨4049538994170119965718387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10798770651120319908582365 4049538994170119965718387)
                      ·
                        rfl

theorem cell23_7886449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_7886449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886449 prefixEnd_7886449 := by exact prefixLift 7886449
  have htrace : WordTrace (prefixWord ++ tailWord_7886449) baseStart_7886449 baseEnd_7886449 := by
    simpa [prefixWord, tailWord_7886449, baseEnd_7886449] using wordTrace_append hprefix tailTrace_7886449
  have hstable : (prefixWord ++ tailWord_7886449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886449).length < 2 ^ (prefixWord ++ tailWord_7886449).sum := by decide
  have hdescent : baseEnd_7886449 < baseStart_7886449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886469 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_7886469 : Nat := 118140960795 + 7886469 * 2 ^ 59
def prefixEnd_7886469 : Nat := 4983230072969 + 3 ^ 40 * 7886469 * 2
def baseEnd_7886469 : Nat := 1349849754594403295822765

theorem tailTrace_7886469 : CollatzResearch.WordTrace tailWord_7886469 prefixEnd_7886469 1349849754594403295822765 := by
  unfold tailWord_7886469
  simp only [CollatzResearch.WordTrace]
  refine ⟨287643155265677189517990461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191762103510451459678660307 287643155265677189517990461)
  ·
    refine ⟨107866183224628946069246423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287643155265677189517990461 107866183224628946069246423)
    ·
      refine ⟨161799274836943419103869635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107866183224628946069246423 161799274836943419103869635)
      ·
        refine ⟨242698912255415128655804453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161799274836943419103869635 242698912255415128655804453)
        ·
          refine ⟨45506046047890336622963335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242698912255415128655804453 45506046047890336622963335)
          ·
            refine ⟨68259069071835504934445003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45506046047890336622963335 68259069071835504934445003)
            ·
              refine ⟨102388603607753257401667505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68259069071835504934445003 102388603607753257401667505)
              ·
                refine ⟨76791452705814943051250629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102388603607753257401667505 76791452705814943051250629)
                ·
                  refine ⟨14398397382340301822109493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76791452705814943051250629 14398397382340301822109493)
                  ·
                    refine ⟨1349849754594403295822765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14398397382340301822109493 1349849754594403295822765)
                    ·
                      rfl

theorem cell23_7886469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_7886469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886469 prefixEnd_7886469 := by exact prefixLift 7886469
  have htrace : WordTrace (prefixWord ++ tailWord_7886469) baseStart_7886469 baseEnd_7886469 := by
    simpa [prefixWord, tailWord_7886469, baseEnd_7886469] using wordTrace_append hprefix tailTrace_7886469
  have hstable : (prefixWord ++ tailWord_7886469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886469).length < 2 ^ (prefixWord ++ tailWord_7886469).sum := by decide
  have hdescent : baseEnd_7886469 < baseStart_7886469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886540 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7886540 : Nat := 118140960795 + 7886540 * 2 ^ 59
def prefixEnd_7886540 : Nat := 4983230072969 + 3 ^ 40 * 7886540 * 2
def baseEnd_7886540 : Nat := 4049585720909679109680469

theorem tailTrace_7886540 : CollatzResearch.WordTrace tailWord_7886540 prefixEnd_7886540 4049585720909679109680469 := by
  unfold tailWord_7886540
  simp only [CollatzResearch.WordTrace]
  refine ⟨143822872424209984321912537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191763829898946645762550049 143822872424209984321912537)
  ·
    refine ⟨107867154318157488241434403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143822872424209984321912537 107867154318157488241434403)
    ·
      refine ⟨161800731477236232362151605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107867154318157488241434403 161800731477236232362151605)
      ·
        refine ⟨15168818575990896783951713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161800731477236232362151605 15168818575990896783951713)
        ·
          refine ⟨11376613931993172587963785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168818575990896783951713 11376613931993172587963785)
          ·
            refine ⟨8532460448994879440972839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376613931993172587963785 8532460448994879440972839)
            ·
              refine ⟨12798690673492319161459259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532460448994879440972839 12798690673492319161459259)
              ·
                refine ⟨19198036010238478742188889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12798690673492319161459259 19198036010238478742188889)
                ·
                  refine ⟨14398527007678859056641667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19198036010238478742188889 14398527007678859056641667)
                  ·
                    refine ⟨21597790511518288584962501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14398527007678859056641667 21597790511518288584962501)
                    ·
                      refine ⟨4049585720909679109680469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21597790511518288584962501 4049585720909679109680469)
                      ·
                        rfl

theorem cell23_7886540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7886540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886540 prefixEnd_7886540 := by exact prefixLift 7886540
  have htrace : WordTrace (prefixWord ++ tailWord_7886540) baseStart_7886540 baseEnd_7886540 := by
    simpa [prefixWord, tailWord_7886540, baseEnd_7886540] using wordTrace_append hprefix tailTrace_7886540
  have hstable : (prefixWord ++ tailWord_7886540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886540).length < 2 ^ (prefixWord ++ tailWord_7886540).sum := by decide
  have hdescent : baseEnd_7886540 < baseStart_7886540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886606 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_7886606 : Nat := 118140960795 + 7886606 * 2 ^ 59
def prefixEnd_7886606 : Nat := 4983230072969 + 3 ^ 40 * 7886606 * 2
def baseEnd_7886606 : Nat := 1349873203544291950485055

theorem tailTrace_7886606 : CollatzResearch.WordTrace tailWord_7886606 prefixEnd_7886606 1349873203544291950485055 := by
  unfold tailWord_7886606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35956019008272607739465959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191765434710787241277151781 35956019008272607739465959)
  ·
    refine ⟨53934028512408911609198939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35956019008272607739465959 53934028512408911609198939)
    ·
      refine ⟨80901042768613367413798409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53934028512408911609198939 80901042768613367413798409)
      ·
        refine ⟨60675782076460025560348807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80901042768613367413798409 60675782076460025560348807)
        ·
          refine ⟨91013673114690038340523211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60675782076460025560348807 91013673114690038340523211)
          ·
            refine ⟨136520509672035057510784817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91013673114690038340523211 136520509672035057510784817)
            ·
              refine ⟨102390382254026293133088613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136520509672035057510784817 102390382254026293133088613)
              ·
                refine ⟨19198196672629929962454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102390382254026293133088613 19198196672629929962454115)
                ·
                  refine ⟨28797295008944894943681173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19198196672629929962454115 28797295008944894943681173)
                  ·
                    refine ⟨1349873203544291950485055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28797295008944894943681173 1349873203544291950485055)
                    ·
                      rfl

theorem cell23_7886606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_7886606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886606 prefixEnd_7886606 := by exact prefixLift 7886606
  have htrace : WordTrace (prefixWord ++ tailWord_7886606) baseStart_7886606 baseEnd_7886606 := by
    simpa [prefixWord, tailWord_7886606, baseEnd_7886606] using wordTrace_append hprefix tailTrace_7886606
  have hstable : (prefixWord ++ tailWord_7886606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886606).length < 2 ^ (prefixWord ++ tailWord_7886606).sum := by decide
  have hdescent : baseEnd_7886606 < baseStart_7886606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886610 : List Nat := [3, 2, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7886610 : Nat := 118140960795 + 7886610 * 2 ^ 59
def prefixEnd_7886610 : Nat := 4983230072969 + 3 ^ 40 * 7886610 * 2
def baseEnd_7886610 : Nat := 1349873888185164611935049

theorem tailTrace_7886610 : CollatzResearch.WordTrace tailWord_7886610 prefixEnd_7886610 1349873888185164611935049 := by
  unfold tailWord_7886610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912074489541592649718321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191765531972110913732582189 71912074489541592649718321)
  ·
    refine ⟨53934055867156194487288741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71912074489541592649718321 53934055867156194487288741)
    ·
      refine ⟨10112635475091786466366639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53934055867156194487288741 10112635475091786466366639)
      ·
        refine ⟨15168953212637679699549959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112635475091786466366639 15168953212637679699549959)
        ·
          refine ⟨22753429818956519549324939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15168953212637679699549959 22753429818956519549324939)
          ·
            refine ⟨34130144728434779323987409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22753429818956519549324939 34130144728434779323987409)
            ·
              refine ⟨25597608546326084492990557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34130144728434779323987409 25597608546326084492990557)
              ·
                refine ⟨9599103204872281684871459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25597608546326084492990557 9599103204872281684871459)
                ·
                  refine ⟨14398654807308422527307189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599103204872281684871459 14398654807308422527307189)
                  ·
                    refine ⟨1349873888185164611935049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14398654807308422527307189 1349873888185164611935049)
                    ·
                      rfl

theorem cell23_7886610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7886610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886610 prefixEnd_7886610 := by exact prefixLift 7886610
  have htrace : WordTrace (prefixWord ++ tailWord_7886610) baseStart_7886610 baseEnd_7886610 := by
    simpa [prefixWord, tailWord_7886610, baseEnd_7886610] using wordTrace_append hprefix tailTrace_7886610
  have hstable : (prefixWord ++ tailWord_7886610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886610).length < 2 ^ (prefixWord ++ tailWord_7886610).sum := by decide
  have hdescent : baseEnd_7886610 < baseStart_7886610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886613 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_7886613 : Nat := 118140960795 + 7886613 * 2 ^ 59
def prefixEnd_7886613 : Nat := 4983230072969 + 3 ^ 40 * 7886613 * 2
def baseEnd_7886613 : Nat := 4049623204997457324067633

theorem tailTrace_7886613 : CollatzResearch.WordTrace tailWord_7886613 prefixEnd_7886613 4049623204997457324067633 := by
  unfold tailWord_7886613
  simp only [CollatzResearch.WordTrace]
  refine ⟨287648407377155502111232493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191765604918103668074154995 287648407377155502111232493)
  ·
    refine ⟨107868152766433313291712185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287648407377155502111232493 107868152766433313291712185)
    ·
      refine ⟨80901114574824984968784139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107868152766433313291712185 80901114574824984968784139)
      ·
        refine ⟨121351671862237477453176209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80901114574824984968784139 121351671862237477453176209)
        ·
          refine ⟨91013753896678108089882157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121351671862237477453176209 91013753896678108089882157)
          ·
            refine ⟨34130157711254290533705809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91013753896678108089882157 34130157711254290533705809)
            ·
              refine ⟨25597618283440717900279357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34130157711254290533705809 25597618283440717900279357)
              ·
                refine ⟨9599106856290269212604759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25597618283440717900279357 9599106856290269212604759)
                ·
                  refine ⟨14398660284435403818907139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599106856290269212604759 14398660284435403818907139)
                  ·
                    refine ⟨21597990426653105728360709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14398660284435403818907139 21597990426653105728360709)
                    ·
                      refine ⟨4049623204997457324067633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21597990426653105728360709 4049623204997457324067633)
                      ·
                        rfl

theorem cell23_7886613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_7886613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886613 prefixEnd_7886613 := by exact prefixLift 7886613
  have htrace : WordTrace (prefixWord ++ tailWord_7886613) baseStart_7886613 baseEnd_7886613 := by
    simpa [prefixWord, tailWord_7886613, baseEnd_7886613] using wordTrace_append hprefix tailTrace_7886613
  have hstable : (prefixWord ++ tailWord_7886613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886613).length < 2 ^ (prefixWord ++ tailWord_7886613).sum := by decide
  have hdescent : baseEnd_7886613 < baseStart_7886613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886616 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7886616 : Nat := 118140960795 + 7886616 * 2 ^ 59
def prefixEnd_7886616 : Nat := 4983230072969 + 3 ^ 40 * 7886616 * 2
def baseEnd_7886616 : Nat := 4049624745439420812330119

theorem tailTrace_7886616 : CollatzResearch.WordTrace tailWord_7886616 prefixEnd_7886616 4049624745439420812330119 := by
  unfold tailWord_7886616
  simp only [CollatzResearch.WordTrace]
  refine ⟨143824258398072316811795851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191765677864096422415727801 143824258398072316811795851)
  ·
    refine ⟨215736387597108475217693777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143824258398072316811795851 215736387597108475217693777)
    ·
      refine ⟨161802290697831356413270333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215736387597108475217693777 161802290697831356413270333)
      ·
        refine ⟨60675859011686758654976375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161802290697831356413270333 60675859011686758654976375)
        ·
          refine ⟨91013788517530137982464563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60675859011686758654976375 91013788517530137982464563)
          ·
            refine ⟨136520682776295206973696845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91013788517530137982464563 136520682776295206973696845)
            ·
              refine ⟨51195256041110702615136317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136520682776295206973696845 51195256041110702615136317)
              ·
                refine ⟨19198221015416513480676119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51195256041110702615136317 19198221015416513480676119)
                ·
                  refine ⟨28797331523124770221014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19198221015416513480676119 28797331523124770221014179)
                  ·
                    refine ⟨43195997284687155331521269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28797331523124770221014179 43195997284687155331521269)
                    ·
                      refine ⟨4049624745439420812330119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43195997284687155331521269 4049624745439420812330119)
                      ·
                        rfl

theorem cell23_7886616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7886616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886616 prefixEnd_7886616 := by exact prefixLift 7886616
  have htrace : WordTrace (prefixWord ++ tailWord_7886616) baseStart_7886616 baseEnd_7886616 := by
    simpa [prefixWord, tailWord_7886616, baseEnd_7886616] using wordTrace_append hprefix tailTrace_7886616
  have hstable : (prefixWord ++ tailWord_7886616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886616).length < 2 ^ (prefixWord ++ tailWord_7886616).sum := by decide
  have hdescent : baseEnd_7886616 < baseStart_7886616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886623 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 2, 4]
def baseStart_7886623 : Nat := 118140960795 + 7886623 * 2 ^ 59
def prefixEnd_7886623 : Nat := 4983230072969 + 3 ^ 40 * 7886623 * 2
def baseEnd_7886623 : Nat := 1349876113268000761647529

theorem tailTrace_7886623 : CollatzResearch.WordTrace tailWord_7886623 prefixEnd_7886623 1349876113268000761647529 := by
  unfold tailWord_7886623
  simp only [CollatzResearch.WordTrace]
  refine ⟨287648772107119273819096523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191765848071412849212731015 287648772107119273819096523)
  ·
    refine ⟨431473158160678910728644785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287648772107119273819096523 431473158160678910728644785)
    ·
      refine ⟨323604868620509183046483589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431473158160678910728644785 323604868620509183046483589)
      ·
        refine ⟨60675912866345471821215673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323604868620509183046483589 60675912866345471821215673)
        ·
          refine ⟨45506934649759103865911755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60675912866345471821215673 45506934649759103865911755)
          ·
            refine ⟨68260401974638655798867633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45506934649759103865911755 68260401974638655798867633)
            ·
              refine ⟨51195301480978991849150725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68260401974638655798867633 51195301480978991849150725)
              ·
                refine ⟨9599119027683560971715761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51195301480978991849150725 9599119027683560971715761)
                ·
                  refine ⟨7199339270762670728786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599119027683560971715761 7199339270762670728786821)
                  ·
                    refine ⟨1349876113268000761647529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199339270762670728786821 1349876113268000761647529)
                    ·
                      rfl

theorem cell23_7886623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_7886623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886623 prefixEnd_7886623 := by exact prefixLift 7886623
  have htrace : WordTrace (prefixWord ++ tailWord_7886623) baseStart_7886623 baseEnd_7886623 := by
    simpa [prefixWord, tailWord_7886623, baseEnd_7886623] using wordTrace_append hprefix tailTrace_7886623
  have hstable : (prefixWord ++ tailWord_7886623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886623).length < 2 ^ (prefixWord ++ tailWord_7886623).sum := by decide
  have hdescent : baseEnd_7886623 < baseStart_7886623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886626 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_7886626 : Nat := 118140960795 + 7886626 * 2 ^ 59
def prefixEnd_7886626 : Nat := 4983230072969 + 3 ^ 40 * 7886626 * 2
def baseEnd_7886626 : Nat := 4049629880245965773205073

theorem tailTrace_7886626 : CollatzResearch.WordTrace tailWord_7886626 prefixEnd_7886626 4049629880245965773205073 := by
  unfold tailWord_7886626
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912220381527101332863933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191765921017405603554303821 71912220381527101332863933)
  ·
    refine ⟨26967082643072662999823975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71912220381527101332863933 26967082643072662999823975)
    ·
      refine ⟨40450623964608994499735963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26967082643072662999823975 40450623964608994499735963)
      ·
        refine ⟨60675935946913491749603945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40450623964608994499735963 60675935946913491749603945)
        ·
          refine ⟨45506951960185118812202959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60675935946913491749603945 45506951960185118812202959)
          ·
            refine ⟨68260427940277678218304439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45506951960185118812202959 68260427940277678218304439)
            ·
              refine ⟨102390641910416517327456659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68260427940277678218304439 102390641910416517327456659)
              ·
                refine ⟨153585962865624775991184989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102390641910416517327456659 153585962865624775991184989)
                ·
                  refine ⟨57594736074609290996694371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153585962865624775991184989 57594736074609290996694371)
                  ·
                    refine ⟨86392104111913936495041557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57594736074609290996694371 86392104111913936495041557)
                    ·
                      refine ⟨4049629880245965773205073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86392104111913936495041557 4049629880245965773205073)
                      ·
                        rfl

theorem cell23_7886626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_7886626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886626 prefixEnd_7886626 := by exact prefixLift 7886626
  have htrace : WordTrace (prefixWord ++ tailWord_7886626) baseStart_7886626 baseEnd_7886626 := by
    simpa [prefixWord, tailWord_7886626, baseEnd_7886626] using wordTrace_append hprefix tailTrace_7886626
  have hstable : (prefixWord ++ tailWord_7886626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886626).length < 2 ^ (prefixWord ++ tailWord_7886626).sum := by decide
  have hdescent : baseEnd_7886626 < baseStart_7886626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886636 : List Nat := [2, 2, 1, 1, 1, 6, 2, 8]
def baseStart_7886636 : Nat := 118140960795 + 7886636 * 2 ^ 59
def prefixEnd_7886636 : Nat := 4983230072969 + 3 ^ 40 * 7886636 * 2
def baseEnd_7886636 : Nat := 149986482038981879040001

theorem tailTrace_7886636 : CollatzResearch.WordTrace tailWord_7886636 prefixEnd_7886636 149986482038981879040001 := by
  unfold tailWord_7886636
  simp only [CollatzResearch.WordTrace]
  refine ⟨143824623128036088519659881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191766164170714784692879841 143824623128036088519659881)
  ·
    refine ⟨107868467346027066389744911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143824623128036088519659881 107868467346027066389744911)
    ·
      refine ⟨161802701019040599584617367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107868467346027066389744911 161802701019040599584617367)
      ·
        refine ⟨242704051528560899376926051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161802701019040599584617367 242704051528560899376926051)
        ·
          refine ⟨364056077292841349065389077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242704051528560899376926051 364056077292841349065389077)
          ·
            refine ⟨17065128623101938237440113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364056077292841349065389077 17065128623101938237440113)
            ·
              refine ⟨12798846467326453678080085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17065128623101938237440113 12798846467326453678080085)
              ·
                refine ⟨149986482038981879040001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12798846467326453678080085 149986482038981879040001)
                ·
                  rfl

theorem cell23_7886636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 8].length) (baseStart_7886636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886636 prefixEnd_7886636 := by exact prefixLift 7886636
  have htrace : WordTrace (prefixWord ++ tailWord_7886636) baseStart_7886636 baseEnd_7886636 := by
    simpa [prefixWord, tailWord_7886636, baseEnd_7886636] using wordTrace_append hprefix tailTrace_7886636
  have hstable : (prefixWord ++ tailWord_7886636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886636).length < 2 ^ (prefixWord ++ tailWord_7886636).sum := by decide
  have hdescent : baseEnd_7886636 < baseStart_7886636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886650 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_7886650 : Nat := 118140960795 + 7886650 * 2 ^ 59
def prefixEnd_7886650 : Nat := 4983230072969 + 3 ^ 40 * 7886650 * 2
def baseEnd_7886650 : Nat := 4049642203781673679304963

theorem tailTrace_7886650 : CollatzResearch.WordTrace tailWord_7886650 prefixEnd_7886650 4049642203781673679304963 := by
  unfold tailWord_7886650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912439219505364357582351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191766504585347638286886269 71912439219505364357582351)
  ·
    refine ⟨107868658829258046536373527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71912439219505364357582351 107868658829258046536373527)
    ·
      refine ⟨161802988243887069804560291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107868658829258046536373527 161802988243887069804560291)
      ·
        refine ⟨242704482365830604706840437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161802988243887069804560291 242704482365830604706840437)
        ·
          refine ⟨22753545221796619191266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242704482365830604706840437 22753545221796619191266291)
          ·
            refine ⟨34130317832694928786899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22753545221796619191266291 34130317832694928786899437)
            ·
              refine ⟨12798869187260598295087289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34130317832694928786899437 12798869187260598295087289)
              ·
                refine ⟨9599151890445448721315467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12798869187260598295087289 9599151890445448721315467)
                ·
                  refine ⟨14398727835668173081973201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599151890445448721315467 14398727835668173081973201)
                  ·
                    refine ⟨10799045876751129811479901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14398727835668173081973201 10799045876751129811479901)
                    ·
                      refine ⟨4049642203781673679304963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799045876751129811479901 4049642203781673679304963)
                      ·
                        rfl

theorem cell23_7886650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_7886650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886650 prefixEnd_7886650 := by exact prefixLift 7886650
  have htrace : WordTrace (prefixWord ++ tailWord_7886650) baseStart_7886650 baseEnd_7886650 := by
    simpa [prefixWord, tailWord_7886650, baseEnd_7886650] using wordTrace_append hprefix tailTrace_7886650
  have hstable : (prefixWord ++ tailWord_7886650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886650).length < 2 ^ (prefixWord ++ tailWord_7886650).sum := by decide
  have hdescent : baseEnd_7886650 < baseStart_7886650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886663 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_7886663 : Nat := 118140960795 + 7886663 * 2 ^ 59
def prefixEnd_7886663 : Nat := 4983230072969 + 3 ^ 40 * 7886663 * 2
def baseEnd_7886663 : Nat := 4049648879030182128442403

theorem tailTrace_7886663 : CollatzResearch.WordTrace tailWord_7886663 prefixEnd_7886663 4049648879030182128442403 := by
  unfold tailWord_7886663
  simp only [CollatzResearch.WordTrace]
  refine ⟨287650231026974360650552643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191766820684649573767035095 287650231026974360650552643)
  ·
    refine ⟨431475346540461540975828965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287650231026974360650552643 431475346540461540975828965)
    ·
      refine ⟨80901627476336538932967931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431475346540461540975828965 80901627476336538932967931)
      ·
        refine ⟨121352441214504808399451897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80901627476336538932967931 121352441214504808399451897)
        ·
          refine ⟨91014330910878606299588923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121352441214504808399451897 91014330910878606299588923)
          ·
            refine ⟨136521496366317909449383385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91014330910878606299588923 136521496366317909449383385)
            ·
              refine ⟨102391122274738432087037539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136521496366317909449383385 102391122274738432087037539)
              ·
                refine ⟨153586683412107648130556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102391122274738432087037539 153586683412107648130556309)
                ·
                  refine ⟨7199375784942546006119827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153586683412107648130556309 7199375784942546006119827)
                  ·
                    refine ⟨10799063677413819009179741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199375784942546006119827 10799063677413819009179741)
                    ·
                      refine ⟨4049648879030182128442403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799063677413819009179741 4049648879030182128442403)
                      ·
                        rfl

theorem cell23_7886663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_7886663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886663 prefixEnd_7886663 := by exact prefixLift 7886663
  have htrace : WordTrace (prefixWord ++ tailWord_7886663) baseStart_7886663 baseEnd_7886663 := by
    simpa [prefixWord, tailWord_7886663, baseEnd_7886663] using wordTrace_append hprefix tailTrace_7886663
  have hstable : (prefixWord ++ tailWord_7886663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886663).length < 2 ^ (prefixWord ++ tailWord_7886663).sum := by decide
  have hdescent : baseEnd_7886663 < baseStart_7886663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886720 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2]
def baseStart_7886720 : Nat := 118140960795 + 7886720 * 2 ^ 59
def prefixEnd_7886720 : Nat := 4983230072969 + 3 ^ 40 * 7886720 * 2
def baseEnd_7886720 : Nat := 4049678147427488405429641

theorem tailTrace_7886720 : CollatzResearch.WordTrace tailWord_7886720 prefixEnd_7886720 4049678147427488405429641 := by
  unfold tailWord_7886720
  simp only [CollatzResearch.WordTrace]
  refine ⟨143826154993883929692688807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191768206658511906256918409 143826154993883929692688807)
  ·
    refine ⟨215739232490825894539033211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143826154993883929692688807 215739232490825894539033211)
    ·
      refine ⟨323608848736238841808549817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215739232490825894539033211 323608848736238841808549817)
      ·
        refine ⟨242706636552179131356412363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323608848736238841808549817 242706636552179131356412363)
        ·
          refine ⟨364059954828268697034618545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242706636552179131356412363 364059954828268697034618545)
          ·
            refine ⟨273044966121201522775963909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364059954828268697034618545 273044966121201522775963909)
            ·
              refine ⟨51195931147725285520493233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273044966121201522775963909 51195931147725285520493233)
              ·
                refine ⟨38396948360793964140369925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51195931147725285520493233 38396948360793964140369925)
                ·
                  refine ⟨7199427817648868276319361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38396948360793964140369925 7199427817648868276319361)
                  ·
                    refine ⟨5399570863236651207239521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7199427817648868276319361 5399570863236651207239521)
                    ·
                      refine ⟨4049678147427488405429641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399570863236651207239521 4049678147427488405429641)
                      ·
                        rfl

theorem cell23_7886720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_7886720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886720 prefixEnd_7886720 := by exact prefixLift 7886720
  have htrace : WordTrace (prefixWord ++ tailWord_7886720) baseStart_7886720 baseEnd_7886720 := by
    simpa [prefixWord, tailWord_7886720, baseEnd_7886720] using wordTrace_append hprefix tailTrace_7886720
  have hstable : (prefixWord ++ tailWord_7886720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886720).length < 2 ^ (prefixWord ++ tailWord_7886720).sum := by decide
  have hdescent : baseEnd_7886720 < baseStart_7886720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886737 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_7886737 : Nat := 118140960795 + 7886737 * 2 ^ 59
def prefixEnd_7886737 : Nat := 4983230072969 + 3 ^ 40 * 7886737 * 2
def baseEnd_7886737 : Nat := 4049686876598614838917063

theorem tailTrace_7886737 : CollatzResearch.WordTrace tailWord_7886737 prefixEnd_7886737 4049686876598614838917063 := by
  unfold tailWord_7886737
  simp only [CollatzResearch.WordTrace]
  refine ⟨287652930028706271288746465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191768620019137514192497643 287652930028706271288746465)
  ·
    refine ⟨215739697521529703466559849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287652930028706271288746465 215739697521529703466559849)
    ·
      refine ⟨161804773141147277599919887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215739697521529703466559849 161804773141147277599919887)
      ·
        refine ⟨242707159711720916399879831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161804773141147277599919887 242707159711720916399879831)
        ·
          refine ⟨364060739567581374599819747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242707159711720916399879831 364060739567581374599819747)
          ·
            refine ⟨546091109351372061899729621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364060739567581374599819747 546091109351372061899729621)
            ·
              refine ⟨12799010375422782700774913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546091109351372061899729621 12799010375422782700774913)
              ·
                refine ⟨9599257781567087025581185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12799010375422782700774913 9599257781567087025581185)
                ·
                  refine ⟨7199443336175315269185889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599257781567087025581185 7199443336175315269185889)
                  ·
                    refine ⟨5399582502131486451889417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7199443336175315269185889 5399582502131486451889417)
                    ·
                      refine ⟨4049686876598614838917063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399582502131486451889417 4049686876598614838917063)
                      ·
                        rfl

theorem cell23_7886737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_7886737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886737 prefixEnd_7886737 := by exact prefixLift 7886737
  have htrace : WordTrace (prefixWord ++ tailWord_7886737) baseStart_7886737 baseEnd_7886737 := by
    simpa [prefixWord, tailWord_7886737, baseEnd_7886737] using wordTrace_append hprefix tailTrace_7886737
  have hstable : (prefixWord ++ tailWord_7886737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886737).length < 2 ^ (prefixWord ++ tailWord_7886737).sum := by decide
  have hdescent : baseEnd_7886737 < baseStart_7886737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886743 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 7]
def baseStart_7886743 : Nat := 118140960795 + 7886743 * 2 ^ 59
def prefixEnd_7886743 : Nat := 4983230072969 + 3 ^ 40 * 7886743 * 2
def baseEnd_7886743 : Nat := 449965550831393535049115

theorem tailTrace_7886743 : CollatzResearch.WordTrace tailWord_7886743 prefixEnd_7886743 449965550831393535049115 := by
  unfold tailWord_7886743
  simp only [CollatzResearch.WordTrace]
  refine ⟨287653148866684534313464883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191768765911123022875643255 287653148866684534313464883)
  ·
    refine ⟨431479723300026801470197325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287653148866684534313464883 431479723300026801470197325)
    ·
      refine ⟨161804896237510050551323997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431479723300026801470197325 161804896237510050551323997)
      ·
        refine ⟨60676836089066268956746499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161804896237510050551323997 60676836089066268956746499)
        ·
          refine ⟨91015254133599403435119749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60676836089066268956746499 91015254133599403435119749)
          ·
            refine ⟨17065360150049888144084953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91015254133599403435119749 17065360150049888144084953)
            ·
              refine ⟨12799020112537416108063715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17065360150049888144084953 12799020112537416108063715)
              ·
                refine ⟨19198530168806124162095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12799020112537416108063715 19198530168806124162095573)
                ·
                  refine ⟨449965550831393535049115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19198530168806124162095573 449965550831393535049115)
                  ·
                    rfl

theorem cell23_7886743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 7].length) (baseStart_7886743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886743 prefixEnd_7886743 := by exact prefixLift 7886743
  have htrace : WordTrace (prefixWord ++ tailWord_7886743) baseStart_7886743 baseEnd_7886743 := by
    simpa [prefixWord, tailWord_7886743, baseEnd_7886743] using wordTrace_append hprefix tailTrace_7886743
  have hstable : (prefixWord ++ tailWord_7886743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886743).length < 2 ^ (prefixWord ++ tailWord_7886743).sum := by decide
  have hdescent : baseEnd_7886743 < baseStart_7886743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886754 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7886754 : Nat := 118140960795 + 7886754 * 2 ^ 59
def prefixEnd_7886754 : Nat := 4983230072969 + 3 ^ 40 * 7886754 * 2
def baseEnd_7886754 : Nat := 4049695605769741272404485

theorem tailTrace_7886754 : CollatzResearch.WordTrace tailWord_7886754 prefixEnd_7886754 4049695605769741272404485 := by
  unfold tailWord_7886754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71913387517411170798028829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191769033379763122128076877 71913387517411170798028829)
  ·
    refine ⟨26967520319029189049260811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71913387517411170798028829 26967520319029189049260811)
    ·
      refine ⟨40451280478543783573891217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26967520319029189049260811 40451280478543783573891217)
      ·
        refine ⟨30338460358907837680418413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40451280478543783573891217 30338460358907837680418413)
        ·
          refine ⟨11376922634590439130156905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30338460358907837680418413 11376922634590439130156905)
          ·
            refine ⟨8532691975942829347617679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376922634590439130156905 8532691975942829347617679)
            ·
              refine ⟨12799037963914244021426519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532691975942829347617679 12799037963914244021426519)
              ·
                refine ⟨19198556945871366032139779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12799037963914244021426519 19198556945871366032139779)
                ·
                  refine ⟨28797835418807049048209669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19198556945871366032139779 28797835418807049048209669)
                  ·
                    refine ⟨5399594141026321696539313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28797835418807049048209669 5399594141026321696539313)
                    ·
                      refine ⟨4049695605769741272404485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399594141026321696539313 4049695605769741272404485)
                      ·
                        rfl

theorem cell23_7886754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7886754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886754 prefixEnd_7886754 := by exact prefixLift 7886754
  have htrace : WordTrace (prefixWord ++ tailWord_7886754) baseStart_7886754 baseEnd_7886754 := by
    simpa [prefixWord, tailWord_7886754, baseEnd_7886754] using wordTrace_append hprefix tailTrace_7886754
  have hstable : (prefixWord ++ tailWord_7886754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886754).length < 2 ^ (prefixWord ++ tailWord_7886754).sum := by decide
  have hdescent : baseEnd_7886754 < baseStart_7886754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886773 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7886773 : Nat := 118140960795 + 7886773 * 2 ^ 59
def prefixEnd_7886773 : Nat := 4983230072969 + 3 ^ 40 * 7886773 * 2
def baseEnd_7886773 : Nat := 1349901787300725566022299

theorem tailTrace_7886773 : CollatzResearch.WordTrace tailWord_7886773 prefixEnd_7886773 1349901787300725566022299 := by
  unfold tailWord_7886773
  simp only [CollatzResearch.WordTrace]
  refine ⟨287654243056575849437056973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191769495371050566291371315 287654243056575849437056973)
  ·
    refine ⟨107870341146215943538896365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287654243056575849437056973 107870341146215943538896365)
    ·
      refine ⟨40451377929830978827086137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107870341146215943538896365 40451377929830978827086137)
      ·
        refine ⟨30338533447373234120314603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40451377929830978827086137 30338533447373234120314603)
        ·
          refine ⟨45507800171059851180471905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30338533447373234120314603 45507800171059851180471905)
          ·
            refine ⟨34130850128294888385353929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45507800171059851180471905 34130850128294888385353929)
            ·
              refine ⟨25598137596221166289015447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34130850128294888385353929 25598137596221166289015447)
              ·
                refine ⟨38397206394331749433523171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25598137596221166289015447 38397206394331749433523171)
                ·
                  refine ⟨57595809591497624150284757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38397206394331749433523171 57595809591497624150284757)
                  ·
                    refine ⟨1349901787300725566022299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57595809591497624150284757 1349901787300725566022299)
                    ·
                      rfl

theorem cell23_7886773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7886773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886773 prefixEnd_7886773 := by exact prefixLift 7886773
  have htrace : WordTrace (prefixWord ++ tailWord_7886773) baseStart_7886773 baseEnd_7886773 := by
    simpa [prefixWord, tailWord_7886773, baseEnd_7886773] using wordTrace_append hprefix tailTrace_7886773
  have hstable : (prefixWord ++ tailWord_7886773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886773).length < 2 ^ (prefixWord ++ tailWord_7886773).sum := by decide
  have hdescent : baseEnd_7886773 < baseStart_7886773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886793 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_7886793 : Nat := 118140960795 + 7886793 * 2 ^ 59
def prefixEnd_7886793 : Nat := 4983230072969 + 3 ^ 40 * 7886793 * 2
def baseEnd_7886793 : Nat := 4049715631515266619816805

theorem tailTrace_7886793 : CollatzResearch.WordTrace tailWord_7886793 prefixEnd_7886793 4049715631515266619816805 := by
  unfold tailWord_7886793
  simp only [CollatzResearch.WordTrace]
  refine ⟨287654972516503392852785033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191769981677668928568523355 287654972516503392852785033)
  ·
    refine ⟨215741229387377544639588775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287654972516503392852785033 215741229387377544639588775)
    ·
      refine ⟨323611844081066316959383163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215741229387377544639588775 323611844081066316959383163)
      ·
        refine ⟨485417766121599475439074745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323611844081066316959383163 485417766121599475439074745)
        ·
          refine ⟨364063324591199606579306059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485417766121599475439074745 364063324591199606579306059)
          ·
            refine ⟨546094986886799409868959089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364063324591199606579306059 546094986886799409868959089)
            ·
              refine ⟨409571240165099557401719317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546094986886799409868959089 409571240165099557401719317)
              ·
                refine ⟨19198651882739041753205593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409571240165099557401719317 19198651882739041753205593)
                ·
                  refine ⟨14398988912054281314904195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19198651882739041753205593 14398988912054281314904195)
                  ·
                    refine ⟨21598483368081421972356293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14398988912054281314904195 21598483368081421972356293)
                    ·
                      refine ⟨4049715631515266619816805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21598483368081421972356293 4049715631515266619816805)
                      ·
                        rfl

theorem cell23_7886793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_7886793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886793 prefixEnd_7886793 := by exact prefixLift 7886793
  have htrace : WordTrace (prefixWord ++ tailWord_7886793) baseStart_7886793 baseEnd_7886793 := by
    simpa [prefixWord, tailWord_7886793, baseEnd_7886793] using wordTrace_append hprefix tailTrace_7886793
  have hstable : (prefixWord ++ tailWord_7886793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886793).length < 2 ^ (prefixWord ++ tailWord_7886793).sum := by decide
  have hdescent : baseEnd_7886793 < baseStart_7886793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886877 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_7886877 : Nat := 118140960795 + 7886877 * 2 ^ 59
def prefixEnd_7886877 : Nat := 4983230072969 + 3 ^ 40 * 7886877 * 2
def baseEnd_7886877 : Nat := 4049758763890244291166419

theorem tailTrace_7886877 : CollatzResearch.WordTrace tailWord_7886877 prefixEnd_7886877 4049758763890244291166419 := by
  unfold tailWord_7886877
  simp only [CollatzResearch.WordTrace]
  refine ⟨287658036248199075198842885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191772024165466050132561923 287658036248199075198842885)
  ·
    refine ⟨53935881796537326599783041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287658036248199075198842885 53935881796537326599783041)
    ·
      refine ⟨40451911347402994949837281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53935881796537326599783041 40451911347402994949837281)
      ·
        refine ⟨30338933510552246212377961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40451911347402994949837281 30338933510552246212377961)
        ·
          refine ⟨22754200132914184659283471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30338933510552246212377961 22754200132914184659283471)
          ·
            refine ⟨34131300199371276988925207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22754200132914184659283471 34131300199371276988925207)
            ·
              refine ⟨51196950299056915483387811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34131300199371276988925207 51196950299056915483387811)
              ·
                refine ⟨76795425448585373225081717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51196950299056915483387811 76795425448585373225081717)
                ·
                  refine ⟨7199571135804878739851411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76795425448585373225081717 7199571135804878739851411)
                  ·
                    refine ⟨10799356703707318109777117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199571135804878739851411 10799356703707318109777117)
                    ·
                      refine ⟨4049758763890244291166419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799356703707318109777117 4049758763890244291166419)
                      ·
                        rfl

theorem cell23_7886877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_7886877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886877 prefixEnd_7886877 := by exact prefixLift 7886877
  have htrace : WordTrace (prefixWord ++ tailWord_7886877) baseStart_7886877 baseEnd_7886877 := by
    simpa [prefixWord, tailWord_7886877, baseEnd_7886877] using wordTrace_append hprefix tailTrace_7886877
  have hstable : (prefixWord ++ tailWord_7886877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886877).length < 2 ^ (prefixWord ++ tailWord_7886877).sum := by decide
  have hdescent : baseEnd_7886877 < baseStart_7886877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886897 : List Nat := [1, 2, 2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_7886897 : Nat := 118140960795 + 7886897 * 2 ^ 59
def prefixEnd_7886897 : Nat := 4983230072969 + 3 ^ 40 * 7886897 * 2
def baseEnd_7886897 : Nat := 1349923011167778070972109

theorem tailTrace_7886897 : CollatzResearch.WordTrace tailWord_7886897 prefixEnd_7886897 1349923011167778070972109 := by
  unfold tailWord_7886897
  simp only [CollatzResearch.WordTrace]
  refine ⟨287658765708126618614570945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191772510472084412409713963 287658765708126618614570945)
  ·
    refine ⟨215744074281094963960928209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287658765708126618614570945 215744074281094963960928209)
    ·
      refine ⟨161808055710821222970696157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215744074281094963960928209 161808055710821222970696157)
      ·
        refine ⟨60678020891557958614011059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161808055710821222970696157 60678020891557958614011059)
        ·
          refine ⟨91017031337336937921016589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60678020891557958614011059 91017031337336937921016589)
          ·
            refine ⟨34131386751501351720381221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91017031337336937921016589 34131386751501351720381221)
            ·
              refine ⟨6399635015906503447571479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34131386751501351720381221 6399635015906503447571479)
              ·
                refine ⟨9599452523859755171357219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399635015906503447571479 9599452523859755171357219)
                ·
                  refine ⟨14399178785789632757035829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599452523859755171357219 14399178785789632757035829)
                  ·
                    refine ⟨1349923011167778070972109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14399178785789632757035829 1349923011167778070972109)
                    ·
                      rfl

theorem cell23_7886897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_7886897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886897 prefixEnd_7886897 := by exact prefixLift 7886897
  have htrace : WordTrace (prefixWord ++ tailWord_7886897) baseStart_7886897 baseEnd_7886897 := by
    simpa [prefixWord, tailWord_7886897, baseEnd_7886897] using wordTrace_append hprefix tailTrace_7886897
  have hstable : (prefixWord ++ tailWord_7886897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886897).length < 2 ^ (prefixWord ++ tailWord_7886897).sum := by decide
  have hdescent : baseEnd_7886897 < baseStart_7886897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886920 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_7886920 : Nat := 118140960795 + 7886920 * 2 ^ 59
def prefixEnd_7886920 : Nat := 4983230072969 + 3 ^ 40 * 7886920 * 2
def baseEnd_7886920 : Nat := 4049780843558387622928721

theorem tailTrace_7886920 : CollatzResearch.WordTrace tailWord_7886920 prefixEnd_7886920 4049780843558387622928721 := by
  unfold tailWord_7886920
  simp only [CollatzResearch.WordTrace]
  refine ⟨143829802293521646771329107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191773069724695529028438809 143829802293521646771329107)
  ·
    refine ⟨215744703440282470156993661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143829802293521646771329107 215744703440282470156993661)
    ·
      refine ⟨80904263790105926308872623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215744703440282470156993661 80904263790105926308872623)
      ·
        refine ⟨121356395685158889463308935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80904263790105926308872623 121356395685158889463308935)
        ·
          refine ⟨182034593527738334194963403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121356395685158889463308935 182034593527738334194963403)
          ·
            refine ⟨273051890291607501292445105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182034593527738334194963403 273051890291607501292445105)
            ·
              refine ⟨204788917718705625969333829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273051890291607501292445105 204788917718705625969333829)
              ·
                refine ⟨38397922072257304869250093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204788917718705625969333829 38397922072257304869250093)
                ·
                  refine ⟨14399220777096489325968785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38397922072257304869250093 14399220777096489325968785)
                  ·
                    refine ⟨10799415582822366994476589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14399220777096489325968785 10799415582822366994476589)
                    ·
                      refine ⟨4049780843558387622928721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799415582822366994476589 4049780843558387622928721)
                      ·
                        rfl

theorem cell23_7886920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_7886920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886920 prefixEnd_7886920 := by exact prefixLift 7886920
  have htrace : WordTrace (prefixWord ++ tailWord_7886920) baseStart_7886920 baseEnd_7886920 := by
    simpa [prefixWord, tailWord_7886920, baseEnd_7886920] using wordTrace_append hprefix tailTrace_7886920
  have hstable : (prefixWord ++ tailWord_7886920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886920).length < 2 ^ (prefixWord ++ tailWord_7886920).sum := by decide
  have hdescent : baseEnd_7886920 < baseStart_7886920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886937 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_7886937 : Nat := 118140960795 + 7886937 * 2 ^ 59
def prefixEnd_7886937 : Nat := 4983230072969 + 3 ^ 40 * 7886937 * 2
def baseEnd_7886937 : Nat := 4049789572729514056416143

theorem tailTrace_7886937 : CollatzResearch.WordTrace tailWord_7886937 prefixEnd_7886937 4049789572729514056416143 := by
  unfold tailWord_7886937
  simp only [CollatzResearch.WordTrace]
  refine ⟨287660224627981705446027065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191773483085321136964018043 287660224627981705446027065)
  ·
    refine ⟨215745168470986279084520299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287660224627981705446027065 215745168470986279084520299)
    ·
      refine ⟨323617752706479418626780449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215745168470986279084520299 323617752706479418626780449)
      ·
        refine ⟨242713314529859563970085337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323617752706479418626780449 242713314529859563970085337)
        ·
          refine ⟨182034985897394672977564003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242713314529859563970085337 182034985897394672977564003)
          ·
            refine ⟨273052478846092009466346005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182034985897394672977564003 273052478846092009466346005)
            ·
              refine ⟨12799334945910562943734969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273052478846092009466346005 12799334945910562943734969)
              ·
                refine ⟨9599501209432922207801227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12799334945910562943734969 9599501209432922207801227)
                ·
                  refine ⟨14399251814149383311701841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599501209432922207801227 14399251814149383311701841)
                  ·
                    refine ⟨10799438860612037483776381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14399251814149383311701841 10799438860612037483776381)
                    ·
                      refine ⟨4049789572729514056416143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799438860612037483776381 4049789572729514056416143)
                      ·
                        rfl

theorem cell23_7886937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_7886937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886937 prefixEnd_7886937 := by exact prefixLift 7886937
  have htrace : WordTrace (prefixWord ++ tailWord_7886937) baseStart_7886937 baseEnd_7886937 := by
    simpa [prefixWord, tailWord_7886937, baseEnd_7886937] using wordTrace_append hprefix tailTrace_7886937
  have hstable : (prefixWord ++ tailWord_7886937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886937).length < 2 ^ (prefixWord ++ tailWord_7886937).sum := by decide
  have hdescent : baseEnd_7886937 < baseStart_7886937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886940 : List Nat := [2, 2, 4, 1, 1, 3, 1, 9]
def baseStart_7886940 : Nat := 118140960795 + 7886940 * 2 ^ 59
def prefixEnd_7886940 : Nat := 4983230072969 + 3 ^ 40 * 7886940 * 2
def baseEnd_7886940 : Nat := 149992263450795464617727

theorem tailTrace_7886940 : CollatzResearch.WordTrace tailWord_7886940 prefixEnd_7886940 149992263450795464617727 := by
  unfold tailWord_7886940
  simp only [CollatzResearch.WordTrace]
  refine ⟨143830167023485418479193137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191773556031313891305590849 143830167023485418479193137)
  ·
    refine ⟨107872625267614063859394853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143830167023485418479193137 107872625267614063859394853)
    ·
      refine ⟨20226117237677636973636535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107872625267614063859394853 20226117237677636973636535)
      ·
        refine ⟨30339175856516455460454803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20226117237677636973636535 30339175856516455460454803)
        ·
          refine ⟨45508763784774683190682205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30339175856516455460454803 45508763784774683190682205)
          ·
            refine ⟨17065786419290506196505827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45508763784774683190682205 17065786419290506196505827)
            ·
              refine ⟨25598679628935759294758741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17065786419290506196505827 25598679628935759294758741)
              ·
                refine ⟨149992263450795464617727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25598679628935759294758741 149992263450795464617727)
                ·
                  rfl

theorem cell23_7886940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 9].length) (baseStart_7886940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886940 prefixEnd_7886940 := by exact prefixLift 7886940
  have htrace : WordTrace (prefixWord ++ tailWord_7886940) baseStart_7886940 baseEnd_7886940 := by
    simpa [prefixWord, tailWord_7886940, baseEnd_7886940] using wordTrace_append hprefix tailTrace_7886940
  have hstable : (prefixWord ++ tailWord_7886940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886940).length < 2 ^ (prefixWord ++ tailWord_7886940).sum := by decide
  have hdescent : baseEnd_7886940 < baseStart_7886940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886967 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_7886967 : Nat := 118140960795 + 7886967 * 2 ^ 59
def prefixEnd_7886967 : Nat := 4983230072969 + 3 ^ 40 * 7886967 * 2
def baseEnd_7886967 : Nat := 4049804977149148939041005

theorem tailTrace_7886967 : CollatzResearch.WordTrace tailWord_7886967 prefixEnd_7886967 4049804977149148939041005 := by
  unfold tailWord_7886967
  simp only [CollatzResearch.WordTrace]
  refine ⟨287661318817873020569619155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191774212545248680379746103 287661318817873020569619155)
  ·
    refine ⟨431491978226809530854428733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287661318817873020569619155 431491978226809530854428733)
    ·
      refine ⟨161809491835053574070410775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431491978226809530854428733 161809491835053574070410775)
      ·
        refine ⟨242714237752580361105616163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161809491835053574070410775 242714237752580361105616163)
        ·
          refine ⟨364071356628870541658424245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242714237752580361105616163 364071356628870541658424245)
          ·
            refine ⟨34131689683956613280477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364071356628870541658424245 34131689683956613280477273)
            ·
              refine ⟨25598767262967459960357955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34131689683956613280477273 25598767262967459960357955)
              ·
                refine ⟨38398150894451189940536933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25598767262967459960357955 38398150894451189940536933)
                ·
                  refine ⟨7199653292709598113850675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38398150894451189940536933 7199653292709598113850675)
                  ·
                    refine ⟨10799479939064397170776013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199653292709598113850675 10799479939064397170776013)
                    ·
                      refine ⟨4049804977149148939041005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799479939064397170776013 4049804977149148939041005)
                      ·
                        rfl

theorem cell23_7886967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_7886967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886967 prefixEnd_7886967 := by exact prefixLift 7886967
  have htrace : WordTrace (prefixWord ++ tailWord_7886967) baseStart_7886967 baseEnd_7886967 := by
    simpa [prefixWord, tailWord_7886967, baseEnd_7886967] using wordTrace_append hprefix tailTrace_7886967
  have hstable : (prefixWord ++ tailWord_7886967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886967).length < 2 ^ (prefixWord ++ tailWord_7886967).sum := by decide
  have hdescent : baseEnd_7886967 < baseStart_7886967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886993 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_7886993 : Nat := 118140960795 + 7886993 * 2 ^ 59
def prefixEnd_7886993 : Nat := 4983230072969 + 3 ^ 40 * 7886993 * 2
def baseEnd_7886993 : Nat := 4049818327646165837315885

theorem tailTrace_7886993 : CollatzResearch.WordTrace tailWord_7886993 prefixEnd_7886993 4049818327646165837315885 := by
  unfold tailWord_7886993
  simp only [CollatzResearch.WordTrace]
  refine ⟨287662267115778827010065633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191774844743852551340043755 287662267115778827010065633)
  ·
    refine ⟨215746700336834120257549225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287662267115778827010065633 215746700336834120257549225)
    ·
      refine ⟨161810025252625590193161919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215746700336834120257549225 161810025252625590193161919)
      ·
        refine ⟨242715037878938385289742879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161810025252625590193161919 242715037878938385289742879)
        ·
          refine ⟨364072556818407577934614319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242715037878938385289742879 364072556818407577934614319)
          ·
            refine ⟨546108835227611366901921479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364072556818407577934614319 546108835227611366901921479)
            ·
              refine ⟨819163252841417050352882219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546108835227611366901921479 819163252841417050352882219)
              ·
                refine ⟨1228744879262125575529323329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819163252841417050352882219 1228744879262125575529323329)
                ·
                  refine ⟨921558659446594181646992497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1228744879262125575529323329 921558659446594181646992497)
                  ·
                    refine ⟨691168994584945636235244373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921558659446594181646992497 691168994584945636235244373)
                    ·
                      refine ⟨4049818327646165837315885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 691168994584945636235244373 4049818327646165837315885)
                      ·
                        rfl

theorem cell23_7886993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_7886993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886993 prefixEnd_7886993 := by exact prefixLift 7886993
  have htrace : WordTrace (prefixWord ++ tailWord_7886993) baseStart_7886993 baseEnd_7886993 := by
    simpa [prefixWord, tailWord_7886993, baseEnd_7886993] using wordTrace_append hprefix tailTrace_7886993
  have hstable : (prefixWord ++ tailWord_7886993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886993).length < 2 ^ (prefixWord ++ tailWord_7886993).sum := by decide
  have hdescent : baseEnd_7886993 < baseStart_7886993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7886994 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7886994 : Nat := 118140960795 + 7886994 * 2 ^ 59
def prefixEnd_7886994 : Nat := 4983230072969 + 3 ^ 40 * 7886994 * 2
def baseEnd_7886994 : Nat := 4049818841126820333403381

theorem tailTrace_7886994 : CollatzResearch.WordTrace tailWord_7886994 prefixEnd_7886994 4049818841126820333403381 := by
  unfold tailWord_7886994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71915575897193801045213009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191774869059183469453901357 71915575897193801045213009)
  ·
    refine ⟨53936681922895350783909757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71915575897193801045213009 53936681922895350783909757)
    ·
      refine ⟨20226255721085756543966159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53936681922895350783909757 20226255721085756543966159)
      ·
        refine ⟨30339383581628634815949239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20226255721085756543966159 30339383581628634815949239)
        ·
          refine ⟨45509075372442952223923859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30339383581628634815949239 45509075372442952223923859)
          ·
            refine ⟨68263613058664428335885789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45509075372442952223923859 68263613058664428335885789)
            ·
              refine ⟨25598854896999160625957171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68263613058664428335885789 25598854896999160625957171)
              ·
                refine ⟨38398282345498740938935757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25598854896999160625957171 38398282345498740938935757)
                ·
                  refine ⟨14399355879562027852100909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38398282345498740938935757 14399355879562027852100909)
                  ·
                    refine ⟨5399758454835760444537841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14399355879562027852100909 5399758454835760444537841)
                    ·
                      refine ⟨4049818841126820333403381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399758454835760444537841 4049818841126820333403381)
                      ·
                        rfl

theorem cell23_7886994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7886994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7886994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7886994 prefixEnd_7886994 := by exact prefixLift 7886994
  have htrace : WordTrace (prefixWord ++ tailWord_7886994) baseStart_7886994 baseEnd_7886994 := by
    simpa [prefixWord, tailWord_7886994, baseEnd_7886994] using wordTrace_append hprefix tailTrace_7886994
  have hstable : (prefixWord ++ tailWord_7886994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7886994).length < 2 ^ (prefixWord ++ tailWord_7886994).sum := by decide
  have hdescent : baseEnd_7886994 < baseStart_7886994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7886994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887018 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7887018 : Nat := 118140960795 + 7887018 * 2 ^ 59
def prefixEnd_7887018 : Nat := 4983230072969 + 3 ^ 40 * 7887018 * 2
def baseEnd_7887018 : Nat := 4049831164662528239503271

theorem tailTrace_7887018 : CollatzResearch.WordTrace tailWord_7887018 prefixEnd_7887018 4049831164662528239503271 := by
  unfold tailWord_7887018
  simp only [CollatzResearch.WordTrace]
  refine ⟨71915794735172064069931427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191775452627125504186483805 71915794735172064069931427)
  ·
    refine ⟨107873692102758096104897141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71915794735172064069931427 107873692102758096104897141)
    ·
      refine ⟨10113158634633571509834107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107873692102758096104897141 10113158634633571509834107)
      ·
        refine ⟨15169737951950357264751161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10113158634633571509834107 15169737951950357264751161)
        ·
          refine ⟨11377303463962767948563371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15169737951950357264751161 11377303463962767948563371)
          ·
            refine ⟨17065955195944151922845057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377303463962767948563371 17065955195944151922845057)
            ·
              refine ⟨12799466396958113942133793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17065955195944151922845057 12799466396958113942133793)
              ·
                refine ⟨9599599797718585456600345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12799466396958113942133793 9599599797718585456600345)
                ·
                  refine ⟨7199699848288939092450259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599599797718585456600345 7199699848288939092450259)
                  ·
                    refine ⟨10799549772433408638675389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199699848288939092450259 10799549772433408638675389)
                    ·
                      refine ⟨4049831164662528239503271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799549772433408638675389 4049831164662528239503271)
                      ·
                        rfl

theorem cell23_7887018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7887018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887018 prefixEnd_7887018 := by exact prefixLift 7887018
  have htrace : WordTrace (prefixWord ++ tailWord_7887018) baseStart_7887018 baseEnd_7887018 := by
    simpa [prefixWord, tailWord_7887018, baseEnd_7887018] using wordTrace_append hprefix tailTrace_7887018
  have hstable : (prefixWord ++ tailWord_7887018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887018).length < 2 ^ (prefixWord ++ tailWord_7887018).sum := by decide
  have hdescent : baseEnd_7887018 < baseStart_7887018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887064 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 5]
def baseStart_7887064 : Nat := 118140960795 + 7887064 * 2 ^ 59
def prefixEnd_7887064 : Nat := 4983230072969 + 3 ^ 40 * 7887064 * 2
def baseEnd_7887064 : Nat := 449983864974737228836451

theorem tailTrace_7887064 : CollatzResearch.WordTrace tailWord_7887064 prefixEnd_7887064 449983864974737228836451 := by
  unfold tailWord_7887064
  simp only [CollatzResearch.WordTrace]
  refine ⟨143832428349260803067950123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191776571132347737423933497 143832428349260803067950123)
  ·
    refine ⟨215748642523891204601925185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143832428349260803067950123 215748642523891204601925185)
    ·
      refine ⟨161811481892918403451443889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215748642523891204601925185 161811481892918403451443889)
      ·
        refine ⟨121358611419688802588582917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161811481892918403451443889 121358611419688802588582917)
        ·
          refine ⟨22754739641191650485359297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121358611419688802588582917 22754739641191650485359297)
          ·
            refine ⟨17066054730893737864019473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22754739641191650485359297 17066054730893737864019473)
            ·
              refine ⟨12799541048170303398014605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17066054730893737864019473 12799541048170303398014605)
              ·
                refine ⟨4799827893063863774255477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12799541048170303398014605 4799827893063863774255477)
                ·
                  refine ⟨449983864974737228836451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799827893063863774255477 449983864974737228836451)
                  ·
                    rfl

theorem cell23_7887064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 5].length) (baseStart_7887064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887064 prefixEnd_7887064 := by exact prefixLift 7887064
  have htrace : WordTrace (prefixWord ++ tailWord_7887064) baseStart_7887064 baseEnd_7887064 := by
    simpa [prefixWord, tailWord_7887064, baseEnd_7887064] using wordTrace_append hprefix tailTrace_7887064
  have hstable : (prefixWord ++ tailWord_7887064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887064).length < 2 ^ (prefixWord ++ tailWord_7887064).sum := by decide
  have hdescent : baseEnd_7887064 < baseStart_7887064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887075 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7887075 : Nat := 118140960795 + 7887075 * 2 ^ 59
def prefixEnd_7887075 : Nat := 4983230072969 + 3 ^ 40 * 7887075 * 2
def baseEnd_7887075 : Nat := 4049860433059834516490509

theorem tailTrace_7887075 : CollatzResearch.WordTrace tailWord_7887075 prefixEnd_7887075 4049860433059834516490509 := by
  unfold tailWord_7887075
  simp only [CollatzResearch.WordTrace]
  refine ⟨287665257901481755014550679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191776838600987836676367119 287665257901481755014550679)
  ·
    refine ⟨431497886852222632521826019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287665257901481755014550679 431497886852222632521826019)
    ·
      refine ⟨647246830278333948782739029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431497886852222632521826019 647246830278333948782739029)
      ·
        refine ⟨7584923792324225962297723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 647246830278333948782739029 7584923792324225962297723)
        ·
          refine ⟨11377385688486338943446585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584923792324225962297723 11377385688486338943446585)
          ·
            refine ⟨8533039266364754207584939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11377385688486338943446585 8533039266364754207584939)
            ·
              refine ⟨12799558899547131311377409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533039266364754207584939 12799558899547131311377409)
              ·
                refine ⟨9599669174660348483533057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12799558899547131311377409 9599669174660348483533057)
                ·
                  refine ⟨7199751880995261362649793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599669174660348483533057 7199751880995261362649793)
                  ·
                    refine ⟨5399813910746446021987345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7199751880995261362649793 5399813910746446021987345)
                    ·
                      refine ⟨4049860433059834516490509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399813910746446021987345 4049860433059834516490509)
                      ·
                        rfl

theorem cell23_7887075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7887075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887075 prefixEnd_7887075 := by exact prefixLift 7887075
  have htrace : WordTrace (prefixWord ++ tailWord_7887075) baseStart_7887075 baseEnd_7887075 := by
    simpa [prefixWord, tailWord_7887075, baseEnd_7887075] using wordTrace_append hprefix tailTrace_7887075
  have hstable : (prefixWord ++ tailWord_7887075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887075).length < 2 ^ (prefixWord ++ tailWord_7887075).sum := by decide
  have hdescent : baseEnd_7887075 < baseStart_7887075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887097 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 6, 2]
def baseStart_7887097 : Nat := 118140960795 + 7887097 * 2 ^ 59
def prefixEnd_7887097 : Nat := 4983230072969 + 3 ^ 40 * 7887097 * 2
def baseEnd_7887097 : Nat := 4049871729634233430415407

theorem tailTrace_7887097 : CollatzResearch.WordTrace tailWord_7887097 prefixEnd_7887097 4049871729634233430415407 := by
  unfold tailWord_7887097
  simp only [CollatzResearch.WordTrace]
  refine ⟨287666060307402052771851545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191777373538268035181234363 287666060307402052771851545)
  ·
    refine ⟨215749545230551539578888659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287666060307402052771851545 215749545230551539578888659)
    ·
      refine ⟨323624317845827309368332989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215749545230551539578888659 323624317845827309368332989)
      ·
        refine ⟨121359119192185241013124871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323624317845827309368332989 121359119192185241013124871)
        ·
          refine ⟨182038678788277861519687307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121359119192185241013124871 182038678788277861519687307)
          ·
            refine ⟨273058018182416792279530961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182038678788277861519687307 273058018182416792279530961)
            ·
              refine ⟨204793513636812594209648221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273058018182416792279530961 204793513636812594209648221)
              ·
                refine ⟨76797567613804722828618083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204793513636812594209648221 76797567613804722828618083)
                ·
                  refine ⟨115196351420707084242927125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76797567613804722828618083 115196351420707084242927125)
                  ·
                    refine ⟨5399828972845644573887209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115196351420707084242927125 5399828972845644573887209)
                    ·
                      refine ⟨4049871729634233430415407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399828972845644573887209 4049871729634233430415407)
                      ·
                        rfl

theorem cell23_7887097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_7887097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887097 prefixEnd_7887097 := by exact prefixLift 7887097
  have htrace : WordTrace (prefixWord ++ tailWord_7887097) baseStart_7887097 baseEnd_7887097 := by
    simpa [prefixWord, tailWord_7887097, baseEnd_7887097] using wordTrace_append hprefix tailTrace_7887097
  have hstable : (prefixWord ++ tailWord_7887097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887097).length < 2 ^ (prefixWord ++ tailWord_7887097).sum := by decide
  have hdescent : baseEnd_7887097 < baseStart_7887097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887107 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 3, 4]
def baseStart_7887107 : Nat := 118140960795 + 7887107 * 2 ^ 59
def prefixEnd_7887107 : Nat := 4983230072969 + 3 ^ 40 * 7887107 * 2
def baseEnd_7887107 : Nat := 1349958954813592797096787

theorem tailTrace_7887107 : CollatzResearch.WordTrace tailWord_7887107 prefixEnd_7887107 1349958954813592797096787 := by
  unfold tailWord_7887107
  simp only [CollatzResearch.WordTrace]
  refine ⟨287666425037365824479715575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191777616691577216319810383 287666425037365824479715575)
  ·
    refine ⟨431499637556048736719573363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287666425037365824479715575 431499637556048736719573363)
    ·
      refine ⟨647249456334073105079360045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431499637556048736719573363 647249456334073105079360045)
      ·
        refine ⟨242718546125277414404760017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647249456334073105079360045 242718546125277414404760017)
        ·
          refine ⟨182038909593958060803570013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242718546125277414404760017 182038909593958060803570013)
          ·
            refine ⟨68264591097734272801338755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182038909593958060803570013 68264591097734272801338755)
            ·
              refine ⟨102396886646601409202008133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68264591097734272801338755 102396886646601409202008133)
              ·
                refine ⟨19199416246237764225376525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102396886646601409202008133 19199416246237764225376525)
                ·
                  refine ⟨7199781092339161584516197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19199416246237764225376525 7199781092339161584516197)
                  ·
                    refine ⟨1349958954813592797096787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199781092339161584516197 1349958954813592797096787)
                    ·
                      rfl

theorem cell23_7887107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 4].length) (baseStart_7887107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887107 prefixEnd_7887107 := by exact prefixLift 7887107
  have htrace : WordTrace (prefixWord ++ tailWord_7887107) baseStart_7887107 baseEnd_7887107 := by
    simpa [prefixWord, tailWord_7887107, baseEnd_7887107] using wordTrace_append hprefix tailTrace_7887107
  have hstable : (prefixWord ++ tailWord_7887107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887107).length < 2 ^ (prefixWord ++ tailWord_7887107).sum := by decide
  have hdescent : baseEnd_7887107 < baseStart_7887107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887141 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_7887141 : Nat := 118140960795 + 7887141 * 2 ^ 59
def prefixEnd_7887141 : Nat := 4983230072969 + 3 ^ 40 * 7887141 * 2
def baseEnd_7887141 : Nat := 1349964774261010419421735

theorem tailTrace_7887141 : CollatzResearch.WordTrace tailWord_7887141 prefixEnd_7887141 1349964774261010419421735 := by
  unfold tailWord_7887141
  simp only [CollatzResearch.WordTrace]
  refine ⟨287667665119242648286453277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191778443412828432190968851 287667665119242648286453277)
  ·
    refine ⟨107875374419715993107419979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287667665119242648286453277 107875374419715993107419979)
    ·
      refine ⟨161813061629573989661129969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107875374419715993107419979 161813061629573989661129969)
      ·
        refine ⟨121359796222180492245847477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161813061629573989661129969 121359796222180492245847477)
        ·
          refine ⟨11377480895829421148048201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121359796222180492245847477 11377480895829421148048201)
          ·
            refine ⟨8533110671872065861036151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11377480895829421148048201 8533110671872065861036151)
            ·
              refine ⟨12799666007808098791554227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533110671872065861036151 12799666007808098791554227)
              ·
                refine ⟨19199499011712148187331341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12799666007808098791554227 19199499011712148187331341)
                ·
                  refine ⟨7199812129392055570249253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19199499011712148187331341 7199812129392055570249253)
                  ·
                    refine ⟨1349964774261010419421735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199812129392055570249253 1349964774261010419421735)
                    ·
                      rfl

theorem cell23_7887141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_7887141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887141 prefixEnd_7887141 := by exact prefixLift 7887141
  have htrace : WordTrace (prefixWord ++ tailWord_7887141) baseStart_7887141 baseEnd_7887141 := by
    simpa [prefixWord, tailWord_7887141, baseEnd_7887141] using wordTrace_append hprefix tailTrace_7887141
  have hstable : (prefixWord ++ tailWord_7887141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887141).length < 2 ^ (prefixWord ++ tailWord_7887141).sum := by decide
  have hdescent : baseEnd_7887141 < baseStart_7887141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887154 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_7887154 : Nat := 118140960795 + 7887154 * 2 ^ 59
def prefixEnd_7887154 : Nat := 4983230072969 + 3 ^ 40 * 7887154 * 2
def baseEnd_7887154 : Nat := 449988999781282189711405

theorem tailTrace_7887154 : CollatzResearch.WordTrace tailWord_7887154 prefixEnd_7887154 449988999781282189711405 := by
  unfold tailWord_7887154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71917034817048887876669129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191778759512130367671117677 71917034817048887876669129)
  ·
    refine ⟨53937776112786665907501847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71917034817048887876669129 53937776112786665907501847)
    ·
      refine ⟨80906664169179998861252771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53937776112786665907501847 80906664169179998861252771)
      ·
        refine ⟨121359996253769998291879157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80906664169179998861252771 121359996253769998291879157)
        ·
          refine ⟨11377499648790937339863671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121359996253769998291879157 11377499648790937339863671)
          ·
            refine ⟨17066249473186406009795507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377499648790937339863671 17066249473186406009795507)
            ·
              refine ⟨25599374209779609014693261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17066249473186406009795507 25599374209779609014693261)
              ·
                refine ⟨9599765328667353380509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25599374209779609014693261 9599765328667353380509973)
                ·
                  refine ⟨449988999781282189711405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9599765328667353380509973 449988999781282189711405)
                  ·
                    rfl

theorem cell23_7887154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_7887154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887154 prefixEnd_7887154 := by exact prefixLift 7887154
  have htrace : WordTrace (prefixWord ++ tailWord_7887154) baseStart_7887154 baseEnd_7887154 := by
    simpa [prefixWord, tailWord_7887154, baseEnd_7887154] using wordTrace_append hprefix tailTrace_7887154
  have hstable : (prefixWord ++ tailWord_7887154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887154).length < 2 ^ (prefixWord ++ tailWord_7887154).sum := by decide
  have hdescent : baseEnd_7887154 < baseStart_7887154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887164 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_7887164 : Nat := 118140960795 + 7887164 * 2 ^ 59
def prefixEnd_7887164 : Nat := 4983230072969 + 3 ^ 40 * 7887164 * 2
def baseEnd_7887164 : Nat := 4049906132838084668277599

theorem tailTrace_7887164 : CollatzResearch.WordTrace tailWord_7887164 prefixEnd_7887164 4049906132838084668277599 := by
  unfold tailWord_7887164
  simp only [CollatzResearch.WordTrace]
  refine ⟨143834251999079661607270273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191779002665439548809693697 143834251999079661607270273)
  ·
    refine ⟨107875688999309746205452705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143834251999079661607270273 107875688999309746205452705)
    ·
      refine ⟨80906766749482309654089529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107875688999309746205452705 80906766749482309654089529)
      ·
        refine ⟨60680075062111732240567147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80906766749482309654089529 60680075062111732240567147)
        ·
          refine ⟨91020112593167598360850721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60680075062111732240567147 91020112593167598360850721)
          ·
            refine ⟨68265084444875698770638041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91020112593167598360850721 68265084444875698770638041)
            ·
              refine ⟨51198813333656774077978531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68265084444875698770638041 51198813333656774077978531)
              ·
                refine ⟨76798220000485161116967797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51198813333656774077978531 76798220000485161116967797)
                ·
                  refine ⟨7199833125045483854715731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76798220000485161116967797 7199833125045483854715731)
                  ·
                    refine ⟨10799749687568225782073597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7199833125045483854715731 10799749687568225782073597)
                    ·
                      refine ⟨4049906132838084668277599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799749687568225782073597 4049906132838084668277599)
                      ·
                        rfl

theorem cell23_7887164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_7887164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887164 prefixEnd_7887164 := by exact prefixLift 7887164
  have htrace : WordTrace (prefixWord ++ tailWord_7887164) baseStart_7887164 baseEnd_7887164 := by
    simpa [prefixWord, tailWord_7887164, baseEnd_7887164] using wordTrace_append hprefix tailTrace_7887164
  have hstable : (prefixWord ++ tailWord_7887164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887164).length < 2 ^ (prefixWord ++ tailWord_7887164).sum := by decide
  have hdescent : baseEnd_7887164 < baseStart_7887164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887167 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 3, 5]
def baseStart_7887167 : Nat := 118140960795 + 7887167 * 2 ^ 59
def prefixEnd_7887167 : Nat := 4983230072969 + 3 ^ 40 * 7887167 * 2
def baseEnd_7887167 : Nat := 1349969224426682718846695

theorem tailTrace_7887167 : CollatzResearch.WordTrace tailWord_7887167 prefixEnd_7887167 1349969224426682718846695 := by
  unfold tailWord_7887167
  simp only [CollatzResearch.WordTrace]
  refine ⟨287668613417148454726899755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191779075611432303151266503 287668613417148454726899755)
  ·
    refine ⟨431502920125722682090349633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287668613417148454726899755 431502920125722682090349633)
    ·
      refine ⟨323627190094292011567762225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431502920125722682090349633 323627190094292011567762225)
      ·
        refine ⟨242720392570719008675821669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323627190094292011567762225 242720392570719008675821669)
        ·
          refine ⟨45510073607009814126716563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242720392570719008675821669 45510073607009814126716563)
          ·
            refine ⟨68265110410514721190074845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45510073607009814126716563 68265110410514721190074845)
            ·
              refine ⟨25599416403943020446278067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68265110410514721190074845 25599416403943020446278067)
              ·
                refine ⟨38399124605914530669417101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25599416403943020446278067 38399124605914530669417101)
                ·
                  refine ⟨14399671727217949001031413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38399124605914530669417101 14399671727217949001031413)
                  ·
                    refine ⟨1349969224426682718846695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14399671727217949001031413 1349969224426682718846695)
                    ·
                      rfl

theorem cell23_7887167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_7887167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887167 prefixEnd_7887167 := by exact prefixLift 7887167
  have htrace : WordTrace (prefixWord ++ tailWord_7887167) baseStart_7887167 baseEnd_7887167 := by
    simpa [prefixWord, tailWord_7887167, baseEnd_7887167] using wordTrace_append hprefix tailTrace_7887167
  have hstable : (prefixWord ++ tailWord_7887167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887167).length < 2 ^ (prefixWord ++ tailWord_7887167).sum := by decide
  have hdescent : baseEnd_7887167 < baseStart_7887167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887241 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_7887241 : Nat := 118140960795 + 7887241 * 2 ^ 59
def prefixEnd_7887241 : Nat := 4983230072969 + 3 ^ 40 * 7887241 * 2
def baseEnd_7887241 : Nat := 4049945670848480867014745

theorem tailTrace_7887241 : CollatzResearch.WordTrace tailWord_7887241 prefixEnd_7887241 4049945670848480867014745 := by
  unfold tailWord_7887241
  simp only [CollatzResearch.WordTrace]
  refine ⟨287671312418880365365093577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191780874945920243576729051 287671312418880365365093577)
  ·
    refine ⟨215753484314160274023820183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287671312418880365365093577 215753484314160274023820183)
    ·
      refine ⟨323630226471240411035730275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215753484314160274023820183 323630226471240411035730275)
      ·
        refine ⟨485445339706860616553595413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323630226471240411035730275 485445339706860616553595413)
        ·
          refine ⟨22755250298759091400949785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485445339706860616553595413 22755250298759091400949785)
          ·
            refine ⟨17066437724069318550712339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22755250298759091400949785 17066437724069318550712339)
            ·
              refine ⟨25599656586103977826068509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17066437724069318550712339 25599656586103977826068509)
              ·
                refine ⟨9599871219788991684775691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25599656586103977826068509 9599871219788991684775691)
                ·
                  refine ⟨14399806829683487527163537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9599871219788991684775691 14399806829683487527163537)
                  ·
                    refine ⟨10799855122262615645372653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14399806829683487527163537 10799855122262615645372653)
                    ·
                      refine ⟨4049945670848480867014745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799855122262615645372653 4049945670848480867014745)
                      ·
                        rfl

theorem cell23_7887241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_7887241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887241 prefixEnd_7887241 := by exact prefixLift 7887241
  have htrace : WordTrace (prefixWord ++ tailWord_7887241) baseStart_7887241 baseEnd_7887241 := by
    simpa [prefixWord, tailWord_7887241, baseEnd_7887241] using wordTrace_append hprefix tailTrace_7887241
  have hstable : (prefixWord ++ tailWord_7887241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887241).length < 2 ^ (prefixWord ++ tailWord_7887241).sum := by decide
  have hdescent : baseEnd_7887241 < baseStart_7887241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887265 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_7887265 : Nat := 118140960795 + 7887265 * 2 ^ 59
def prefixEnd_7887265 : Nat := 4983230072969 + 3 ^ 40 * 7887265 * 2
def baseEnd_7887265 : Nat := 1349985998128062924371545

theorem tailTrace_7887265 : CollatzResearch.WordTrace tailWord_7887265 prefixEnd_7887265 1349985998128062924371545 := by
  unfold tailWord_7887265
  simp only [CollatzResearch.WordTrace]
  refine ⟨287672187770793417463967249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191781458513862278309311499 287672187770793417463967249)
  ·
    refine ⟨215754140828095063097975437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287672187770793417463967249 215754140828095063097975437)
    ·
      refine ⟨80907802810535648661740789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215754140828095063097975437 80907802810535648661740789)
      ·
        refine ⟨7585106513487717062038199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80907802810535648661740789 7585106513487717062038199)
        ·
          refine ⟨11377659770231575593057299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585106513487717062038199 11377659770231575593057299)
          ·
            refine ⟨17066489655347363389585949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11377659770231575593057299 17066489655347363389585949)
            ·
              refine ⟨6399933620755261271094731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17066489655347363389585949 6399933620755261271094731)
              ·
                refine ⟨9599900431132891906642097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6399933620755261271094731 9599900431132891906642097)
                ·
                  refine ⟨7199925323349668929981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599900431132891906642097 7199925323349668929981573)
                  ·
                    refine ⟨1349985998128062924371545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7199925323349668929981573 1349985998128062924371545)
                    ·
                      rfl

theorem cell23_7887265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_7887265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887265 prefixEnd_7887265 := by exact prefixLift 7887265
  have htrace : WordTrace (prefixWord ++ tailWord_7887265) baseStart_7887265 baseEnd_7887265 := by
    simpa [prefixWord, tailWord_7887265, baseEnd_7887265] using wordTrace_append hprefix tailTrace_7887265
  have hstable : (prefixWord ++ tailWord_7887265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887265).length < 2 ^ (prefixWord ++ tailWord_7887265).sum := by decide
  have hdescent : baseEnd_7887265 < baseStart_7887265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887271 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7887271 : Nat := 118140960795 + 7887271 * 2 ^ 59
def prefixEnd_7887271 : Nat := 4983230072969 + 3 ^ 40 * 7887271 * 2
def baseEnd_7887271 : Nat := 4049961075268115749639607

theorem tailTrace_7887271 : CollatzResearch.WordTrace tailWord_7887271 prefixEnd_7887271 4049961075268115749639607 := by
  unfold tailWord_7887271
  simp only [CollatzResearch.WordTrace]
  refine ⟨287672406608771680488685667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191781604405847786992457111 287672406608771680488685667)
  ·
    refine ⟨431508609913157520733028501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287672406608771680488685667 431508609913157520733028501)
    ·
      refine ⟨20226966089679258784360711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 431508609913157520733028501 20226966089679258784360711)
      ·
        refine ⟨30340449134518888176541067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20226966089679258784360711 30340449134518888176541067)
        ·
          refine ⟨45510673701778332264811601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30340449134518888176541067 45510673701778332264811601)
          ·
            refine ⟨34133005276333749198608701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45510673701778332264811601 34133005276333749198608701)
            ·
              refine ⟨12799876978625155949478263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34133005276333749198608701 12799876978625155949478263)
              ·
                refine ⟨19199815467937733924217395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12799876978625155949478263 19199815467937733924217395)
                ·
                  refine ⟨28799723201906600886326093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19199815467937733924217395 28799723201906600886326093)
                  ·
                    refine ⟨10799896200714975332372285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28799723201906600886326093 10799896200714975332372285)
                    ·
                      refine ⟨4049961075268115749639607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10799896200714975332372285 4049961075268115749639607)
                      ·
                        rfl

theorem cell23_7887271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7887271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887271 prefixEnd_7887271 := by exact prefixLift 7887271
  have htrace : WordTrace (prefixWord ++ tailWord_7887271) baseStart_7887271 baseEnd_7887271 := by
    simpa [prefixWord, tailWord_7887271, baseEnd_7887271] using wordTrace_append hprefix tailTrace_7887271
  have hstable : (prefixWord ++ tailWord_7887271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887271).length < 2 ^ (prefixWord ++ tailWord_7887271).sum := by decide
  have hdescent : baseEnd_7887271 < baseStart_7887271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887328 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2]
def baseStart_7887328 : Nat := 118140960795 + 7887328 * 2 ^ 59
def prefixEnd_7887328 : Nat := 4983230072969 + 3 ^ 40 * 7887328 * 2
def baseEnd_7887328 : Nat := 4049990343665422026626845

theorem tailTrace_7887328 : CollatzResearch.WordTrace tailWord_7887328 prefixEnd_7887328 4049990343665422026626845 := by
  unfold tailWord_7887328
  simp only [CollatzResearch.WordTrace]
  refine ⟨143837242784782589611755319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191782990379710119482340425 143837242784782589611755319)
  ·
    refine ⟨215755864177173884417632979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143837242784782589611755319 215755864177173884417632979)
    ·
      refine ⟨323633796265760826626449469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215755864177173884417632979 323633796265760826626449469)
      ·
        refine ⟨121362673599660309984918551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323633796265760826626449469 121362673599660309984918551)
        ·
          refine ⟨182044010399490464977377827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121362673599660309984918551 182044010399490464977377827)
          ·
            refine ⟨273066015599235697466066741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182044010399490464977377827 273066015599235697466066741)
            ·
              refine ⟨25599938962428346637443757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273066015599235697466066741 25599938962428346637443757)
              ·
                refine ⟨9599977110910629989041409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25599938962428346637443757 9599977110910629989041409)
                ·
                  refine ⟨7199982833182972491781057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9599977110910629989041409 7199982833182972491781057)
                  ·
                    refine ⟨5399987124887229368835793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7199982833182972491781057 5399987124887229368835793)
                    ·
                      refine ⟨4049990343665422026626845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5399987124887229368835793 4049990343665422026626845)
                      ·
                        rfl

theorem cell23_7887328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_7887328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887328 prefixEnd_7887328 := by exact prefixLift 7887328
  have htrace : WordTrace (prefixWord ++ tailWord_7887328) baseStart_7887328 baseEnd_7887328 := by
    simpa [prefixWord, tailWord_7887328, baseEnd_7887328] using wordTrace_append hprefix tailTrace_7887328
  have hstable : (prefixWord ++ tailWord_7887328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887328).length < 2 ^ (prefixWord ++ tailWord_7887328).sum := by decide
  have hdescent : baseEnd_7887328 < baseStart_7887328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887371 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 5, 2]
def baseStart_7887371 : Nat := 118140960795 + 7887371 * 2 ^ 59
def prefixEnd_7887371 : Nat := 4983230072969 + 3 ^ 40 * 7887371 * 2
def baseEnd_7887371 : Nat := 4050012423333565358389147

theorem tailTrace_7887371 : CollatzResearch.WordTrace tailWord_7887371 prefixEnd_7887371 4050012423333565358389147 := by
  unfold tailWord_7887371
  simp only [CollatzResearch.WordTrace]
  refine ⟨287676053908409397567325967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191784035938939598378217311 287676053908409397567325967)
  ·
    refine ⟨431514080862614096350988951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287676053908409397567325967 431514080862614096350988951)
    ·
      refine ⟨647271121293921144526483427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431514080862614096350988951 647271121293921144526483427)
      ·
        refine ⟨970906681940881716789725141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647271121293921144526483427 970906681940881716789725141)
        ·
          refine ⟨22755625357989415237259183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 970906681940881716789725141 22755625357989415237259183)
          ·
            refine ⟨34133438036984122855888775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22755625357989415237259183 34133438036984122855888775)
            ·
              refine ⟨51200157055476184283833163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34133438036984122855888775 51200157055476184283833163)
              ·
                refine ⟨76800235583214276425749745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51200157055476184283833163 76800235583214276425749745)
                ·
                  refine ⟨57600176687410707319312309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76800235583214276425749745 57600176687410707319312309)
                  ·
                    refine ⟨5400016564444753811185529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57600176687410707319312309 5400016564444753811185529)
                    ·
                      refine ⟨4050012423333565358389147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400016564444753811185529 4050012423333565358389147)
                      ·
                        rfl

theorem cell23_7887371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5, 2].length) (baseStart_7887371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887371 prefixEnd_7887371 := by exact prefixLift 7887371
  have htrace : WordTrace (prefixWord ++ tailWord_7887371) baseStart_7887371 baseEnd_7887371 := by
    simpa [prefixWord, tailWord_7887371, baseEnd_7887371] using wordTrace_append hprefix tailTrace_7887371
  have hstable : (prefixWord ++ tailWord_7887371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887371).length < 2 ^ (prefixWord ++ tailWord_7887371).sum := by decide
  have hdescent : baseEnd_7887371 < baseStart_7887371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887471 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 1, 5]
def baseStart_7887471 : Nat := 118140960795 + 7887471 * 2 ^ 59
def prefixEnd_7887471 : Nat := 4983230072969 + 3 ^ 40 * 7887471 * 2
def baseEnd_7887471 : Nat := 1350021257133004989046229

theorem tailTrace_7887471 : CollatzResearch.WordTrace tailWord_7887471 prefixEnd_7887471 1350021257133004989046229 := by
  unfold tailWord_7887471
  simp only [CollatzResearch.WordTrace]
  refine ⟨287679701208047114645966267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191786467472031409763977511 287679701208047114645966267)
  ·
    refine ⟨431519551812070671968949401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287679701208047114645966267 431519551812070671968949401)
    ·
      refine ⟨323639663859053003976712051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431519551812070671968949401 323639663859053003976712051)
      ·
        refine ⟨485459495788579505965068077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323639663859053003976712051 485459495788579505965068077)
        ·
          refine ⟨182047310920717314736900529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485459495788579505965068077 182047310920717314736900529)
          ·
            refine ⟨136535483190537986052675397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182047310920717314736900529 136535483190537986052675397)
            ·
              refine ⟨25600403098225872384876637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136535483190537986052675397 25600403098225872384876637)
              ·
                refine ⟨9600151161834702144328739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25600403098225872384876637 9600151161834702144328739)
                ·
                  refine ⟨14400226742752053216493109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9600151161834702144328739 14400226742752053216493109)
                  ·
                    refine ⟨1350021257133004989046229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14400226742752053216493109 1350021257133004989046229)
                    ·
                      rfl

theorem cell23_7887471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_7887471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887471 prefixEnd_7887471 := by exact prefixLift 7887471
  have htrace : WordTrace (prefixWord ++ tailWord_7887471) baseStart_7887471 baseEnd_7887471 := by
    simpa [prefixWord, tailWord_7887471, baseEnd_7887471] using wordTrace_append hprefix tailTrace_7887471
  have hstable : (prefixWord ++ tailWord_7887471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887471).length < 2 ^ (prefixWord ++ tailWord_7887471).sum := by decide
  have hdescent : baseEnd_7887471 < baseStart_7887471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887518 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7887518 : Nat := 118140960795 + 7887518 * 2 ^ 59
def prefixEnd_7887518 : Nat := 4983230072969 + 3 ^ 40 * 7887518 * 2
def baseEnd_7887518 : Nat := 1350029301663258761083657

theorem tailTrace_7887518 : CollatzResearch.WordTrace tailWord_7887518 prefixEnd_7887518 1350029301663258761083657 := by
  unfold tailWord_7887518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960176929859605209115901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191787610292584561115284805 35960176929859605209115901)
  ·
    refine ⟨13485066348697351953418463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35960176929859605209115901 13485066348697351953418463)
    ·
      refine ⟨20227599523046027930127695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13485066348697351953418463 20227599523046027930127695)
      ·
        refine ⟨30341399284569041895191543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20227599523046027930127695 30341399284569041895191543)
        ·
          refine ⟨45512098926853562842787315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30341399284569041895191543 45512098926853562842787315)
          ·
            refine ⟨68268148390280344264180973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45512098926853562842787315 68268148390280344264180973)
            ·
              refine ⟨25600555646355129099067865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68268148390280344264180973 25600555646355129099067865)
              ·
                refine ⟨19200416734766346824300899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25600555646355129099067865 19200416734766346824300899)
                ·
                  refine ⟨28800625102149520236451349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19200416734766346824300899 28800625102149520236451349)
                  ·
                    refine ⟨1350029301663258761083657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28800625102149520236451349 1350029301663258761083657)
                    ·
                      rfl

theorem cell23_7887518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7887518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887518 prefixEnd_7887518 := by exact prefixLift 7887518
  have htrace : WordTrace (prefixWord ++ tailWord_7887518) baseStart_7887518 baseEnd_7887518 := by
    simpa [prefixWord, tailWord_7887518, baseEnd_7887518] using wordTrace_append hprefix tailTrace_7887518
  have hstable : (prefixWord ++ tailWord_7887518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887518).length < 2 ^ (prefixWord ++ tailWord_7887518).sum := by decide
  have hdescent : baseEnd_7887518 < baseStart_7887518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887728 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 6]
def baseStart_7887728 : Nat := 118140960795 + 7887728 * 2 ^ 59
def prefixEnd_7887728 : Nat := 4983230072969 + 3 ^ 40 * 7887728 * 2
def baseEnd_7887728 : Nat := 450021748436357829069445

theorem tailTrace_7887728 : CollatzResearch.WordTrace tailWord_7887728 prefixEnd_7887728 450021748436357829069445 := by
  unfold tailWord_7887728
  simp only [CollatzResearch.WordTrace]
  refine ⟨143844537384058023769035919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191792716512077365025381225 143844537384058023769035919)
  ·
    refine ⟨215766806076087035653553879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143844537384058023769035919 215766806076087035653553879)
    ·
      refine ⟨323650209114130553480330819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215766806076087035653553879 323650209114130553480330819)
      ·
        refine ⟨485475313671195830220496229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323650209114130553480330819 485475313671195830220496229)
        ·
          refine ⟨91026621313349218166343043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485475313671195830220496229 91026621313349218166343043)
          ·
            refine ⟨136539931970023827249514565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91026621313349218166343043 136539931970023827249514565)
            ·
              refine ⟨25601237244379467609283981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136539931970023827249514565 25601237244379467609283981)
              ·
                refine ⟨9600463966642300353481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25601237244379467609283981 9600463966642300353481493)
                ·
                  refine ⟨450021748436357829069445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9600463966642300353481493 450021748436357829069445)
                  ·
                    rfl

theorem cell23_7887728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_7887728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887728 prefixEnd_7887728 := by exact prefixLift 7887728
  have htrace : WordTrace (prefixWord ++ tailWord_7887728) baseStart_7887728 baseEnd_7887728 := by
    simpa [prefixWord, tailWord_7887728, baseEnd_7887728] using wordTrace_append hprefix tailTrace_7887728
  have hstable : (prefixWord ++ tailWord_7887728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887728).length < 2 ^ (prefixWord ++ tailWord_7887728).sum := by decide
  have hdescent : baseEnd_7887728 < baseStart_7887728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887766 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7887766 : Nat := 118140960795 + 7887766 * 2 ^ 59
def prefixEnd_7887766 : Nat := 4983230072969 + 3 ^ 40 * 7887766 * 2
def baseEnd_7887766 : Nat := 1350071749397363770983277

theorem tailTrace_7887766 : CollatzResearch.WordTrace tailWord_7887766 prefixEnd_7887766 1350071749397363770983277 := by
  unfold tailWord_7887766
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980653796373648751747197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191793640494652253351970101 17980653796373648751747197)
  ·
    refine ⟨6742745173640118281905199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17980653796373648751747197 6742745173640118281905199)
    ·
      refine ⟨10114117760460177422857799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742745173640118281905199 10114117760460177422857799)
      ·
        refine ⟨15171176640690266134286699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114117760460177422857799 15171176640690266134286699)
        ·
          refine ⟨22756764961035399201430049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171176640690266134286699 22756764961035399201430049)
          ·
            refine ⟨17067573720776549401072537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22756764961035399201430049 17067573720776549401072537)
            ·
              refine ⟨12800680290582412050804403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17067573720776549401072537 12800680290582412050804403)
              ·
                refine ⟨19201020435873618076206605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12800680290582412050804403 19201020435873618076206605)
                ·
                  refine ⟨7200382663452606778577477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19201020435873618076206605 7200382663452606778577477)
                  ·
                    refine ⟨1350071749397363770983277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200382663452606778577477 1350071749397363770983277)
                    ·
                      rfl

theorem cell23_7887766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7887766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887766 prefixEnd_7887766 := by exact prefixLift 7887766
  have htrace : WordTrace (prefixWord ++ tailWord_7887766) baseStart_7887766 baseEnd_7887766 := by
    simpa [prefixWord, tailWord_7887766, baseEnd_7887766] using wordTrace_append hprefix tailTrace_7887766
  have hstable : (prefixWord ++ tailWord_7887766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887766).length < 2 ^ (prefixWord ++ tailWord_7887766).sum := by decide
  have hdescent : baseEnd_7887766 < baseStart_7887766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887842 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7887842 : Nat := 118140960795 + 7887842 * 2 ^ 59
def prefixEnd_7887842 : Nat := 4983230072969 + 3 ^ 40 * 7887842 * 2
def baseEnd_7887842 : Nat := 4050254272721833015599481

theorem tailTrace_7887842 : CollatzResearch.WordTrace tailWord_7887842 prefixEnd_7887842 4050254272721833015599481 := by
  unfold tailWord_7887842
  simp only [CollatzResearch.WordTrace]
  refine ⟨71923308172425761251930445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191795488459802030005147853 71923308172425761251930445)
  ·
    refine ⟨26971240564659660469473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71923308172425761251930445 26971240564659660469473917)
    ·
      refine ⟨10114215211747372676052719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26971240564659660469473917 10114215211747372676052719)
      ·
        refine ⟨15171322817621059014079079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10114215211747372676052719 15171322817621059014079079)
        ·
          refine ⟨22756984226431588521118619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171322817621059014079079 22756984226431588521118619)
          ·
            refine ⟨34135476339647382781677929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22756984226431588521118619 34135476339647382781677929)
            ·
              refine ⟨25601607254735537086258447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34135476339647382781677929 25601607254735537086258447)
              ·
                refine ⟨38402410882103305629387671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25601607254735537086258447 38402410882103305629387671)
                ·
                  refine ⟨57603616323154958444081507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38402410882103305629387671 57603616323154958444081507)
                  ·
                    refine ⟨86405424484732437666122261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57603616323154958444081507 86405424484732437666122261)
                    ·
                      refine ⟨4050254272721833015599481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86405424484732437666122261 4050254272721833015599481)
                      ·
                        rfl

theorem cell23_7887842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7887842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887842 prefixEnd_7887842 := by exact prefixLift 7887842
  have htrace : WordTrace (prefixWord ++ tailWord_7887842) baseStart_7887842 baseEnd_7887842 := by
    simpa [prefixWord, tailWord_7887842, baseEnd_7887842] using wordTrace_append hprefix tailTrace_7887842
  have hstable : (prefixWord ++ tailWord_7887842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887842).length < 2 ^ (prefixWord ++ tailWord_7887842).sum := by decide
  have hdescent : baseEnd_7887842 < baseStart_7887842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887860 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7887860 : Nat := 118140960795 + 7887860 * 2 ^ 59
def prefixEnd_7887860 : Nat := 4983230072969 + 3 ^ 40 * 7887860 * 2
def baseEnd_7887860 : Nat := 1350087838457871315058133

theorem tailTrace_7887860 : CollatzResearch.WordTrace tailWord_7887860 prefixEnd_7887860 1350087838457871315058133 := by
  unfold tailWord_7887860
  simp only [CollatzResearch.WordTrace]
  refine ⟨143846944601818917040938517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191795926135758556054584689 143846944601818917040938517)
  ·
    refine ⟨6742825528210261736293993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143846944601818917040938517 6742825528210261736293993)
    ·
      refine ⟨5057119146157696302220495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6742825528210261736293993 5057119146157696302220495)
      ·
        refine ⟨7585678719236544453330743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057119146157696302220495 7585678719236544453330743)
        ·
          refine ⟨11378518078854816679996115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585678719236544453330743 11378518078854816679996115)
          ·
            refine ⟨17067777118282225019994173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11378518078854816679996115 17067777118282225019994173)
            ·
              refine ⟨6400416419355834382497815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17067777118282225019994173 6400416419355834382497815)
              ·
                refine ⟨9600624629033751573746723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400416419355834382497815 9600624629033751573746723)
                ·
                  refine ⟨14400936943550627360620085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9600624629033751573746723 14400936943550627360620085)
                  ·
                    refine ⟨1350087838457871315058133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14400936943550627360620085 1350087838457871315058133)
                    ·
                      rfl

theorem cell23_7887860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7887860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887860 prefixEnd_7887860 := by exact prefixLift 7887860
  have htrace : WordTrace (prefixWord ++ tailWord_7887860) baseStart_7887860 baseEnd_7887860 := by
    simpa [prefixWord, tailWord_7887860, baseEnd_7887860] using wordTrace_append hprefix tailTrace_7887860
  have hstable : (prefixWord ++ tailWord_7887860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887860).length < 2 ^ (prefixWord ++ tailWord_7887860).sum := by decide
  have hdescent : baseEnd_7887860 < baseStart_7887860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887862 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7887862 : Nat := 118140960795 + 7887862 * 2 ^ 59
def prefixEnd_7887862 : Nat := 4983230072969 + 3 ^ 40 * 7887862 * 2
def baseEnd_7887862 : Nat := 4050264542334922937349389

theorem tailTrace_7887862 : CollatzResearch.WordTrace tailWord_7887862 prefixEnd_7887862 4050264542334922937349389 := by
  unfold tailWord_7887862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980872634351911776465615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191795974766420392282299893 17980872634351911776465615)
  ·
    refine ⟨26971308951527867664698423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17980872634351911776465615 26971308951527867664698423)
    ·
      refine ⟨40456963427291801497047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26971308951527867664698423 40456963427291801497047635)
      ·
        refine ⟨60685445140937702245571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40456963427291801497047635 60685445140937702245571453)
        ·
          refine ⟨22757041927851638342089295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60685445140937702245571453 22757041927851638342089295)
          ·
            refine ⟨34135562891777457513133943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22757041927851638342089295 34135562891777457513133943)
            ·
              refine ⟨51203344337666186269700915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34135562891777457513133943 51203344337666186269700915)
              ·
                refine ⟨76805016506499279404551373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51203344337666186269700915 76805016506499279404551373)
                ·
                  refine ⟨28801881189937229776706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76805016506499279404551373 28801881189937229776706765)
                  ·
                    refine ⟨10800705446226461166265037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28801881189937229776706765 10800705446226461166265037)
                    ·
                      refine ⟨4050264542334922937349389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10800705446226461166265037 4050264542334922937349389)
                      ·
                        rfl

theorem cell23_7887862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7887862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887862 prefixEnd_7887862 := by exact prefixLift 7887862
  have htrace : WordTrace (prefixWord ++ tailWord_7887862) baseStart_7887862 baseEnd_7887862 := by
    simpa [prefixWord, tailWord_7887862, baseEnd_7887862] using wordTrace_append hprefix tailTrace_7887862
  have hstable : (prefixWord ++ tailWord_7887862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887862).length < 2 ^ (prefixWord ++ tailWord_7887862).sum := by decide
  have hdescent : baseEnd_7887862 < baseStart_7887862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887879 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7887879 : Nat := 118140960795 + 7887879 * 2 ^ 59
def prefixEnd_7887879 : Nat := 4983230072969 + 3 ^ 40 * 7887879 * 2
def baseEnd_7887879 : Nat := 4050273271506049370836811

theorem tailTrace_7887879 : CollatzResearch.WordTrace tailWord_7887879 prefixEnd_7887879 4050273271506049370836811 := by
  unfold tailWord_7887879
  simp only [CollatzResearch.WordTrace]
  refine ⟨287694582190569000326818691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191796388127046000217879127 287694582190569000326818691)
  ·
    refine ⟨431541873285853500490228037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287694582190569000326818691 431541873285853500490228037)
    ·
      refine ⟨80914101241097531341917757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 431541873285853500490228037 80914101241097531341917757)
      ·
        refine ⟨30342787965411574253219159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80914101241097531341917757 30342787965411574253219159)
        ·
          refine ⟨45514181948117361379828739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30342787965411574253219159 45514181948117361379828739)
          ·
            refine ⟨68271272922176042069743109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45514181948117361379828739 68271272922176042069743109)
            ·
              refine ⟨12800863672908007888076833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68271272922176042069743109 12800863672908007888076833)
              ·
                refine ⟨9600647754681005916057625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12800863672908007888076833 9600647754681005916057625)
                ·
                  refine ⟨7200485816010754437043219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9600647754681005916057625 7200485816010754437043219)
                  ·
                    refine ⟨10800728724016131655564829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7200485816010754437043219 10800728724016131655564829)
                    ·
                      refine ⟨4050273271506049370836811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10800728724016131655564829 4050273271506049370836811)
                      ·
                        rfl

theorem cell23_7887879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7887879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887879 prefixEnd_7887879 := by exact prefixLift 7887879
  have htrace : WordTrace (prefixWord ++ tailWord_7887879) baseStart_7887879 baseEnd_7887879 := by
    simpa [prefixWord, tailWord_7887879, baseEnd_7887879] using wordTrace_append hprefix tailTrace_7887879
  have hstable : (prefixWord ++ tailWord_7887879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887879).length < 2 ^ (prefixWord ++ tailWord_7887879).sum := by decide
  have hdescent : baseEnd_7887879 < baseStart_7887879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887895 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 8]
def baseStart_7887895 : Nat := 118140960795 + 7887895 * 2 ^ 59
def prefixEnd_7887895 : Nat := 4983230072969 + 3 ^ 40 * 7887895 * 2
def baseEnd_7887895 : Nat := 1350093829065507102745579

theorem tailTrace_7887895 : CollatzResearch.WordTrace tailWord_7887895 prefixEnd_7887895 1350093829065507102745579 := by
  unfold tailWord_7887895
  simp only [CollatzResearch.WordTrace]
  refine ⟨287695165758511035059401139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191796777172340690039600759 287695165758511035059401139)
  ·
    refine ⟨431542748637766552589101709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287695165758511035059401139 431542748637766552589101709)
    ·
      refine ⟨161828530739162457220913141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431542748637766552589101709 161828530739162457220913141)
      ·
        refine ⟨15171424756796480364460607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161828530739162457220913141 15171424756796480364460607)
        ·
          refine ⟨22757137135194720546690911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171424756796480364460607 22757137135194720546690911)
          ·
            refine ⟨34135705702792080820036367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22757137135194720546690911 34135705702792080820036367)
            ·
              refine ⟨51203558554188121230054551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34135705702792080820036367 51203558554188121230054551)
              ·
                refine ⟨76805337831282181845081827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51203558554188121230054551 76805337831282181845081827)
                ·
                  refine ⟨115208006746923272767622741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76805337831282181845081827 115208006746923272767622741)
                  ·
                    refine ⟨1350093829065507102745579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115208006746923272767622741 1350093829065507102745579)
                    ·
                      rfl

theorem cell23_7887895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_7887895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887895 prefixEnd_7887895 := by exact prefixLift 7887895
  have htrace : WordTrace (prefixWord ++ tailWord_7887895) baseStart_7887895 baseEnd_7887895 := by
    simpa [prefixWord, tailWord_7887895, baseEnd_7887895] using wordTrace_append hprefix tailTrace_7887895
  have hstable : (prefixWord ++ tailWord_7887895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887895).length < 2 ^ (prefixWord ++ tailWord_7887895).sum := by decide
  have hdescent : baseEnd_7887895 < baseStart_7887895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7887992 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_7887992 : Nat := 118140960795 + 7887992 * 2 ^ 59
def prefixEnd_7887992 : Nat := 4983230072969 + 3 ^ 40 * 7887992 * 2
def baseEnd_7887992 : Nat := 4050331294820007428723791

theorem tailTrace_7887992 : CollatzResearch.WordTrace tailWord_7887992 prefixEnd_7887992 4050331294820007428723791 := by
  unfold tailWord_7887992
  simp only [CollatzResearch.WordTrace]
  refine ⟨143849351819579810312841115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191799135759439747083788153 143849351819579810312841115)
  ·
    refine ⟨215774027729369715469261673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143849351819579810312841115 215774027729369715469261673)
    ·
      refine ⟨161830520797027286601946255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215774027729369715469261673 161830520797027286601946255)
      ·
        refine ⟨242745781195540929902919383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161830520797027286601946255 242745781195540929902919383)
        ·
          refine ⟨364118671793311394854379075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242745781195540929902919383 364118671793311394854379075)
          ·
            refine ⟨546178007689967092281568613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364118671793311394854379075 546178007689967092281568613)
            ·
              refine ⟨102408376441868829802794115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 546178007689967092281568613 102408376441868829802794115)
              ·
                refine ⟨153612564662803244704191173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102408376441868829802794115 153612564662803244704191173)
                ·
                  refine ⟨28802355874275608382035845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153612564662803244704191173 28802355874275608382035845)
                  ·
                    refine ⟨5400441726426676571631721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28802355874275608382035845 5400441726426676571631721)
                    ·
                      refine ⟨4050331294820007428723791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400441726426676571631721 4050331294820007428723791)
                      ·
                        rfl

theorem cell23_7887992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_7887992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7887992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7887992 prefixEnd_7887992 := by exact prefixLift 7887992
  have htrace : WordTrace (prefixWord ++ tailWord_7887992) baseStart_7887992 baseEnd_7887992 := by
    simpa [prefixWord, tailWord_7887992, baseEnd_7887992] using wordTrace_append hprefix tailTrace_7887992
  have hstable : (prefixWord ++ tailWord_7887992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7887992).length < 2 ^ (prefixWord ++ tailWord_7887992).sum := by decide
  have hdescent : baseEnd_7887992 < baseStart_7887992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7887992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888029 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_7888029 : Nat := 118140960795 + 7888029 * 2 ^ 59
def prefixEnd_7888029 : Nat := 4983230072969 + 3 ^ 40 * 7888029 * 2
def baseEnd_7888029 : Nat := 4050350293604223783961121

theorem tailTrace_7888029 : CollatzResearch.WordTrace tailWord_7888029 prefixEnd_7888029 4050350293604223783961121 := by
  unfold tailWord_7888029
  simp only [CollatzResearch.WordTrace]
  refine ⟨287700053140025575944779141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191800035426683717296519427 287700053140025575944779141)
  ·
    refine ⟨53943759963754795489646089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287700053140025575944779141 53943759963754795489646089)
    ·
      refine ⟨40457819972816096617234567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53943759963754795489646089 40457819972816096617234567)
      ·
        refine ⟨60686729959224144925851851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40457819972816096617234567 60686729959224144925851851)
        ·
          refine ⟨91030094938836217388777777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60686729959224144925851851 91030094938836217388777777)
          ·
            refine ⟨68272571204127163041583333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91030094938836217388777777 68272571204127163041583333)
            ·
              refine ⟨12801107100773843070296875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68272571204127163041583333 12801107100773843070296875)
              ·
                refine ⟨19201660651160764605445313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801107100773843070296875 19201660651160764605445313)
                ·
                  refine ⟨14401245488370573454083985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19201660651160764605445313 14401245488370573454083985)
                  ·
                    refine ⟨10800934116277930090562989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14401245488370573454083985 10800934116277930090562989)
                    ·
                      refine ⟨4050350293604223783961121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10800934116277930090562989 4050350293604223783961121)
                      ·
                        rfl

theorem cell23_7888029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_7888029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888029 prefixEnd_7888029 := by exact prefixLift 7888029
  have htrace : WordTrace (prefixWord ++ tailWord_7888029) baseStart_7888029 baseEnd_7888029 := by
    simpa [prefixWord, tailWord_7888029, baseEnd_7888029] using wordTrace_append hprefix tailTrace_7888029
  have hstable : (prefixWord ++ tailWord_7888029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888029).length < 2 ^ (prefixWord ++ tailWord_7888029).sum := by decide
  have hdescent : baseEnd_7888029 < baseStart_7888029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888049 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 6]
def baseStart_7888049 : Nat := 118140960795 + 7888049 * 2 ^ 59
def prefixEnd_7888049 : Nat := 4983230072969 + 3 ^ 40 * 7888049 * 2
def baseEnd_7888049 : Nat := 450040062579701522856781

theorem tailTrace_7888049 : CollatzResearch.WordTrace tailWord_7888049 prefixEnd_7888049 450040062579701522856781 := by
  unfold tailWord_7888049
  simp only [CollatzResearch.WordTrace]
  refine ⟨287700782599953119360507201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191800521733302079573671467 287700782599953119360507201)
  ·
    refine ⟨215775586949964839520380401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287700782599953119360507201 215775586949964839520380401)
    ·
      refine ⟨161831690212473629640285301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215775586949964839520380401 161831690212473629640285301)
      ·
        refine ⟨15171720957419402778776747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161831690212473629640285301 15171720957419402778776747)
        ·
          refine ⟨22757581436129104168165121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171720957419402778776747 22757581436129104168165121)
          ·
            refine ⟨17068186077096828126123841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22757581436129104168165121 17068186077096828126123841)
            ·
              refine ⟨12801139557822621094592881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17068186077096828126123841 12801139557822621094592881)
              ·
                refine ⟨9600854668366965820944661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801139557822621094592881 9600854668366965820944661)
                ·
                  refine ⟨450040062579701522856781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9600854668366965820944661 450040062579701522856781)
                  ·
                    rfl

theorem cell23_7888049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_7888049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888049 prefixEnd_7888049 := by exact prefixLift 7888049
  have htrace : WordTrace (prefixWord ++ tailWord_7888049) baseStart_7888049 baseEnd_7888049 := by
    simpa [prefixWord, tailWord_7888049, baseEnd_7888049] using wordTrace_append hprefix tailTrace_7888049
  have hstable : (prefixWord ++ tailWord_7888049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888049).length < 2 ^ (prefixWord ++ tailWord_7888049).sum := by decide
  have hdescent : baseEnd_7888049 < baseStart_7888049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888070 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7888070 : Nat := 118140960795 + 7888070 * 2 ^ 59
def prefixEnd_7888070 : Nat := 4983230072969 + 3 ^ 40 * 7888070 * 2
def baseEnd_7888070 : Nat := 1350123782103686041182811

theorem tailTrace_7888070 : CollatzResearch.WordTrace tailWord_7888070 prefixEnd_7888070 1350123782103686041182811 := by
  unfold tailWord_7888070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990673391652407498344427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 191801032355251359964681109 8990673391652407498344427)
  ·
    refine ⟨13486010087478611247516641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8990673391652407498344427 13486010087478611247516641)
    ·
      refine ⟨10114507565608958435637481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13486010087478611247516641 10114507565608958435637481)
      ·
        refine ⟨7585880674206718826728111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10114507565608958435637481 7585880674206718826728111)
        ·
          refine ⟨11378821011310078240092167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585880674206718826728111 11378821011310078240092167)
          ·
            refine ⟨17068231516965117360138251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11378821011310078240092167 17068231516965117360138251)
            ·
              refine ⟨25602347275447676040207377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068231516965117360138251 25602347275447676040207377)
              ·
                refine ⟨19201760456585757030155533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25602347275447676040207377 19201760456585757030155533)
                ·
                  refine ⟨7200660171219658886308325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19201760456585757030155533 7200660171219658886308325)
                  ·
                    refine ⟨1350123782103686041182811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200660171219658886308325 1350123782103686041182811)
                    ·
                      rfl

theorem cell23_7888070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7888070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888070 prefixEnd_7888070 := by exact prefixLift 7888070
  have htrace : WordTrace (prefixWord ++ tailWord_7888070) baseStart_7888070 baseEnd_7888070 := by
    simpa [prefixWord, tailWord_7888070, baseEnd_7888070] using wordTrace_append hprefix tailTrace_7888070
  have hstable : (prefixWord ++ tailWord_7888070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888070).length < 2 ^ (prefixWord ++ tailWord_7888070).sum := by decide
  have hdescent : baseEnd_7888070 < baseStart_7888070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888096 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_7888096 : Nat := 118140960795 + 7888096 * 2 ^ 59
def prefixEnd_7888096 : Nat := 4983230072969 + 3 ^ 40 * 7888096 * 2
def baseEnd_7888096 : Nat := 1350128232269358340607771

theorem tailTrace_7888096 : CollatzResearch.WordTrace tailWord_7888096 prefixEnd_7888096 1350128232269358340607771 := by
  unfold tailWord_7888096
  simp only [CollatzResearch.WordTrace]
  refine ⟨143851248415391423193734071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191801664553855230924978761 143851248415391423193734071)
  ·
    refine ⟨215776872623087134790601107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143851248415391423193734071 215776872623087134790601107)
    ·
      refine ⟨323665308934630702185901661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215776872623087134790601107 323665308934630702185901661)
      ·
        refine ⟨121374490850486513319713123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323665308934630702185901661 121374490850486513319713123)
        ·
          refine ⟨182061736275729769979569685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121374490850486513319713123 182061736275729769979569685)
          ·
            refine ⟨8534143887924832967792329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182061736275729769979569685 8534143887924832967792329)
            ·
              refine ⟨6400607915943624725844247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534143887924832967792329 6400607915943624725844247)
              ·
                refine ⟨9600911873915437088766371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400607915943624725844247 9600911873915437088766371)
                ·
                  refine ⟨14401367810873155633149557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9600911873915437088766371 14401367810873155633149557)
                  ·
                    refine ⟨1350128232269358340607771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14401367810873155633149557 1350128232269358340607771)
                    ·
                      rfl

theorem cell23_7888096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_7888096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888096 prefixEnd_7888096 := by exact prefixLift 7888096
  have htrace : WordTrace (prefixWord ++ tailWord_7888096) baseStart_7888096 baseEnd_7888096 := by
    simpa [prefixWord, tailWord_7888096, baseEnd_7888096] using wordTrace_append hprefix tailTrace_7888096
  have hstable : (prefixWord ++ tailWord_7888096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888096).length < 2 ^ (prefixWord ++ tailWord_7888096).sum := by decide
  have hdescent : baseEnd_7888096 < baseStart_7888096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888126 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7888126 : Nat := 118140960795 + 7888126 * 2 ^ 59
def prefixEnd_7888126 : Nat := 4983230072969 + 3 ^ 40 * 7888126 * 2
def baseEnd_7888126 : Nat := 1350133367075903301482725

theorem tailTrace_7888126 : CollatzResearch.WordTrace tailWord_7888126 prefixEnd_7888126 1350133367075903301482725 := by
  unfold tailWord_7888126
  simp only [CollatzResearch.WordTrace]
  refine ⟨35962948877584270188882529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191802394013782774340706821 35962948877584270188882529)
  ·
    refine ⟨26972211658188202641661897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35962948877584270188882529 26972211658188202641661897)
    ·
      refine ⟨20229158743641151981246423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26972211658188202641661897 20229158743641151981246423)
      ·
        refine ⟨30343738115461727971869635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20229158743641151981246423 30343738115461727971869635)
        ·
          refine ⟨45515607173192591957804453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30343738115461727971869635 45515607173192591957804453)
          ·
            refine ⟨8534176344973610992088335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45515607173192591957804453 8534176344973610992088335)
            ·
              refine ⟨12801264517460416488132503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534176344973610992088335 12801264517460416488132503)
              ·
                refine ⟨19201896776190624732198755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801264517460416488132503 19201896776190624732198755)
                ·
                  refine ⟨28802845164285937098298133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19201896776190624732198755 28802845164285937098298133)
                  ·
                    refine ⟨1350133367075903301482725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28802845164285937098298133 1350133367075903301482725)
                    ·
                      rfl

theorem cell23_7888126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7888126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888126 prefixEnd_7888126 := by exact prefixLift 7888126
  have htrace : WordTrace (prefixWord ++ tailWord_7888126) baseStart_7888126 baseEnd_7888126 := by
    simpa [prefixWord, tailWord_7888126, baseEnd_7888126] using wordTrace_append hprefix tailTrace_7888126
  have hstable : (prefixWord ++ tailWord_7888126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888126).length < 2 ^ (prefixWord ++ tailWord_7888126).sum := by decide
  have hdescent : baseEnd_7888126 < baseStart_7888126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888129 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_7888129 : Nat := 118140960795 + 7888129 * 2 ^ 59
def prefixEnd_7888129 : Nat := 4983230072969 + 3 ^ 40 * 7888129 * 2
def baseEnd_7888129 : Nat := 4050401641669673392710661

theorem tailTrace_7888129 : CollatzResearch.WordTrace tailWord_7888129 prefixEnd_7888129 4050401641669673392710661 := by
  unfold tailWord_7888129
  simp only [CollatzResearch.WordTrace]
  refine ⟨287703700439663293023419441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191802466959775528682279627 287703700439663293023419441)
  ·
    refine ⟨215777775329747469767564581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287703700439663293023419441 215777775329747469767564581)
    ·
      refine ⟨40458332874327650581418359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215777775329747469767564581 40458332874327650581418359)
      ·
        refine ⟨60687499311491475872127539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40458332874327650581418359 60687499311491475872127539)
        ·
          refine ⟨91031248967237213808191309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60687499311491475872127539 91031248967237213808191309)
          ·
            refine ⟨34136718362713955178071741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91031248967237213808191309 34136718362713955178071741)
            ·
              refine ⟨12801269386017733191776903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34136718362713955178071741 12801269386017733191776903)
              ·
                refine ⟨19201904079026599787665355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801269386017733191776903 19201904079026599787665355)
                ·
                  refine ⟨28802856118539899681498033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19201904079026599787665355 28802856118539899681498033)
                  ·
                    refine ⟨21602142088904924761123525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28802856118539899681498033 21602142088904924761123525)
                    ·
                      refine ⟨4050401641669673392710661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21602142088904924761123525 4050401641669673392710661)
                      ·
                        rfl

theorem cell23_7888129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_7888129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888129 prefixEnd_7888129 := by exact prefixLift 7888129
  have htrace : WordTrace (prefixWord ++ tailWord_7888129) baseStart_7888129 baseEnd_7888129 := by
    simpa [prefixWord, tailWord_7888129, baseEnd_7888129] using wordTrace_append hprefix tailTrace_7888129
  have hstable : (prefixWord ++ tailWord_7888129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888129).length < 2 ^ (prefixWord ++ tailWord_7888129).sum := by decide
  have hdescent : baseEnd_7888129 < baseStart_7888129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888139 : List Nat := [1, 1, 1, 1, 5, 5, 2, 7]
def baseStart_7888139 : Nat := 118140960795 + 7888139 * 2 ^ 59
def prefixEnd_7888139 : Nat := 4983230072969 + 3 ^ 40 * 7888139 * 2
def baseEnd_7888139 : Nat := 150015065795415494577245

theorem tailTrace_7888139 : CollatzResearch.WordTrace tailWord_7888139 prefixEnd_7888139 150015065795415494577245 := by
  unfold tailWord_7888139
  simp only [CollatzResearch.WordTrace]
  refine ⟨287704065169627064731283471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191802710113084709820855647 287704065169627064731283471)
  ·
    refine ⟨431556097754440597096925207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287704065169627064731283471 431556097754440597096925207)
    ·
      refine ⟨647334146631660895645387811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431556097754440597096925207 647334146631660895645387811)
      ·
        refine ⟨971001219947491343468081717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647334146631660895645387811 971001219947491343468081717)
        ·
          refine ⟨91031364370077313450132661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 971001219947491343468081717 91031364370077313450132661)
          ·
            refine ⟨8534190409694748135949937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91031364370077313450132661 8534190409694748135949937)
            ·
              refine ⟨6400642807271061101962453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534190409694748135949937 6400642807271061101962453)
              ·
                refine ⟨150015065795415494577245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6400642807271061101962453 150015065795415494577245)
                ·
                  rfl

theorem cell23_7888139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 7].length) (baseStart_7888139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888139 prefixEnd_7888139 := by exact prefixLift 7888139
  have htrace : WordTrace (prefixWord ++ tailWord_7888139) baseStart_7888139 baseEnd_7888139 := by
    simpa [prefixWord, tailWord_7888139, baseEnd_7888139] using wordTrace_append hprefix tailTrace_7888139
  have hstable : (prefixWord ++ tailWord_7888139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888139).length < 2 ^ (prefixWord ++ tailWord_7888139).sum := by decide
  have hdescent : baseEnd_7888139 < baseStart_7888139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888172 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_7888172 : Nat := 118140960795 + 7888172 * 2 ^ 59
def prefixEnd_7888172 : Nat := 4983230072969 + 3 ^ 40 * 7888172 * 2
def baseEnd_7888172 : Nat := 4050423721337816724472963

theorem tailTrace_7888172 : CollatzResearch.WordTrace tailWord_7888172 prefixEnd_7888172 4050423721337816724472963 := by
  unfold tailWord_7888172
  simp only [CollatzResearch.WordTrace]
  refine ⟨143852634389253755683617385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191803512519005007578156513 143852634389253755683617385)
  ·
    refine ⟨107889475791940316762713039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143852634389253755683617385 107889475791940316762713039)
    ·
      refine ⟨161834213687910475144069559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107889475791940316762713039 161834213687910475144069559)
      ·
        refine ⟨242751320531865712716104339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161834213687910475144069559 242751320531865712716104339)
        ·
          refine ⟨364126980797798569074156509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242751320531865712716104339 364126980797798569074156509)
          ·
            refine ⟨136547617799174463402808691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364126980797798569074156509 136547617799174463402808691)
            ·
              refine ⟨204821426698761695104213037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136547617799174463402808691 204821426698761695104213037)
              ·
                refine ⟨76808035012035635664079889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204821426698761695104213037 76808035012035635664079889)
                ·
                  refine ⟨57606026259026726748059917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76808035012035635664079889 57606026259026726748059917)
                  ·
                    refine ⟨21602259847135022530522469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57606026259026726748059917 21602259847135022530522469)
                    ·
                      refine ⟨4050423721337816724472963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21602259847135022530522469 4050423721337816724472963)
                      ·
                        rfl

theorem cell23_7888172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_7888172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888172 prefixEnd_7888172 := by exact prefixLift 7888172
  have htrace : WordTrace (prefixWord ++ tailWord_7888172) baseStart_7888172 baseEnd_7888172 := by
    simpa [prefixWord, tailWord_7888172, baseEnd_7888172] using wordTrace_append hprefix tailTrace_7888172
  have hstable : (prefixWord ++ tailWord_7888172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888172).length < 2 ^ (prefixWord ++ tailWord_7888172).sum := by decide
  have hdescent : baseEnd_7888172 < baseStart_7888172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888192 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_7888192 : Nat := 118140960795 + 7888192 * 2 ^ 59
def prefixEnd_7888192 : Nat := 4983230072969 + 3 ^ 40 * 7888192 * 2
def baseEnd_7888192 : Nat := 4050433990950906646222871

theorem tailTrace_7888192 : CollatzResearch.WordTrace tailWord_7888192 prefixEnd_7888192 4050433990950906646222871 := by
  unfold tailWord_7888192
  simp only [CollatzResearch.WordTrace]
  refine ⟨143852999119217527391481415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191803998825623369855308553 143852999119217527391481415)
  ·
    refine ⟨215779498678826291087222123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143852999119217527391481415 215779498678826291087222123)
    ·
      refine ⟨323669248018239436630833185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215779498678826291087222123 323669248018239436630833185)
      ·
        refine ⟨242751936013679577473124889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323669248018239436630833185 242751936013679577473124889)
        ·
          refine ⟨182063952010259683104843667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242751936013679577473124889 182063952010259683104843667)
          ·
            refine ⟨273095928015389524657265501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182063952010259683104843667 273095928015389524657265501)
            ·
              refine ⟨102410973005771071746474563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273095928015389524657265501 102410973005771071746474563)
              ·
                refine ⟨153616459508656607619711845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102410973005771071746474563 153616459508656607619711845)
                ·
                  refine ⟨28803086157873113928695971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153616459508656607619711845 28803086157873113928695971)
                  ·
                    refine ⟨43204629236809670893043957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28803086157873113928695971 43204629236809670893043957)
                    ·
                      refine ⟨4050433990950906646222871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43204629236809670893043957 4050433990950906646222871)
                      ·
                        rfl

theorem cell23_7888192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_7888192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888192 prefixEnd_7888192 := by exact prefixLift 7888192
  have htrace : WordTrace (prefixWord ++ tailWord_7888192) baseStart_7888192 baseEnd_7888192 := by
    simpa [prefixWord, tailWord_7888192, baseEnd_7888192] using wordTrace_append hprefix tailTrace_7888192
  have hstable : (prefixWord ++ tailWord_7888192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888192).length < 2 ^ (prefixWord ++ tailWord_7888192).sum := by decide
  have hdescent : baseEnd_7888192 < baseStart_7888192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888193 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7888193 : Nat := 118140960795 + 7888193 * 2 ^ 59
def prefixEnd_7888193 : Nat := 4983230072969 + 3 ^ 40 * 7888193 * 2
def baseEnd_7888193 : Nat := 4050434504431561142310367

theorem tailTrace_7888193 : CollatzResearch.WordTrace tailWord_7888193 prefixEnd_7888193 4050434504431561142310367 := by
  unfold tailWord_7888193
  simp only [CollatzResearch.WordTrace]
  refine ⟨287706034711431431953749233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191804023140954287969166155 287706034711431431953749233)
  ·
    refine ⟨215779526033573573965311925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287706034711431431953749233 215779526033573573965311925)
    ·
      refine ⟨20229330565647522559247993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215779526033573573965311925 20229330565647522559247993)
      ·
        refine ⟨15171997924235641919435995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20229330565647522559247993 15171997924235641919435995)
        ·
          refine ⟨22757996886353462879153993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15171997924235641919435995 22757996886353462879153993)
          ·
            refine ⟨17068497664765097159365495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22757996886353462879153993 17068497664765097159365495)
            ·
              refine ⟨25602746497147645739048243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068497664765097159365495 25602746497147645739048243)
              ·
                refine ⟨38404119745721468608572365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25602746497147645739048243 38404119745721468608572365)
                ·
                  refine ⟨14401544904645550728214637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38404119745721468608572365 14401544904645550728214637)
                  ·
                    refine ⟨5400579339242081523080489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14401544904645550728214637 5400579339242081523080489)
                    ·
                      refine ⟨4050434504431561142310367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400579339242081523080489 4050434504431561142310367)
                      ·
                        rfl

theorem cell23_7888193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7888193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888193 prefixEnd_7888193 := by exact prefixLift 7888193
  have htrace : WordTrace (prefixWord ++ tailWord_7888193) baseStart_7888193 baseEnd_7888193 := by
    simpa [prefixWord, tailWord_7888193, baseEnd_7888193] using wordTrace_append hprefix tailTrace_7888193
  have hstable : (prefixWord ++ tailWord_7888193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888193).length < 2 ^ (prefixWord ++ tailWord_7888193).sum := by decide
  have hdescent : baseEnd_7888193 < baseStart_7888193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888206 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_7888206 : Nat := 118140960795 + 7888206 * 2 ^ 59
def prefixEnd_7888206 : Nat := 4983230072969 + 3 ^ 40 * 7888206 * 2
def baseEnd_7888206 : Nat := 4050441179680069591447807

theorem tailTrace_7888206 : CollatzResearch.WordTrace tailWord_7888206 prefixEnd_7888206 4050441179680069591447807 := by
  unfold tailWord_7888206
  simp only [CollatzResearch.WordTrace]
  refine ⟨35963313607548041896746559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191804339240256223449314981 35963313607548041896746559)
  ·
    refine ⟨53944970411322062845119839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35963313607548041896746559 53944970411322062845119839)
    ·
      refine ⟨80917455616983094267679759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53944970411322062845119839 80917455616983094267679759)
      ·
        refine ⟨121376183425474641401519639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80917455616983094267679759 121376183425474641401519639)
        ·
          refine ⟨182064275138211962102279459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121376183425474641401519639 182064275138211962102279459)
          ·
            refine ⟨273096412707317943153419189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182064275138211962102279459 273096412707317943153419189)
            ·
              refine ⟨25602788691311057170633049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273096412707317943153419189 25602788691311057170633049)
              ·
                refine ⟨19202091518483292877974787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25602788691311057170633049 19202091518483292877974787)
                ·
                  refine ⟨28803137277724939316962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19202091518483292877974787 28803137277724939316962181)
                  ·
                    refine ⟨5400588239573426121930409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28803137277724939316962181 5400588239573426121930409)
                    ·
                      refine ⟨4050441179680069591447807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400588239573426121930409 4050441179680069591447807)
                      ·
                        rfl

theorem cell23_7888206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_7888206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888206 prefixEnd_7888206 := by exact prefixLift 7888206
  have htrace : WordTrace (prefixWord ++ tailWord_7888206) baseStart_7888206 baseEnd_7888206 := by
    simpa [prefixWord, tailWord_7888206, baseEnd_7888206] using wordTrace_append hprefix tailTrace_7888206
  have hstable : (prefixWord ++ tailWord_7888206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888206).length < 2 ^ (prefixWord ++ tailWord_7888206).sum := by decide
  have hdescent : baseEnd_7888206 < baseStart_7888206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888239 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_7888239 : Nat := 118140960795 + 7888239 * 2 ^ 59
def prefixEnd_7888239 : Nat := 4983230072969 + 3 ^ 40 * 7888239 * 2
def baseEnd_7888239 : Nat := 4050458124541667962335155

theorem tailTrace_7888239 : CollatzResearch.WordTrace tailWord_7888239 prefixEnd_7888239 4050458124541667962335155 := by
  unfold tailWord_7888239
  simp only [CollatzResearch.WordTrace]
  refine ⟨287707712469264781809923771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191805141646176521206615847 287707712469264781809923771)
  ·
    refine ⟨431561568703897172714885657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287707712469264781809923771 431561568703897172714885657)
    ·
      refine ⟨323671176527922879536164243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431561568703897172714885657 323671176527922879536164243)
      ·
        refine ⟨485506764791884319304246365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323671176527922879536164243 485506764791884319304246365)
        ·
          refine ⟨182065036796956619739092387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485506764791884319304246365 182065036796956619739092387)
          ·
            refine ⟨273097555195434929608638581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182065036796956619739092387 273097555195434929608638581)
            ·
              refine ⟨25602895799572024650809867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273097555195434929608638581 25602895799572024650809867)
              ·
                refine ⟨38404343699358036976214801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25602895799572024650809867 38404343699358036976214801)
                ·
                  refine ⟨28803257774518527732161101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38404343699358036976214801 28803257774518527732161101)
                  ·
                    refine ⟨10801221665444447899560413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28803257774518527732161101 10801221665444447899560413)
                    ·
                      refine ⟨4050458124541667962335155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10801221665444447899560413 4050458124541667962335155)
                      ·
                        rfl

theorem cell23_7888239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_7888239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888239 prefixEnd_7888239 := by exact prefixLift 7888239
  have htrace : WordTrace (prefixWord ++ tailWord_7888239) baseStart_7888239 baseEnd_7888239 := by
    simpa [prefixWord, tailWord_7888239, baseEnd_7888239] using wordTrace_append hprefix tailTrace_7888239
  have hstable : (prefixWord ++ tailWord_7888239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888239).length < 2 ^ (prefixWord ++ tailWord_7888239).sum := by decide
  have hdescent : baseEnd_7888239 < baseStart_7888239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888259 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 7]
def baseStart_7888259 : Nat := 118140960795 + 7888259 * 2 ^ 59
def prefixEnd_7888259 : Nat := 4983230072969 + 3 ^ 40 * 7888259 * 2
def baseEnd_7888259 : Nat := 1350156131384919294695021

theorem tailTrace_7888259 : CollatzResearch.WordTrace tailWord_7888259 prefixEnd_7888259 1350156131384919294695021 := by
  unfold tailWord_7888259
  simp only [CollatzResearch.WordTrace]
  refine ⟨287708441929192325225651831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191805627952794883483767887 287708441929192325225651831)
  ·
    refine ⟨431562662893788487838477747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287708441929192325225651831 431562662893788487838477747)
    ·
      refine ⟨647343994340682731757716621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431562662893788487838477747 647343994340682731757716621)
      ·
        refine ⟨242753997877756024409143733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647343994340682731757716621 242753997877756024409143733)
        ·
          refine ⟨22758187301039627288357225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242753997877756024409143733 22758187301039627288357225)
          ·
            refine ⟨17068640475779720466267919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22758187301039627288357225 17068640475779720466267919)
            ·
              refine ⟨25602960713669580699401879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17068640475779720466267919 25602960713669580699401879)
              ·
                refine ⟨38404441070504371049102819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25602960713669580699401879 38404441070504371049102819)
                ·
                  refine ⟨57606661605756556573654229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38404441070504371049102819 57606661605756556573654229)
                  ·
                    refine ⟨1350156131384919294695021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57606661605756556573654229 1350156131384919294695021)
                    ·
                      rfl

theorem cell23_7888259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_7888259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888259 prefixEnd_7888259 := by exact prefixLift 7888259
  have htrace : WordTrace (prefixWord ++ tailWord_7888259) baseStart_7888259 baseEnd_7888259 := by
    simpa [prefixWord, tailWord_7888259, baseEnd_7888259] using wordTrace_append hprefix tailTrace_7888259
  have hstable : (prefixWord ++ tailWord_7888259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888259).length < 2 ^ (prefixWord ++ tailWord_7888259).sum := by decide
  have hdescent : baseEnd_7888259 < baseStart_7888259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888274 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7888274 : Nat := 118140960795 + 7888274 * 2 ^ 59
def prefixEnd_7888274 : Nat := 4983230072969 + 3 ^ 40 * 7888274 * 2
def baseEnd_7888274 : Nat := 4050476096364575325397495

theorem tailTrace_7888274 : CollatzResearch.WordTrace tailWord_7888274 prefixEnd_7888274 4050476096364575325397495 := by
  unfold tailWord_7888274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71927247256034495696861969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191805992682758655191631917 71927247256034495696861969)
  ·
    refine ⟨53945435442025871772646477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71927247256034495696861969 53945435442025871772646477)
    ·
      refine ⟨20229538290759701914742429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53945435442025871772646477 20229538290759701914742429)
      ·
        refine ⟨7586076859034888218028411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20229538290759701914742429 7586076859034888218028411)
        ·
          refine ⟨11379115288552332327042617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586076859034888218028411 11379115288552332327042617)
          ·
            refine ⟨8534336466414249245281963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379115288552332327042617 8534336466414249245281963)
            ·
              refine ⟨12801504699621373867922945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534336466414249245281963 12801504699621373867922945)
              ·
                refine ⟨9601128524716030400942209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801504699621373867922945 9601128524716030400942209)
                ·
                  refine ⟨7200846393537022800706657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9601128524716030400942209 7200846393537022800706657)
                  ·
                    refine ⟨5400634795152767100529993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7200846393537022800706657 5400634795152767100529993)
                    ·
                      refine ⟨4050476096364575325397495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400634795152767100529993 4050476096364575325397495)
                      ·
                        rfl

theorem cell23_7888274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7888274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888274 prefixEnd_7888274 := by exact prefixLift 7888274
  have htrace : WordTrace (prefixWord ++ tailWord_7888274) baseStart_7888274 baseEnd_7888274 := by
    simpa [prefixWord, tailWord_7888274, baseEnd_7888274] using wordTrace_append hprefix tailTrace_7888274
  have hstable : (prefixWord ++ tailWord_7888274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888274).length < 2 ^ (prefixWord ++ tailWord_7888274).sum := by decide
  have hdescent : baseEnd_7888274 < baseStart_7888274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888279 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7888279 : Nat := 118140960795 + 7888279 * 2 ^ 59
def prefixEnd_7888279 : Nat := 4983230072969 + 3 ^ 40 * 7888279 * 2
def baseEnd_7888279 : Nat := 4050478663767847805834971

theorem tailTrace_7888279 : CollatzResearch.WordTrace tailWord_7888279 prefixEnd_7888279 4050478663767847805834971 := by
  unfold tailWord_7888279
  simp only [CollatzResearch.WordTrace]
  refine ⟨287709171389119868641379891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191806114259413245760919927 287709171389119868641379891)
  ·
    refine ⟨431563757083679802962069837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287709171389119868641379891 431563757083679802962069837)
    ·
      refine ⟨161836408906379926110776189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431563757083679802962069837 161836408906379926110776189)
      ·
        refine ⟨60688653339892472291541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161836408906379926110776189 60688653339892472291541071)
        ·
          refine ⟨91032980009838708437311607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60688653339892472291541071 91032980009838708437311607)
          ·
            refine ⟨136549470014758062655967411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91032980009838708437311607 136549470014758062655967411)
            ·
              refine ⟨204824205022137093983951117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136549470014758062655967411 204824205022137093983951117)
              ·
                refine ⟨76809076883301410243981669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204824205022137093983951117 76809076883301410243981669)
                ·
                  refine ⟨14401701915619014420746563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76809076883301410243981669 14401701915619014420746563)
                  ·
                    refine ⟨21602552873428521631119845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14401701915619014420746563 21602552873428521631119845)
                    ·
                      refine ⟨4050478663767847805834971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21602552873428521631119845 4050478663767847805834971)
                      ·
                        rfl

theorem cell23_7888279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7888279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888279 prefixEnd_7888279 := by exact prefixLift 7888279
  have htrace : WordTrace (prefixWord ++ tailWord_7888279) baseStart_7888279 baseEnd_7888279 := by
    simpa [prefixWord, tailWord_7888279, baseEnd_7888279] using wordTrace_append hprefix tailTrace_7888279
  have hstable : (prefixWord ++ tailWord_7888279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888279).length < 2 ^ (prefixWord ++ tailWord_7888279).sum := by decide
  have hdescent : baseEnd_7888279 < baseStart_7888279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888323 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 1, 4]
def baseStart_7888323 : Nat := 118140960795 + 7888323 * 2 ^ 59
def prefixEnd_7888323 : Nat := 4983230072969 + 3 ^ 40 * 7888323 * 2
def baseEnd_7888323 : Nat := 1350167085638881877894923

theorem tailTrace_7888323 : CollatzResearch.WordTrace tailWord_7888323 prefixEnd_7888323 1350167085638881877894923 := by
  unfold tailWord_7888323
  simp only [CollatzResearch.WordTrace]
  refine ⟨287710776200960464155981623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191807184133973642770654415 287710776200960464155981623)
  ·
    refine ⟨431566164301440696233972435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287710776200960464155981623 431566164301440696233972435)
    ·
      refine ⟨647349246452161044350958653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431566164301440696233972435 647349246452161044350958653)
      ·
        refine ⟨242755967419560391631609495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647349246452161044350958653 242755967419560391631609495)
        ·
          refine ⟨364133951129340587447414243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242755967419560391631609495 364133951129340587447414243)
          ·
            refine ⟨546200926694010881171121365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364133951129340587447414243 546200926694010881171121365)
            ·
              refine ⟨12801584219390880027448157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 546200926694010881171121365 12801584219390880027448157)
              ·
                refine ⟨4800594082271580010293059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12801584219390880027448157 4800594082271580010293059)
                ·
                  refine ⟨7200891123407370015439589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800594082271580010293059 7200891123407370015439589)
                  ·
                    refine ⟨1350167085638881877894923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200891123407370015439589 1350167085638881877894923)
                    ·
                      rfl

theorem cell23_7888323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 1, 4].length) (baseStart_7888323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888323 prefixEnd_7888323 := by exact prefixLift 7888323
  have htrace : WordTrace (prefixWord ++ tailWord_7888323) baseStart_7888323 baseEnd_7888323 := by
    simpa [prefixWord, tailWord_7888323, baseEnd_7888323] using wordTrace_append hprefix tailTrace_7888323
  have hstable : (prefixWord ++ tailWord_7888323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888323).length < 2 ^ (prefixWord ++ tailWord_7888323).sum := by decide
  have hdescent : baseEnd_7888323 < baseStart_7888323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888340 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_7888340 : Nat := 118140960795 + 7888340 * 2 ^ 59
def prefixEnd_7888340 : Nat := 4983230072969 + 3 ^ 40 * 7888340 * 2
def baseEnd_7888340 : Nat := 1350169995362590689057397

theorem tailTrace_7888340 : CollatzResearch.WordTrace tailWord_7888340 prefixEnd_7888340 1350169995362590689057397 := by
  unfold tailWord_7888340
  simp only [CollatzResearch.WordTrace]
  refine ⟨143855698120949438029675237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191807597494599250706233649 143855698120949438029675237)
  ·
    refine ⟨26972943397678019630564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143855698120949438029675237 26972943397678019630564107)
    ·
      refine ⟨40459415096517029445846161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26972943397678019630564107 40459415096517029445846161)
      ·
        refine ⟨30344561322387772084384621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40459415096517029445846161 30344561322387772084384621)
        ·
          refine ⟨11379210495895414531644233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30344561322387772084384621 11379210495895414531644233)
          ·
            refine ⟨8534407871921560898733175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379210495895414531644233 8534407871921560898733175)
            ·
              refine ⟨12801611807882341348099763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534407871921560898733175 12801611807882341348099763)
              ·
                refine ⟨19202417711823512022149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801611807882341348099763 19202417711823512022149645)
                ·
                  refine ⟨7200906641933817008306117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19202417711823512022149645 7200906641933817008306117)
                  ·
                    refine ⟨1350169995362590689057397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200906641933817008306117 1350169995362590689057397)
                    ·
                      rfl

theorem cell23_7888340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_7888340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888340 prefixEnd_7888340 := by exact prefixLift 7888340
  have htrace : WordTrace (prefixWord ++ tailWord_7888340) baseStart_7888340 baseEnd_7888340 := by
    simpa [prefixWord, tailWord_7888340, baseEnd_7888340] using wordTrace_append hprefix tailTrace_7888340
  have hstable : (prefixWord ++ tailWord_7888340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888340).length < 2 ^ (prefixWord ++ tailWord_7888340).sum := by decide
  have hdescent : baseEnd_7888340 < baseStart_7888340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888353 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 6]
def baseStart_7888353 : Nat := 118140960795 + 7888353 * 2 ^ 59
def prefixEnd_7888353 : Nat := 4983230072969 + 3 ^ 40 * 7888353 * 2
def baseEnd_7888353 : Nat := 450057406815142279589959

theorem tailTrace_7888353 : CollatzResearch.WordTrace tailWord_7888353 prefixEnd_7888353 450057406815142279589959 := by
  unfold tailWord_7888353
  simp only [CollatzResearch.WordTrace]
  refine ⟨287711870390851779279573713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191807913593901186186382475 287711870390851779279573713)
  ·
    refine ⟨215783902793138834459680285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287711870390851779279573713 215783902793138834459680285)
    ·
      refine ⟨80918963547427062922380107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215783902793138834459680285 80918963547427062922380107)
      ·
        refine ⟨121378445321140594383570161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80918963547427062922380107 121378445321140594383570161)
        ·
          refine ⟨91033833990855445787677621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121378445321140594383570161 91033833990855445787677621)
          ·
            refine ⟨8534421936642698042594777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91033833990855445787677621 8534421936642698042594777)
            ·
              refine ⟨6400816452482023531946083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534421936642698042594777 6400816452482023531946083)
              ·
                refine ⟨9601224678723035297919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400816452482023531946083 9601224678723035297919125)
                ·
                  refine ⟨450057406815142279589959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9601224678723035297919125 450057406815142279589959)
                  ·
                    rfl

theorem cell23_7888353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_7888353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888353 prefixEnd_7888353 := by exact prefixLift 7888353
  have htrace : WordTrace (prefixWord ++ tailWord_7888353) baseStart_7888353 baseEnd_7888353 := by
    simpa [prefixWord, tailWord_7888353, baseEnd_7888353] using wordTrace_append hprefix tailTrace_7888353
  have hstable : (prefixWord ++ tailWord_7888353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888353).length < 2 ^ (prefixWord ++ tailWord_7888353).sum := by decide
  have hdescent : baseEnd_7888353 < baseStart_7888353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888356 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_7888356 : Nat := 118140960795 + 7888356 * 2 ^ 59
def prefixEnd_7888356 : Nat := 4983230072969 + 3 ^ 40 * 7888356 * 2
def baseEnd_7888356 : Nat := 4050518201778244004572117

theorem tailTrace_7888356 : CollatzResearch.WordTrace tailWord_7888356 prefixEnd_7888356 4050518201778244004572117 := by
  unfold tailWord_7888356
  simp only [CollatzResearch.WordTrace]
  refine ⟨143855989904920455395966461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191807986539893940527955281 143855989904920455395966461)
  ·
    refine ⟨53945996214345170773487423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143855989904920455395966461 53945996214345170773487423)
    ·
      refine ⟨80918994321517756160231135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53945996214345170773487423 80918994321517756160231135)
      ·
        refine ⟨121378491482276634240346703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80918994321517756160231135 121378491482276634240346703)
        ·
          refine ⟨182067737223414951360520055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121378491482276634240346703 182067737223414951360520055)
          ·
            refine ⟨273101605835122427040780083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182067737223414951360520055 273101605835122427040780083)
            ·
              refine ⟨409652408752683640561170125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273101605835122427040780083 409652408752683640561170125)
              ·
                refine ⟨153619653282256365210438797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409652408752683640561170125 153619653282256365210438797)
                ·
                  refine ⟨57607369980846136953914549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153619653282256365210438797 57607369980846136953914549)
                  ·
                    refine ⟨5400690935704325339429489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57607369980846136953914549 5400690935704325339429489)
                    ·
                      refine ⟨4050518201778244004572117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400690935704325339429489 4050518201778244004572117)
                      ·
                        rfl

theorem cell23_7888356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_7888356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888356 prefixEnd_7888356 := by exact prefixLift 7888356
  have htrace : WordTrace (prefixWord ++ tailWord_7888356) baseStart_7888356 baseEnd_7888356 := by
    simpa [prefixWord, tailWord_7888356, baseEnd_7888356] using wordTrace_append hprefix tailTrace_7888356
  have hstable : (prefixWord ++ tailWord_7888356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888356).length < 2 ^ (prefixWord ++ tailWord_7888356).sum := by decide
  have hdescent : baseEnd_7888356 < baseStart_7888356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888366 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7888366 : Nat := 118140960795 + 7888366 * 2 ^ 59
def prefixEnd_7888366 : Nat := 4983230072969 + 3 ^ 40 * 7888366 * 2
def baseEnd_7888366 : Nat := 1350174445528262988482357

theorem tailTrace_7888366 : CollatzResearch.WordTrace tailWord_7888366 prefixEnd_7888366 1350174445528262988482357 := by
  unfold tailWord_7888366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35964043067475585312474619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191808229693203121666531301 35964043067475585312474619)
  ·
    refine ⟨53946064601213377968711929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35964043067475585312474619 53946064601213377968711929)
    ·
      refine ⟨40459548450910033476533947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53946064601213377968711929 40459548450910033476533947)
      ·
        refine ⟨60689322676365050214800921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40459548450910033476533947 60689322676365050214800921)
        ·
          refine ⟨45516992007273787661100691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60689322676365050214800921 45516992007273787661100691)
          ·
            refine ⟨68275488010910681491651037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45516992007273787661100691 68275488010910681491651037)
            ·
              refine ⟨25603308004091505559369139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68275488010910681491651037 25603308004091505559369139)
              ·
                refine ⟨38404962006137258339053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25603308004091505559369139 38404962006137258339053709)
                ·
                  refine ⟨14401860752301471877145141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38404962006137258339053709 14401860752301471877145141)
                  ·
                    refine ⟨1350174445528262988482357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14401860752301471877145141 1350174445528262988482357)
                    ·
                      rfl

theorem cell23_7888366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7888366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888366 prefixEnd_7888366 := by exact prefixLift 7888366
  have htrace : WordTrace (prefixWord ++ tailWord_7888366) baseStart_7888366 baseEnd_7888366 := by
    simpa [prefixWord, tailWord_7888366, baseEnd_7888366] using wordTrace_append hprefix tailTrace_7888366
  have hstable : (prefixWord ++ tailWord_7888366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888366).length < 2 ^ (prefixWord ++ tailWord_7888366).sum := by decide
  have hdescent : baseEnd_7888366 < baseStart_7888366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888379 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 6]
def baseStart_7888379 : Nat := 118140960795 + 7888379 * 2 ^ 59
def prefixEnd_7888379 : Nat := 4983230072969 + 3 ^ 40 * 7888379 * 2
def baseEnd_7888379 : Nat := 1350176670611099138194837

theorem tailTrace_7888379 : CollatzResearch.WordTrace tailWord_7888379 prefixEnd_7888379 1350176670611099138194837 := by
  unfold tailWord_7888379
  simp only [CollatzResearch.WordTrace]
  refine ⟨287712818688757585720020191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191808545792505057146680127 287712818688757585720020191)
  ·
    refine ⟨431569228033136378580030287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287712818688757585720020191 431569228033136378580030287)
    ·
      refine ⟨647353842049704567870045431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431569228033136378580030287 647353842049704567870045431)
      ·
        refine ⟨971030763074556851805068147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647353842049704567870045431 971030763074556851805068147)
        ·
          refine ⟨1456546144611835277707602221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971030763074556851805068147 1456546144611835277707602221)
          ·
            refine ⟨546204804229438229140350833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1456546144611835277707602221 546204804229438229140350833)
            ·
              refine ⟨409653603172078671855263125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546204804229438229140350833 409653603172078671855263125)
              ·
                refine ⟨19202512648691187743215459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 409653603172078671855263125 19202512648691187743215459)
                ·
                  refine ⟨28803768973036781614823189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19202512648691187743215459 28803768973036781614823189)
                  ·
                    refine ⟨1350176670611099138194837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28803768973036781614823189 1350176670611099138194837)
                    ·
                      rfl

theorem cell23_7888379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_7888379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888379 prefixEnd_7888379 := by exact prefixLift 7888379
  have htrace : WordTrace (prefixWord ++ tailWord_7888379) baseStart_7888379 baseEnd_7888379 := by
    simpa [prefixWord, tailWord_7888379, baseEnd_7888379] using wordTrace_append hprefix tailTrace_7888379
  have hstable : (prefixWord ++ tailWord_7888379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888379).length < 2 ^ (prefixWord ++ tailWord_7888379).sum := by decide
  have hdescent : baseEnd_7888379 < baseStart_7888379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888413 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7888413 : Nat := 118140960795 + 7888413 * 2 ^ 59
def prefixEnd_7888413 : Nat := 4983230072969 + 3 ^ 40 * 7888413 * 2
def baseEnd_7888413 : Nat := 1350182490058516760519785

theorem tailTrace_7888413 : CollatzResearch.WordTrace tailWord_7888413 prefixEnd_7888413 1350182490058516760519785 := by
  unfold tailWord_7888413
  simp only [CollatzResearch.WordTrace]
  refine ⟨287714058770634409526757893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191809372513756273017838595 287714058770634409526757893)
  ·
    refine ⟨53946386019493951786267105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287714058770634409526757893 53946386019493951786267105)
    ·
      refine ⟨40459789514620463839700329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53946386019493951786267105 40459789514620463839700329)
      ·
        refine ⟨30344842135965347879775247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40459789514620463839700329 30344842135965347879775247)
        ·
          refine ⟨45517263203948021819662871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30344842135965347879775247 45517263203948021819662871)
          ·
            refine ⟨68275894805922032729494307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45517263203948021819662871 68275894805922032729494307)
            ·
              refine ⟨102413842208883049094241461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68275894805922032729494307 102413842208883049094241461)
              ·
                refine ⟨9601297707082785852585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102413842208883049094241461 9601297707082785852585137)
                ·
                  refine ⟨7200973280312089389438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9601297707082785852585137 7200973280312089389438853)
                  ·
                    refine ⟨1350182490058516760519785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7200973280312089389438853 1350182490058516760519785)
                    ·
                      rfl

theorem cell23_7888413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7888413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888413 prefixEnd_7888413 := by exact prefixLift 7888413
  have htrace : WordTrace (prefixWord ++ tailWord_7888413) baseStart_7888413 baseEnd_7888413 := by
    simpa [prefixWord, tailWord_7888413, baseEnd_7888413] using wordTrace_append hprefix tailTrace_7888413
  have hstable : (prefixWord ++ tailWord_7888413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888413).length < 2 ^ (prefixWord ++ tailWord_7888413).sum := by decide
  have hdescent : baseEnd_7888413 < baseStart_7888413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888424 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7888424 : Nat := 118140960795 + 7888424 * 2 ^ 59
def prefixEnd_7888424 : Nat := 4983230072969 + 3 ^ 40 * 7888424 * 2
def baseEnd_7888424 : Nat := 4050553118462749738521805

theorem tailTrace_7888424 : CollatzResearch.WordTrace tailWord_7888424 prefixEnd_7888424 4050553118462749738521805 := by
  unfold tailWord_7888424
  simp only [CollatzResearch.WordTrace]
  refine ⟨143857229986797279202704163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191809639982396372270272217 143857229986797279202704163)
  ·
    refine ⟨215785844980195918804056245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143857229986797279202704163 215785844980195918804056245)
    ·
      refine ⟨20229922966893367387880273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215785844980195918804056245 20229922966893367387880273)
      ·
        refine ⟨15172442225170025540910205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20229922966893367387880273 15172442225170025540910205)
        ·
          refine ⟨5689665834438759577841327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15172442225170025540910205 5689665834438759577841327)
          ·
            refine ⟨8534498751658139366761991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689665834438759577841327 8534498751658139366761991)
            ·
              refine ⟨12801748127487209050142987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534498751658139366761991 12801748127487209050142987)
              ·
                refine ⟨19202622191230813575214481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12801748127487209050142987 19202622191230813575214481)
                ·
                  refine ⟨14401966643423110181410861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19202622191230813575214481 14401966643423110181410861)
                  ·
                    refine ⟨5400737491283666318029073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14401966643423110181410861 5400737491283666318029073)
                    ·
                      refine ⟨4050553118462749738521805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400737491283666318029073 4050553118462749738521805)
                      ·
                        rfl

theorem cell23_7888424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7888424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888424 prefixEnd_7888424 := by exact prefixLift 7888424
  have htrace : WordTrace (prefixWord ++ tailWord_7888424) baseStart_7888424 baseEnd_7888424 := by
    simpa [prefixWord, tailWord_7888424, baseEnd_7888424] using wordTrace_append hprefix tailTrace_7888424
  have hstable : (prefixWord ++ tailWord_7888424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888424).length < 2 ^ (prefixWord ++ tailWord_7888424).sum := by decide
  have hdescent : baseEnd_7888424 < baseStart_7888424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888437 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_7888437 : Nat := 118140960795 + 7888437 * 2 ^ 59
def prefixEnd_7888437 : Nat := 4983230072969 + 3 ^ 40 * 7888437 * 2
def baseEnd_7888437 : Nat := 4050559793711258187659245

theorem tailTrace_7888437 : CollatzResearch.WordTrace tailWord_7888437 prefixEnd_7888437 4050559793711258187659245 := by
  unfold tailWord_7888437
  simp only [CollatzResearch.WordTrace]
  refine ⟨287714934122547461625631565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191809956081698307750421043 287714934122547461625631565)
  ·
    refine ⟨107893100295955298109611837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287714934122547461625631565 107893100295955298109611837)
    ·
      refine ⟨40459912610983236791104439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107893100295955298109611837 40459912610983236791104439)
      ·
        refine ⟨60689868916474855186656659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40459912610983236791104439 60689868916474855186656659)
        ·
          refine ⟨91034803374712282779984989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60689868916474855186656659 91034803374712282779984989)
          ·
            refine ⟨34138051265517106042494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91034803374712282779984989 34138051265517106042494371)
            ·
              refine ⟨51207076898275659063741557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34138051265517106042494371 51207076898275659063741557)
              ·
                refine ⟨4800663459213343037225771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51207076898275659063741557 4800663459213343037225771)
                ·
                  refine ⟨7200995188820014555838657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800663459213343037225771 7200995188820014555838657)
                  ·
                    refine ⟨5400746391615010916878993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7200995188820014555838657 5400746391615010916878993)
                    ·
                      refine ⟨4050559793711258187659245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400746391615010916878993 4050559793711258187659245)
                      ·
                        rfl

theorem cell23_7888437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_7888437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888437 prefixEnd_7888437 := by exact prefixLift 7888437
  have htrace : WordTrace (prefixWord ++ tailWord_7888437) baseStart_7888437 baseEnd_7888437 := by
    simpa [prefixWord, tailWord_7888437, baseEnd_7888437] using wordTrace_append hprefix tailTrace_7888437
  have hstable : (prefixWord ++ tailWord_7888437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888437).length < 2 ^ (prefixWord ++ tailWord_7888437).sum := by decide
  have hdescent : baseEnd_7888437 < baseStart_7888437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888440 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_7888440 : Nat := 118140960795 + 7888440 * 2 ^ 59
def prefixEnd_7888440 : Nat := 4983230072969 + 3 ^ 40 * 7888440 * 2
def baseEnd_7888440 : Nat := 4050561334153221675921731

theorem tailTrace_7888440 : CollatzResearch.WordTrace tailWord_7888440 prefixEnd_7888440 4050561334153221675921731 := by
  unfold tailWord_7888440
  simp only [CollatzResearch.WordTrace]
  refine ⟨143857521770768296568995387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191810029027691062091993849 143857521770768296568995387)
  ·
    refine ⟨215786282656152444853493081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143857521770768296568995387 215786282656152444853493081)
    ·
      refine ⟨161839711992114333640119811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215786282656152444853493081 161839711992114333640119811)
      ·
        refine ⟨242759567988171500460179717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161839711992114333640119811 242759567988171500460179717)
        ·
          refine ⟨45517418997782156336283697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242759567988171500460179717 45517418997782156336283697)
          ·
            refine ⟨34138064248336617252212773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45517418997782156336283697 34138064248336617252212773)
            ·
              refine ⟨6400887046563115734789895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34138064248336617252212773 6400887046563115734789895)
              ·
                refine ⟨9601330569844673602184843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400887046563115734789895 9601330569844673602184843)
                ·
                  refine ⟨14401995854767010403277265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601330569844673602184843 14401995854767010403277265)
                  ·
                    refine ⟨10801496891075257802457949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14401995854767010403277265 10801496891075257802457949)
                    ·
                      refine ⟨4050561334153221675921731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10801496891075257802457949 4050561334153221675921731)
                      ·
                        rfl

theorem cell23_7888440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_7888440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888440 prefixEnd_7888440 := by exact prefixLift 7888440
  have htrace : WordTrace (prefixWord ++ tailWord_7888440) baseStart_7888440 baseEnd_7888440 := by
    simpa [prefixWord, tailWord_7888440, baseEnd_7888440] using wordTrace_append hprefix tailTrace_7888440
  have hstable : (prefixWord ++ tailWord_7888440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888440).length < 2 ^ (prefixWord ++ tailWord_7888440).sum := by decide
  have hdescent : baseEnd_7888440 < baseStart_7888440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888453 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_7888453 : Nat := 118140960795 + 7888453 * 2 ^ 59
def prefixEnd_7888453 : Nat := 4983230072969 + 3 ^ 40 * 7888453 * 2
def baseEnd_7888453 : Nat := 4050568009401730125059171

theorem tailTrace_7888453 : CollatzResearch.WordTrace tailWord_7888453 prefixEnd_7888453 4050568009401730125059171 := by
  unfold tailWord_7888453
  simp only [CollatzResearch.WordTrace]
  refine ⟨287715517690489496358214013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191810345126992997572142675 287715517690489496358214013)
  ·
    refine ⟨107893319133933561134330255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287715517690489496358214013 107893319133933561134330255)
    ·
      refine ⟨161839978700900341701495383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107893319133933561134330255 161839978700900341701495383)
      ·
        refine ⟨242759968051350512552243075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161839978700900341701495383 242759968051350512552243075)
        ·
          refine ⟨364139952077025768828364613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242759968051350512552243075 364139952077025768828364613)
          ·
            refine ⟨68276241014442331655318365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364139952077025768828364613 68276241014442331655318365)
            ·
              refine ⟨25603590380415874370744387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68276241014442331655318365 25603590380415874370744387)
              ·
                refine ⟨38405385570623811556116581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25603590380415874370744387 38405385570623811556116581)
                ·
                  refine ⟨7201009794491964666771859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38405385570623811556116581 7201009794491964666771859)
                  ·
                    refine ⟨10801514691737947000157789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7201009794491964666771859 10801514691737947000157789)
                    ·
                      refine ⟨4050568009401730125059171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10801514691737947000157789 4050568009401730125059171)
                      ·
                        rfl

theorem cell23_7888453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_7888453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888453 prefixEnd_7888453 := by exact prefixLift 7888453
  have htrace : WordTrace (prefixWord ++ tailWord_7888453) baseStart_7888453 baseEnd_7888453 := by
    simpa [prefixWord, tailWord_7888453, baseEnd_7888453] using wordTrace_append hprefix tailTrace_7888453
  have hstable : (prefixWord ++ tailWord_7888453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888453).length < 2 ^ (prefixWord ++ tailWord_7888453).sum := by decide
  have hdescent : baseEnd_7888453 < baseStart_7888453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888477 : List Nat := [1, 4, 4, 2, 1, 2, 2, 7]
def baseStart_7888477 : Nat := 118140960795 + 7888477 * 2 ^ 59
def prefixEnd_7888477 : Nat := 4983230072969 + 3 ^ 40 * 7888477 * 2
def baseEnd_7888477 : Nat := 150021493812497704857743

theorem tailTrace_7888477 : CollatzResearch.WordTrace tailWord_7888477 prefixEnd_7888477 150021493812497704857743 := by
  unfold tailWord_7888477
  simp only [CollatzResearch.WordTrace]
  refine ⟨287716393042402548457087685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191810928694935032304725123 287716393042402548457087685)
  ·
    refine ⟨53946823695450477835703941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287716393042402548457087685 53946823695450477835703941)
    ·
      refine ⟨10115029442896964594194489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53946823695450477835703941 10115029442896964594194489)
      ·
        refine ⟨7586272082172723445645867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10115029442896964594194489 7586272082172723445645867)
        ·
          refine ⟨11379408123259085168468801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586272082172723445645867 11379408123259085168468801)
          ·
            refine ⟨8534556092444313876351601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379408123259085168468801 8534556092444313876351601)
            ·
              refine ⟨6400917069333235407263701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534556092444313876351601 6400917069333235407263701)
              ·
                refine ⟨150021493812497704857743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6400917069333235407263701 150021493812497704857743)
                ·
                  rfl

theorem cell23_7888477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 7].length) (baseStart_7888477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888477 prefixEnd_7888477 := by exact prefixLift 7888477
  have htrace : WordTrace (prefixWord ++ tailWord_7888477) baseStart_7888477 baseEnd_7888477 := by
    simpa [prefixWord, tailWord_7888477, baseEnd_7888477] using wordTrace_append hprefix tailTrace_7888477
  have hstable : (prefixWord ++ tailWord_7888477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888477).length < 2 ^ (prefixWord ++ tailWord_7888477).sum := by decide
  have hdescent : baseEnd_7888477 < baseStart_7888477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888496 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_7888496 : Nat := 118140960795 + 7888496 * 2 ^ 59
def prefixEnd_7888496 : Nat := 4983230072969 + 3 ^ 40 * 7888496 * 2
def baseEnd_7888496 : Nat := 4050590089069873456821473

theorem tailTrace_7888496 : CollatzResearch.WordTrace tailWord_7888496 prefixEnd_7888496 4050590089069873456821473 := by
  unfold tailWord_7888496
  simp only [CollatzResearch.WordTrace]
  refine ⟨143858543014666857351014671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191811390686222476468019561 143858543014666857351014671)
  ·
    refine ⟨215787814522000286026522007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143858543014666857351014671 215787814522000286026522007)
    ·
      refine ⟨323681721783000429039783011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215787814522000286026522007 323681721783000429039783011)
      ·
        refine ⟨485522582674500643559674517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323681721783000429039783011 485522582674500643559674517)
        ·
          refine ⟨22758871062867217666859743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485522582674500643559674517 22758871062867217666859743)
          ·
            refine ⟨34138306594300826500289615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22758871062867217666859743 34138306594300826500289615)
            ·
              refine ⟨51207459891451239750434423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34138306594300826500289615 51207459891451239750434423)
              ·
                refine ⟨76811189837176859625651635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51207459891451239750434423 76811189837176859625651635)
                ·
                  refine ⟨115216784755765289438477453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76811189837176859625651635 115216784755765289438477453)
                  ·
                    refine ⟨43206294283411983539429045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115216784755765289438477453 43206294283411983539429045)
                    ·
                      refine ⟨4050590089069873456821473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43206294283411983539429045 4050590089069873456821473)
                      ·
                        rfl

theorem cell23_7888496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_7888496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888496 prefixEnd_7888496 := by exact prefixLift 7888496
  have htrace : WordTrace (prefixWord ++ tailWord_7888496) baseStart_7888496 baseEnd_7888496 := by
    simpa [prefixWord, tailWord_7888496, baseEnd_7888496] using wordTrace_append hprefix tailTrace_7888496
  have hstable : (prefixWord ++ tailWord_7888496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888496).length < 2 ^ (prefixWord ++ tailWord_7888496).sum := by decide
  have hdescent : baseEnd_7888496 < baseStart_7888496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888506 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_7888506 : Nat := 118140960795 + 7888506 * 2 ^ 59
def prefixEnd_7888506 : Nat := 4983230072969 + 3 ^ 40 * 7888506 * 2
def baseEnd_7888506 : Nat := 4050595223876418417696427

theorem tailTrace_7888506 : CollatzResearch.WordTrace tailWord_7888506 prefixEnd_7888506 4050595223876418417696427 := by
  unfold tailWord_7888506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71929362689824371602473343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191811633839531657606595581 71929362689824371602473343)
  ·
    refine ⟨107894044034736557403710015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71929362689824371602473343 107894044034736557403710015)
    ·
      refine ⟨161841066052104836105565023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107894044034736557403710015 161841066052104836105565023)
      ·
        refine ⟨242761599078157254158347535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161841066052104836105565023 242761599078157254158347535)
        ·
          refine ⟨364142398617235881237521303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242761599078157254158347535 364142398617235881237521303)
          ·
            refine ⟨546213597925853821856281955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364142398617235881237521303 546213597925853821856281955)
            ·
              refine ⟨819320396888780732784422933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546213597925853821856281955 819320396888780732784422933)
              ·
                refine ⟨38405643604161596849269825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 819320396888780732784422933 38405643604161596849269825)
                ·
                  refine ⟨28804232703121197636952369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38405643604161596849269825 28804232703121197636952369)
                  ·
                    refine ⟨21603174527340898227714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28804232703121197636952369 21603174527340898227714277)
                    ·
                      refine ⟨4050595223876418417696427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21603174527340898227714277 4050595223876418417696427)
                      ·
                        rfl

theorem cell23_7888506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_7888506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888506 prefixEnd_7888506 := by exact prefixLift 7888506
  have htrace : WordTrace (prefixWord ++ tailWord_7888506) baseStart_7888506 baseEnd_7888506 := by
    simpa [prefixWord, tailWord_7888506, baseEnd_7888506] using wordTrace_append hprefix tailTrace_7888506
  have hstable : (prefixWord ++ tailWord_7888506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888506).length < 2 ^ (prefixWord ++ tailWord_7888506).sum := by decide
  have hdescent : baseEnd_7888506 < baseStart_7888506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888567 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 5]
def baseStart_7888567 : Nat := 118140960795 + 7888567 * 2 ^ 59
def prefixEnd_7888567 : Nat := 4983230072969 + 3 ^ 40 * 7888567 * 2
def baseEnd_7888567 : Nat := 450069616244038075448183

theorem tailTrace_7888567 : CollatzResearch.WordTrace tailWord_7888567 prefixEnd_7888567 450069616244038075448183 := by
  unfold tailWord_7888567
  simp only [CollatzResearch.WordTrace]
  refine ⟨287719675612076493827863955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191813117074717662551909303 287719675612076493827863955)
  ·
    refine ⟨431579513418114740741795933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287719675612076493827863955 431579513418114740741795933)
    ·
      refine ⟨161842317531793027778173475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431579513418114740741795933 161842317531793027778173475)
      ·
        refine ⟨242763476297689541667260213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161842317531793027778173475 242763476297689541667260213)
        ·
          refine ⟨22759075902908394531305645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242763476297689541667260213 22759075902908394531305645)
          ·
            refine ⟨8534653463590647949239617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22759075902908394531305645 8534653463590647949239617)
            ·
              refine ⟨6400990097692985961929713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534653463590647949239617 6400990097692985961929713)
              ·
                refine ⟨4800742573269739471447285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6400990097692985961929713 4800742573269739471447285)
                ·
                  refine ⟨450069616244038075448183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4800742573269739471447285 450069616244038075448183)
                  ·
                    rfl

theorem cell23_7888567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 5].length) (baseStart_7888567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888567 prefixEnd_7888567 := by exact prefixLift 7888567
  have htrace : WordTrace (prefixWord ++ tailWord_7888567) baseStart_7888567 baseEnd_7888567 := by
    simpa [prefixWord, tailWord_7888567, baseEnd_7888567] using wordTrace_append hprefix tailTrace_7888567
  have hstable : (prefixWord ++ tailWord_7888567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888567).length < 2 ^ (prefixWord ++ tailWord_7888567).sum := by decide
  have hdescent : baseEnd_7888567 < baseStart_7888567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888593 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_7888593 : Nat := 118140960795 + 7888593 * 2 ^ 59
def prefixEnd_7888593 : Nat := 4983230072969 + 3 ^ 40 * 7888593 * 2
def baseEnd_7888593 : Nat := 1350213298897786525769509

theorem tailTrace_7888593 : CollatzResearch.WordTrace tailWord_7888593 prefixEnd_7888593 1350213298897786525769509 := by
  unfold tailWord_7888593
  simp only [CollatzResearch.WordTrace]
  refine ⟨287720623909982300268310433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191813749273321533512206955 287720623909982300268310433)
  ·
    refine ⟨215790467932486725201232825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287720623909982300268310433 215790467932486725201232825)
    ·
      refine ⟨161842850949365043900924619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215790467932486725201232825 161842850949365043900924619)
      ·
        refine ⟨242764276424047565851386929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161842850949365043900924619 242764276424047565851386929)
        ·
          refine ⟨182073207318035674388540197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242764276424047565851386929 182073207318035674388540197)
          ·
            refine ⟨34138726372131688947851287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182073207318035674388540197 34138726372131688947851287)
            ·
              refine ⟨51208089558197533421776931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34138726372131688947851287 51208089558197533421776931)
              ·
                refine ⟨76812134337296300132665397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51208089558197533421776931 76812134337296300132665397)
                ·
                  refine ⟨7201137594121528137437381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76812134337296300132665397 7201137594121528137437381)
                  ·
                    refine ⟨1350213298897786525769509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201137594121528137437381 1350213298897786525769509)
                    ·
                      rfl

theorem cell23_7888593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_7888593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888593 prefixEnd_7888593 := by exact prefixLift 7888593
  have htrace : WordTrace (prefixWord ++ tailWord_7888593) baseStart_7888593 baseEnd_7888593 := by
    simpa [prefixWord, tailWord_7888593, baseEnd_7888593] using wordTrace_append hprefix tailTrace_7888593
  have hstable : (prefixWord ++ tailWord_7888593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888593).length < 2 ^ (prefixWord ++ tailWord_7888593).sum := by decide
  have hdescent : baseEnd_7888593 < baseStart_7888593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888677 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_7888677 : Nat := 118140960795 + 7888677 * 2 ^ 59
def prefixEnd_7888677 : Nat := 4983230072969 + 3 ^ 40 * 7888677 * 2
def baseEnd_7888677 : Nat := 4050683029068337248658141

theorem tailTrace_7888677 : CollatzResearch.WordTrace tailWord_7888677 prefixEnd_7888677 4050683029068337248658141 := by
  unfold tailWord_7888677
  simp only [CollatzResearch.WordTrace]
  refine ⟨287723687641677982614368285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191815791761118655076245523 287723687641677982614368285)
  ·
    refine ⟨107896382865629243480388107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287723687641677982614368285 107896382865629243480388107)
    ·
      refine ⟨161844574298443865220582161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107896382865629243480388107 161844574298443865220582161)
      ·
        refine ⟨121383430723832898915436621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161844574298443865220582161 121383430723832898915436621)
        ·
          refine ⟨45518786521437337093288733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121383430723832898915436621 45518786521437337093288733)
          ·
            refine ⟨17069544945539001409983275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45518786521437337093288733 17069544945539001409983275)
            ·
              refine ⟨25604317418308502114974913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17069544945539001409983275 25604317418308502114974913)
              ·
                refine ⟨19203238063731376586231185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25604317418308502114974913 19203238063731376586231185)
                ·
                  refine ⟨14402428547798532439673389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19203238063731376586231185 14402428547798532439673389)
                  ·
                    refine ⟨5400910705424449664877521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14402428547798532439673389 5400910705424449664877521)
                    ·
                      refine ⟨4050683029068337248658141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400910705424449664877521 4050683029068337248658141)
                      ·
                        rfl

theorem cell23_7888677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_7888677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888677 prefixEnd_7888677 := by exact prefixLift 7888677
  have htrace : WordTrace (prefixWord ++ tailWord_7888677) baseStart_7888677 baseEnd_7888677 := by
    simpa [prefixWord, tailWord_7888677, baseEnd_7888677] using wordTrace_append hprefix tailTrace_7888677
  have hstable : (prefixWord ++ tailWord_7888677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888677).length < 2 ^ (prefixWord ++ tailWord_7888677).sum := by decide
  have hdescent : baseEnd_7888677 < baseStart_7888677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888683 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 8, 4]
def baseStart_7888683 : Nat := 118140960795 + 7888683 * 2 ^ 59
def prefixEnd_7888683 : Nat := 4983230072969 + 3 ^ 40 * 7888683 * 2
def baseEnd_7888683 : Nat := 1350228703317421408394371

theorem tailTrace_7888683 : CollatzResearch.WordTrace tailWord_7888683 prefixEnd_7888683 1350228703317421408394371 := by
  unfold tailWord_7888683
  simp only [CollatzResearch.WordTrace]
  refine ⟨287723906479656245639086703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191815937653104163759391135 287723906479656245639086703)
  ·
    refine ⟨431585859719484368458630055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287723906479656245639086703 431585859719484368458630055)
    ·
      refine ⟨647378789579226552687945083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431585859719484368458630055 647378789579226552687945083)
      ·
        refine ⟨971068184368839829031917625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647378789579226552687945083 971068184368839829031917625)
        ·
          refine ⟨728301138276629871773938219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971068184368839829031917625 728301138276629871773938219)
          ·
            refine ⟨1092451707414944807660907329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728301138276629871773938219 1092451707414944807660907329)
            ·
              refine ⟨819338780561208605745680497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092451707414944807660907329 819338780561208605745680497)
              ·
                refine ⟨614504085420906454309260373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819338780561208605745680497 614504085420906454309260373)
                ·
                  refine ⟨7201219751026247511436645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 614504085420906454309260373 7201219751026247511436645)
                  ·
                    refine ⟨1350228703317421408394371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7201219751026247511436645 1350228703317421408394371)
                    ·
                      rfl

theorem cell23_7888683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 4].length) (baseStart_7888683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888683 prefixEnd_7888683 := by exact prefixLift 7888683
  have htrace : WordTrace (prefixWord ++ tailWord_7888683) baseStart_7888683 baseEnd_7888683 := by
    simpa [prefixWord, tailWord_7888683, baseEnd_7888683] using wordTrace_append hprefix tailTrace_7888683
  have hstable : (prefixWord ++ tailWord_7888683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888683).length < 2 ^ (prefixWord ++ tailWord_7888683).sum := by decide
  have hdescent : baseEnd_7888683 < baseStart_7888683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888707 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 4]
def baseStart_7888707 : Nat := 118140960795 + 7888707 * 2 ^ 59
def prefixEnd_7888707 : Nat := 4983230072969 + 3 ^ 40 * 7888707 * 2
def baseEnd_7888707 : Nat := 4050698433487972131283003

theorem tailTrace_7888707 : CollatzResearch.WordTrace tailWord_7888707 prefixEnd_7888707 4050698433487972131283003 := by
  unfold tailWord_7888707
  simp only [CollatzResearch.WordTrace]
  refine ⟨287724781831569297737960375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191816521221046198491973583 287724781831569297737960375)
  ·
    refine ⟨431587172747353946606940563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287724781831569297737960375 431587172747353946606940563)
    ·
      refine ⟨647380759121030919910410845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431587172747353946606940563 647380759121030919910410845)
      ·
        refine ⟨242767784670386594966404067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 647380759121030919910410845 242767784670386594966404067)
        ·
          refine ⟨364151677005579892449606101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242767784670386594966404067 364151677005579892449606101)
          ·
            refine ⟨8534804929818278729287643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364151677005579892449606101 8534804929818278729287643)
            ·
              refine ⟨12802207394727418093931465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534804929818278729287643 12802207394727418093931465)
              ·
                refine ⟨9601655546045563570448599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12802207394727418093931465 9601655546045563570448599)
                ·
                  refine ⟨14402483319068345355672899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601655546045563570448599 14402483319068345355672899)
                  ·
                    refine ⟨21603724978602518033509349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14402483319068345355672899 21603724978602518033509349)
                    ·
                      refine ⟨4050698433487972131283003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21603724978602518033509349 4050698433487972131283003)
                      ·
                        rfl

theorem cell23_7888707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_7888707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888707 prefixEnd_7888707 := by exact prefixLift 7888707
  have htrace : WordTrace (prefixWord ++ tailWord_7888707) baseStart_7888707 baseEnd_7888707 := by
    simpa [prefixWord, tailWord_7888707, baseEnd_7888707] using wordTrace_append hprefix tailTrace_7888707
  have hstable : (prefixWord ++ tailWord_7888707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888707).length < 2 ^ (prefixWord ++ tailWord_7888707).sum := by decide
  have hdescent : baseEnd_7888707 < baseStart_7888707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888717 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7888717 : Nat := 118140960795 + 7888717 * 2 ^ 59
def prefixEnd_7888717 : Nat := 4983230072969 + 3 ^ 40 * 7888717 * 2
def baseEnd_7888717 : Nat := 1350234522764839030719319

theorem tailTrace_7888717 : CollatzResearch.WordTrace tailWord_7888717 prefixEnd_7888717 1350234522764839030719319 := by
  unfold tailWord_7888717
  simp only [CollatzResearch.WordTrace]
  refine ⟨287725146561533069445824405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191816764374355379630549603 287725146561533069445824405)
  ·
    refine ⟨13487116245071862630273019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 287725146561533069445824405 13487116245071862630273019)
    ·
      refine ⟨20230674367607793945409529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13487116245071862630273019 20230674367607793945409529)
      ·
        refine ⟨15173005775705845459057147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20230674367607793945409529 15173005775705845459057147)
        ·
          refine ⟨22759508663558768188585721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173005775705845459057147 22759508663558768188585721)
          ·
            refine ⟨17069631497669076141439291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22759508663558768188585721 17069631497669076141439291)
            ·
              refine ⟨25604447246503614212158937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17069631497669076141439291 25604447246503614212158937)
              ·
                refine ⟨19203335434877710659119203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25604447246503614212158937 19203335434877710659119203)
                ·
                  refine ⟨28805003152316565988678805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19203335434877710659119203 28805003152316565988678805)
                  ·
                    refine ⟨1350234522764839030719319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28805003152316565988678805 1350234522764839030719319)
                    ·
                      rfl

theorem cell23_7888717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7888717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888717 prefixEnd_7888717 := by exact prefixLift 7888717
  have htrace : WordTrace (prefixWord ++ tailWord_7888717) baseStart_7888717 baseEnd_7888717 := by
    simpa [prefixWord, tailWord_7888717, baseEnd_7888717] using wordTrace_append hprefix tailTrace_7888717
  have hstable : (prefixWord ++ tailWord_7888717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888717).length < 2 ^ (prefixWord ++ tailWord_7888717).sum := by decide
  have hdescent : baseEnd_7888717 < baseStart_7888717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888724 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_7888724 : Nat := 118140960795 + 7888724 * 2 ^ 59
def prefixEnd_7888724 : Nat := 4983230072969 + 3 ^ 40 * 7888724 * 2
def baseEnd_7888724 : Nat := 4050707162659098564770425

theorem tailTrace_7888724 : CollatzResearch.WordTrace tailWord_7888724 prefixEnd_7888724 4050707162659098564770425 := by
  unfold tailWord_7888724
  simp only [CollatzResearch.WordTrace]
  refine ⟨143862700936253854820664613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191816934581671806427552817 143862700936253854820664613)
  ·
    refine ⟨26974256425547597778874615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143862700936253854820664613 26974256425547597778874615)
    ·
      refine ⟨40461384638321396668311923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26974256425547597778874615 40461384638321396668311923)
      ·
        refine ⟨60692076957482095002467885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40461384638321396668311923 60692076957482095002467885)
        ·
          refine ⟨22759528859055785625925457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60692076957482095002467885 22759528859055785625925457)
          ·
            refine ⟨17069646644291839219444093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22759528859055785625925457 17069646644291839219444093)
            ·
              refine ⟨6401117491609439707291535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17069646644291839219444093 6401117491609439707291535)
              ·
                refine ⟨9601676237414159560937303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401117491609439707291535 9601676237414159560937303)
                ·
                  refine ⟨14402514356121239341405955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601676237414159560937303 14402514356121239341405955)
                  ·
                    refine ⟨21603771534181859012108933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14402514356121239341405955 21603771534181859012108933)
                    ·
                      refine ⟨4050707162659098564770425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21603771534181859012108933 4050707162659098564770425)
                      ·
                        rfl

theorem cell23_7888724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_7888724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888724 prefixEnd_7888724 := by exact prefixLift 7888724
  have htrace : WordTrace (prefixWord ++ tailWord_7888724) baseStart_7888724 baseEnd_7888724 := by
    simpa [prefixWord, tailWord_7888724, baseEnd_7888724] using wordTrace_append hprefix tailTrace_7888724
  have hstable : (prefixWord ++ tailWord_7888724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888724).length < 2 ^ (prefixWord ++ tailWord_7888724).sum := by decide
  have hdescent : baseEnd_7888724 < baseStart_7888724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888727 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_7888727 : Nat := 118140960795 + 7888727 * 2 ^ 59
def prefixEnd_7888727 : Nat := 4983230072969 + 3 ^ 40 * 7888727 * 2
def baseEnd_7888727 : Nat := 4050708703101062053032911

theorem tailTrace_7888727 : CollatzResearch.WordTrace tailWord_7888727 prefixEnd_7888727 4050708703101062053032911 := by
  unfold tailWord_7888727
  simp only [CollatzResearch.WordTrace]
  refine ⟨287725511291496841153688435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191817007527664560769125623 287725511291496841153688435)
  ·
    refine ⟨431588266937245261730532653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287725511291496841153688435 431588266937245261730532653)
    ·
      refine ⟨161845600101466973148949745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431588266937245261730532653 161845600101466973148949745)
      ·
        refine ⟨121384200076100229861712309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161845600101466973148949745 121384200076100229861712309)
        ·
          refine ⟨11379768757134396549535529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121384200076100229861712309 11379768757134396549535529)
          ·
            refine ⟨8534826567850797412151647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11379768757134396549535529 8534826567850797412151647)
            ·
              refine ⟨12802239851776196118227471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534826567850797412151647 12802239851776196118227471)
              ·
                refine ⟨19203359777664294177341207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802239851776196118227471 19203359777664294177341207)
                ·
                  refine ⟨28805039666496441266011811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19203359777664294177341207 28805039666496441266011811)
                  ·
                    refine ⟨43207559499744661899017717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28805039666496441266011811 43207559499744661899017717)
                    ·
                      refine ⟨4050708703101062053032911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43207559499744661899017717 4050708703101062053032911)
                      ·
                        rfl

theorem cell23_7888727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_7888727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888727 prefixEnd_7888727 := by exact prefixLift 7888727
  have htrace : WordTrace (prefixWord ++ tailWord_7888727) baseStart_7888727 baseEnd_7888727 := by
    simpa [prefixWord, tailWord_7888727, baseEnd_7888727] using wordTrace_append hprefix tailTrace_7888727
  have hstable : (prefixWord ++ tailWord_7888727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888727).length < 2 ^ (prefixWord ++ tailWord_7888727).sum := by decide
  have hdescent : baseEnd_7888727 < baseStart_7888727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888743 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 9]
def baseStart_7888743 : Nat := 118140960795 + 7888743 * 2 ^ 59
def prefixEnd_7888743 : Nat := 4983230072969 + 3 ^ 40 * 7888743 * 2
def baseEnd_7888743 : Nat := 1350238972930511330144279

theorem tailTrace_7888743 : CollatzResearch.WordTrace tailWord_7888743 prefixEnd_7888743 1350238972930511330144279 := by
  unfold tailWord_7888743
  simp only [CollatzResearch.WordTrace]
  refine ⟨287726094859438875886270883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191817396572959250590847255 287726094859438875886270883)
  ·
    refine ⟨431589142289158313829406325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287726094859438875886270883 431589142289158313829406325)
    ·
      refine ⟨40461482089608591921506843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 431589142289158313829406325 40461482089608591921506843)
      ·
        refine ⟨60692223134412887882260265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40461482089608591921506843 60692223134412887882260265)
        ·
          refine ⟨45519167350809665911695199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60692223134412887882260265 45519167350809665911695199)
          ·
            refine ⟨68278751026214498867542799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45519167350809665911695199 68278751026214498867542799)
            ·
              refine ⟨102418126539321748301314199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68278751026214498867542799 102418126539321748301314199)
              ·
                refine ⟨153627189808982622451971299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102418126539321748301314199 153627189808982622451971299)
                ·
                  refine ⟨230440784713473933677956949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153627189808982622451971299 230440784713473933677956949)
                  ·
                    refine ⟨1350238972930511330144279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230440784713473933677956949 1350238972930511330144279)
                    ·
                      rfl

theorem cell23_7888743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_7888743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888743 prefixEnd_7888743 := by exact prefixLift 7888743
  have htrace : WordTrace (prefixWord ++ tailWord_7888743) baseStart_7888743 baseEnd_7888743 := by
    simpa [prefixWord, tailWord_7888743, baseEnd_7888743] using wordTrace_append hprefix tailTrace_7888743
  have hstable : (prefixWord ++ tailWord_7888743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888743).length < 2 ^ (prefixWord ++ tailWord_7888743).sum := by decide
  have hdescent : baseEnd_7888743 < baseStart_7888743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888757 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7888757 : Nat := 118140960795 + 7888757 * 2 ^ 59
def prefixEnd_7888757 : Nat := 4983230072969 + 3 ^ 40 * 7888757 * 2
def baseEnd_7888757 : Nat := 4050724107520696935657773

theorem tailTrace_7888757 : CollatzResearch.WordTrace tailWord_7888757 prefixEnd_7888757 4050724107520696935657773 := by
  unfold tailWord_7888757
  simp only [CollatzResearch.WordTrace]
  refine ⟨287726605481388156277280525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191817736987592104184853683 287726605481388156277280525)
  ·
    refine ⟨107897477055520558603980197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287726605481388156277280525 107897477055520558603980197)
    ·
      refine ⟨20230776947910104738246287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107897477055520558603980197 20230776947910104738246287)
      ·
        refine ⟨30346165421865157107369431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20230776947910104738246287 30346165421865157107369431)
        ·
          refine ⟨45519248132797735661054147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30346165421865157107369431 45519248132797735661054147)
          ·
            refine ⟨68278872199196603491581221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45519248132797735661054147 68278872199196603491581221)
            ·
              refine ⟨12802288537349363154671479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68278872199196603491581221 12802288537349363154671479)
              ·
                refine ⟨19203432806024044732007219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802288537349363154671479 19203432806024044732007219)
                ·
                  refine ⟨28805149209036067098010829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19203432806024044732007219 28805149209036067098010829)
                  ·
                    refine ⟨10801930953388525161754061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28805149209036067098010829 10801930953388525161754061)
                    ·
                      refine ⟨4050724107520696935657773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10801930953388525161754061 4050724107520696935657773)
                      ·
                        rfl

theorem cell23_7888757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7888757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888757 prefixEnd_7888757 := by exact prefixLift 7888757
  have htrace : WordTrace (prefixWord ++ tailWord_7888757) baseStart_7888757 baseEnd_7888757 := by
    simpa [prefixWord, tailWord_7888757, baseEnd_7888757] using wordTrace_append hprefix tailTrace_7888757
  have hstable : (prefixWord ++ tailWord_7888757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888757).length < 2 ^ (prefixWord ++ tailWord_7888757).sum := by decide
  have hdescent : baseEnd_7888757 < baseStart_7888757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888763 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_7888763 : Nat := 118140960795 + 7888763 * 2 ^ 59
def prefixEnd_7888763 : Nat := 4983230072969 + 3 ^ 40 * 7888763 * 2
def baseEnd_7888763 : Nat := 4050727188404623912182745

theorem tailTrace_7888763 : CollatzResearch.WordTrace tailWord_7888763 prefixEnd_7888763 4050727188404623912182745 := by
  unfold tailWord_7888763
  simp only [CollatzResearch.WordTrace]
  refine ⟨287726824319366419301998943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191817882879577612867999295 287726824319366419301998943)
  ·
    refine ⟨431590236479049628952998415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287726824319366419301998943 431590236479049628952998415)
    ·
      refine ⟨647385354718574443429497623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431590236479049628952998415 647385354718574443429497623)
      ·
        refine ⟨971078032077861665144246435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647385354718574443429497623 971078032077861665144246435)
        ·
          refine ⟨1456617048116792497716369653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971078032077861665144246435 1456617048116792497716369653)
          ·
            refine ⟨136557848260949296660909655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1456617048116792497716369653 136557848260949296660909655)
            ·
              refine ⟨204836772391423944991364483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136557848260949296660909655 204836772391423944991364483)
              ·
                refine ⟨307255158587135917487046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204836772391423944991364483 307255158587135917487046725)
                ·
                  refine ⟨57610342235087984528821261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307255158587135917487046725 57610342235087984528821261)
                  ·
                    refine ⟨21603878338157994198307973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57610342235087984528821261 21603878338157994198307973)
                    ·
                      refine ⟨4050727188404623912182745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21603878338157994198307973 4050727188404623912182745)
                      ·
                        rfl

theorem cell23_7888763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_7888763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888763 prefixEnd_7888763 := by exact prefixLift 7888763
  have htrace : WordTrace (prefixWord ++ tailWord_7888763) baseStart_7888763 baseEnd_7888763 := by
    simpa [prefixWord, tailWord_7888763, baseEnd_7888763] using wordTrace_append hprefix tailTrace_7888763
  have hstable : (prefixWord ++ tailWord_7888763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888763).length < 2 ^ (prefixWord ++ tailWord_7888763).sum := by decide
  have hdescent : baseEnd_7888763 < baseStart_7888763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888767 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 1, 3, 2]
def baseStart_7888767 : Nat := 118140960795 + 7888767 * 2 ^ 59
def prefixEnd_7888767 : Nat := 4983230072969 + 3 ^ 40 * 7888767 * 2
def baseEnd_7888767 : Nat := 4050729242327241896532727

theorem tailTrace_7888767 : CollatzResearch.WordTrace tailWord_7888767 prefixEnd_7888767 4050729242327241896532727 := by
  unfold tailWord_7888767
  simp only [CollatzResearch.WordTrace]
  refine ⟨287726970211351927985144555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191817980140901285323429703 287726970211351927985144555)
  ·
    refine ⟨431590455317027891977716833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287726970211351927985144555 431590455317027891977716833)
    ·
      refine ⟨323692841487770918983287625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431590455317027891977716833 323692841487770918983287625)
      ·
        refine ⟨242769631115828189237465719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323692841487770918983287625 242769631115828189237465719)
        ·
          refine ⟨364154446673742283856198579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242769631115828189237465719 364154446673742283856198579)
          ·
            refine ⟨546231670010613425784297869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364154446673742283856198579 546231670010613425784297869)
            ·
              refine ⟨204836876253980034669111701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546231670010613425784297869 204836876253980034669111701)
              ·
                refine ⟨9601728574405314125114611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204836876253980034669111701 9601728574405314125114611)
                ·
                  refine ⟨14402592861607971187671917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601728574405314125114611 14402592861607971187671917)
                  ·
                    refine ⟨5400972323102989195376969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14402592861607971187671917 5400972323102989195376969)
                    ·
                      refine ⟨4050729242327241896532727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5400972323102989195376969 4050729242327241896532727)
                      ·
                        rfl

theorem cell23_7888767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_7888767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888767 prefixEnd_7888767 := by exact prefixLift 7888767
  have htrace : WordTrace (prefixWord ++ tailWord_7888767) baseStart_7888767 baseEnd_7888767 := by
    simpa [prefixWord, tailWord_7888767, baseEnd_7888767] using wordTrace_append hprefix tailTrace_7888767
  have hstable : (prefixWord ++ tailWord_7888767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888767).length < 2 ^ (prefixWord ++ tailWord_7888767).sum := by decide
  have hdescent : baseEnd_7888767 < baseStart_7888767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888773 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_7888773 : Nat := 118140960795 + 7888773 * 2 ^ 59
def prefixEnd_7888773 : Nat := 4983230072969 + 3 ^ 40 * 7888773 * 2
def baseEnd_7888773 : Nat := 1350244107737056291019233

theorem tailTrace_7888773 : CollatzResearch.WordTrace tailWord_7888773 prefixEnd_7888773 1350244107737056291019233 := by
  unfold tailWord_7888773
  simp only [CollatzResearch.WordTrace]
  refine ⟨287727189049330191009862973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191818126032886794006575315 287727189049330191009862973)
  ·
    refine ⟨107897695893498821628698615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287727189049330191009862973 107897695893498821628698615)
    ·
      refine ⟨161846543840248232443047923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107897695893498821628698615 161846543840248232443047923)
      ·
        refine ⟨242769815760372348664571885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161846543840248232443047923 242769815760372348664571885)
        ·
          refine ⟨91038680910139630749214457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242769815760372348664571885 91038680910139630749214457)
          ·
            refine ⟨68279010682604723061910843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91038680910139630749214457 68279010682604723061910843)
            ·
              refine ⟨102418516023907084592866265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68279010682604723061910843 102418516023907084592866265)
              ·
                refine ⟨76813887017930313444649699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102418516023907084592866265 76813887017930313444649699)
                ·
                  refine ⟨115220830526895470166974549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76813887017930313444649699 115220830526895470166974549)
                  ·
                    refine ⟨1350244107737056291019233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115220830526895470166974549 1350244107737056291019233)
                    ·
                      rfl

theorem cell23_7888773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_7888773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888773 prefixEnd_7888773 := by exact prefixLift 7888773
  have htrace : WordTrace (prefixWord ++ tailWord_7888773) baseStart_7888773 baseEnd_7888773 := by
    simpa [prefixWord, tailWord_7888773, baseEnd_7888773] using wordTrace_append hprefix tailTrace_7888773
  have hstable : (prefixWord ++ tailWord_7888773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888773).length < 2 ^ (prefixWord ++ tailWord_7888773).sum := by decide
  have hdescent : baseEnd_7888773 < baseStart_7888773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888778 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7888778 : Nat := 118140960795 + 7888778 * 2 ^ 59
def prefixEnd_7888778 : Nat := 4983230072969 + 3 ^ 40 * 7888778 * 2
def baseEnd_7888778 : Nat := 4050734890614441353495177

theorem tailTrace_7888778 : CollatzResearch.WordTrace tailWord_7888778 prefixEnd_7888778 4050734890614441353495177 := by
  unfold tailWord_7888778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71931842853578019215948747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191818247609541384575863325 71931842853578019215948747)
  ·
    refine ⟨107897764280367028823923121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71931842853578019215948747 107897764280367028823923121)
    ·
      refine ⟨80923323210275271617942341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107897764280367028823923121 80923323210275271617942341)
      ·
        refine ⟨15173123101926613428364189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80923323210275271617942341 15173123101926613428364189)
        ·
          refine ⟨5689921163222480035636571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15173123101926613428364189 5689921163222480035636571)
          ·
            refine ⟨8534881744833720053454857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689921163222480035636571 8534881744833720053454857)
            ·
              refine ⟨6401161308625290040091143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534881744833720053454857 6401161308625290040091143)
              ·
                refine ⟨9601741962937935060136715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401161308625290040091143 9601741962937935060136715)
                ·
                  refine ⟨14402612944406902590205073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9601741962937935060136715 14402612944406902590205073)
                  ·
                    refine ⟨10801959708305176942653805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14402612944406902590205073 10801959708305176942653805)
                    ·
                      refine ⟨4050734890614441353495177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10801959708305176942653805 4050734890614441353495177)
                      ·
                        rfl

theorem cell23_7888778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7888778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888778 prefixEnd_7888778 := by exact prefixLift 7888778
  have htrace : WordTrace (prefixWord ++ tailWord_7888778) baseStart_7888778 baseEnd_7888778 := by
    simpa [prefixWord, tailWord_7888778, baseEnd_7888778] using wordTrace_append hprefix tailTrace_7888778
  have hstable : (prefixWord ++ tailWord_7888778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888778).length < 2 ^ (prefixWord ++ tailWord_7888778).sum := by decide
  have hdescent : baseEnd_7888778 < baseStart_7888778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888783 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_7888783 : Nat := 118140960795 + 7888783 * 2 ^ 59
def prefixEnd_7888783 : Nat := 4983230072969 + 3 ^ 40 * 7888783 * 2
def baseEnd_7888783 : Nat := 4050737458017713833932653

theorem tailTrace_7888783 : CollatzResearch.WordTrace tailWord_7888783 prefixEnd_7888783 4050737458017713833932653 := by
  unfold tailWord_7888783
  simp only [CollatzResearch.WordTrace]
  refine ⟨287727553779293962717727003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191818369186195975145151335 287727553779293962717727003)
  ·
    refine ⟨431591330668940944076590505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287727553779293962717727003 431591330668940944076590505)
    ·
      refine ⟨323693498001705708057442879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431591330668940944076590505 323693498001705708057442879)
      ·
        refine ⟨485540247002558562086164319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323693498001705708057442879 485540247002558562086164319)
        ·
          refine ⟨728310370503837843129246479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485540247002558562086164319 728310370503837843129246479)
          ·
            refine ⟨1092465555755756764693869719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728310370503837843129246479 1092465555755756764693869719)
            ·
              refine ⟨1638698333633635147040804579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092465555755756764693869719 1638698333633635147040804579)
              ·
                refine ⟨2458047500450452720561206869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638698333633635147040804579 2458047500450452720561206869)
                ·
                  refine ⟨28805244145903742819076643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2458047500450452720561206869 28805244145903742819076643)
                  ·
                    refine ⟨43207866218855614228614965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28805244145903742819076643 43207866218855614228614965)
                    ·
                      refine ⟨4050737458017713833932653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43207866218855614228614965 4050737458017713833932653)
                      ·
                        rfl

theorem cell23_7888783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_7888783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888783 prefixEnd_7888783 := by exact prefixLift 7888783
  have htrace : WordTrace (prefixWord ++ tailWord_7888783) baseStart_7888783 baseEnd_7888783 := by
    simpa [prefixWord, tailWord_7888783, baseEnd_7888783] using wordTrace_append hprefix tailTrace_7888783
  have hstable : (prefixWord ++ tailWord_7888783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888783).length < 2 ^ (prefixWord ++ tailWord_7888783).sum := by decide
  have hdescent : baseEnd_7888783 < baseStart_7888783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888808 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_7888808 : Nat := 118140960795 + 7888808 * 2 ^ 59
def prefixEnd_7888808 : Nat := 4983230072969 + 3 ^ 40 * 7888808 * 2
def baseEnd_7888808 : Nat := 4050750295034076236120039

theorem tailTrace_7888808 : CollatzResearch.WordTrace tailWord_7888808 prefixEnd_7888808 4050750295034076236120039 := by
  unfold tailWord_7888808
  simp only [CollatzResearch.WordTrace]
  refine ⟨143864232802101695993693539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191818977069468927991591385 143864232802101695993693539)
  ·
    refine ⟨215796349203152543990540309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143864232802101695993693539 215796349203152543990540309)
    ·
      refine ⟨10115453868897775499556577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 215796349203152543990540309 10115453868897775499556577)
      ·
        refine ⟨7586590401673331624667433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10115453868897775499556577 7586590401673331624667433)
        ·
          refine ⟨5689942801254998718500575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7586590401673331624667433 5689942801254998718500575)
          ·
            refine ⟨8534914201882498077750863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689942801254998718500575 8534914201882498077750863)
            ·
              refine ⟨12802371302823747116626295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534914201882498077750863 12802371302823747116626295)
              ·
                refine ⟨19203556954235620674939443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802371302823747116626295 19203556954235620674939443)
                ·
                  refine ⟨28805335431353431012409165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19203556954235620674939443 28805335431353431012409165)
                  ·
                    refine ⟨10802000786757536629653437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28805335431353431012409165 10802000786757536629653437)
                    ·
                      refine ⟨4050750295034076236120039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10802000786757536629653437 4050750295034076236120039)
                      ·
                        rfl

theorem cell23_7888808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_7888808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888808 prefixEnd_7888808 := by exact prefixLift 7888808
  have htrace : WordTrace (prefixWord ++ tailWord_7888808) baseStart_7888808 baseEnd_7888808 := by
    simpa [prefixWord, tailWord_7888808, baseEnd_7888808] using wordTrace_append hprefix tailTrace_7888808
  have hstable : (prefixWord ++ tailWord_7888808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888808).length < 2 ^ (prefixWord ++ tailWord_7888808).sum := by decide
  have hdescent : baseEnd_7888808 < baseStart_7888808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888907 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3]
def baseStart_7888907 : Nat := 118140960795 + 7888907 * 2 ^ 59
def prefixEnd_7888907 : Nat := 4983230072969 + 3 ^ 40 * 7888907 * 2
def baseEnd_7888907 : Nat := 4050801129618871348782083

theorem tailTrace_7888907 : CollatzResearch.WordTrace tailWord_7888907 prefixEnd_7888907 4050801129618871348782083 := by
  unfold tailWord_7888907
  simp only [CollatzResearch.WordTrace]
  refine ⟨287732076430844731895240975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191821384287229821263493983 287732076430844731895240975)
  ·
    refine ⟨431598114646267097842861463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287732076430844731895240975 431598114646267097842861463)
    ·
      refine ⟨647397171969400646764292195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431598114646267097842861463 647397171969400646764292195)
      ·
        refine ⟨971095757954100970146438293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647397171969400646764292195 971095757954100970146438293)
        ·
          refine ⟨45520113654098482975614295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 971095757954100970146438293 45520113654098482975614295)
          ·
            refine ⟨68280170481147724463421443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45520113654098482975614295 68280170481147724463421443)
            ·
              refine ⟨102420255721721586695132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68280170481147724463421443 102420255721721586695132165)
              ·
                refine ⟨19203797947822797505337281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102420255721721586695132165 19203797947822797505337281)
                ·
                  refine ⟨14402848460867098129002961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19203797947822797505337281 14402848460867098129002961)
                  ·
                    refine ⟨10802136345650323596752221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14402848460867098129002961 10802136345650323596752221)
                    ·
                      refine ⟨4050801129618871348782083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10802136345650323596752221 4050801129618871348782083)
                      ·
                        rfl

theorem cell23_7888907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].length) (baseStart_7888907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7888907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7888907 prefixEnd_7888907 := by exact prefixLift 7888907
  have htrace : WordTrace (prefixWord ++ tailWord_7888907) baseStart_7888907 baseEnd_7888907 := by
    simpa [prefixWord, tailWord_7888907, baseEnd_7888907] using wordTrace_append hprefix tailTrace_7888907
  have hstable : (prefixWord ++ tailWord_7888907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888907).length < 2 ^ (prefixWord ++ tailWord_7888907).sum := by decide
  have hdescent : baseEnd_7888907 < baseStart_7888907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889014 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7889014 : Nat := 118140960795 + 7889014 * 2 ^ 59
def prefixEnd_7889014 : Nat := 4983230072969 + 3 ^ 40 * 7889014 * 2
def baseEnd_7889014 : Nat := 4050856072048902430144091

theorem tailTrace_7889014 : CollatzResearch.WordTrace tailWord_7889014 prefixEnd_7889014 4050856072048902430144091 := by
  unfold tailWord_7889014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983498690091068073086631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191823986027638059446257397 17983498690091068073086631)
  ·
    refine ⟨26975248035136602109629947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983498690091068073086631 26975248035136602109629947)
    ·
      refine ⟨40462872052704903164444921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26975248035136602109629947 40462872052704903164444921)
      ·
        refine ⟨30347154039528677373333691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40462872052704903164444921 30347154039528677373333691)
        ·
          refine ⟨45520731059293016060000537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30347154039528677373333691 45520731059293016060000537)
          ·
            refine ⟨34140548294469762045000403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45520731059293016060000537 34140548294469762045000403)
            ·
              refine ⟨51210822441704643067500605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34140548294469762045000403 51210822441704643067500605)
              ·
                refine ⟨19204058415639241150312727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51210822441704643067500605 19204058415639241150312727)
                ·
                  refine ⟨28806087623458861725469091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204058415639241150312727 28806087623458861725469091)
                  ·
                    refine ⟨43209131435188292588203637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28806087623458861725469091 43209131435188292588203637)
                    ·
                      refine ⟨4050856072048902430144091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43209131435188292588203637 4050856072048902430144091)
                      ·
                        rfl

theorem cell23_7889014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7889014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889014 prefixEnd_7889014 := by exact prefixLift 7889014
  have htrace : WordTrace (prefixWord ++ tailWord_7889014) baseStart_7889014 baseEnd_7889014 := by
    simpa [prefixWord, tailWord_7889014, baseEnd_7889014] using wordTrace_append hprefix tailTrace_7889014
  have hstable : (prefixWord ++ tailWord_7889014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889014).length < 2 ^ (prefixWord ++ tailWord_7889014).sum := by decide
  have hdescent : baseEnd_7889014 < baseStart_7889014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889017 : List Nat := [1, 2, 1, 3, 4, 3, 9]
def baseStart_7889017 : Nat := 118140960795 + 7889017 * 2 ^ 59
def prefixEnd_7889017 : Nat := 4983230072969 + 3 ^ 40 * 7889017 * 2
def baseEnd_7889017 : Nat := 50010587808529208869217

theorem tailTrace_7889017 : CollatzResearch.WordTrace tailWord_7889017 prefixEnd_7889017 50010587808529208869217 := by
  unfold tailWord_7889017
  simp only [CollatzResearch.WordTrace]
  refine ⟨287736088460446220681745305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191824058973630813787830203 287736088460446220681745305)
  ·
    refine ⟨215802066345334665511308979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287736088460446220681745305 215802066345334665511308979)
    ·
      refine ⟨323703099518001998266963469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215802066345334665511308979 323703099518001998266963469)
      ·
        refine ⟨121388662319250749350111301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323703099518001998266963469 121388662319250749350111301)
        ·
          refine ⟨22760374184859515503145869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121388662319250749350111301 22760374184859515503145869)
          ·
            refine ⟨8535140319322318313679701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22760374184859515503145869 8535140319322318313679701)
            ·
              refine ⟨50010587808529208869217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8535140319322318313679701 50010587808529208869217)
              ·
                rfl

theorem cell23_7889017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 9].length) (baseStart_7889017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889017 prefixEnd_7889017 := by exact prefixLift 7889017
  have htrace : WordTrace (prefixWord ++ tailWord_7889017) baseStart_7889017 baseEnd_7889017 := by
    simpa [prefixWord, tailWord_7889017, baseEnd_7889017] using wordTrace_append hprefix tailTrace_7889017
  have hstable : (prefixWord ++ tailWord_7889017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889017).length < 2 ^ (prefixWord ++ tailWord_7889017).sum := by decide
  have hdescent : baseEnd_7889017 < baseStart_7889017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889048 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7889048 : Nat := 118140960795 + 7889048 * 2 ^ 59
def prefixEnd_7889048 : Nat := 4983230072969 + 3 ^ 40 * 7889048 * 2
def baseEnd_7889048 : Nat := 4050873530391155297118935

theorem tailTrace_7889048 : CollatzResearch.WordTrace tailWord_7889048 prefixEnd_7889048 4050873530391155297118935 := by
  unfold tailWord_7889048
  simp only [CollatzResearch.WordTrace]
  refine ⟨143868609561666956488061899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191824812748889275317415865 143868609561666956488061899)
  ·
    refine ⟨215802914342500434732092849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143868609561666956488061899 215802914342500434732092849)
    ·
      refine ⟨161852185756875326049069637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215802914342500434732092849 161852185756875326049069637)
      ·
        refine ⟨30347284829414123634200557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161852185756875326049069637 30347284829414123634200557)
        ·
          refine ⟨11380231811030296362825209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30347284829414123634200557 11380231811030296362825209)
          ·
            refine ⟨8535173858272722272118907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11380231811030296362825209 8535173858272722272118907)
            ·
              refine ⟨12802760787409083408178361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8535173858272722272118907 12802760787409083408178361)
              ·
                refine ⟨9602070590556812556133771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12802760787409083408178361 9602070590556812556133771)
                ·
                  refine ⟨14403105885835218834200657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9602070590556812556133771 14403105885835218834200657)
                  ·
                    refine ⟨10802329414376414125650493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14403105885835218834200657 10802329414376414125650493)
                    ·
                      refine ⟨4050873530391155297118935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10802329414376414125650493 4050873530391155297118935)
                      ·
                        rfl

theorem cell23_7889048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7889048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889048 prefixEnd_7889048 := by exact prefixLift 7889048
  have htrace : WordTrace (prefixWord ++ tailWord_7889048) baseStart_7889048 baseEnd_7889048 := by
    simpa [prefixWord, tailWord_7889048, baseEnd_7889048] using wordTrace_append hprefix tailTrace_7889048
  have hstable : (prefixWord ++ tailWord_7889048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889048).length < 2 ^ (prefixWord ++ tailWord_7889048).sum := by decide
  have hdescent : baseEnd_7889048 < baseStart_7889048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889135 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 2, 2, 2]
def baseStart_7889135 : Nat := 118140960795 + 7889135 * 2 ^ 59
def prefixEnd_7889135 : Nat := 4983230072969 + 3 ^ 40 * 7889135 * 2
def baseEnd_7889135 : Nat := 4050918203208096456731035

theorem tailTrace_7889135 : CollatzResearch.WordTrace tailWord_7889135 prefixEnd_7889135 4050918203208096456731035 := by
  unfold tailWord_7889135
  simp only [CollatzResearch.WordTrace]
  refine ⟨287740392274018726834540859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191826928182679151223027239 287740392274018726834540859)
  ·
    refine ⟨431610588411028090251811289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287740392274018726834540859 431610588411028090251811289)
    ·
      refine ⟨323707941308271067688858467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431610588411028090251811289 323707941308271067688858467)
      ·
        refine ⟨485561911962406601533287701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323707941308271067688858467 485561911962406601533287701)
        ·
          refine ⟨22760714623237809446872861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 485561911962406601533287701 22760714623237809446872861)
          ·
            refine ⟨8535267983714178542577323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22760714623237809446872861 8535267983714178542577323)
            ·
              refine ⟨12802901975571267813865985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8535267983714178542577323 12802901975571267813865985)
              ·
                refine ⟨9602176481678450860399489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12802901975571267813865985 9602176481678450860399489)
                ·
                  refine ⟨7201632361258838145299617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602176481678450860399489 7201632361258838145299617)
                  ·
                    refine ⟨5401224270944128608974713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201632361258838145299617 5401224270944128608974713)
                    ·
                      refine ⟨4050918203208096456731035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401224270944128608974713 4050918203208096456731035)
                      ·
                        rfl

theorem cell23_7889135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 2, 2].length) (baseStart_7889135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889135 prefixEnd_7889135 := by exact prefixLift 7889135
  have htrace : WordTrace (prefixWord ++ tailWord_7889135) baseStart_7889135 baseEnd_7889135 := by
    simpa [prefixWord, tailWord_7889135, baseEnd_7889135] using wordTrace_append hprefix tailTrace_7889135
  have hstable : (prefixWord ++ tailWord_7889135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889135).length < 2 ^ (prefixWord ++ tailWord_7889135).sum := by decide
  have hdescent : baseEnd_7889135 < baseStart_7889135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889144 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_7889144 : Nat := 118140960795 + 7889144 * 2 ^ 59
def prefixEnd_7889144 : Nat := 4983230072969 + 3 ^ 40 * 7889144 * 2
def baseEnd_7889144 : Nat := 4050922824533986921518493

theorem tailTrace_7889144 : CollatzResearch.WordTrace tailWord_7889144 prefixEnd_7889144 4050922824533986921518493 := by
  unfold tailWord_7889144
  simp only [CollatzResearch.WordTrace]
  refine ⟨143870360265493060685809243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191827147020657414247745657 143870360265493060685809243)
  ·
    refine ⟨215805540398239591028713865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143870360265493060685809243 215805540398239591028713865)
    ·
      refine ⟨161854155298679693271535399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215805540398239591028713865 161854155298679693271535399)
      ·
        refine ⟨242781232948019539907303099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161854155298679693271535399 242781232948019539907303099)
        ·
          refine ⟨364171849422029309860954649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242781232948019539907303099 364171849422029309860954649)
          ·
            refine ⟨273128887066521982395715987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364171849422029309860954649 273128887066521982395715987)
            ·
              refine ⟨409693330599782973593573981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273128887066521982395715987 409693330599782973593573981)
              ·
                refine ⟨153634998974918615097590243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409693330599782973593573981 153634998974918615097590243)
                ·
                  refine ⟨230452498462377922646385365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153634998974918615097590243 230452498462377922646385365)
                  ·
                    refine ⟨5401230432711982562024657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230452498462377922646385365 5401230432711982562024657)
                    ·
                      refine ⟨4050922824533986921518493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401230432711982562024657 4050922824533986921518493)
                      ·
                        rfl

theorem cell23_7889144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_7889144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889144 prefixEnd_7889144 := by exact prefixLift 7889144
  have htrace : WordTrace (prefixWord ++ tailWord_7889144) baseStart_7889144 baseEnd_7889144 := by
    simpa [prefixWord, tailWord_7889144, baseEnd_7889144] using wordTrace_append hprefix tailTrace_7889144
  have hstable : (prefixWord ++ tailWord_7889144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889144).length < 2 ^ (prefixWord ++ tailWord_7889144).sum := by decide
  have hdescent : baseEnd_7889144 < baseStart_7889144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889198 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7889198 : Nat := 118140960795 + 7889198 * 2 ^ 59
def prefixEnd_7889198 : Nat := 4983230072969 + 3 ^ 40 * 7889198 * 2
def baseEnd_7889198 : Nat := 4050950552489329710243245

theorem tailTrace_7889198 : CollatzResearch.WordTrace tailWord_7889198 prefixEnd_7889198 4050950552489329710243245 := by
  unfold tailWord_7889198
  simp only [CollatzResearch.WordTrace]
  refine ⟨35967836259098811074260531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191828460048526992396056165 35967836259098811074260531)
  ·
    refine ⟨53951754388648216611390797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35967836259098811074260531 53951754388648216611390797)
    ·
      refine ⟨20231907895743081229271549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53951754388648216611390797 20231907895743081229271549)
      ·
        refine ⟨7586965460903655460976831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20231907895743081229271549 7586965460903655460976831)
        ·
          refine ⟨11380448191355483191465247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7586965460903655460976831 11380448191355483191465247)
          ·
            refine ⟨17070672287033224787197871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11380448191355483191465247 17070672287033224787197871)
            ·
              refine ⟨25606008430549837180796807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17070672287033224787197871 25606008430549837180796807)
              ·
                refine ⟨38409012645824755771195211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25606008430549837180796807 38409012645824755771195211)
                ·
                  refine ⟨57613518968737133656792817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38409012645824755771195211 57613518968737133656792817)
                  ·
                    refine ⟨43210139226552850242594613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57613518968737133656792817 43210139226552850242594613)
                    ·
                      refine ⟨4050950552489329710243245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43210139226552850242594613 4050950552489329710243245)
                      ·
                        rfl

theorem cell23_7889198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7889198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889198 prefixEnd_7889198 := by exact prefixLift 7889198
  have htrace : WordTrace (prefixWord ++ tailWord_7889198) baseStart_7889198 baseEnd_7889198 := by
    simpa [prefixWord, tailWord_7889198, baseEnd_7889198] using wordTrace_append hprefix tailTrace_7889198
  have hstable : (prefixWord ++ tailWord_7889198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889198).length < 2 ^ (prefixWord ++ tailWord_7889198).sum := by decide
  have hdescent : baseEnd_7889198 < baseStart_7889198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889224 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_7889224 : Nat := 118140960795 + 7889224 * 2 ^ 59
def prefixEnd_7889224 : Nat := 4983230072969 + 3 ^ 40 * 7889224 * 2
def baseEnd_7889224 : Nat := 4050963902986346608518125

theorem tailTrace_7889224 : CollatzResearch.WordTrace tailWord_7889224 prefixEnd_7889224 4050963902986346608518125 := by
  unfold tailWord_7889224
  simp only [CollatzResearch.WordTrace]
  refine ⟨143871819185348147517265363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191829092247130863356353817 143871819185348147517265363)
  ·
    refine ⟨215807728778022221275898045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143871819185348147517265363 215807728778022221275898045)
    ·
      refine ⟨80927898291758332978461767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215807728778022221275898045 80927898291758332978461767)
      ·
        refine ⟨121391847437637499467692651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80927898291758332978461767 121391847437637499467692651)
        ·
          refine ⟨182087771156456249201538977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121391847437637499467692651 182087771156456249201538977)
          ·
            refine ⟨136565828367342186901154233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182087771156456249201538977 136565828367342186901154233)
            ·
              refine ⟨102424371275506640175865675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136565828367342186901154233 102424371275506640175865675)
              ·
                refine ⟨153636556913259960263798513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102424371275506640175865675 153636556913259960263798513)
                ·
                  refine ⟨115227417684944970197848885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153636556913259960263798513 115227417684944970197848885)
                  ·
                    refine ⟨10802570407963590956048333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115227417684944970197848885 10802570407963590956048333)
                    ·
                      refine ⟨4050963902986346608518125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10802570407963590956048333 4050963902986346608518125)
                      ·
                        rfl

theorem cell23_7889224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_7889224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889224 prefixEnd_7889224 := by exact prefixLift 7889224
  have htrace : WordTrace (prefixWord ++ tailWord_7889224) baseStart_7889224 baseEnd_7889224 := by
    simpa [prefixWord, tailWord_7889224, baseEnd_7889224] using wordTrace_append hprefix tailTrace_7889224
  have hstable : (prefixWord ++ tailWord_7889224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889224).length < 2 ^ (prefixWord ++ tailWord_7889224).sum := by decide
  have hdescent : baseEnd_7889224 < baseStart_7889224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889315 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 3, 2, 2]
def baseStart_7889315 : Nat := 118140960795 + 7889315 * 2 ^ 59
def prefixEnd_7889315 : Nat := 4983230072969 + 3 ^ 40 * 7889315 * 2
def baseEnd_7889315 : Nat := 4051010629725905752480207

theorem tailTrace_7889315 : CollatzResearch.WordTrace tailWord_7889315 prefixEnd_7889315 4051010629725905752480207 := by
  unfold tailWord_7889315
  simp only [CollatzResearch.WordTrace]
  refine ⟨287746957413366617576093399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191831304942244411717395599 287746957413366617576093399)
  ·
    refine ⟨431620436120049926364140099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287746957413366617576093399 431620436120049926364140099)
    ·
      refine ⟨647430654180074889546210149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431620436120049926364140099 647430654180074889546210149)
      ·
        refine ⟨121393247658764041789914403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 647430654180074889546210149 121393247658764041789914403)
        ·
          refine ⟨182089871488146062684871605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121393247658764041789914403 182089871488146062684871605)
          ·
            refine ⟨17070925452013693376706713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182089871488146062684871605 17070925452013693376706713)
            ·
              refine ⟨12803194089010270032530035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17070925452013693376706713 12803194089010270032530035)
              ·
                refine ⟨19204791133515405048795053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803194089010270032530035 19204791133515405048795053)
                ·
                  refine ⟨7201796675068276893298145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19204791133515405048795053 7201796675068276893298145)
                  ·
                    refine ⟨5401347506301207669973609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201796675068276893298145 5401347506301207669973609)
                    ·
                      refine ⟨4051010629725905752480207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401347506301207669973609 4051010629725905752480207)
                      ·
                        rfl

theorem cell23_7889315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_7889315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889315 prefixEnd_7889315 := by exact prefixLift 7889315
  have htrace : WordTrace (prefixWord ++ tailWord_7889315) baseStart_7889315 baseEnd_7889315 := by
    simpa [prefixWord, tailWord_7889315, baseEnd_7889315] using wordTrace_append hprefix tailTrace_7889315
  have hstable : (prefixWord ++ tailWord_7889315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889315).length < 2 ^ (prefixWord ++ tailWord_7889315).sum := by decide
  have hdescent : baseEnd_7889315 < baseStart_7889315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889325 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_7889325 : Nat := 118140960795 + 7889325 * 2 ^ 59
def prefixEnd_7889325 : Nat := 4983230072969 + 3 ^ 40 * 7889325 * 2
def baseEnd_7889325 : Nat := 1350338588177483571118387

theorem tailTrace_7889325 : CollatzResearch.WordTrace tailWord_7889325 prefixEnd_7889325 1350338588177483571118387 := by
  unfold tailWord_7889325
  simp only [CollatzResearch.WordTrace]
  refine ⟨287747322143330389283957429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191831548095553592855971619 287747322143330389283957429)
  ·
    refine ⟨26976311450937223995371009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 287747322143330389283957429 26976311450937223995371009)
    ·
      refine ⟨20232233588202917996528257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26976311450937223995371009 20232233588202917996528257)
      ·
        refine ⟨15174175191152188497396193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20232233588202917996528257 15174175191152188497396193)
        ·
          refine ⟨11380631393364141373047145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15174175191152188497396193 11380631393364141373047145)
          ·
            refine ⟨8535473545023106029785359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11380631393364141373047145 8535473545023106029785359)
            ·
              refine ⟨12803210317534659044678039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8535473545023106029785359 12803210317534659044678039)
              ·
                refine ⟨19204815476301988567017059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803210317534659044678039 19204815476301988567017059)
                ·
                  refine ⟨28807223214452982850525589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204815476301988567017059 28807223214452982850525589)
                  ·
                    refine ⟨1350338588177483571118387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28807223214452982850525589 1350338588177483571118387)
                    ·
                      rfl

theorem cell23_7889325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_7889325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889325 prefixEnd_7889325 := by exact prefixLift 7889325
  have htrace : WordTrace (prefixWord ++ tailWord_7889325) baseStart_7889325 baseEnd_7889325 := by
    simpa [prefixWord, tailWord_7889325, baseEnd_7889325] using wordTrace_append hprefix tailTrace_7889325
  have hstable : (prefixWord ++ tailWord_7889325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889325).length < 2 ^ (prefixWord ++ tailWord_7889325).sum := by decide
  have hdescent : baseEnd_7889325 < baseStart_7889325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889358 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_7889358 : Nat := 118140960795 + 7889358 * 2 ^ 59
def prefixEnd_7889358 : Nat := 4983230072969 + 3 ^ 40 * 7889358 * 2
def baseEnd_7889358 : Nat := 4051032709394049084242509

theorem tailTrace_7889358 : CollatzResearch.WordTrace tailWord_7889358 prefixEnd_7889358 4051032709394049084242509 := by
  unfold tailWord_7889358
  simp only [CollatzResearch.WordTrace]
  refine ⟨35968565719026354489988591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191832350501473890613272485 35968565719026354489988591)
  ·
    refine ⟨53952848578539531734982887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35968565719026354489988591 53952848578539531734982887)
    ·
      refine ⟨80929272867809297602474331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53952848578539531734982887 80929272867809297602474331)
      ·
        refine ⟨121393909301713946403711497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80929272867809297602474331 121393909301713946403711497)
        ·
          refine ⟨91045431976285459802783623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121393909301713946403711497 91045431976285459802783623)
          ·
            refine ⟨136568147964428189704175435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91045431976285459802783623 136568147964428189704175435)
            ·
              refine ⟨204852221946642284556263153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136568147964428189704175435 204852221946642284556263153)
              ·
                refine ⟨153639166459981713417197365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204852221946642284556263153 153639166459981713417197365)
                ·
                  refine ⟨14403671855623285632862253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153639166459981713417197365 14403671855623285632862253)
                  ·
                    refine ⟨5401376945858732112323345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14403671855623285632862253 5401376945858732112323345)
                    ·
                      refine ⟨4051032709394049084242509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401376945858732112323345 4051032709394049084242509)
                      ·
                        rfl

theorem cell23_7889358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_7889358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889358 prefixEnd_7889358 := by exact prefixLift 7889358
  have htrace : WordTrace (prefixWord ++ tailWord_7889358) baseStart_7889358 baseEnd_7889358 := by
    simpa [prefixWord, tailWord_7889358, baseEnd_7889358] using wordTrace_append hprefix tailTrace_7889358
  have hstable : (prefixWord ++ tailWord_7889358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889358).length < 2 ^ (prefixWord ++ tailWord_7889358).sum := by decide
  have hdescent : baseEnd_7889358 < baseStart_7889358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889366 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7889366 : Nat := 118140960795 + 7889366 * 2 ^ 59
def prefixEnd_7889366 : Nat := 4983230072969 + 3 ^ 40 * 7889366 * 2
def baseEnd_7889366 : Nat := 4051036817239285052942473

theorem tailTrace_7889366 : CollatzResearch.WordTrace tailWord_7889366 prefixEnd_7889366 4051036817239285052942473 := by
  unfold tailWord_7889366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984301096011365830387497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191832545024121235524133301 17984301096011365830387497)
  ·
    refine ⟨13488225822008524372790623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17984301096011365830387497 13488225822008524372790623)
    ·
      refine ⟨20232338733012786559185935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13488225822008524372790623 20232338733012786559185935)
      ·
        refine ⟨30348508099519179838778903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232338733012786559185935 30348508099519179838778903)
        ·
          refine ⟨45522762149278769758168355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30348508099519179838778903 45522762149278769758168355)
          ·
            refine ⟨68284143223918154637252533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45522762149278769758168355 68284143223918154637252533)
            ·
              refine ⟨6401638427242326997242425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68284143223918154637252533 6401638427242326997242425)
              ·
                refine ⟨4801228820431745247931819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401638427242326997242425 4801228820431745247931819)
                ·
                  refine ⟨7201843230647617871897729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801228820431745247931819 7201843230647617871897729)
                  ·
                    refine ⟨5401382422985713403923297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201843230647617871897729 5401382422985713403923297)
                    ·
                      refine ⟨4051036817239285052942473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401382422985713403923297 4051036817239285052942473)
                      ·
                        rfl

theorem cell23_7889366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7889366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889366 prefixEnd_7889366 := by exact prefixLift 7889366
  have htrace : WordTrace (prefixWord ++ tailWord_7889366) baseStart_7889366 baseEnd_7889366 := by
    simpa [prefixWord, tailWord_7889366, baseEnd_7889366] using wordTrace_append hprefix tailTrace_7889366
  have hstable : (prefixWord ++ tailWord_7889366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889366).length < 2 ^ (prefixWord ++ tailWord_7889366).sum := by decide
  have hdescent : baseEnd_7889366 < baseStart_7889366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889388 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_7889388 : Nat := 118140960795 + 7889388 * 2 ^ 59
def prefixEnd_7889388 : Nat := 4983230072969 + 3 ^ 40 * 7889388 * 2
def baseEnd_7889388 : Nat := 4051048113813683966867371

theorem tailTrace_7889388 : CollatzResearch.WordTrace tailWord_7889388 prefixEnd_7889388 4051048113813683966867371 := by
  unfold tailWord_7889388
  simp only [CollatzResearch.WordTrace]
  refine ⟨143874809971051075521750409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191833079961401434029000545 143874809971051075521750409)
  ·
    refine ⟨107906107478288306641312807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143874809971051075521750409 107906107478288306641312807)
    ·
      refine ⟨161859161217432459961969211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107906107478288306641312807 161859161217432459961969211)
      ·
        refine ⟨242788741826148689942953817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161859161217432459961969211 242788741826148689942953817)
        ·
          refine ⟨182091556369611517457215363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242788741826148689942953817 182091556369611517457215363)
          ·
            refine ⟨273137334554417276185823045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182091556369611517457215363 273137334554417276185823045)
            ·
              refine ⟨51213250228953239284841821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273137334554417276185823045 51213250228953239284841821)
              ·
                refine ⟨19204968835857464731815683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51213250228953239284841821 19204968835857464731815683)
                ·
                  refine ⟨28807453253786197097723525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19204968835857464731815683 28807453253786197097723525)
                  ·
                    refine ⟨5401397485084911955823161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28807453253786197097723525 5401397485084911955823161)
                    ·
                      refine ⟨4051048113813683966867371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401397485084911955823161 4051048113813683966867371)
                      ·
                        rfl

theorem cell23_7889388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_7889388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889388 prefixEnd_7889388 := by exact prefixLift 7889388
  have htrace : WordTrace (prefixWord ++ tailWord_7889388) baseStart_7889388 baseEnd_7889388 := by
    simpa [prefixWord, tailWord_7889388, baseEnd_7889388] using wordTrace_append hprefix tailTrace_7889388
  have hstable : (prefixWord ++ tailWord_7889388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889388).length < 2 ^ (prefixWord ++ tailWord_7889388).sum := by decide
  have hdescent : baseEnd_7889388 < baseStart_7889388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889422 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7889422 : Nat := 118140960795 + 7889422 * 2 ^ 59
def prefixEnd_7889422 : Nat := 4983230072969 + 3 ^ 40 * 7889422 * 2
def baseEnd_7889422 : Nat := 4051065572155936833842215

theorem tailTrace_7889422 : CollatzResearch.WordTrace tailWord_7889422 prefixEnd_7889422 4051065572155936833842215 := by
  unfold tailWord_7889422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35968857502997371856279815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191833906682652649900159013 35968857502997371856279815)
  ·
    refine ⟨53953286254496057784419723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35968857502997371856279815 53953286254496057784419723)
    ·
      refine ⟨80929929381744086676629585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53953286254496057784419723 80929929381744086676629585)
      ·
        refine ⟨60697447036308065007472189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80929929381744086676629585 60697447036308065007472189)
        ·
          refine ⟨22761542638615524377802071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60697447036308065007472189 22761542638615524377802071)
          ·
            refine ⟨34142313957923286566703107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22761542638615524377802071 34142313957923286566703107)
            ·
              refine ⟨51213470936884929850054661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34142313957923286566703107 51213470936884929850054661)
              ·
                refine ⟨9602525800665924346885249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51213470936884929850054661 9602525800665924346885249)
                ·
                  refine ⟨7201894350499443260163937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602525800665924346885249 7201894350499443260163937)
                  ·
                    refine ⟨5401420762874582445122953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201894350499443260163937 5401420762874582445122953)
                    ·
                      refine ⟨4051065572155936833842215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401420762874582445122953 4051065572155936833842215)
                      ·
                        rfl

theorem cell23_7889422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7889422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889422 prefixEnd_7889422 := by exact prefixLift 7889422
  have htrace : WordTrace (prefixWord ++ tailWord_7889422) baseStart_7889422 baseEnd_7889422 := by
    simpa [prefixWord, tailWord_7889422, baseEnd_7889422] using wordTrace_append hprefix tailTrace_7889422
  have hstable : (prefixWord ++ tailWord_7889422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889422).length < 2 ^ (prefixWord ++ tailWord_7889422).sum := by decide
  have hdescent : baseEnd_7889422 < baseStart_7889422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889441 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_7889441 : Nat := 118140960795 + 7889441 * 2 ^ 59
def prefixEnd_7889441 : Nat := 4983230072969 + 3 ^ 40 * 7889441 * 2
def baseEnd_7889441 : Nat := 1350358442762790753168209

theorem tailTrace_7889441 : CollatzResearch.WordTrace tailWord_7889441 prefixEnd_7889441 1350358442762790753168209 := by
  unfold tailWord_7889441
  simp only [CollatzResearch.WordTrace]
  refine ⟨287751553010910141095180177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191834368673940094063453451 287751553010910141095180177)
  ·
    refine ⟨215813664758182605821385133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287751553010910141095180177 215813664758182605821385133)
    ·
      refine ⟨80930124284318477183019425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215813664758182605821385133 80930124284318477183019425)
      ·
        refine ⟨60697593213238857887264569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80930124284318477183019425 60697593213238857887264569)
        ·
          refine ⟨45523194909929143415448427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60697593213238857887264569 45523194909929143415448427)
          ·
            refine ⟨68284792364893715123172641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45523194909929143415448427 68284792364893715123172641)
            ·
              refine ⟨51213594273670286342379481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68284792364893715123172641 51213594273670286342379481)
              ·
                refine ⟨38410195705252714756784611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51213594273670286342379481 38410195705252714756784611)
                ·
                  refine ⟨57615293557879072135176917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38410195705252714756784611 57615293557879072135176917)
                  ·
                    refine ⟨1350358442762790753168209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57615293557879072135176917 1350358442762790753168209)
                    ·
                      rfl

theorem cell23_7889441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_7889441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889441 prefixEnd_7889441 := by exact prefixLift 7889441
  have htrace : WordTrace (prefixWord ++ tailWord_7889441) baseStart_7889441 baseEnd_7889441 := by
    simpa [prefixWord, tailWord_7889441, baseEnd_7889441] using wordTrace_append hprefix tailTrace_7889441
  have hstable : (prefixWord ++ tailWord_7889441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889441).length < 2 ^ (prefixWord ++ tailWord_7889441).sum := by decide
  have hdescent : baseEnd_7889441 < baseStart_7889441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889458 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_7889458 : Nat := 118140960795 + 7889458 * 2 ^ 59
def prefixEnd_7889458 : Nat := 4983230072969 + 3 ^ 40 * 7889458 * 2
def baseEnd_7889458 : Nat := 1350361352486499564330683

theorem tailTrace_7889458 : CollatzResearch.WordTrace tailWord_7889458 prefixEnd_7889458 1350361352486499564330683 := by
  unfold tailWord_7889458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71938043262962138249637257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191834782034565701999032685 71938043262962138249637257)
  ·
    refine ⟨53953532447221603687227943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71938043262962138249637257 53953532447221603687227943)
    ·
      refine ⟨80930298670832405530841915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53953532447221603687227943 80930298670832405530841915)
      ·
        refine ⟨121395448006248608296262873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80930298670832405530841915 121395448006248608296262873)
        ·
          refine ⟨91046586004686456222197155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121395448006248608296262873 91046586004686456222197155)
          ·
            refine ⟨136569879007029684333295733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91046586004686456222197155 136569879007029684333295733)
            ·
              refine ⟨12803426156909032906246475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136569879007029684333295733 12803426156909032906246475)
              ·
                refine ⟨19205139235363549359369713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803426156909032906246475 19205139235363549359369713)
                ·
                  refine ⟨14403854426522662019527285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19205139235363549359369713 14403854426522662019527285)
                  ·
                    refine ⟨1350361352486499564330683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14403854426522662019527285 1350361352486499564330683)
                    ·
                      rfl

theorem cell23_7889458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_7889458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889458 prefixEnd_7889458 := by exact prefixLift 7889458
  have htrace : WordTrace (prefixWord ++ tailWord_7889458) baseStart_7889458 baseEnd_7889458 := by
    simpa [prefixWord, tailWord_7889458, baseEnd_7889458] using wordTrace_append hprefix tailTrace_7889458
  have hstable : (prefixWord ++ tailWord_7889458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889458).length < 2 ^ (prefixWord ++ tailWord_7889458).sum := by decide
  have hdescent : baseEnd_7889458 < baseStart_7889458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889462 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7889462 : Nat := 118140960795 + 7889462 * 2 ^ 59
def prefixEnd_7889462 : Nat := 4983230072969 + 3 ^ 40 * 7889462 * 2
def baseEnd_7889462 : Nat := 450120679042457408593559

theorem tailTrace_7889462 : CollatzResearch.WordTrace tailWord_7889462 prefixEnd_7889462 450120679042457408593559 := by
  unfold tailWord_7889462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984519933989628855105915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191834879295889374454463093 17984519933989628855105915)
  ·
    refine ⟨26976779900984443282658873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984519933989628855105915 26976779900984443282658873)
    ·
      refine ⟨20232584925738332461994155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26976779900984443282658873 20232584925738332461994155)
      ·
        refine ⟨30348877388607498692991233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20232584925738332461994155 30348877388607498692991233)
        ·
          refine ⟨22761658041455624019743425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30348877388607498692991233 22761658041455624019743425)
          ·
            refine ⟨17071243531091718014807569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22761658041455624019743425 17071243531091718014807569)
            ·
              refine ⟨12803432648318788511105677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17071243531091718014807569 12803432648318788511105677)
              ·
                refine ⟨4801287243119545691664629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12803432648318788511105677 4801287243119545691664629)
                ·
                  refine ⟨450120679042457408593559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801287243119545691664629 450120679042457408593559)
                  ·
                    rfl

theorem cell23_7889462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7889462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889462 prefixEnd_7889462 := by exact prefixLift 7889462
  have htrace : WordTrace (prefixWord ++ tailWord_7889462) baseStart_7889462 baseEnd_7889462 := by
    simpa [prefixWord, tailWord_7889462, baseEnd_7889462] using wordTrace_append hprefix tailTrace_7889462
  have hstable : (prefixWord ++ tailWord_7889462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889462).length < 2 ^ (prefixWord ++ tailWord_7889462).sum := by decide
  have hdescent : baseEnd_7889462 < baseStart_7889462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889518 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_7889518 : Nat := 118140960795 + 7889518 * 2 ^ 59
def prefixEnd_7889518 : Nat := 4983230072969 + 3 ^ 40 * 7889518 * 2
def baseEnd_7889518 : Nat := 450123874033196495360197

theorem tailTrace_7889518 : CollatzResearch.WordTrace tailWord_7889518 prefixEnd_7889518 450123874033196495360197 := by
  unfold tailWord_7889518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35969295178953897905716651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 191836240954420788830488805 35969295178953897905716651)
  ·
    refine ⟨53953942768430846858574977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35969295178953897905716651 53953942768430846858574977)
    ·
      refine ⟨40465457076323135143931233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53953942768430846858574977 40465457076323135143931233)
      ·
        refine ⟨30349092807242351357948425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40465457076323135143931233 30349092807242351357948425)
        ·
          refine ⟨22761819605431763518461319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30349092807242351357948425 22761819605431763518461319)
          ·
            refine ⟨34142729408147645277691979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22761819605431763518461319 34142729408147645277691979)
            ·
              refine ⟨51214094112221467916537969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34142729408147645277691979 51214094112221467916537969)
              ·
                refine ⟨38410570584166100937403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51214094112221467916537969 38410570584166100937403477)
                ·
                  refine ⟨450123874033196495360197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38410570584166100937403477 450123874033196495360197)
                  ·
                    rfl

theorem cell23_7889518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_7889518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889518 prefixEnd_7889518 := by exact prefixLift 7889518
  have htrace : WordTrace (prefixWord ++ tailWord_7889518) baseStart_7889518 baseEnd_7889518 := by
    simpa [prefixWord, tailWord_7889518, baseEnd_7889518] using wordTrace_append hprefix tailTrace_7889518
  have hstable : (prefixWord ++ tailWord_7889518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889518).length < 2 ^ (prefixWord ++ tailWord_7889518).sum := by decide
  have hdescent : baseEnd_7889518 < baseStart_7889518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889565 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7889565 : Nat := 118140960795 + 7889565 * 2 ^ 59
def prefixEnd_7889565 : Nat := 4983230072969 + 3 ^ 40 * 7889565 * 2
def baseEnd_7889565 : Nat := 1350379666629843258118019

theorem tailTrace_7889565 : CollatzResearch.WordTrace tailWord_7889565 prefixEnd_7889565 1350379666629843258118019 := by
  unfold tailWord_7889565
  simp only [CollatzResearch.WordTrace]
  refine ⟨287756075662460910272694149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191837383774973940181796099 287756075662460910272694149)
  ·
    refine ⟨53954264186711420676130153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 287756075662460910272694149 53954264186711420676130153)
    ·
      refine ⟨40465698140033565507097615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53954264186711420676130153 40465698140033565507097615)
      ·
        refine ⟨60698547210050348260646423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40465698140033565507097615 60698547210050348260646423)
        ·
          refine ⟨91047820815075522390969635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60698547210050348260646423 91047820815075522390969635)
          ·
            refine ⟨136571731222613283586454453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91047820815075522390969635 136571731222613283586454453)
            ·
              refine ⟨12803599802119995336230105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136571731222613283586454453 12803599802119995336230105)
              ·
                refine ⟨9602699851589996502172579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12803599802119995336230105 9602699851589996502172579)
                ·
                  refine ⟨14404049777384994753258869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9602699851589996502172579 14404049777384994753258869)
                  ·
                    refine ⟨1350379666629843258118019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14404049777384994753258869 1350379666629843258118019)
                    ·
                      rfl

theorem cell23_7889565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7889565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889565 prefixEnd_7889565 := by exact prefixLift 7889565
  have htrace : WordTrace (prefixWord ++ tailWord_7889565) baseStart_7889565 baseEnd_7889565 := by
    simpa [prefixWord, tailWord_7889565, baseEnd_7889565] using wordTrace_append hprefix tailTrace_7889565
  have hstable : (prefixWord ++ tailWord_7889565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889565).length < 2 ^ (prefixWord ++ tailWord_7889565).sum := by decide
  have hdescent : baseEnd_7889565 < baseStart_7889565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889572 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_7889572 : Nat := 118140960795 + 7889572 * 2 ^ 59
def prefixEnd_7889572 : Nat := 4983230072969 + 3 ^ 40 * 7889572 * 2
def baseEnd_7889572 : Nat := 4051142594254111246966525

theorem tailTrace_7889572 : CollatzResearch.WordTrace tailWord_7889572 prefixEnd_7889572 4051142594254111246966525 := by
  unfold tailWord_7889572
  simp only [CollatzResearch.WordTrace]
  refine ⟨143878165486717775234099485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191837553982290366978799313 143878165486717775234099485)
  ·
    refine ⟨53954312057519165712787307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143878165486717775234099485 53954312057519165712787307)
    ·
      refine ⟨80931468086278748569180961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53954312057519165712787307 80931468086278748569180961)
      ·
        refine ⟨60698601064709061426885721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80931468086278748569180961 60698601064709061426885721)
        ·
          refine ⟨45523950798531796070164291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60698601064709061426885721 45523950798531796070164291)
          ·
            refine ⟨68285926197797694105246437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45523950798531796070164291 68285926197797694105246437)
            ·
              refine ⟨12803611162087067644733707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68285926197797694105246437 12803611162087067644733707)
              ·
                refine ⟨19205416743130601467100561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12803611162087067644733707 19205416743130601467100561)
                ·
                  refine ⟨14404062557347951100325421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19205416743130601467100561 14404062557347951100325421)
                  ·
                    refine ⟨5401523459005481662622033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14404062557347951100325421 5401523459005481662622033)
                    ·
                      refine ⟨4051142594254111246966525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401523459005481662622033 4051142594254111246966525)
                      ·
                        rfl

theorem cell23_7889572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_7889572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889572 prefixEnd_7889572 := by exact prefixLift 7889572
  have htrace : WordTrace (prefixWord ++ tailWord_7889572) baseStart_7889572 baseEnd_7889572 := by
    simpa [prefixWord, tailWord_7889572, baseEnd_7889572] using wordTrace_append hprefix tailTrace_7889572
  have hstable : (prefixWord ++ tailWord_7889572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889572).length < 2 ^ (prefixWord ++ tailWord_7889572).sum := by decide
  have hdescent : baseEnd_7889572 < baseStart_7889572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889590 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7889590 : Nat := 118140960795 + 7889590 * 2 ^ 59
def prefixEnd_7889590 : Nat := 4983230072969 + 3 ^ 40 * 7889590 * 2
def baseEnd_7889590 : Nat := 1350383945635297392180481

theorem tailTrace_7889590 : CollatzResearch.WordTrace tailWord_7889590 prefixEnd_7889590 1350383945635297392180481 := by
  unfold tailWord_7889590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984811717960646221397139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 191837991658246893028236149 17984811717960646221397139)
  ·
    refine ⟨26977217576940969332095709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984811717960646221397139 26977217576940969332095709)
    ·
      refine ⟨10116456591352863499535891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26977217576940969332095709 10116456591352863499535891)
      ·
        refine ⟨15174684887029295249303837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10116456591352863499535891 15174684887029295249303837)
        ·
          refine ⟨5690506832635985718488939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15174684887029295249303837 5690506832635985718488939)
          ·
            refine ⟨8535760248953978577733409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690506832635985718488939 8535760248953978577733409)
            ·
              refine ⟨6401820186715483933300057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8535760248953978577733409 6401820186715483933300057)
              ·
                refine ⟨4801365140036612949975043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6401820186715483933300057 4801365140036612949975043)
                ·
                  refine ⟨7202047710054919424962565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801365140036612949975043 7202047710054919424962565)
                  ·
                    refine ⟨1350383945635297392180481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202047710054919424962565 1350383945635297392180481)
                    ·
                      rfl

theorem cell23_7889590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7889590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889590 prefixEnd_7889590 := by exact prefixLift 7889590
  have htrace : WordTrace (prefixWord ++ tailWord_7889590) baseStart_7889590 baseEnd_7889590 := by
    simpa [prefixWord, tailWord_7889590, baseEnd_7889590] using wordTrace_append hprefix tailTrace_7889590
  have hstable : (prefixWord ++ tailWord_7889590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889590).length < 2 ^ (prefixWord ++ tailWord_7889590).sum := by decide
  have hdescent : baseEnd_7889590 < baseStart_7889590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889591 : List Nat := [1, 1, 3, 1, 17]
def baseStart_7889591 : Nat := 118140960795 + 7889591 * 2 ^ 59
def prefixEnd_7889591 : Nat := 4983230072969 + 3 ^ 40 * 7889591 * 2
def baseEnd_7889591 : Nat := 5557136283109117520753

theorem tailTrace_7889591 : CollatzResearch.WordTrace tailWord_7889591 prefixEnd_7889591 5557136283109117520753 := by
  unfold tailWord_7889591
  simp only [CollatzResearch.WordTrace]
  refine ⟨287757023960366716713140627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191838015973577811142093751 287757023960366716713140627)
  ·
    refine ⟨431635535940550075069710941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287757023960366716713140627 431635535940550075069710941)
    ·
      refine ⟨161863325977706278151141603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431635535940550075069710941 161863325977706278151141603)
      ·
        refine ⟨242794988966559417226712405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161863325977706278151141603 242794988966559417226712405)
        ·
          refine ⟨5557136283109117520753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 242794988966559417226712405 5557136283109117520753)
          ·
            rfl

theorem cell23_7889591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 17].length) (baseStart_7889591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889591 prefixEnd_7889591 := by exact prefixLift 7889591
  have htrace : WordTrace (prefixWord ++ tailWord_7889591) baseStart_7889591 baseEnd_7889591 := by
    simpa [prefixWord, tailWord_7889591, baseEnd_7889591] using wordTrace_append hprefix tailTrace_7889591
  have hstable : (prefixWord ++ tailWord_7889591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889591).length < 2 ^ (prefixWord ++ tailWord_7889591).sum := by decide
  have hdescent : baseEnd_7889591 < baseStart_7889591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889608 : List Nat := [2, 1, 3, 1, 2, 3, 3, 8]
def baseStart_7889608 : Nat := 118140960795 + 7889608 * 2 ^ 59
def prefixEnd_7889608 : Nat := 4983230072969 + 3 ^ 40 * 7889608 * 2
def baseEnd_7889608 : Nat := 150043002946580485411717

theorem tailTrace_7889608 : CollatzResearch.WordTrace tailWord_7889608 prefixEnd_7889608 150043002946580485411717 := by
  unfold tailWord_7889608
  simp only [CollatzResearch.WordTrace]
  refine ⟨143878822000652564308254739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191838429334203419077672985 143878822000652564308254739)
  ·
    refine ⟨215818233000978846462382109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143878822000652564308254739 215818233000978846462382109)
    ·
      refine ⟨80931837375367067423393291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215818233000978846462382109 80931837375367067423393291)
      ·
        refine ⟨121397756063050601135089937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80931837375367067423393291 121397756063050601135089937)
        ·
          refine ⟨91048317047287950851317453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121397756063050601135089937 91048317047287950851317453)
          ·
            refine ⟨34143118892732981569244045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91048317047287950851317453 34143118892732981569244045)
            ·
              refine ⟨12803669584774868088466517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34143118892732981569244045 12803669584774868088466517)
              ·
                refine ⟨150043002946580485411717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12803669584774868088466517 150043002946580485411717)
                ·
                  rfl

theorem cell23_7889608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 8].length) (baseStart_7889608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889608 prefixEnd_7889608 := by exact prefixLift 7889608
  have htrace : WordTrace (prefixWord ++ tailWord_7889608) baseStart_7889608 baseEnd_7889608 := by
    simpa [prefixWord, tailWord_7889608, baseEnd_7889608] using wordTrace_append hprefix tailTrace_7889608
  have hstable : (prefixWord ++ tailWord_7889608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889608).length < 2 ^ (prefixWord ++ tailWord_7889608).sum := by decide
  have hdescent : baseEnd_7889608 < baseStart_7889608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889612 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_7889612 : Nat := 118140960795 + 7889612 * 2 ^ 59
def prefixEnd_7889612 : Nat := 4983230072969 + 3 ^ 40 * 7889612 * 2
def baseEnd_7889612 : Nat := 1350387711160097030155447

theorem tailTrace_7889612 : CollatzResearch.WordTrace tailWord_7889612 prefixEnd_7889612 1350387711160097030155447 := by
  unfold tailWord_7889612
  simp only [CollatzResearch.WordTrace]
  refine ⟨143878894946645318649827545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191838526595527091533103393 143878894946645318649827545)
  ·
    refine ⟨107909171209983988987370659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143878894946645318649827545 107909171209983988987370659)
    ·
      refine ⟨161863756814975983481055989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107909171209983988987370659 161863756814975983481055989)
      ·
        refine ⟨15174727201403998451348999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161863756814975983481055989 15174727201403998451348999)
        ·
          refine ⟨22762090802105997677023499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15174727201403998451348999 22762090802105997677023499)
          ·
            refine ⟨34143136203158996515535249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22762090802105997677023499 34143136203158996515535249)
            ·
              refine ⟨25607352152369247386651437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34143136203158996515535249 25607352152369247386651437)
              ·
                refine ⟨9602757057138467769994289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25607352152369247386651437 9602757057138467769994289)
                ·
                  refine ⟨7202067792853850827495717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9602757057138467769994289 7202067792853850827495717)
                  ·
                    refine ⟨1350387711160097030155447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7202067792853850827495717 1350387711160097030155447)
                    ·
                      rfl

theorem cell23_7889612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_7889612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889612 prefixEnd_7889612 := by exact prefixLift 7889612
  have htrace : WordTrace (prefixWord ++ tailWord_7889612) baseStart_7889612 baseEnd_7889612 := by
    simpa [prefixWord, tailWord_7889612, baseEnd_7889612] using wordTrace_append hprefix tailTrace_7889612
  have hstable : (prefixWord ++ tailWord_7889612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889612).length < 2 ^ (prefixWord ++ tailWord_7889612).sum := by decide
  have hdescent : baseEnd_7889612 < baseStart_7889612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889636 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_7889636 : Nat := 118140960795 + 7889636 * 2 ^ 59
def prefixEnd_7889636 : Nat := 4983230072969 + 3 ^ 40 * 7889636 * 2
def baseEnd_7889636 : Nat := 4051175457015998996566231

theorem tailTrace_7889636 : CollatzResearch.WordTrace tailWord_7889636 prefixEnd_7889636 4051175457015998996566231 := by
  unfold tailWord_7889636
  simp only [CollatzResearch.WordTrace]
  refine ⟨143879332622601844699264381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191839110163469126265685841 143879332622601844699264381)
  ·
    refine ⟨53954749733475691762224143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143879332622601844699264381 53954749733475691762224143)
    ·
      refine ⟨80932124600213537643336215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53954749733475691762224143 80932124600213537643336215)
      ·
        refine ⟨121398186900320306465004323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80932124600213537643336215 121398186900320306465004323)
        ·
          refine ⟨182097280350480459697506485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121398186900320306465004323 182097280350480459697506485)
          ·
            refine ⟨17071620032857543096641233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182097280350480459697506485 17071620032857543096641233)
            ·
              refine ⟨12803715024643157322480925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17071620032857543096641233 12803715024643157322480925)
              ·
                refine ⟨4801393134241183995930347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12803715024643157322480925 4801393134241183995930347)
                ·
                  refine ⟨7202089701361775993895521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801393134241183995930347 7202089701361775993895521)
                  ·
                    refine ⟨5401567276021331995421641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7202089701361775993895521 5401567276021331995421641)
                    ·
                      refine ⟨4051175457015998996566231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5401567276021331995421641 4051175457015998996566231)
                      ·
                        rfl

theorem cell23_7889636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_7889636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889636 prefixEnd_7889636 := by exact prefixLift 7889636
  have htrace : WordTrace (prefixWord ++ tailWord_7889636) baseStart_7889636 baseEnd_7889636 := by
    simpa [prefixWord, tailWord_7889636, baseEnd_7889636] using wordTrace_append hprefix tailTrace_7889636
  have hstable : (prefixWord ++ tailWord_7889636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889636).length < 2 ^ (prefixWord ++ tailWord_7889636).sum := by decide
  have hdescent : baseEnd_7889636 < baseStart_7889636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7889658 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_7889658 : Nat := 118140960795 + 7889658 * 2 ^ 59
def prefixEnd_7889658 : Nat := 4983230072969 + 3 ^ 40 * 7889658 * 2
def baseEnd_7889658 : Nat := 4051186753590397910491129

theorem tailTrace_7889658 : CollatzResearch.WordTrace tailWord_7889658 prefixEnd_7889658 4051186753590397910491129 := by
  unfold tailWord_7889658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71939866912780996788957407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 191839645100749324770553085 71939866912780996788957407)
  ·
    refine ⟨107909800369171495183436111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71939866912780996788957407 107909800369171495183436111)
    ·
      refine ⟨161864700553757242775154167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107909800369171495183436111 161864700553757242775154167)
      ·
        refine ⟨242797050830635864162731251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161864700553757242775154167 242797050830635864162731251)
        ·
          refine ⟨364195576245953796244096877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242797050830635864162731251 364195576245953796244096877)
          ·
            refine ⟨136573341092232673591536329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364195576245953796244096877 136573341092232673591536329)
            ·
              refine ⟨102430005819174505193652247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136573341092232673591536329 102430005819174505193652247)
              ·
                refine ⟨153645008728761757790478371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102430005819174505193652247 153645008728761757790478371)
                ·
                  refine ⟨230467513093142636685717557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153645008728761757790478371 230467513093142636685717557)
                  ·
                    refine ⟨21606329352482122189286021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230467513093142636685717557 21606329352482122189286021)
                    ·
                      refine ⟨4051186753590397910491129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21606329352482122189286021 4051186753590397910491129)
                      ·
                        rfl

theorem cell23_7889658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_7889658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7889658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7889658 prefixEnd_7889658 := by exact prefixLift 7889658
  have htrace : WordTrace (prefixWord ++ tailWord_7889658) baseStart_7889658 baseEnd_7889658 := by
    simpa [prefixWord, tailWord_7889658, baseEnd_7889658] using wordTrace_append hprefix tailTrace_7889658
  have hstable : (prefixWord ++ tailWord_7889658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7889658).length < 2 ^ (prefixWord ++ tailWord_7889658).sum := by decide
  have hdescent : baseEnd_7889658 < baseStart_7889658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7889658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
