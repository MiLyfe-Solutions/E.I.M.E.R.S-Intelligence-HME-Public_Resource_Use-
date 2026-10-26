import V185TrunkScan23Chunk1035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6133523 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 7, 2]
def baseStart_6133523 : Nat := 118140960795 + 6133523 * 2 ^ 59
def prefixEnd_6133523 : Nat := 4983230072969 + 3 ^ 40 * 6133523 * 2
def baseEnd_6133523 : Nat := 3149445404406911296754947

theorem tailTrace_6133523 : CollatzResearch.WordTrace tailWord_6133523 prefixEnd_6133523 3149445404406911296754947 := by
  unfold tailWord_6133523
  simp only [CollatzResearch.WordTrace]
  refine ⟨223707962158301168175997223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149138641438867445450664815 223707962158301168175997223)
  ·
    refine ⟨335561943237451752263995835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223707962158301168175997223 335561943237451752263995835)
    ·
      refine ⟨503342914856177628395993753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335561943237451752263995835 503342914856177628395993753)
      ·
        refine ⟨377507186142133221296995315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503342914856177628395993753 377507186142133221296995315)
        ·
          refine ⟨566260779213199831945492973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377507186142133221296995315 566260779213199831945492973)
          ·
            refine ⟨212347792204949936979559865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566260779213199831945492973 212347792204949936979559865)
            ·
              refine ⟨159260844153712452734669899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212347792204949936979559865 159260844153712452734669899)
              ·
                refine ⟨238891266230568679102004849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159260844153712452734669899 238891266230568679102004849)
                ·
                  refine ⟨179168449672926509326503637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238891266230568679102004849 179168449672926509326503637)
                  ·
                    refine ⟨4199260539209215062339929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179168449672926509326503637 4199260539209215062339929)
                    ·
                      refine ⟨3149445404406911296754947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199260539209215062339929 3149445404406911296754947)
                      ·
                        rfl

theorem cell23_6133523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7, 2].length) (baseStart_6133523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133523 prefixEnd_6133523 := by exact prefixLift 6133523
  have htrace : WordTrace (prefixWord ++ tailWord_6133523) baseStart_6133523 baseEnd_6133523 := by
    simpa [prefixWord, tailWord_6133523, baseEnd_6133523] using wordTrace_append hprefix tailTrace_6133523
  have hstable : (prefixWord ++ tailWord_6133523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133523).length < 2 ^ (prefixWord ++ tailWord_6133523).sum := by decide
  have hdescent : baseEnd_6133523 < baseStart_6133523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133530 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_6133530 : Nat := 118140960795 + 6133530 * 2 ^ 59
def prefixEnd_6133530 : Nat := 4983230072969 + 3 ^ 40 * 6133530 * 2
def baseEnd_6133530 : Nat := 3149448998771492769367415

theorem tailTrace_6133530 : CollatzResearch.WordTrace tailWord_6133530 prefixEnd_6133530 3149448998771492769367415 := by
  unfold tailWord_6133530
  simp only [CollatzResearch.WordTrace]
  refine ⟨55927054367318952092875511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149138811646183872247668029 55927054367318952092875511)
  ·
    refine ⟨83890581550978428139313267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55927054367318952092875511 83890581550978428139313267)
    ·
      refine ⟨125835872326467642208969901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83890581550978428139313267 125835872326467642208969901)
      ·
        refine ⟨47188452122425365828363713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125835872326467642208969901 47188452122425365828363713)
        ·
          refine ⟨35391339091819024371272785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47188452122425365828363713 35391339091819024371272785)
          ·
            refine ⟨26543504318864268278454589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35391339091819024371272785 26543504318864268278454589)
            ·
              refine ⟨9953814119574100604420471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26543504318864268278454589 9953814119574100604420471)
              ·
                refine ⟨14930721179361150906630707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9953814119574100604420471 14930721179361150906630707)
                ·
                  refine ⟨22396081769041726359946061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14930721179361150906630707 22396081769041726359946061)
                  ·
                    refine ⟨8398530663390647384979773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22396081769041726359946061 8398530663390647384979773)
                    ·
                      refine ⟨3149448998771492769367415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398530663390647384979773 3149448998771492769367415)
                      ·
                        rfl

theorem cell23_6133530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_6133530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133530 prefixEnd_6133530 := by exact prefixLift 6133530
  have htrace : WordTrace (prefixWord ++ tailWord_6133530) baseStart_6133530 baseEnd_6133530 := by
    simpa [prefixWord, tailWord_6133530, baseEnd_6133530] using wordTrace_append hprefix tailTrace_6133530
  have hstable : (prefixWord ++ tailWord_6133530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133530).length < 2 ^ (prefixWord ++ tailWord_6133530).sum := by decide
  have hdescent : baseEnd_6133530 < baseStart_6133530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133573 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_6133573 : Nat := 118140960795 + 6133573 * 2 ^ 59
def prefixEnd_6133573 : Nat := 4983230072969 + 3 ^ 40 * 6133573 * 2
def baseEnd_6133573 : Nat := 3149471078439636101129717

theorem tailTrace_6133573 : CollatzResearch.WordTrace tailWord_6133573 prefixEnd_6133573 3149471078439636101129717 := by
  unfold tailWord_6133573
  simp only [CollatzResearch.WordTrace]
  refine ⟨223709785808120026715317373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149139857205413351143544915 223709785808120026715317373)
  ·
    refine ⟨83891169678045010018244015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223709785808120026715317373 83891169678045010018244015)
    ·
      refine ⟨125836754517067515027366023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83891169678045010018244015 125836754517067515027366023)
      ·
        refine ⟨188755131775601272541049035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125836754517067515027366023 188755131775601272541049035)
        ·
          refine ⟨283132697663401908811573553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188755131775601272541049035 283132697663401908811573553)
          ·
            refine ⟨212349523247551431608680165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283132697663401908811573553 212349523247551431608680165)
            ·
              refine ⟨39815535608915893426627531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212349523247551431608680165 39815535608915893426627531)
              ·
                refine ⟨59723303413373840139941297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39815535608915893426627531 59723303413373840139941297)
                ·
                  refine ⟨44792477560030380104955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59723303413373840139941297 44792477560030380104955973)
                  ·
                    refine ⟨8398589542505696269679245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44792477560030380104955973 8398589542505696269679245)
                    ·
                      refine ⟨3149471078439636101129717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398589542505696269679245 3149471078439636101129717)
                      ·
                        rfl

theorem cell23_6133573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_6133573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133573 prefixEnd_6133573 := by exact prefixLift 6133573
  have htrace : WordTrace (prefixWord ++ tailWord_6133573) baseStart_6133573 baseEnd_6133573 := by
    simpa [prefixWord, tailWord_6133573, baseEnd_6133573] using wordTrace_append hprefix tailTrace_6133573
  have hstable : (prefixWord ++ tailWord_6133573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133573).length < 2 ^ (prefixWord ++ tailWord_6133573).sum := by decide
  have hdescent : baseEnd_6133573 < baseStart_6133573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133581 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6133581 : Nat := 118140960795 + 6133581 * 2 ^ 59
def prefixEnd_6133581 : Nat := 4983230072969 + 3 ^ 40 * 6133581 * 2
def baseEnd_6133581 : Nat := 3149475186284872069829681

theorem tailTrace_6133581 : CollatzResearch.WordTrace tailWord_6133581 prefixEnd_6133581 3149475186284872069829681 := by
  unfold tailWord_6133581
  simp only [CollatzResearch.WordTrace]
  refine ⟨223710077592091044081608597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149140051728060696054405731 223710077592091044081608597)
  ·
    refine ⟨10486409887129267691325403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223710077592091044081608597 10486409887129267691325403)
    ·
      refine ⟨15729614830693901536988105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10486409887129267691325403 15729614830693901536988105)
      ·
        refine ⟨11797211123020426152741079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15729614830693901536988105 11797211123020426152741079)
        ·
          refine ⟨17695816684530639229111619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797211123020426152741079 17695816684530639229111619)
          ·
            refine ⟨26543725026795958843667429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17695816684530639229111619 26543725026795958843667429)
            ·
              refine ⟨4976948442524242283187643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26543725026795958843667429 4976948442524242283187643)
              ·
                refine ⟨7465422663786363424781465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976948442524242283187643 7465422663786363424781465)
                ·
                  refine ⟨5599066997839772568586099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465422663786363424781465 5599066997839772568586099)
                  ·
                    refine ⟨8398600496759658852879149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599066997839772568586099 8398600496759658852879149)
                    ·
                      refine ⟨3149475186284872069829681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398600496759658852879149 3149475186284872069829681)
                      ·
                        rfl

theorem cell23_6133581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6133581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133581 prefixEnd_6133581 := by exact prefixLift 6133581
  have htrace : WordTrace (prefixWord ++ tailWord_6133581) baseStart_6133581 baseEnd_6133581 := by
    simpa [prefixWord, tailWord_6133581, baseEnd_6133581] using wordTrace_append hprefix tailTrace_6133581
  have hstable : (prefixWord ++ tailWord_6133581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133581).length < 2 ^ (prefixWord ++ tailWord_6133581).sum := by decide
  have hdescent : baseEnd_6133581 < baseStart_6133581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133591 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_6133591 : Nat := 118140960795 + 6133591 * 2 ^ 59
def prefixEnd_6133591 : Nat := 4983230072969 + 3 ^ 40 * 6133591 * 2
def baseEnd_6133591 : Nat := 3149480321091417030704635

theorem tailTrace_6133591 : CollatzResearch.WordTrace tailWord_6133591 prefixEnd_6133591 3149480321091417030704635 := by
  unfold tailWord_6133591
  simp only [CollatzResearch.WordTrace]
  refine ⟨223710442322054815789472627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149140294881369877192981751 223710442322054815789472627)
  ·
    refine ⟨335565663483082223684208941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223710442322054815789472627 335565663483082223684208941)
    ·
      refine ⟨125837123806155833881578353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335565663483082223684208941 125837123806155833881578353)
      ·
        refine ⟨94377842854616875411183765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125837123806155833881578353 94377842854616875411183765)
        ·
          refine ⟨4423961383810166034899239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94377842854616875411183765 4423961383810166034899239)
          ·
            refine ⟨6635942075715249052348859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423961383810166034899239 6635942075715249052348859)
            ·
              refine ⟨9953913113572873578523289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635942075715249052348859 9953913113572873578523289)
              ·
                refine ⟨7465434835179655183892467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953913113572873578523289 7465434835179655183892467)
                ·
                  refine ⟨11198152252769482775838701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465434835179655183892467 11198152252769482775838701)
                  ·
                    refine ⟨4199307094788556040939513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11198152252769482775838701 4199307094788556040939513)
                    ·
                      refine ⟨3149480321091417030704635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199307094788556040939513 3149480321091417030704635)
                      ·
                        rfl

theorem cell23_6133591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_6133591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133591 prefixEnd_6133591 := by exact prefixLift 6133591
  have htrace : WordTrace (prefixWord ++ tailWord_6133591) baseStart_6133591 baseEnd_6133591 := by
    simpa [prefixWord, tailWord_6133591, baseEnd_6133591] using wordTrace_append hprefix tailTrace_6133591
  have hstable : (prefixWord ++ tailWord_6133591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133591).length < 2 ^ (prefixWord ++ tailWord_6133591).sum := by decide
  have hdescent : baseEnd_6133591 < baseStart_6133591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133643 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4]
def baseStart_6133643 : Nat := 118140960795 + 6133643 * 2 ^ 59
def prefixEnd_6133643 : Nat := 4983230072969 + 3 ^ 40 * 6133643 * 2
def baseEnd_6133643 : Nat := 3149507022085450827254395

theorem tailTrace_6133643 : CollatzResearch.WordTrace tailWord_6133643 prefixEnd_6133643 3149507022085450827254395 := by
  unfold tailWord_6133643
  simp only [CollatzResearch.WordTrace]
  refine ⟨223712338917866428670365583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149141559278577619113577055 223712338917866428670365583)
  ·
    refine ⟨335568508376799643005548375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223712338917866428670365583 335568508376799643005548375)
    ·
      refine ⟨503352762565199464508322563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335568508376799643005548375 503352762565199464508322563)
      ·
        refine ⟨755029143847799196762483845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503352762565199464508322563 755029143847799196762483845)
        ·
          refine ⟨141567964471462349392965721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 755029143847799196762483845 141567964471462349392965721)
          ·
            refine ⟨106175973353596762044724291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141567964471462349392965721 106175973353596762044724291)
            ·
              refine ⟨159263960030395143067086437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106175973353596762044724291 159263960030395143067086437)
              ·
                refine ⟨29861992505699089325078707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159263960030395143067086437 29861992505699089325078707)
                ·
                  refine ⟨44792988758548633987618061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29861992505699089325078707 44792988758548633987618061)
                  ·
                    refine ⟨16797370784455737745356773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44792988758548633987618061 16797370784455737745356773)
                    ·
                      refine ⟨3149507022085450827254395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16797370784455737745356773 3149507022085450827254395)
                      ·
                        rfl

theorem cell23_6133643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_6133643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133643 prefixEnd_6133643 := by exact prefixLift 6133643
  have htrace : WordTrace (prefixWord ++ tailWord_6133643) baseStart_6133643 baseEnd_6133643 := by
    simpa [prefixWord, tailWord_6133643, baseEnd_6133643] using wordTrace_append hprefix tailTrace_6133643
  have hstable : (prefixWord ++ tailWord_6133643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133643).length < 2 ^ (prefixWord ++ tailWord_6133643).sum := by decide
  have hdescent : baseEnd_6133643 < baseStart_6133643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133683 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 8]
def baseStart_6133683 : Nat := 118140960795 + 6133683 * 2 ^ 59
def prefixEnd_6133683 : Nat := 4983230072969 + 3 ^ 40 * 6133683 * 2
def baseEnd_6133683 : Nat := 349947506812403407861579

theorem tailTrace_6133683 : CollatzResearch.WordTrace tailWord_6133683 prefixEnd_6133683 349947506812403407861579 := by
  unfold tailWord_6133683
  simp only [CollatzResearch.WordTrace]
  refine ⟨223713797837721515501821703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149142531891814343667881135 223713797837721515501821703)
  ·
    refine ⟨335570696756582273252732555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223713797837721515501821703 335570696756582273252732555)
    ·
      refine ⟨503356045134873409879098833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335570696756582273252732555 503356045134873409879098833)
      ·
        refine ⟨377517033851155057409324125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503356045134873409879098833 377517033851155057409324125)
        ·
          refine ⟨141568887694183146528496547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377517033851155057409324125 141568887694183146528496547)
          ·
            refine ⟨212353331541274719792744821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141568887694183146528496547 212353331541274719792744821)
            ·
              refine ⟨19908124831994504980569827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212353331541274719792744821 19908124831994504980569827)
              ·
                refine ⟨29862187247991757470854741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19908124831994504980569827 29862187247991757470854741)
                ·
                  refine ⟨349947506812403407861579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29862187247991757470854741 349947506812403407861579)
                  ·
                    rfl

theorem cell23_6133683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 8].length) (baseStart_6133683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133683 prefixEnd_6133683 := by exact prefixLift 6133683
  have htrace : WordTrace (prefixWord ++ tailWord_6133683) baseStart_6133683 baseEnd_6133683 := by
    simpa [prefixWord, tailWord_6133683, baseEnd_6133683] using wordTrace_append hprefix tailTrace_6133683
  have hstable : (prefixWord ++ tailWord_6133683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133683).length < 2 ^ (prefixWord ++ tailWord_6133683).sum := by decide
  have hdescent : baseEnd_6133683 < baseStart_6133683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133703 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_6133703 : Nat := 118140960795 + 6133703 * 2 ^ 59
def prefixEnd_6133703 : Nat := 4983230072969 + 3 ^ 40 * 6133703 * 2
def baseEnd_6133703 : Nat := 3149537830924720592504119

theorem tailTrace_6133703 : CollatzResearch.WordTrace tailWord_6133703 prefixEnd_6133703 3149537830924720592504119 := by
  unfold tailWord_6133703
  simp only [CollatzResearch.WordTrace]
  refine ⟨223714527297649058917549763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149143018198432705945033175 223714527297649058917549763)
  ·
    refine ⟨335571790946473588376324645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223714527297649058917549763 335571790946473588376324645)
    ·
      refine ⟨62919710802463797820560871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335571790946473588376324645 62919710802463797820560871)
      ·
        refine ⟨94379566203695696730841307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62919710802463797820560871 94379566203695696730841307)
        ·
          refine ⟨141569349305543545096261961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94379566203695696730841307 141569349305543545096261961)
          ·
            refine ⟨106177011979157658822196471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141569349305543545096261961 106177011979157658822196471)
            ·
              refine ⟨159265517968736488233294707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106177011979157658822196471 159265517968736488233294707)
              ·
                refine ⟨238898276953104732349942061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159265517968736488233294707 238898276953104732349942061)
                ·
                  refine ⟨89586853857414274631228273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238898276953104732349942061 89586853857414274631228273)
                  ·
                    refine ⟨67190140393060705973421205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89586853857414274631228273 67190140393060705973421205)
                    ·
                      refine ⟨3149537830924720592504119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67190140393060705973421205 3149537830924720592504119)
                      ·
                        rfl

theorem cell23_6133703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_6133703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133703 prefixEnd_6133703 := by exact prefixLift 6133703
  have htrace : WordTrace (prefixWord ++ tailWord_6133703) baseStart_6133703 baseEnd_6133703 := by
    simpa [prefixWord, tailWord_6133703, baseEnd_6133703] using wordTrace_append hprefix tailTrace_6133703
  have hstable : (prefixWord ++ tailWord_6133703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133703).length < 2 ^ (prefixWord ++ tailWord_6133703).sum := by decide
  have hdescent : baseEnd_6133703 < baseStart_6133703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133710 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_6133710 : Nat := 118140960795 + 6133710 * 2 ^ 59
def prefixEnd_6133710 : Nat := 4983230072969 + 3 ^ 40 * 6133710 * 2
def baseEnd_6133710 : Nat := 3149541425289302065116587

theorem tailTrace_6133710 : CollatzResearch.WordTrace tailWord_6133710 prefixEnd_6133710 3149541425289302065116587 := by
  unfold tailWord_6133710
  simp only [CollatzResearch.WordTrace]
  refine ⟨27964347826077962389131823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149143188405749132742036389 27964347826077962389131823)
  ·
    refine ⟨41946521739116943583697735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27964347826077962389131823 41946521739116943583697735)
    ·
      refine ⟨62919782608675415375546603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41946521739116943583697735 62919782608675415375546603)
      ·
        refine ⟨94379673913013123063319905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62919782608675415375546603 94379673913013123063319905)
        ·
          refine ⟨70784755434759842297489929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94379673913013123063319905 70784755434759842297489929)
          ·
            refine ⟨53088566576069881723117447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70784755434759842297489929 53088566576069881723117447)
            ·
              refine ⟨79632849864104822584676171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53088566576069881723117447 79632849864104822584676171)
              ·
                refine ⟨119449274796157233877014257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79632849864104822584676171 119449274796157233877014257)
                ·
                  refine ⟨89586956097117925407760693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119449274796157233877014257 89586956097117925407760693)
                  ·
                    refine ⟨8398777134104805506977565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89586956097117925407760693 8398777134104805506977565)
                    ·
                      refine ⟨3149541425289302065116587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398777134104805506977565 3149541425289302065116587)
                      ·
                        rfl

theorem cell23_6133710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_6133710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133710 prefixEnd_6133710 := by exact prefixLift 6133710
  have htrace : WordTrace (prefixWord ++ tailWord_6133710) baseStart_6133710 baseEnd_6133710 := by
    simpa [prefixWord, tailWord_6133710, baseEnd_6133710] using wordTrace_append hprefix tailTrace_6133710
  have hstable : (prefixWord ++ tailWord_6133710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133710).length < 2 ^ (prefixWord ++ tailWord_6133710).sum := by decide
  have hdescent : baseEnd_6133710 < baseStart_6133710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133721 : List Nat := [1, 2, 1, 2, 6, 2, 1, 3, 1, 4]
def baseStart_6133721 : Nat := 118140960795 + 6133721 * 2 ^ 59
def prefixEnd_6133721 : Nat := 4983230072969 + 3 ^ 40 * 6133721 * 2
def baseEnd_6133721 : Nat := 1049849024525500507359679

theorem tailTrace_6133721 : CollatzResearch.WordTrace tailWord_6133721 prefixEnd_6133721 1049849024525500507359679 := by
  unfold tailWord_6133721
  simp only [CollatzResearch.WordTrace]
  refine ⟨223715183811583847991705017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149143455874389231994470011 223715183811583847991705017)
  ·
    refine ⟨167786387858687885993778763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223715183811583847991705017 167786387858687885993778763)
    ·
      refine ⟨251679581788031828990668145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167786387858687885993778763 251679581788031828990668145)
      ·
        refine ⟨188759686341023871743001109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251679581788031828990668145 188759686341023871743001109)
        ·
          refine ⟨8848110297235493987953177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188759686341023871743001109 8848110297235493987953177)
          ·
            refine ⟨6636082722926620490964883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8848110297235493987953177 6636082722926620490964883)
            ·
              refine ⟨9954124084389930736447325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636082722926620490964883 9954124084389930736447325)
              ·
                refine ⟨3732796531646224026167747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9954124084389930736447325 3732796531646224026167747)
                ·
                  refine ⟨5599194797469336039251621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732796531646224026167747 5599194797469336039251621)
                  ·
                    refine ⟨1049849024525500507359679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599194797469336039251621 1049849024525500507359679)
                    ·
                      rfl

theorem cell23_6133721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_6133721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133721 prefixEnd_6133721 := by exact prefixLift 6133721
  have htrace : WordTrace (prefixWord ++ tailWord_6133721) baseStart_6133721 baseEnd_6133721 := by
    simpa [prefixWord, tailWord_6133721, baseEnd_6133721] using wordTrace_append hprefix tailTrace_6133721
  have hstable : (prefixWord ++ tailWord_6133721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133721).length < 2 ^ (prefixWord ++ tailWord_6133721).sum := by decide
  have hdescent : baseEnd_6133721 < baseStart_6133721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133744 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 1, 1, 3]
def baseStart_6133744 : Nat := 118140960795 + 6133744 * 2 ^ 59
def prefixEnd_6133744 : Nat := 4983230072969 + 3 ^ 40 * 6133744 * 2
def baseEnd_6133744 : Nat := 3149558883631554932091431

theorem tailTrace_6133744 : CollatzResearch.WordTrace tailWord_6133744 prefixEnd_6133744 3149558883631554932091431 := by
  unfold tailWord_6133744
  simp only [CollatzResearch.WordTrace]
  refine ⟨111858011345250261459896143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149144015127000348613194857 111858011345250261459896143)
  ·
    refine ⟨167787017017875392189844215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111858011345250261459896143 167787017017875392189844215)
    ·
      refine ⟨251680525526813088284766323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167787017017875392189844215 251680525526813088284766323)
      ·
        refine ⟨377520788290219632427149485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251680525526813088284766323 377520788290219632427149485)
        ·
          refine ⟨141570295608832362160181057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377520788290219632427149485 141570295608832362160181057)
          ·
            refine ⟨106177721706624271620135793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141570295608832362160181057 106177721706624271620135793)
            ·
              refine ⟨79633291279968203715101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106177721706624271620135793 79633291279968203715101845)
              ·
                refine ⟨3732810528748509549145399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79633291279968203715101845 3732810528748509549145399)
                ·
                  refine ⟨5599215793122764323718099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732810528748509549145399 5599215793122764323718099)
                  ·
                    refine ⟨8398823689684146485577149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599215793122764323718099 8398823689684146485577149)
                    ·
                      refine ⟨3149558883631554932091431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8398823689684146485577149 3149558883631554932091431)
                      ·
                        rfl

theorem cell23_6133744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 1, 3].length) (baseStart_6133744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133744 prefixEnd_6133744 := by exact prefixLift 6133744
  have htrace : WordTrace (prefixWord ++ tailWord_6133744) baseStart_6133744 baseEnd_6133744 := by
    simpa [prefixWord, tailWord_6133744, baseEnd_6133744] using wordTrace_append hprefix tailTrace_6133744
  have hstable : (prefixWord ++ tailWord_6133744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133744).length < 2 ^ (prefixWord ++ tailWord_6133744).sum := by decide
  have hdescent : baseEnd_6133744 < baseStart_6133744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133760 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_6133760 : Nat := 118140960795 + 6133760 * 2 ^ 59
def prefixEnd_6133760 : Nat := 4983230072969 + 3 ^ 40 * 6133760 * 2
def baseEnd_6133760 : Nat := 1049855699774008956497119

theorem tailTrace_6133760 : CollatzResearch.WordTrace tailWord_6133760 prefixEnd_6133760 1049855699774008956497119 := by
  unfold tailWord_6133760
  simp only [CollatzResearch.WordTrace]
  refine ⟨111858303129221278826187367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149144404172295038434916489 111858303129221278826187367)
  ·
    refine ⟨167787454693831918239281051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111858303129221278826187367 167787454693831918239281051)
    ·
      refine ⟨251681182040747877358921577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167787454693831918239281051 251681182040747877358921577)
      ·
        refine ⟨188760886530560908019191183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251681182040747877358921577 188760886530560908019191183)
        ·
          refine ⟨283141329795841362028786775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188760886530560908019191183 283141329795841362028786775)
          ·
            refine ⟨424711994693762043043180163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283141329795841362028786775 424711994693762043043180163)
            ·
              refine ⟨637067992040643064564770245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424711994693762043043180163 637067992040643064564770245)
              ·
                refine ⟨119450248507620574605894421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637067992040643064564770245 119450248507620574605894421)
                ·
                  refine ⟨5599230398794714434651301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119450248507620574605894421 5599230398794714434651301)
                  ·
                    refine ⟨1049855699774008956497119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599230398794714434651301 1049855699774008956497119)
                    ·
                      rfl

theorem cell23_6133760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_6133760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133760 prefixEnd_6133760 := by exact prefixLift 6133760
  have htrace : WordTrace (prefixWord ++ tailWord_6133760) baseStart_6133760 baseEnd_6133760 := by
    simpa [prefixWord, tailWord_6133760, baseEnd_6133760] using wordTrace_append hprefix tailTrace_6133760
  have hstable : (prefixWord ++ tailWord_6133760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133760).length < 2 ^ (prefixWord ++ tailWord_6133760).sum := by decide
  have hdescent : baseEnd_6133760 < baseStart_6133760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133764 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_6133764 : Nat := 118140960795 + 6133764 * 2 ^ 59
def prefixEnd_6133764 : Nat := 4983230072969 + 3 ^ 40 * 6133764 * 2
def baseEnd_6133764 : Nat := 1049856384414881617947113

theorem tailTrace_6133764 : CollatzResearch.WordTrace tailWord_6133764 prefixEnd_6133764 1049856384414881617947113 := by
  unfold tailWord_6133764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111858376075214033167760173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149144501433618710890346897 111858376075214033167760173)
  ·
    refine ⟨41946891028205262437910065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111858376075214033167760173 41946891028205262437910065)
    ·
      refine ⟨31460168271153946828432549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41946891028205262437910065 31460168271153946828432549)
      ·
        refine ⟨5898781550841365030331103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31460168271153946828432549 5898781550841365030331103)
        ·
          refine ⟨8848172326262047545496655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898781550841365030331103 8848172326262047545496655)
          ·
            refine ⟨13272258489393071318244983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8848172326262047545496655 13272258489393071318244983)
            ·
              refine ⟨19908387734089606977367475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13272258489393071318244983 19908387734089606977367475)
              ·
                refine ⟨29862581601134410466051213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19908387734089606977367475 29862581601134410466051213)
                ·
                  refine ⟨11198468100425403924769205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29862581601134410466051213 11198468100425403924769205)
                  ·
                    refine ⟨1049856384414881617947113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11198468100425403924769205 1049856384414881617947113)
                    ·
                      rfl

theorem cell23_6133764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_6133764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133764 prefixEnd_6133764 := by exact prefixLift 6133764
  have htrace : WordTrace (prefixWord ++ tailWord_6133764) baseStart_6133764 baseEnd_6133764 := by
    simpa [prefixWord, tailWord_6133764, baseEnd_6133764] using wordTrace_append hprefix tailTrace_6133764
  have hstable : (prefixWord ++ tailWord_6133764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133764).length < 2 ^ (prefixWord ++ tailWord_6133764).sum := by decide
  have hdescent : baseEnd_6133764 < baseStart_6133764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133767 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6133767 : Nat := 118140960795 + 6133767 * 2 ^ 59
def prefixEnd_6133767 : Nat := 4983230072969 + 3 ^ 40 * 6133767 * 2
def baseEnd_6133767 : Nat := 3149570693686608342103825

theorem tailTrace_6133767 : CollatzResearch.WordTrace tailWord_6133767 prefixEnd_6133767 3149570693686608342103825 := by
  unfold tailWord_6133767
  simp only [CollatzResearch.WordTrace]
  refine ⟨223716861569417197847879555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149144574379611465231919703 223716861569417197847879555)
  ·
    refine ⟨335575292354125796771819333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223716861569417197847879555 335575292354125796771819333)
    ·
      refine ⟨62920367316398586894716125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335575292354125796771819333 62920367316398586894716125)
      ·
        refine ⟨23595137743649470085518547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62920367316398586894716125 23595137743649470085518547)
        ·
          refine ⟨35392706615474205128277821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23595137743649470085518547 35392706615474205128277821)
          ·
            refine ⟨13272264980802826923104183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35392706615474205128277821 13272264980802826923104183)
            ·
              refine ⟨19908397471204240384656275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13272264980802826923104183 19908397471204240384656275)
              ·
                refine ⟨29862596206806360576984413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19908397471204240384656275 29862596206806360576984413)
                ·
                  refine ⟨11198473577552385216369155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29862596206806360576984413 11198473577552385216369155)
                  ·
                    refine ⟨16797710366328577824553733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11198473577552385216369155 16797710366328577824553733)
                    ·
                      refine ⟨3149570693686608342103825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16797710366328577824553733 3149570693686608342103825)
                      ·
                        rfl

theorem cell23_6133767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6133767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133767 prefixEnd_6133767 := by exact prefixLift 6133767
  have htrace : WordTrace (prefixWord ++ tailWord_6133767) baseStart_6133767 baseEnd_6133767 := by
    simpa [prefixWord, tailWord_6133767, baseEnd_6133767] using wordTrace_append hprefix tailTrace_6133767
  have hstable : (prefixWord ++ tailWord_6133767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133767).length < 2 ^ (prefixWord ++ tailWord_6133767).sum := by decide
  have hdescent : baseEnd_6133767 < baseStart_6133767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133784 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6133784 : Nat := 118140960795 + 6133784 * 2 ^ 59
def prefixEnd_6133784 : Nat := 4983230072969 + 3 ^ 40 * 6133784 * 2
def baseEnd_6133784 : Nat := 3149579422857734775591247

theorem tailTrace_6133784 : CollatzResearch.WordTrace tailWord_6133784 prefixEnd_6133784 3149579422857734775591247 := by
  unfold tailWord_6133784
  simp only [CollatzResearch.WordTrace]
  refine ⟨111858740805177804875624203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149144987740237073167498937 111858740805177804875624203)
  ·
    refine ⟨167788111207766707313436305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111858740805177804875624203 167788111207766707313436305)
    ·
      refine ⟨125841083405825030485077229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167788111207766707313436305 125841083405825030485077229)
      ·
        refine ⟨47190406277184386431903961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125841083405825030485077229 47190406277184386431903961)
        ·
          refine ⟨35392804707888289823927971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47190406277184386431903961 35392804707888289823927971)
          ·
            refine ⟨53089207061832434735891957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35392804707888289823927971 53089207061832434735891957)
            ·
              refine ⟨4977113162046790756489871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53089207061832434735891957 4977113162046790756489871)
              ·
                refine ⟨7465669743070186134734807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977113162046790756489871 7465669743070186134734807)
                ·
                  refine ⟨11198504614605279202102211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465669743070186134734807 11198504614605279202102211)
                  ·
                    refine ⟨16797756921907918803153317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11198504614605279202102211 16797756921907918803153317)
                    ·
                      refine ⟨3149579422857734775591247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16797756921907918803153317 3149579422857734775591247)
                      ·
                        rfl

theorem cell23_6133784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6133784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133784 prefixEnd_6133784 := by exact prefixLift 6133784
  have htrace : WordTrace (prefixWord ++ tailWord_6133784) baseStart_6133784 baseEnd_6133784 := by
    simpa [prefixWord, tailWord_6133784, baseEnd_6133784] using wordTrace_append hprefix tailTrace_6133784
  have hstable : (prefixWord ++ tailWord_6133784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133784).length < 2 ^ (prefixWord ++ tailWord_6133784).sum := by decide
  have hdescent : baseEnd_6133784 < baseStart_6133784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133794 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_6133794 : Nat := 118140960795 + 6133794 * 2 ^ 59
def prefixEnd_6133794 : Nat := 4983230072969 + 3 ^ 40 * 6133794 * 2
def baseEnd_6133794 : Nat := 1049861519221426578822067

theorem tailTrace_6133794 : CollatzResearch.WordTrace tailWord_6133794 prefixEnd_6133794 1049861519221426578822067 := by
  unfold tailWord_6133794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55929461585079845364778109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149145230893546254306074957 55929461585079845364778109)
  ·
    refine ⟨20973548094404942011791791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55929461585079845364778109 20973548094404942011791791)
    ·
      refine ⟨31460322141607413017687687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20973548094404942011791791 31460322141607413017687687)
      ·
        refine ⟨47190483212411119526531531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31460322141607413017687687 47190483212411119526531531)
        ·
          refine ⟨70785724818616679289797297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47190483212411119526531531 70785724818616679289797297)
          ·
            refine ⟨53089293613962509467347973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70785724818616679289797297 53089293613962509467347973)
            ·
              refine ⟨9954242552617970525127745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53089293613962509467347973 9954242552617970525127745)
              ·
                refine ⟨7465681914463477893845809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954242552617970525127745 7465681914463477893845809)
                ·
                  refine ⟨5599261435847608420384357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465681914463477893845809 5599261435847608420384357)
                  ·
                    refine ⟨1049861519221426578822067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599261435847608420384357 1049861519221426578822067)
                    ·
                      rfl

theorem cell23_6133794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_6133794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133794 prefixEnd_6133794 := by exact prefixLift 6133794
  have htrace : WordTrace (prefixWord ++ tailWord_6133794) baseStart_6133794 baseEnd_6133794 := by
    simpa [prefixWord, tailWord_6133794, baseEnd_6133794] using wordTrace_append hprefix tailTrace_6133794
  have hstable : (prefixWord ++ tailWord_6133794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133794).length < 2 ^ (prefixWord ++ tailWord_6133794).sum := by decide
  have hdescent : baseEnd_6133794 < baseStart_6133794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133814 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6133814 : Nat := 118140960795 + 6133814 * 2 ^ 59
def prefixEnd_6133814 : Nat := 4983230072969 + 3 ^ 40 * 6133814 * 2
def baseEnd_6133814 : Nat := 3149594827277369658216109

theorem tailTrace_6133814 : CollatzResearch.WordTrace tailWord_6133814 prefixEnd_6133814 3149594827277369658216109 := by
  unfold tailWord_6133814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982410987515432804677531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149145717200164616583226997 13982410987515432804677531)
  ·
    refine ⟨20973616481273149207016297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13982410987515432804677531 20973616481273149207016297)
    ·
      refine ⟨15730212360954861905262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20973616481273149207016297 15730212360954861905262223)
      ·
        refine ⟨23595318541432292857893335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15730212360954861905262223 23595318541432292857893335)
        ·
          refine ⟨35392977812148439286840003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23595318541432292857893335 35392977812148439286840003)
          ·
            refine ⟨53089466718222658930260005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35392977812148439286840003 53089466718222658930260005)
            ·
              refine ⟨9954275009666748549423751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53089466718222658930260005 9954275009666748549423751)
              ·
                refine ⟨14931412514500122824135627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9954275009666748549423751 14931412514500122824135627)
                ·
                  refine ⟨22397118771750184236203441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14931412514500122824135627 22397118771750184236203441)
                  ·
                    refine ⟨16797839078812638177152581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22397118771750184236203441 16797839078812638177152581)
                    ·
                      refine ⟨3149594827277369658216109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16797839078812638177152581 3149594827277369658216109)
                      ·
                        rfl

theorem cell23_6133814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6133814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133814 prefixEnd_6133814 := by exact prefixLift 6133814
  have htrace : WordTrace (prefixWord ++ tailWord_6133814) baseStart_6133814 baseEnd_6133814 := by
    simpa [prefixWord, tailWord_6133814, baseEnd_6133814] using wordTrace_append hprefix tailTrace_6133814
  have hstable : (prefixWord ++ tailWord_6133814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133814).length < 2 ^ (prefixWord ++ tailWord_6133814).sum := by decide
  have hdescent : baseEnd_6133814 < baseStart_6133814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133820 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_6133820 : Nat := 118140960795 + 6133820 * 2 ^ 59
def prefixEnd_6133820 : Nat := 4983230072969 + 3 ^ 40 * 6133820 * 2
def baseEnd_6133820 : Nat := 1049865969387098878247027

theorem tailTrace_6133820 : CollatzResearch.WordTrace tailWord_6133820 prefixEnd_6133820 1049865969387098878247027 := by
  unfold tailWord_6133820
  simp only [CollatzResearch.WordTrace]
  refine ⟨111859397319112593949779457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149145863092150125266372609 111859397319112593949779457)
  ·
    refine ⟨83894547989334445462334593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111859397319112593949779457 83894547989334445462334593)
    ·
      refine ⟨62920910992000834096750945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83894547989334445462334593 62920910992000834096750945)
      ·
        refine ⟨47190683244000625572563209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62920910992000834096750945 47190683244000625572563209)
        ·
          refine ⟨35393012433000469179422407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47190683244000625572563209 35393012433000469179422407)
          ·
            refine ⟨53089518649500703769133611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35393012433000469179422407 53089518649500703769133611)
            ·
              refine ⟨79634277974251055653700417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53089518649500703769133611 79634277974251055653700417)
              ·
                refine ⟨59725708480688291740275313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79634277974251055653700417 59725708480688291740275313)
                ·
                  refine ⟨44794281360516218805206485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59725708480688291740275313 44794281360516218805206485)
                  ·
                    refine ⟨1049865969387098878247027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44794281360516218805206485 1049865969387098878247027)
                    ·
                      rfl

theorem cell23_6133820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_6133820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133820 prefixEnd_6133820 := by exact prefixLift 6133820
  have htrace : WordTrace (prefixWord ++ tailWord_6133820) baseStart_6133820 baseEnd_6133820 := by
    simpa [prefixWord, tailWord_6133820, baseEnd_6133820] using wordTrace_append hprefix tailTrace_6133820
  have hstable : (prefixWord ++ tailWord_6133820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133820).length < 2 ^ (prefixWord ++ tailWord_6133820).sum := by decide
  have hdescent : baseEnd_6133820 < baseStart_6133820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133850 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_6133850 : Nat := 118140960795 + 6133850 * 2 ^ 59
def prefixEnd_6133850 : Nat := 4983230072969 + 3 ^ 40 * 6133850 * 2
def baseEnd_6133850 : Nat := 1049871104193643839121981

theorem tailTrace_6133850 : CollatzResearch.WordTrace tailWord_6133850 prefixEnd_6133850 1049871104193643839121981 := by
  unfold tailWord_6133850
  simp only [CollatzResearch.WordTrace]
  refine ⟨55929972207029125755787751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149146592552077668682100669 55929972207029125755787751)
  ·
    refine ⟨83894958310543688633681627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55929972207029125755787751 83894958310543688633681627)
    ·
      refine ⟨125842437465815532950522441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83894958310543688633681627 125842437465815532950522441)
      ·
        refine ⟨94381828099361649712891831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125842437465815532950522441 94381828099361649712891831)
        ·
          refine ⟨141572742149042474569337747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94381828099361649712891831 141572742149042474569337747)
          ·
            refine ⟨212359113223563711854006621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141572742149042474569337747 212359113223563711854006621)
            ·
              refine ⟨79634667458836391945252483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212359113223563711854006621 79634667458836391945252483)
              ·
                refine ⟨119452001188254587917878725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79634667458836391945252483 119452001188254587917878725)
                ·
                  refine ⟨22397250222797735234602261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119452001188254587917878725 22397250222797735234602261)
                  ·
                    refine ⟨1049871104193643839121981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22397250222797735234602261 1049871104193643839121981)
                    ·
                      rfl

theorem cell23_6133850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_6133850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133850 prefixEnd_6133850 := by exact prefixLift 6133850
  have htrace : WordTrace (prefixWord ++ tailWord_6133850) baseStart_6133850 baseEnd_6133850 := by
    simpa [prefixWord, tailWord_6133850, baseEnd_6133850] using wordTrace_append hprefix tailTrace_6133850
  have hstable : (prefixWord ++ tailWord_6133850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133850).length < 2 ^ (prefixWord ++ tailWord_6133850).sum := by decide
  have hdescent : baseEnd_6133850 < baseStart_6133850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133878 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6133878 : Nat := 118140960795 + 6133878 * 2 ^ 59
def prefixEnd_6133878 : Nat := 4983230072969 + 3 ^ 40 * 6133878 * 2
def baseEnd_6133878 : Nat := 3149627690039257407815815

theorem tailTrace_6133878 : CollatzResearch.WordTrace tailWord_6133878 prefixEnd_6133878 3149627690039257407815815 := by
  unfold tailWord_6133878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982556879500941487823143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149147273381343375870113525 13982556879500941487823143)
  ·
    refine ⟨20973835319251412231734715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13982556879500941487823143 20973835319251412231734715)
    ·
      refine ⟨31460752978877118347602073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20973835319251412231734715 31460752978877118347602073)
      ·
        refine ⟨23595564734157838760701555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31460752978877118347602073 23595564734157838760701555)
        ·
          refine ⟨35393347101236758141052333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23595564734157838760701555 35393347101236758141052333)
          ·
            refine ⟨13272505162963784302894625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35393347101236758141052333 13272505162963784302894625)
            ·
              refine ⟨9954378872222838227170969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13272505162963784302894625 9954378872222838227170969)
              ·
                refine ⟨7465784154167128670378227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954378872222838227170969 7465784154167128670378227)
                ·
                  refine ⟨11198676231250693005567341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7465784154167128670378227 11198676231250693005567341)
                  ·
                    refine ⟨4199503586719009877087753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11198676231250693005567341 4199503586719009877087753)
                    ·
                      refine ⟨3149627690039257407815815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199503586719009877087753 3149627690039257407815815)
                      ·
                        rfl

theorem cell23_6133878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6133878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133878 prefixEnd_6133878 := by exact prefixLift 6133878
  have htrace : WordTrace (prefixWord ++ tailWord_6133878) baseStart_6133878 baseEnd_6133878 := by
    simpa [prefixWord, tailWord_6133878, baseEnd_6133878] using wordTrace_append hprefix tailTrace_6133878
  have hstable : (prefixWord ++ tailWord_6133878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133878).length < 2 ^ (prefixWord ++ tailWord_6133878).sum := by decide
  have hdescent : baseEnd_6133878 < baseStart_6133878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133900 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6133900 : Nat := 118140960795 + 6133900 * 2 ^ 59
def prefixEnd_6133900 : Nat := 4983230072969 + 3 ^ 40 * 6133900 * 2
def baseEnd_6133900 : Nat := 3149638986613656321740713

theorem tailTrace_6133900 : CollatzResearch.WordTrace tailWord_6133900 prefixEnd_6133900 3149638986613656321740713 := by
  unfold tailWord_6133900
  simp only [CollatzResearch.WordTrace]
  refine ⟨111860856238967680781235577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149147808318623574374980769 111860856238967680781235577)
  ·
    refine ⟨83895642179225760585926683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111860856238967680781235577 83895642179225760585926683)
    ·
      refine ⟨125843463268838640878890025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83895642179225760585926683 125843463268838640878890025)
      ·
        refine ⟨94382597451628980659167519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125843463268838640878890025 94382597451628980659167519)
        ·
          refine ⟨141573896177443470988751279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94382597451628980659167519 141573896177443470988751279)
          ·
            refine ⟨212360844266165206483126919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141573896177443470988751279 212360844266165206483126919)
            ·
              refine ⟨318541266399247809724690379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212360844266165206483126919 318541266399247809724690379)
              ·
                refine ⟨477811899598871714587035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318541266399247809724690379 477811899598871714587035569)
                ·
                  refine ⟨358358924699153785940276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 477811899598871714587035569 358358924699153785940276677)
                  ·
                    refine ⟨67192298381091334863801877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 358358924699153785940276677 67192298381091334863801877)
                    ·
                      refine ⟨3149638986613656321740713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67192298381091334863801877 3149638986613656321740713)
                      ·
                        rfl

theorem cell23_6133900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6133900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133900 prefixEnd_6133900 := by exact prefixLift 6133900
  have htrace : WordTrace (prefixWord ++ tailWord_6133900) baseStart_6133900 baseEnd_6133900 := by
    simpa [prefixWord, tailWord_6133900, baseEnd_6133900] using wordTrace_append hprefix tailTrace_6133900
  have hstable : (prefixWord ++ tailWord_6133900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133900).length < 2 ^ (prefixWord ++ tailWord_6133900).sum := by decide
  have hdescent : baseEnd_6133900 < baseStart_6133900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133981 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6133981 : Nat := 118140960795 + 6133981 * 2 ^ 59
def prefixEnd_6133981 : Nat := 4983230072969 + 3 ^ 40 * 6133981 * 2
def baseEnd_6133981 : Nat := 3149680578546670504827841

theorem tailTrace_6133981 : CollatzResearch.WordTrace tailWord_6133981 prefixEnd_6133981 3149680578546670504827841 := by
  unfold tailWord_6133981
  simp only [CollatzResearch.WordTrace]
  refine ⟨223724666790641912396169797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149149777860427941597446531 223724666790641912396169797)
  ·
    refine ⟨41948375023245358574281837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223724666790641912396169797 41948375023245358574281837)
    ·
      refine ⟨15730640633717009465355689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41948375023245358574281837 15730640633717009465355689)
      ·
        refine ⟨11797980475287757099016767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15730640633717009465355689 11797980475287757099016767)
        ·
          refine ⟨17696970712931635648525151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797980475287757099016767 17696970712931635648525151)
          ·
            refine ⟨26545456069397453472787727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17696970712931635648525151 26545456069397453472787727)
            ·
              refine ⟨39818184104096180209181591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26545456069397453472787727 39818184104096180209181591)
              ·
                refine ⟨59727276156144270313772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39818184104096180209181591 59727276156144270313772387)
                ·
                  refine ⟨89590914234216405470658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59727276156144270313772387 89590914234216405470658581)
                  ·
                    refine ⟨4199574104728894006437121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89590914234216405470658581 4199574104728894006437121)
                    ·
                      refine ⟨3149680578546670504827841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199574104728894006437121 3149680578546670504827841)
                      ·
                        rfl

theorem cell23_6133981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6133981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133981 prefixEnd_6133981 := by exact prefixLift 6133981
  have htrace : WordTrace (prefixWord ++ tailWord_6133981) baseStart_6133981 baseEnd_6133981 := by
    simpa [prefixWord, tailWord_6133981, baseEnd_6133981] using wordTrace_append hprefix tailTrace_6133981
  have hstable : (prefixWord ++ tailWord_6133981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133981).length < 2 ^ (prefixWord ++ tailWord_6133981).sum := by decide
  have hdescent : baseEnd_6133981 < baseStart_6133981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6133991 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 3, 4]
def baseStart_6133991 : Nat := 118140960795 + 6133991 * 2 ^ 59
def prefixEnd_6133991 : Nat := 4983230072969 + 3 ^ 40 * 6133991 * 2
def baseEnd_6133991 : Nat := 1049895237784405155234265

theorem tailTrace_6133991 : CollatzResearch.WordTrace tailWord_6133991 prefixEnd_6133991 1049895237784405155234265 := by
  unfold tailWord_6133991
  simp only [CollatzResearch.WordTrace]
  refine ⟨223725031520605684104033827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149150021013737122736022551 223725031520605684104033827)
  ·
    refine ⟨335587547280908526156050741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223725031520605684104033827 335587547280908526156050741)
    ·
      refine ⟨31461332557585174327129757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 335587547280908526156050741 31461332557585174327129757)
      ·
        refine ⟨11797999709094440372673659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31461332557585174327129757 11797999709094440372673659)
        ·
          refine ⟨17696999563641660559010489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797999709094440372673659 17696999563641660559010489)
          ·
            refine ⟨13272749672731245419257867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17696999563641660559010489 13272749672731245419257867)
            ·
              refine ⟨19909124509096868128886801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13272749672731245419257867 19909124509096868128886801)
              ·
                refine ⟨14931843381822651096665101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19909124509096868128886801 14931843381822651096665101)
                ·
                  refine ⟨5599441268183494161249413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14931843381822651096665101 5599441268183494161249413)
                  ·
                    refine ⟨1049895237784405155234265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599441268183494161249413 1049895237784405155234265)
                    ·
                      rfl

theorem cell23_6133991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_6133991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6133991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6133991 prefixEnd_6133991 := by exact prefixLift 6133991
  have htrace : WordTrace (prefixWord ++ tailWord_6133991) baseStart_6133991 baseEnd_6133991 := by
    simpa [prefixWord, tailWord_6133991, baseEnd_6133991] using wordTrace_append hprefix tailTrace_6133991
  have hstable : (prefixWord ++ tailWord_6133991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6133991).length < 2 ^ (prefixWord ++ tailWord_6133991).sum := by decide
  have hdescent : baseEnd_6133991 < baseStart_6133991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6133991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134071 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_6134071 : Nat := 118140960795 + 6134071 * 2 ^ 59
def prefixEnd_6134071 : Nat := 4983230072969 + 3 ^ 40 * 6134071 * 2
def baseEnd_6134071 : Nat := 3149726791805575152702427

theorem tailTrace_6134071 : CollatzResearch.WordTrace tailWord_6134071 prefixEnd_6134071 3149726791805575152702427 := by
  unfold tailWord_6134071
  simp only [CollatzResearch.WordTrace]
  refine ⟨223727949360315857766946067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149151966240210571844630711 223727949360315857766946067)
  ·
    refine ⟨335591924040473786650419101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223727949360315857766946067 335591924040473786650419101)
    ·
      refine ⟨125846971515177669993907163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335591924040473786650419101 125846971515177669993907163)
      ·
        refine ⟨188770457272766504990860745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125846971515177669993907163 188770457272766504990860745)
        ·
          refine ⟨141577842954574878743145559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188770457272766504990860745 141577842954574878743145559)
          ·
            refine ⟨212366764431862318114718339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141577842954574878743145559 212366764431862318114718339)
            ·
              refine ⟨318550146647793477172077509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212366764431862318114718339 318550146647793477172077509)
              ·
                refine ⟨59728152496461276969764533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318550146647793477172077509 59728152496461276969764533)
                ·
                  refine ⟨5599514296543244715915425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59728152496461276969764533 5599514296543244715915425)
                  ·
                    refine ⟨4199635722407433536936569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599514296543244715915425 4199635722407433536936569)
                    ·
                      refine ⟨3149726791805575152702427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199635722407433536936569 3149726791805575152702427)
                      ·
                        rfl

theorem cell23_6134071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_6134071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134071 prefixEnd_6134071 := by exact prefixLift 6134071
  have htrace : WordTrace (prefixWord ++ tailWord_6134071) baseStart_6134071 baseEnd_6134071 := by
    simpa [prefixWord, tailWord_6134071, baseEnd_6134071] using wordTrace_append hprefix tailTrace_6134071
  have hstable : (prefixWord ++ tailWord_6134071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134071).length < 2 ^ (prefixWord ++ tailWord_6134071).sum := by decide
  have hdescent : baseEnd_6134071 < baseStart_6134071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134074 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_6134074 : Nat := 118140960795 + 6134074 * 2 ^ 59
def prefixEnd_6134074 : Nat := 4983230072969 + 3 ^ 40 * 6134074 * 2
def baseEnd_6134074 : Nat := 3149728332247538640964913

theorem tailTrace_6134074 : CollatzResearch.WordTrace tailWord_6134074 prefixEnd_6134074 3149728332247538640964913 := by
  unfold tailWord_6134074
  simp only [CollatzResearch.WordTrace]
  refine ⟨55932014694826247319826319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149152039186203326186203517 55932014694826247319826319)
  ·
    refine ⟨83898022042239370979739479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55932014694826247319826319 83898022042239370979739479)
    ·
      refine ⟨125847033063359056469609219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83898022042239370979739479 125847033063359056469609219)
      ·
        refine ⟨188770549595038584704413829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125847033063359056469609219 188770549595038584704413829)
        ·
          refine ⟨35394478049069734632077593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188770549595038584704413829 35394478049069734632077593)
          ·
            refine ⟨26545858536802300974058195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35394478049069734632077593 26545858536802300974058195)
            ·
              refine ⟨39818787805203451461087293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26545858536802300974058195 39818787805203451461087293)
              ·
                refine ⟨14932045426951294297907735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39818787805203451461087293 14932045426951294297907735)
                ·
                  refine ⟨22398068140426941446861603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932045426951294297907735 22398068140426941446861603)
                  ·
                    refine ⟨33597102210640412170292405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22398068140426941446861603 33597102210640412170292405)
                    ·
                      refine ⟨3149728332247538640964913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33597102210640412170292405 3149728332247538640964913)
                      ·
                        rfl

theorem cell23_6134074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_6134074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134074 prefixEnd_6134074 := by exact prefixLift 6134074
  have htrace : WordTrace (prefixWord ++ tailWord_6134074) baseStart_6134074 baseEnd_6134074 := by
    simpa [prefixWord, tailWord_6134074, baseEnd_6134074] using wordTrace_append hprefix tailTrace_6134074
  have hstable : (prefixWord ++ tailWord_6134074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134074).length < 2 ^ (prefixWord ++ tailWord_6134074).sum := by decide
  have hdescent : baseEnd_6134074 < baseStart_6134074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134088 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_6134088 : Nat := 118140960795 + 6134088 * 2 ^ 59
def prefixEnd_6134088 : Nat := 4983230072969 + 3 ^ 40 * 6134088 * 2
def baseEnd_6134088 : Nat := 3149735520976701586189849

theorem tailTrace_6134088 : CollatzResearch.WordTrace tailWord_6134088 prefixEnd_6134088 3149735520976701586189849 := by
  unfold tailWord_6134088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111864284700627134835157459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149152379600836179780209945 111864284700627134835157459)
  ·
    refine ⟨167796427050940702252736189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111864284700627134835157459 167796427050940702252736189)
    ·
      refine ⟨62923660144102763344776071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167796427050940702252736189 62923660144102763344776071)
      ·
        refine ⟨94385490216154145017164107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62923660144102763344776071 94385490216154145017164107)
        ·
          refine ⟨141578235324231217525746161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94385490216154145017164107 141578235324231217525746161)
          ·
            refine ⟨106183676493173413144309621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141578235324231217525746161 106183676493173413144309621)
            ·
              refine ⟨9954719671235007482279027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106183676493173413144309621 9954719671235007482279027)
              ·
                refine ⟨14932079506852511223418541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9954719671235007482279027 14932079506852511223418541)
                ·
                  refine ⟨5599529815069691708781953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14932079506852511223418541 5599529815069691708781953)
                  ·
                    refine ⟨4199647361302268781586465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599529815069691708781953 4199647361302268781586465)
                    ·
                      refine ⟨3149735520976701586189849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199647361302268781586465 3149735520976701586189849)
                      ·
                        rfl

theorem cell23_6134088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_6134088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134088 prefixEnd_6134088 := by exact prefixLift 6134088
  have htrace : WordTrace (prefixWord ++ tailWord_6134088) baseStart_6134088 baseEnd_6134088 := by
    simpa [prefixWord, tailWord_6134088, baseEnd_6134088] using wordTrace_append hprefix tailTrace_6134088
  have hstable : (prefixWord ++ tailWord_6134088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134088).length < 2 ^ (prefixWord ++ tailWord_6134088).sum := by decide
  have hdescent : baseEnd_6134088 < baseStart_6134088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134098 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_6134098 : Nat := 118140960795 + 6134098 * 2 ^ 59
def prefixEnd_6134098 : Nat := 4983230072969 + 3 ^ 40 * 6134098 * 2
def baseEnd_6134098 : Nat := 1049913551927748849021601

theorem tailTrace_6134098 : CollatzResearch.WordTrace tailWord_6134098 prefixEnd_6134098 1049913551927748849021601 := by
  unfold tailWord_6134098
  simp only [CollatzResearch.WordTrace]
  refine ⟨55932233532804510344544737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149152622754145360918785965 55932233532804510344544737)
  ·
    refine ⟨41949175149603382758408553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55932233532804510344544737 41949175149603382758408553)
    ·
      refine ⟨31461881362202537068806415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41949175149603382758408553 31461881362202537068806415)
      ·
        refine ⟨47192822043303805603209623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31461881362202537068806415 47192822043303805603209623)
        ·
          refine ⟨70789233064955708404814435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47192822043303805603209623 70789233064955708404814435)
          ·
            refine ⟨106183849597433562607221653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70789233064955708404814435 106183849597433562607221653)
            ·
              refine ⟨4977367949879698247213515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106183849597433562607221653 4977367949879698247213515)
              ·
                refine ⟨7466051924819547370820273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977367949879698247213515 7466051924819547370820273)
                ·
                  refine ⟨5599538943614660528115205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466051924819547370820273 5599538943614660528115205)
                  ·
                    refine ⟨1049913551927748849021601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599538943614660528115205 1049913551927748849021601)
                    ·
                      rfl

theorem cell23_6134098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_6134098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134098 prefixEnd_6134098 := by exact prefixLift 6134098
  have htrace : WordTrace (prefixWord ++ tailWord_6134098) baseStart_6134098 baseEnd_6134098 := by
    simpa [prefixWord, tailWord_6134098, baseEnd_6134098] using wordTrace_append hprefix tailTrace_6134098
  have hstable : (prefixWord ++ tailWord_6134098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134098).length < 2 ^ (prefixWord ++ tailWord_6134098).sum := by decide
  have hdescent : baseEnd_6134098 < baseStart_6134098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134178 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_6134178 : Nat := 118140960795 + 6134178 * 2 ^ 59
def prefixEnd_6134178 : Nat := 4983230072969 + 3 ^ 40 * 6134178 * 2
def baseEnd_6134178 : Nat := 3149781734235606234064435

theorem tailTrace_6134178 : CollatzResearch.WordTrace tailWord_6134178 prefixEnd_6134178 3149781734235606234064435 := by
  unfold tailWord_6134178
  simp only [CollatzResearch.WordTrace]
  refine ⟨55932962992732053760272797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149154567980618810027394125 55932962992732053760272797)
  ·
    refine ⟨20974861122274520160102299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55932962992732053760272797 20974861122274520160102299)
    ·
      refine ⟨31462291683411780240153449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20974861122274520160102299 31462291683411780240153449)
      ·
        refine ⟨23596718762558835180115087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31462291683411780240153449 23596718762558835180115087)
        ·
          refine ⟨35395078143838252770172631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23596718762558835180115087 35395078143838252770172631)
          ·
            refine ⟨53092617215757379155258947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35395078143838252770172631 53092617215757379155258947)
            ·
              refine ⟨79638925823636068732888421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53092617215757379155258947 79638925823636068732888421)
              ·
                refine ⟨14932298591931762887416579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79638925823636068732888421 14932298591931762887416579)
                ·
                  refine ⟨22398447887897644331124869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932298591931762887416579 22398447887897644331124869)
                  ·
                    refine ⟨4199708978980808312085913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22398447887897644331124869 4199708978980808312085913)
                    ·
                      refine ⟨3149781734235606234064435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199708978980808312085913 3149781734235606234064435)
                      ·
                        rfl

theorem cell23_6134178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_6134178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134178 prefixEnd_6134178 := by exact prefixLift 6134178
  have htrace : WordTrace (prefixWord ++ tailWord_6134178) baseStart_6134178 baseEnd_6134178 := by
    simpa [prefixWord, tailWord_6134178, baseEnd_6134178] using wordTrace_append hprefix tailTrace_6134178
  have hstable : (prefixWord ++ tailWord_6134178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134178).length < 2 ^ (prefixWord ++ tailWord_6134178).sum := by decide
  have hdescent : baseEnd_6134178 < baseStart_6134178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134189 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6134189 : Nat := 118140960795 + 6134189 * 2 ^ 59
def prefixEnd_6134189 : Nat := 4983230072969 + 3 ^ 40 * 6134189 * 2
def baseEnd_6134189 : Nat := 3149787382522805691026885

theorem tailTrace_6134189 : CollatzResearch.WordTrace tailWord_6134189 prefixEnd_6134189 3149787382522805691026885 := by
  unfold tailWord_6134189
  simp only [CollatzResearch.WordTrace]
  refine ⟨223732253173888363919741621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149154835449258909279827747 223732253173888363919741621)
  ·
    refine ⟨20974898735052034117475777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223732253173888363919741621 20974898735052034117475777)
    ·
      refine ⟨15731174051289025588106833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20974898735052034117475777 15731174051289025588106833)
      ·
        refine ⟨11798380538466769191080125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731174051289025588106833 11798380538466769191080125)
        ·
          refine ⟨4424392701925038446655047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11798380538466769191080125 4424392701925038446655047)
          ·
            refine ⟨6636589052887557669982571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424392701925038446655047 6636589052887557669982571)
            ·
              refine ⟨9954883579331336504973857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636589052887557669982571 9954883579331336504973857)
              ·
                refine ⟨7466162684498502378730393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954883579331336504973857 7466162684498502378730393)
                ·
                  refine ⟨5599622013373876784047795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466162684498502378730393 5599622013373876784047795)
                  ·
                    refine ⟨8399433020060815176071693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599622013373876784047795 8399433020060815176071693)
                    ·
                      refine ⟨3149787382522805691026885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8399433020060815176071693 3149787382522805691026885)
                      ·
                        rfl

theorem cell23_6134189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6134189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134189 prefixEnd_6134189 := by exact prefixLift 6134189
  have htrace : WordTrace (prefixWord ++ tailWord_6134189) baseStart_6134189 baseEnd_6134189 := by
    simpa [prefixWord, tailWord_6134189, baseEnd_6134189] using wordTrace_append hprefix tailTrace_6134189
  have hstable : (prefixWord ++ tailWord_6134189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134189).length < 2 ^ (prefixWord ++ tailWord_6134189).sum := by decide
  have hdescent : baseEnd_6134189 < baseStart_6134189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134201 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 7]
def baseStart_6134201 : Nat := 118140960795 + 6134201 * 2 ^ 59
def prefixEnd_6134201 : Nat := 4983230072969 + 3 ^ 40 * 6134201 * 2
def baseEnd_6134201 : Nat := 349977060476739960452981

theorem tailTrace_6134201 : CollatzResearch.WordTrace tailWord_6134201 prefixEnd_6134201 349977060476739960452981 := by
  unfold tailWord_6134201
  simp only [CollatzResearch.WordTrace]
  refine ⟨223732690849844889969178457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149155127233229926646118971 223732690849844889969178457)
  ·
    refine ⟨167799518137383667476883843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223732690849844889969178457 167799518137383667476883843)
    ·
      refine ⟨251699277206075501215325765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167799518137383667476883843 251699277206075501215325765)
      ·
        refine ⟨47193614476139156477873581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251699277206075501215325765 47193614476139156477873581)
        ·
          refine ⟨17697605428552183679202593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47193614476139156477873581 17697605428552183679202593)
          ·
            refine ⟨13273204071414137759401945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17697605428552183679202593 13273204071414137759401945)
            ·
              refine ⟨9954903053560603319551459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13273204071414137759401945 9954903053560603319551459)
              ·
                refine ⟨14932354580340904979327189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9954903053560603319551459 14932354580340904979327189)
                ·
                  refine ⟨349977060476739960452981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14932354580340904979327189 349977060476739960452981)
                  ·
                    rfl

theorem cell23_6134201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_6134201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134201 prefixEnd_6134201 := by exact prefixLift 6134201
  have htrace : WordTrace (prefixWord ++ tailWord_6134201) baseStart_6134201 baseEnd_6134201 := by
    simpa [prefixWord, tailWord_6134201, baseEnd_6134201] using wordTrace_append hprefix tailTrace_6134201
  have hstable : (prefixWord ++ tailWord_6134201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134201).length < 2 ^ (prefixWord ++ tailWord_6134201).sum := by decide
  have hdescent : baseEnd_6134201 < baseStart_6134201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134212 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6134212 : Nat := 118140960795 + 6134212 * 2 ^ 59
def prefixEnd_6134212 : Nat := 4983230072969 + 3 ^ 40 * 6134212 * 2
def baseEnd_6134212 : Nat := 3149799192577859101039279

theorem tailTrace_6134212 : CollatzResearch.WordTrace tailWord_6134212 prefixEnd_6134212 3149799192577859101039279 := by
  unfold tailWord_6134212
  simp only [CollatzResearch.WordTrace]
  refine ⟨111866546026402519423914445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149155394701870025898552593 111866546026402519423914445)
  ·
    refine ⟨41949954759900944783967917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111866546026402519423914445 41949954759900944783967917)
    ·
      refine ⟨15731233034962854293987969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41949954759900944783967917 15731233034962854293987969)
      ·
        refine ⟨11798424776222140720490977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731233034962854293987969 11798424776222140720490977)
        ·
          refine ⟨8848818582166605540368233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11798424776222140720490977 8848818582166605540368233)
          ·
            refine ⟨6636613936624954155276175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8848818582166605540368233 6636613936624954155276175)
            ·
              refine ⟨9954920904937431232914263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636613936624954155276175 9954920904937431232914263)
              ·
                refine ⟨14932381357406146849371395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9954920904937431232914263 14932381357406146849371395)
                ·
                  refine ⟨22398572036109220274057093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932381357406146849371395 22398572036109220274057093)
                  ·
                    refine ⟨4199732256770478801385705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22398572036109220274057093 4199732256770478801385705)
                    ·
                      refine ⟨3149799192577859101039279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199732256770478801385705 3149799192577859101039279)
                      ·
                        rfl

theorem cell23_6134212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6134212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134212 prefixEnd_6134212 := by exact prefixLift 6134212
  have htrace : WordTrace (prefixWord ++ tailWord_6134212) baseStart_6134212 baseEnd_6134212 := by
    simpa [prefixWord, tailWord_6134212, baseEnd_6134212] using wordTrace_append hprefix tailTrace_6134212
  have hstable : (prefixWord ++ tailWord_6134212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134212).length < 2 ^ (prefixWord ++ tailWord_6134212).sum := by decide
  have hdescent : baseEnd_6134212 < baseStart_6134212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134251 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4]
def baseStart_6134251 : Nat := 118140960795 + 6134251 * 2 ^ 59
def prefixEnd_6134251 : Nat := 4983230072969 + 3 ^ 40 * 6134251 * 2
def baseEnd_6134251 : Nat := 3149819218323384448451599

theorem tailTrace_6134251 : CollatzResearch.WordTrace tailWord_6134251 prefixEnd_6134251 3149819218323384448451599 := by
  unfold tailWord_6134251
  simp only [CollatzResearch.WordTrace]
  refine ⟨223734514499663748508498607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149156342999775832338999071 223734514499663748508498607)
  ·
    refine ⟨335601771749495622762747911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223734514499663748508498607 335601771749495622762747911)
    ·
      refine ⟨503402657624243434144121867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335601771749495622762747911 503402657624243434144121867)
      ·
        refine ⟨755103986436365151216182801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503402657624243434144121867 755103986436365151216182801)
        ·
          refine ⟨566327989827273863412137101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755103986436365151216182801 566327989827273863412137101)
          ·
            refine ⟨212372996185227698779551413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566327989827273863412137101 212372996185227698779551413)
            ·
              refine ⟨19909968392365096760582945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212372996185227698779551413 19909968392365096760582945)
              ·
                refine ⟨14932476294273822570437209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19909968392365096760582945 14932476294273822570437209)
                ·
                  refine ⟨11199357220705366927827907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14932476294273822570437209 11199357220705366927827907)
                  ·
                    refine ⟨16799035831058050391741861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11199357220705366927827907 16799035831058050391741861)
                    ·
                      refine ⟨3149819218323384448451599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16799035831058050391741861 3149819218323384448451599)
                      ·
                        rfl

theorem cell23_6134251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_6134251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134251 prefixEnd_6134251 := by exact prefixLift 6134251
  have htrace : WordTrace (prefixWord ++ tailWord_6134251) baseStart_6134251 baseEnd_6134251 := by
    simpa [prefixWord, tailWord_6134251, baseEnd_6134251] using wordTrace_append hprefix tailTrace_6134251
  have hstable : (prefixWord ++ tailWord_6134251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134251).length < 2 ^ (prefixWord ++ tailWord_6134251).sum := by decide
  have hdescent : baseEnd_6134251 < baseStart_6134251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134258 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6134258 : Nat := 118140960795 + 6134258 * 2 ^ 59
def prefixEnd_6134258 : Nat := 4983230072969 + 3 ^ 40 * 6134258 * 2
def baseEnd_6134258 : Nat := 3149822812687965921064067

theorem tailTrace_6134258 : CollatzResearch.WordTrace tailWord_6134258 prefixEnd_6134258 3149822812687965921064067 := by
  unfold tailWord_6134258
  simp only [CollatzResearch.WordTrace]
  refine ⟨55933692452659597176000857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149156513207092259136002285 55933692452659597176000857)
  ·
    refine ⟨41950269339494697882000643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55933692452659597176000857 41950269339494697882000643)
    ·
      refine ⟨62925404009242046823000965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41950269339494697882000643 62925404009242046823000965)
      ·
        refine ⟨11798513251732883779312681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62925404009242046823000965 11798513251732883779312681)
        ·
          refine ⟨8848884938799662834484511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11798513251732883779312681 8848884938799662834484511)
          ·
            refine ⟨13273327408199494251726767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8848884938799662834484511 13273327408199494251726767)
            ·
              refine ⟨19909991112299241377590151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13273327408199494251726767 19909991112299241377590151)
              ·
                refine ⟨29864986668448862066385227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19909991112299241377590151 29864986668448862066385227)
                ·
                  refine ⟨44797480002673293099577841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29864986668448862066385227 44797480002673293099577841)
                  ·
                    refine ⟨33598110002004969824683381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44797480002673293099577841 33598110002004969824683381)
                    ·
                      refine ⟨3149822812687965921064067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33598110002004969824683381 3149822812687965921064067)
                      ·
                        rfl

theorem cell23_6134258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6134258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134258 prefixEnd_6134258 := by exact prefixLift 6134258
  have htrace : WordTrace (prefixWord ++ tailWord_6134258) baseStart_6134258 baseEnd_6134258 := by
    simpa [prefixWord, tailWord_6134258, baseEnd_6134258] using wordTrace_append hprefix tailTrace_6134258
  have hstable : (prefixWord ++ tailWord_6134258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134258).length < 2 ^ (prefixWord ++ tailWord_6134258).sum := by decide
  have hdescent : baseEnd_6134258 < baseStart_6134258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134271 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_6134271 : Nat := 118140960795 + 6134271 * 2 ^ 59
def prefixEnd_6134271 : Nat := 4983230072969 + 3 ^ 40 * 6134271 * 2
def baseEnd_6134271 : Nat := 3149829487936474370201507

theorem tailTrace_6134271 : CollatzResearch.WordTrace tailWord_6134271 prefixEnd_6134271 3149829487936474370201507 := by
  unfold tailWord_6134271
  simp only [CollatzResearch.WordTrace]
  refine ⟨223735243959591291924226667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149156829306394194616151111 223735243959591291924226667)
  ·
    refine ⟨335602865939386937886340001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223735243959591291924226667 335602865939386937886340001)
    ·
      refine ⟨251702149454540203414755001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335602865939386937886340001 251702149454540203414755001)
      ·
        refine ⟨188776612090905152561066251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251702149454540203414755001 188776612090905152561066251)
        ·
          refine ⟨283164918136357728841599377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188776612090905152561066251 283164918136357728841599377)
          ·
            refine ⟨212373688602268296631199533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283164918136357728841599377 212373688602268296631199533)
            ·
              refine ⟨79640133225850611236699825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212373688602268296631199533 79640133225850611236699825)
              ·
                refine ⟨59730099919387958427524869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79640133225850611236699825 59730099919387958427524869)
                ·
                  refine ⟨11199393734885242205160913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59730099919387958427524869 11199393734885242205160913)
                  ·
                    refine ⟨8399545301163931653870685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11199393734885242205160913 8399545301163931653870685)
                    ·
                      refine ⟨3149829487936474370201507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8399545301163931653870685 3149829487936474370201507)
                      ·
                        rfl

theorem cell23_6134271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_6134271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134271 prefixEnd_6134271 := by exact prefixLift 6134271
  have htrace : WordTrace (prefixWord ++ tailWord_6134271) baseStart_6134271 baseEnd_6134271 := by
    simpa [prefixWord, tailWord_6134271, baseEnd_6134271] using wordTrace_append hprefix tailTrace_6134271
  have hstable : (prefixWord ++ tailWord_6134271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134271).length < 2 ^ (prefixWord ++ tailWord_6134271).sum := by decide
  have hdescent : baseEnd_6134271 < baseStart_6134271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134312 : List Nat := [2, 1, 5, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6134312 : Nat := 118140960795 + 6134312 * 2 ^ 59
def prefixEnd_6134312 : Nat := 4983230072969 + 3 ^ 40 * 6134312 * 2
def baseEnd_6134312 : Nat := 1049950180214436236596273

theorem tailTrace_6134312 : CollatzResearch.WordTrace tailWord_6134312 prefixEnd_6134312 1049950180214436236596273 := by
  unfold tailWord_6134312
  simp only [CollatzResearch.WordTrace]
  refine ⟨111868369676221377963234595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149157826234961837284312793 111868369676221377963234595)
  ·
    refine ⟨167802554514332066944851893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111868369676221377963234595 167802554514332066944851893)
    ·
      refine ⟨15731489485718631276079865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167802554514332066944851893 15731489485718631276079865)
      ·
        refine ⟨11798617114288973457059899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731489485718631276079865 11798617114288973457059899)
        ·
          refine ⟨17697925671433460185589849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798617114288973457059899 17697925671433460185589849)
          ·
            refine ⟨13273444253575095139192387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17697925671433460185589849 13273444253575095139192387)
            ·
              refine ⟨19910166380362642708788581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13273444253575095139192387 19910166380362642708788581)
              ·
                refine ⟨3733156196317995507897859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19910166380362642708788581 3733156196317995507897859)
                ·
                  refine ⟨5599734294476993261846789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733156196317995507897859 5599734294476993261846789)
                  ·
                    refine ⟨1049950180214436236596273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599734294476993261846789 1049950180214436236596273)
                    ·
                      rfl

theorem cell23_6134312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6134312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134312 prefixEnd_6134312 := by exact prefixLift 6134312
  have htrace : WordTrace (prefixWord ++ tailWord_6134312) baseStart_6134312 baseEnd_6134312 := by
    simpa [prefixWord, tailWord_6134312, baseEnd_6134312] using wordTrace_append hprefix tailTrace_6134312
  have hstable : (prefixWord ++ tailWord_6134312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134312).length < 2 ^ (prefixWord ++ tailWord_6134312).sum := by decide
  have hdescent : baseEnd_6134312 < baseStart_6134312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134321 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_6134321 : Nat := 118140960795 + 6134321 * 2 ^ 59
def prefixEnd_6134321 : Nat := 4983230072969 + 3 ^ 40 * 6134321 * 2
def baseEnd_6134321 : Nat := 1049951720656399724858759

theorem tailTrace_6134321 : CollatzResearch.WordTrace tailWord_6134321 prefixEnd_6134321 1049951720656399724858759 := by
  unfold tailWord_6134321
  simp only [CollatzResearch.WordTrace]
  refine ⟨223737067609410150463546817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149158045072940100309031211 223737067609410150463546817)
  ·
    refine ⟨167802800707057612847660113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223737067609410150463546817 167802800707057612847660113)
    ·
      refine ⟨125852100530293209635745085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167802800707057612847660113 125852100530293209635745085)
      ·
        refine ⟨47194537698859953613404407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125852100530293209635745085 47194537698859953613404407)
        ·
          refine ⟨70791806548289930420106611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47194537698859953613404407 70791806548289930420106611)
          ·
            refine ⟨106187709822434895630159917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70791806548289930420106611 106187709822434895630159917)
            ·
              refine ⟨39820391183413085861309969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106187709822434895630159917 39820391183413085861309969)
              ·
                refine ⟨29865293387559814395982477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39820391183413085861309969 29865293387559814395982477)
                ·
                  refine ⟨11199485020334930398493429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29865293387559814395982477 11199485020334930398493429)
                  ·
                    refine ⟨1049951720656399724858759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11199485020334930398493429 1049951720656399724858759)
                    ·
                      rfl

theorem cell23_6134321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_6134321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134321 prefixEnd_6134321 := by exact prefixLift 6134321
  have htrace : WordTrace (prefixWord ++ tailWord_6134321) baseStart_6134321 baseEnd_6134321 := by
    simpa [prefixWord, tailWord_6134321, baseEnd_6134321] using wordTrace_append hprefix tailTrace_6134321
  have hstable : (prefixWord ++ tailWord_6134321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134321).length < 2 ^ (prefixWord ++ tailWord_6134321).sum := by decide
  have hdescent : baseEnd_6134321 < baseStart_6134321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134328 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_6134328 : Nat := 118140960795 + 6134328 * 2 ^ 59
def prefixEnd_6134328 : Nat := 4983230072969 + 3 ^ 40 * 6134328 * 2
def baseEnd_6134328 : Nat := 3149858756333780647188745

theorem tailTrace_6134328 : CollatzResearch.WordTrace tailWord_6134328 prefixEnd_6134328 3149858756333780647188745 := by
  unfold tailWord_6134328
  simp only [CollatzResearch.WordTrace]
  refine ⟨111868661460192395329525819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149158215280256527106034425 111868661460192395329525819)
  ·
    refine ⟨167802992190288592994288729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111868661460192395329525819 167802992190288592994288729)
    ·
      refine ⟨125852244142716444745716547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167802992190288592994288729 125852244142716444745716547)
      ·
        refine ⟨188778366214074667118574821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125852244142716444745716547 188778366214074667118574821)
        ·
          refine ⟨35395943665139000084732779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188778366214074667118574821 35395943665139000084732779)
          ·
            refine ⟨53093915497708500127099169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35395943665139000084732779 53093915497708500127099169)
            ·
              refine ⟨39820436623281375095324377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53093915497708500127099169 39820436623281375095324377)
              ·
                refine ⟨29865327467461031321493283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39820436623281375095324377 29865327467461031321493283)
                ·
                  refine ⟨44797991201191546982239925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29865327467461031321493283 44797991201191546982239925)
                  ·
                    refine ⟨4199811675111707529584993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44797991201191546982239925 4199811675111707529584993)
                    ·
                      refine ⟨3149858756333780647188745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199811675111707529584993 3149858756333780647188745)
                      ·
                        rfl

theorem cell23_6134328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_6134328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134328 prefixEnd_6134328 := by exact prefixLift 6134328
  have htrace : WordTrace (prefixWord ++ tailWord_6134328) baseStart_6134328 baseEnd_6134328 := by
    simpa [prefixWord, tailWord_6134328, baseEnd_6134328] using wordTrace_append hprefix tailTrace_6134328
  have hstable : (prefixWord ++ tailWord_6134328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134328).length < 2 ^ (prefixWord ++ tailWord_6134328).sum := by decide
  have hdescent : baseEnd_6134328 < baseStart_6134328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134351 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 6]
def baseStart_6134351 : Nat := 118140960795 + 6134351 * 2 ^ 59
def prefixEnd_6134351 : Nat := 4983230072969 + 3 ^ 40 * 6134351 * 2
def baseEnd_6134351 : Nat := 1049956855462944685733713

theorem tailTrace_6134351 : CollatzResearch.WordTrace tailWord_6134351 prefixEnd_6134351 1049956855462944685733713 := by
  unfold tailWord_6134351
  simp only [CollatzResearch.WordTrace]
  refine ⟨223738161799301465587138907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149158774532867643724759271 223738161799301465587138907)
  ·
    refine ⟨335607242698952198380708361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223738161799301465587138907 335607242698952198380708361)
    ·
      refine ⟨251705432024214148785531271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335607242698952198380708361 251705432024214148785531271)
      ·
        refine ⟨377558148036321223178296907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251705432024214148785531271 377558148036321223178296907)
        ·
          refine ⟨566337222054481834767445361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377558148036321223178296907 566337222054481834767445361)
          ·
            refine ⟨424752916540861376075584021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566337222054481834767445361 424752916540861376075584021)
            ·
              refine ⟨19910292962852877003543001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 424752916540861376075584021 19910292962852877003543001)
              ·
                refine ⟨14932719722139657752657251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19910292962852877003543001 14932719722139657752657251)
                ·
                  refine ⟨22399079583209486628985877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932719722139657752657251 22399079583209486628985877)
                  ·
                    refine ⟨1049956855462944685733713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22399079583209486628985877 1049956855462944685733713)
                    ·
                      rfl

theorem cell23_6134351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_6134351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134351 prefixEnd_6134351 := by exact prefixLift 6134351
  have htrace : WordTrace (prefixWord ++ tailWord_6134351) baseStart_6134351 baseEnd_6134351 := by
    simpa [prefixWord, tailWord_6134351, baseEnd_6134351] using wordTrace_append hprefix tailTrace_6134351
  have hstable : (prefixWord ++ tailWord_6134351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134351).length < 2 ^ (prefixWord ++ tailWord_6134351).sum := by decide
  have hdescent : baseEnd_6134351 < baseStart_6134351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134371 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6134371 : Nat := 118140960795 + 6134371 * 2 ^ 59
def prefixEnd_6134371 : Nat := 4983230072969 + 3 ^ 40 * 6134371 * 2
def baseEnd_6134371 : Nat := 3149880836001923978951047

theorem tailTrace_6134371 : CollatzResearch.WordTrace tailWord_6134371 prefixEnd_6134371 3149880836001923978951047 := by
  unfold tailWord_6134371
  simp only [CollatzResearch.WordTrace]
  refine ⟨223738891259229009002866967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149159260839486006001911311 223738891259229009002866967)
  ·
    refine ⟨335608336888843513504300451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223738891259229009002866967 335608336888843513504300451)
    ·
      refine ⟨503412505333265270256450677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335608336888843513504300451 503412505333265270256450677)
      ·
        refine ⟨47194922374993619086542251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 503412505333265270256450677 47194922374993619086542251)
        ·
          refine ⟨70792383562490428629813377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47194922374993619086542251 70792383562490428629813377)
          ·
            refine ⟨53094287671867821472360033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70792383562490428629813377 53094287671867821472360033)
            ·
              refine ⟨39820715753900866104270025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53094287671867821472360033 39820715753900866104270025)
              ·
                refine ⟨29865536815425649578202519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39820715753900866104270025 29865536815425649578202519)
                ·
                  refine ⟨44798305223138474367303779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29865536815425649578202519 44798305223138474367303779)
                  ·
                    refine ⟨67197457834707711550955669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44798305223138474367303779 67197457834707711550955669)
                    ·
                      refine ⟨3149880836001923978951047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67197457834707711550955669 3149880836001923978951047)
                      ·
                        rfl

theorem cell23_6134371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6134371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134371 prefixEnd_6134371 := by exact prefixLift 6134371
  have htrace : WordTrace (prefixWord ++ tailWord_6134371) baseStart_6134371 baseEnd_6134371 := by
    simpa [prefixWord, tailWord_6134371, baseEnd_6134371] using wordTrace_append hprefix tailTrace_6134371
  have hstable : (prefixWord ++ tailWord_6134371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134371).length < 2 ^ (prefixWord ++ tailWord_6134371).sum := by decide
  have hdescent : baseEnd_6134371 < baseStart_6134371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134378 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6134378 : Nat := 118140960795 + 6134378 * 2 ^ 59
def prefixEnd_6134378 : Nat := 4983230072969 + 3 ^ 40 * 6134378 * 2
def baseEnd_6134378 : Nat := 3149884430366505451563515

theorem tailTrace_6134378 : CollatzResearch.WordTrace tailWord_6134378 prefixEnd_6134378 3149884430366505451563515 := by
  unfold tailWord_6134378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55934786642550912299592947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149159431046802432798914525 55934786642550912299592947)
  ·
    refine ⟨83902179963826368449389421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55934786642550912299592947 83902179963826368449389421)
    ·
      refine ⟨31463317486434888168521033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83902179963826368449389421 31463317486434888168521033)
      ·
        refine ⟨23597488114826166126390775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31463317486434888168521033 23597488114826166126390775)
        ·
          refine ⟨35396232172239249189586163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23597488114826166126390775 35396232172239249189586163)
          ·
            refine ⟨53094348258358873784379245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35396232172239249189586163 53094348258358873784379245)
            ·
              refine ⟨19910380596884577669142217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53094348258358873784379245 19910380596884577669142217)
              ·
                refine ⟨14932785447663433251856663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19910380596884577669142217 14932785447663433251856663)
                ·
                  refine ⟨22399178171495149877784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14932785447663433251856663 22399178171495149877784995)
                  ·
                    refine ⟨33598767257242724816677493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22399178171495149877784995 33598767257242724816677493)
                    ·
                      refine ⟨3149884430366505451563515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33598767257242724816677493 3149884430366505451563515)
                      ·
                        rfl

theorem cell23_6134378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6134378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134378 prefixEnd_6134378 := by exact prefixLift 6134378
  have htrace : WordTrace (prefixWord ++ tailWord_6134378) baseStart_6134378 baseEnd_6134378 := by
    simpa [prefixWord, tailWord_6134378, baseEnd_6134378] using wordTrace_append hprefix tailTrace_6134378
  have hstable : (prefixWord ++ tailWord_6134378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134378).length < 2 ^ (prefixWord ++ tailWord_6134378).sum := by decide
  have hdescent : baseEnd_6134378 < baseStart_6134378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134425 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_6134425 : Nat := 118140960795 + 6134425 * 2 ^ 59
def prefixEnd_6134425 : Nat := 4983230072969 + 3 ^ 40 * 6134425 * 2
def baseEnd_6134425 : Nat := 3149908563957266767675799

theorem tailTrace_6134425 : CollatzResearch.WordTrace tailWord_6134425 prefixEnd_6134425 3149908563957266767675799 := by
  unfold tailWord_6134425
  simp only [CollatzResearch.WordTrace]
  refine ⟨223740860801033376225332729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149160573867355584150221819 223740860801033376225332729)
  ·
    refine ⟨167805645600775032168999547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223740860801033376225332729 167805645600775032168999547)
    ·
      refine ⟨251708468401162548253499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167805645600775032168999547 251708468401162548253499321)
      ·
        refine ⟨188781351300871911190124491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251708468401162548253499321 188781351300871911190124491)
        ·
          refine ⟨283172026951307866785186737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188781351300871911190124491 283172026951307866785186737)
          ·
            refine ⟨212379020213480900088890053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283172026951307866785186737 212379020213480900088890053)
            ·
              refine ⟨39821066290027668766666885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212379020213480900088890053 39821066290027668766666885)
              ·
                refine ⟨7466449929380187893750041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39821066290027668766666885 7466449929380187893750041)
                ·
                  refine ⟨5599837447035140920312531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466449929380187893750041 5599837447035140920312531)
                  ·
                    refine ⟨8399756170552711380468797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599837447035140920312531 8399756170552711380468797)
                    ·
                      refine ⟨3149908563957266767675799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8399756170552711380468797 3149908563957266767675799)
                      ·
                        rfl

theorem cell23_6134425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_6134425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134425 prefixEnd_6134425 := by exact prefixLift 6134425
  have htrace : WordTrace (prefixWord ++ tailWord_6134425) baseStart_6134425 baseEnd_6134425 := by
    simpa [prefixWord, tailWord_6134425, baseEnd_6134425] using wordTrace_append hprefix tailTrace_6134425
  have hstable : (prefixWord ++ tailWord_6134425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134425).length < 2 ^ (prefixWord ++ tailWord_6134425).sum := by decide
  have hdescent : baseEnd_6134425 < baseStart_6134425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134426 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6134426 : Nat := 118140960795 + 6134426 * 2 ^ 59
def prefixEnd_6134426 : Nat := 4983230072969 + 3 ^ 40 * 6134426 * 2
def baseEnd_6134426 : Nat := 3149909077437921263763295

theorem tailTrace_6134426 : CollatzResearch.WordTrace tailWord_6134426 prefixEnd_6134426 3149909077437921263763295 := by
  unfold tailWord_6134426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55935224318507438349029783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149160598182686502264079421 55935224318507438349029783)
  ·
    refine ⟨83902836477761157523544675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55935224318507438349029783 83902836477761157523544675)
    ·
      refine ⟨125854254716641736285317013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83902836477761157523544675 125854254716641736285317013)
      ·
        refine ⟨5899418189842581388374235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125854254716641736285317013 5899418189842581388374235)
        ·
          refine ⟨8849127284763872082561353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5899418189842581388374235 8849127284763872082561353)
          ·
            refine ⟨6636845463572904061921015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8849127284763872082561353 6636845463572904061921015)
            ·
              refine ⟨9955268195359356092881523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6636845463572904061921015 9955268195359356092881523)
              ·
                refine ⟨14932902293039034139322285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9955268195359356092881523 14932902293039034139322285)
                ·
                  refine ⟨5599838359889637802245857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14932902293039034139322285 5599838359889637802245857)
                  ·
                    refine ⟨4199878769917228351684393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599838359889637802245857 4199878769917228351684393)
                    ·
                      refine ⟨3149909077437921263763295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199878769917228351684393 3149909077437921263763295)
                      ·
                        rfl

theorem cell23_6134426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6134426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134426 prefixEnd_6134426 := by exact prefixLift 6134426
  have htrace : WordTrace (prefixWord ++ tailWord_6134426) baseStart_6134426 baseEnd_6134426 := by
    simpa [prefixWord, tailWord_6134426, baseEnd_6134426] using wordTrace_append hprefix tailTrace_6134426
  have hstable : (prefixWord ++ tailWord_6134426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134426).length < 2 ^ (prefixWord ++ tailWord_6134426).sum := by decide
  have hdescent : baseEnd_6134426 < baseStart_6134426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134471 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 11]
def baseStart_6134471 : Nat := 118140960795 + 6134471 * 2 ^ 59
def prefixEnd_6134471 : Nat := 4983230072969 + 3 ^ 40 * 6134471 * 2
def baseEnd_6134471 : Nat := 349992464896374843077843

theorem tailTrace_6134471 : CollatzResearch.WordTrace tailWord_6134471 prefixEnd_6134471 349992464896374843077843 := by
  unfold tailWord_6134471
  simp only [CollatzResearch.WordTrace]
  refine ⟨223742538558866726081507267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149161692372577817387671511 223742538558866726081507267)
  ·
    refine ⟨335613807838300089122260901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223742538558866726081507267 335613807838300089122260901)
    ·
      refine ⟨62927588969681266710423919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335613807838300089122260901 62927588969681266710423919)
      ·
        refine ⟨94391383454521900065635879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62927588969681266710423919 94391383454521900065635879)
        ·
          refine ⟨141587075181782850098453819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94391383454521900065635879 141587075181782850098453819)
          ·
            refine ⟨212380612772674275147680729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141587075181782850098453819 212380612772674275147680729)
            ·
              refine ⟨159285459579505706360760547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212380612772674275147680729 159285459579505706360760547)
              ·
                refine ⟨238928189369258559541140821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159285459579505706360760547 238928189369258559541140821)
                ·
                  refine ⟨349992464896374843077843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 238928189369258559541140821 349992464896374843077843)
                  ·
                    rfl

theorem cell23_6134471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 11].length) (baseStart_6134471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134471 prefixEnd_6134471 := by exact prefixLift 6134471
  have htrace : WordTrace (prefixWord ++ tailWord_6134471) baseStart_6134471 baseEnd_6134471 := by
    simpa [prefixWord, tailWord_6134471, baseEnd_6134471] using wordTrace_append hprefix tailTrace_6134471
  have hstable : (prefixWord ++ tailWord_6134471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134471).length < 2 ^ (prefixWord ++ tailWord_6134471).sum := by decide
  have hdescent : baseEnd_6134471 < baseStart_6134471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134477 : List Nat := [1, 6, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6134477 : Nat := 118140960795 + 6134477 * 2 ^ 59
def prefixEnd_6134477 : Nat := 4983230072969 + 3 ^ 40 * 6134477 * 2
def baseEnd_6134477 : Nat := 3149935264951300564225561

theorem tailTrace_6134477 : CollatzResearch.WordTrace tailWord_6134477 prefixEnd_6134477 3149935264951300564225561 := by
  unfold tailWord_6134477
  simp only [CollatzResearch.WordTrace]
  refine ⟨223742757396844989106225685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149161838264563326070817123 223742757396844989106225685)
  ·
    refine ⟨10487941752977108864354329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223742757396844989106225685 10487941752977108864354329)
    ·
      refine ⟨7865956314732831648265747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10487941752977108864354329 7865956314732831648265747)
      ·
        refine ⟨11798934472099247472398621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7865956314732831648265747 11798934472099247472398621)
        ·
          refine ⟨4424600427037217802149483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11798934472099247472398621 4424600427037217802149483)
          ·
            refine ⟨6636900640555826703224225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424600427037217802149483 6636900640555826703224225)
            ·
              refine ⟨4977675480416870027418169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636900640555826703224225 4977675480416870027418169)
              ·
                refine ⟨3733256610312652520563627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4977675480416870027418169 3733256610312652520563627)
                ·
                  refine ⟨5599884915468978780845441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733256610312652520563627 5599884915468978780845441)
                  ·
                    refine ⟨4199913686601734085634081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599884915468978780845441 4199913686601734085634081)
                    ·
                      refine ⟨3149935264951300564225561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199913686601734085634081 3149935264951300564225561)
                      ·
                        rfl

theorem cell23_6134477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6134477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134477 prefixEnd_6134477 := by exact prefixLift 6134477
  have htrace : WordTrace (prefixWord ++ tailWord_6134477) baseStart_6134477 baseEnd_6134477 := by
    simpa [prefixWord, tailWord_6134477, baseEnd_6134477] using wordTrace_append hprefix tailTrace_6134477
  have hstable : (prefixWord ++ tailWord_6134477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134477).length < 2 ^ (prefixWord ++ tailWord_6134477).sum := by decide
  have hdescent : baseEnd_6134477 < baseStart_6134477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134499 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6134499 : Nat := 118140960795 + 6134499 * 2 ^ 59
def prefixEnd_6134499 : Nat := 4983230072969 + 3 ^ 40 * 6134499 * 2
def baseEnd_6134499 : Nat := 3149946561525699478150459

theorem tailTrace_6134499 : CollatzResearch.WordTrace tailWord_6134499 prefixEnd_6134499 3149946561525699478150459 := by
  unfold tailWord_6134499
  simp only [CollatzResearch.WordTrace]
  refine ⟨223743559802765286863526551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149162373201843524575684367 223743559802765286863526551)
  ·
    refine ⟨335615339704147930295289827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223743559802765286863526551 335615339704147930295289827)
    ·
      refine ⟨503423009556221895442934741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335615339704147930295289827 503423009556221895442934741)
      ·
        refine ⟨11798976786473950674443783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 503423009556221895442934741 11798976786473950674443783)
        ·
          refine ⟨17698465179710926011665675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798976786473950674443783 17698465179710926011665675)
          ·
            refine ⟨26547697769566389017498513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17698465179710926011665675 26547697769566389017498513)
            ·
              refine ⟨19910773327174791763123885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26547697769566389017498513 19910773327174791763123885)
              ·
                refine ⟨7466539997690546911171457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19910773327174791763123885 7466539997690546911171457)
                ·
                  refine ⟨5599904998267910183378593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466539997690546911171457 5599904998267910183378593)
                  ·
                    refine ⟨4199928748700932637533945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5599904998267910183378593 4199928748700932637533945)
                    ·
                      refine ⟨3149946561525699478150459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4199928748700932637533945 3149946561525699478150459)
                      ·
                        rfl

theorem cell23_6134499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6134499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134499 prefixEnd_6134499 := by exact prefixLift 6134499
  have htrace : WordTrace (prefixWord ++ tailWord_6134499) baseStart_6134499 baseEnd_6134499 := by
    simpa [prefixWord, tailWord_6134499, baseEnd_6134499] using wordTrace_append hprefix tailTrace_6134499
  have hstable : (prefixWord ++ tailWord_6134499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134499).length < 2 ^ (prefixWord ++ tailWord_6134499).sum := by decide
  have hdescent : baseEnd_6134499 < baseStart_6134499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134565 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_6134565 : Nat := 118140960795 + 6134565 * 2 ^ 59
def prefixEnd_6134565 : Nat := 4983230072969 + 3 ^ 40 * 6134565 * 2
def baseEnd_6134565 : Nat := 1049993483749632073308385

theorem tailTrace_6134565 : CollatzResearch.WordTrace tailWord_6134565 prefixEnd_6134565 1049993483749632073308385 := by
  unfold tailWord_6134565
  simp only [CollatzResearch.WordTrace]
  refine ⟨223745967020526180135429149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149163978013684120090286099 223745967020526180135429149)
  ·
    refine ⟨83904737632697317550785931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223745967020526180135429149 83904737632697317550785931)
    ·
      refine ⟨125857106449045976326178897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83904737632697317550785931 125857106449045976326178897)
      ·
        refine ⟨94392829836784482244634173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125857106449045976326178897 94392829836784482244634173)
        ·
          refine ⟨35397311188794180841737815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94392829836784482244634173 35397311188794180841737815)
          ·
            refine ⟨53095966783191271262606723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35397311188794180841737815 53095966783191271262606723)
            ·
              refine ⟨79643950174786906893910085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53095966783191271262606723 79643950174786906893910085)
              ·
                refine ⟨14933240657772545042608141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79643950174786906893910085 14933240657772545042608141)
                ·
                  refine ⟨5599965246664704390978053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14933240657772545042608141 5599965246664704390978053)
                  ·
                    refine ⟨1049993483749632073308385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599965246664704390978053 1049993483749632073308385)
                    ·
                      rfl

theorem cell23_6134565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_6134565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134565 prefixEnd_6134565 := by exact prefixLift 6134565
  have htrace : WordTrace (prefixWord ++ tailWord_6134565) baseStart_6134565 baseEnd_6134565 := by
    simpa [prefixWord, tailWord_6134565, baseEnd_6134565] using wordTrace_append hprefix tailTrace_6134565
  have hstable : (prefixWord ++ tailWord_6134565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134565).length < 2 ^ (prefixWord ++ tailWord_6134565).sum := by decide
  have hdescent : baseEnd_6134565 < baseStart_6134565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134573 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 5]
def baseStart_6134573 : Nat := 118140960795 + 6134573 * 2 ^ 59
def prefixEnd_6134573 : Nat := 4983230072969 + 3 ^ 40 * 6134573 * 2
def baseEnd_6134573 : Nat := 349998284343792465402791

theorem tailTrace_6134573 : CollatzResearch.WordTrace tailWord_6134573 prefixEnd_6134573 349998284343792465402791 := by
  unfold tailWord_6134573
  simp only [CollatzResearch.WordTrace]
  refine ⟨223746258804497197501720373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149164172536331465001146915 223746258804497197501720373)
  ·
    refine ⟨20976211762921612265786285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223746258804497197501720373 20976211762921612265786285)
    ·
      refine ⟨7866079411095604599669857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20976211762921612265786285 7866079411095604599669857)
      ·
        refine ⟨5899559558321703449752393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7866079411095604599669857 5899559558321703449752393)
        ·
          refine ⟨4424669668741277587314295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899559558321703449752393 4424669668741277587314295)
          ·
            refine ⟨6637004503111916380971443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424669668741277587314295 6637004503111916380971443)
            ·
              refine ⟨9955506754667874571457165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637004503111916380971443 9955506754667874571457165)
              ·
                refine ⟨3733315033000452964296437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9955506754667874571457165 3733315033000452964296437)
                ·
                  refine ⟨349998284343792465402791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3733315033000452964296437 349998284343792465402791)
                  ·
                    rfl

theorem cell23_6134573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_6134573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134573 prefixEnd_6134573 := by exact prefixLift 6134573
  have htrace : WordTrace (prefixWord ++ tailWord_6134573) baseStart_6134573 baseEnd_6134573 := by
    simpa [prefixWord, tailWord_6134573, baseEnd_6134573] using wordTrace_append hprefix tailTrace_6134573
  have hstable : (prefixWord ++ tailWord_6134573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134573).length < 2 ^ (prefixWord ++ tailWord_6134573).sum := by decide
  have hdescent : baseEnd_6134573 < baseStart_6134573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134578 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_6134578 : Nat := 118140960795 + 6134578 * 2 ^ 59
def prefixEnd_6134578 : Nat := 4983230072969 + 3 ^ 40 * 6134578 * 2
def baseEnd_6134578 : Nat := 349998569610822741006955

theorem tailTrace_6134578 : CollatzResearch.WordTrace tailWord_6134578 prefixEnd_6134578 349998569610822741006955 := by
  unfold tailWord_6134578
  simp only [CollatzResearch.WordTrace]
  refine ⟨55936610292369770838913097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149164294112986055570434925 55936610292369770838913097)
  ·
    refine ⟨41952457719277328129184823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55936610292369770838913097 41952457719277328129184823)
    ·
      refine ⟨62928686578915992193777235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41952457719277328129184823 62928686578915992193777235)
      ·
        refine ⟨94393029868373988290665853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62928686578915992193777235 94393029868373988290665853)
        ·
          refine ⟨35397386200640245608999695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94393029868373988290665853 35397386200640245608999695)
          ·
            refine ⟨53096079300960368413499543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35397386200640245608999695 53096079300960368413499543)
            ·
              refine ⟨79644118951440552620249315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53096079300960368413499543 79644118951440552620249315)
              ·
                refine ⟨119466178427160828930373973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79644118951440552620249315 119466178427160828930373973)
                ·
                  refine ⟨349998569610822741006955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119466178427160828930373973 349998569610822741006955)
                  ·
                    rfl

theorem cell23_6134578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_6134578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134578 prefixEnd_6134578 := by exact prefixLift 6134578
  have htrace : WordTrace (prefixWord ++ tailWord_6134578) baseStart_6134578 baseEnd_6134578 := by
    simpa [prefixWord, tailWord_6134578, baseEnd_6134578] using wordTrace_append hprefix tailTrace_6134578
  have hstable : (prefixWord ++ tailWord_6134578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134578).length < 2 ^ (prefixWord ++ tailWord_6134578).sum := by decide
  have hdescent : baseEnd_6134578 < baseStart_6134578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134612 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 6]
def baseStart_6134612 : Nat := 118140960795 + 6134612 * 2 ^ 59
def prefixEnd_6134612 : Nat := 4983230072969 + 3 ^ 40 * 6134612 * 2
def baseEnd_6134612 : Nat := 350000509426628615115271

theorem tailTrace_6134612 : CollatzResearch.WordTrace tailWord_6134612 prefixEnd_6134612 350000509426628615115271 := by
  unfold tailWord_6134612
  simp only [CollatzResearch.WordTrace]
  refine ⟨111873840625677953581195045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149165120834237271441593393 111873840625677953581195045)
  ·
    refine ⟨20976345117314616296474071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111873840625677953581195045 20976345117314616296474071)
    ·
      refine ⟨31464517675971924444711107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20976345117314616296474071 31464517675971924444711107)
      ·
        refine ⟨47196776513957886667066661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31464517675971924444711107 47196776513957886667066661)
        ·
          refine ⟨8849395596367103750074999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47196776513957886667066661 8849395596367103750074999)
          ·
            refine ⟨13274093394550655625112499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8849395596367103750074999 13274093394550655625112499)
            ·
              refine ⟨19911140091825983437668749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13274093394550655625112499 19911140091825983437668749)
              ·
                refine ⟨7466677534434743789125781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19911140091825983437668749 7466677534434743789125781)
                ·
                  refine ⟨350000509426628615115271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7466677534434743789125781 350000509426628615115271)
                  ·
                    rfl

theorem cell23_6134612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_6134612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134612 prefixEnd_6134612 := by exact prefixLift 6134612
  have htrace : WordTrace (prefixWord ++ tailWord_6134612) baseStart_6134612 baseEnd_6134612 := by
    simpa [prefixWord, tailWord_6134612, baseEnd_6134612] using wordTrace_append hprefix tailTrace_6134612
  have hstable : (prefixWord ++ tailWord_6134612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134612).length < 2 ^ (prefixWord ++ tailWord_6134612).sum := by decide
  have hdescent : baseEnd_6134612 < baseStart_6134612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134625 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6134625 : Nat := 118140960795 + 6134625 * 2 ^ 59
def prefixEnd_6134625 : Nat := 4983230072969 + 3 ^ 40 * 6134625 * 2
def baseEnd_6134625 : Nat := 1050003753362721995058293

theorem tailTrace_6134625 : CollatzResearch.WordTrace tailWord_6134625 prefixEnd_6134625 1050003753362721995058293 := by
  unfold tailWord_6134625
  simp only [CollatzResearch.WordTrace]
  refine ⟨223748155400308810382613329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149165436933539206921742219 223748155400308810382613329)
  ·
    refine ⟨167811116550231607786959997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223748155400308810382613329 167811116550231607786959997)
    ·
      refine ⟨62929168706336852920109999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167811116550231607786959997 62929168706336852920109999)
      ·
        refine ⟨94393753059505279380164999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62929168706336852920109999 94393753059505279380164999)
        ·
          refine ⟨141590629589257919070247499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94393753059505279380164999 141590629589257919070247499)
          ·
            refine ⟨212385944383886878605371249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141590629589257919070247499 212385944383886878605371249)
            ·
              refine ⟨159289458287915158954028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212385944383886878605371249 159289458287915158954028437)
              ·
                refine ⟨7466693357246023075970083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159289458287915158954028437 7466693357246023075970083)
                ·
                  refine ⟨11200040035869034613955125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7466693357246023075970083 11200040035869034613955125)
                  ·
                    refine ⟨1050003753362721995058293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11200040035869034613955125 1050003753362721995058293)
                    ·
                      rfl

theorem cell23_6134625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6134625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134625 prefixEnd_6134625 := by exact prefixLift 6134625
  have htrace : WordTrace (prefixWord ++ tailWord_6134625) baseStart_6134625 baseEnd_6134625 := by
    simpa [prefixWord, tailWord_6134625, baseEnd_6134625] using wordTrace_append hprefix tailTrace_6134625
  have hstable : (prefixWord ++ tailWord_6134625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134625).length < 2 ^ (prefixWord ++ tailWord_6134625).sum := by decide
  have hdescent : baseEnd_6134625 < baseStart_6134625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134655 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 4, 4]
def baseStart_6134655 : Nat := 118140960795 + 6134655 * 2 ^ 59
def prefixEnd_6134655 : Nat := 4983230072969 + 3 ^ 40 * 6134655 * 2
def baseEnd_6134655 : Nat := 1050008888169266955933247

theorem tailTrace_6134655 : CollatzResearch.WordTrace tailWord_6134655 prefixEnd_6134655 1050008888169266955933247 := by
  unfold tailWord_6134655
  simp only [CollatzResearch.WordTrace]
  refine ⟨223749249590200125506205419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149166166393466750337470279 223749249590200125506205419)
  ·
    refine ⟨335623874385300188259308129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223749249590200125506205419 335623874385300188259308129)
    ·
      refine ⟨251717905788975141194481097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335623874385300188259308129 251717905788975141194481097)
      ·
        refine ⟨188788429341731355895860823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251717905788975141194481097 188788429341731355895860823)
        ·
          refine ⟨283182644012597033843791235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188788429341731355895860823 283182644012597033843791235)
          ·
            refine ⟨424773966018895550765686853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283182644012597033843791235 424773966018895550765686853)
            ·
              refine ⟨79645118628542915768566285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 424773966018895550765686853 79645118628542915768566285)
              ·
                refine ⟨29866919485703593413212357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79645118628542915768566285 29866919485703593413212357)
                ·
                  refine ⟨5600047403569423764977317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29866919485703593413212357 5600047403569423764977317)
                  ·
                    refine ⟨1050008888169266955933247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600047403569423764977317 1050008888169266955933247)
                    ·
                      rfl

theorem cell23_6134655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_6134655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134655 prefixEnd_6134655 := by exact prefixLift 6134655
  have htrace : WordTrace (prefixWord ++ tailWord_6134655) baseStart_6134655 baseEnd_6134655 := by
    simpa [prefixWord, tailWord_6134655, baseEnd_6134655] using wordTrace_append hprefix tailTrace_6134655
  have hstable : (prefixWord ++ tailWord_6134655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134655).length < 2 ^ (prefixWord ++ tailWord_6134655).sum := by decide
  have hdescent : baseEnd_6134655 < baseStart_6134655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134679 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_6134679 : Nat := 118140960795 + 6134679 * 2 ^ 59
def prefixEnd_6134679 : Nat := 4983230072969 + 3 ^ 40 * 6134679 * 2
def baseEnd_6134679 : Nat := 3150038988043508773899631

theorem tailTrace_6134679 : CollatzResearch.WordTrace tailWord_6134679 prefixEnd_6134679 3150038988043508773899631 := by
  unfold tailWord_6134679
  simp only [CollatzResearch.WordTrace]
  refine ⟨223750124942113177605079091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149166749961408785070052727 223750124942113177605079091)
  ·
    refine ⟨335625187413169766407618637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223750124942113177605079091 335625187413169766407618637)
    ·
      refine ⟨125859445279938662402856989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335625187413169766407618637 125859445279938662402856989)
      ·
        refine ⟨47197291979976998401071371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125859445279938662402856989 47197291979976998401071371)
        ·
          refine ⟨70795937969965497601607057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47197291979976998401071371 70795937969965497601607057)
          ·
            refine ⟨53096953477474123201205293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70795937969965497601607057 53096953477474123201205293)
            ·
              refine ⟨19911357554052796200451985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53096953477474123201205293 19911357554052796200451985)
              ·
                refine ⟨14933518165539597150338989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19911357554052796200451985 14933518165539597150338989)
                ·
                  refine ⟨5600069312077348931377121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14933518165539597150338989 5600069312077348931377121)
                  ·
                    refine ⟨4200051984058011698532841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5600069312077348931377121 4200051984058011698532841)
                    ·
                      refine ⟨3150038988043508773899631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200051984058011698532841 3150038988043508773899631)
                      ·
                        rfl

theorem cell23_6134679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_6134679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134679 prefixEnd_6134679 := by exact prefixLift 6134679
  have htrace : WordTrace (prefixWord ++ tailWord_6134679) baseStart_6134679 baseEnd_6134679 := by
    simpa [prefixWord, tailWord_6134679, baseEnd_6134679] using wordTrace_append hprefix tailTrace_6134679
  have hstable : (prefixWord ++ tailWord_6134679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134679).length < 2 ^ (prefixWord ++ tailWord_6134679).sum := by decide
  have hdescent : baseEnd_6134679 < baseStart_6134679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134826 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 5]
def baseStart_6134826 : Nat := 118140960795 + 6134826 * 2 ^ 59
def prefixEnd_6134826 : Nat := 4983230072969 + 3 ^ 40 * 6134826 * 2
def baseEnd_6134826 : Nat := 350012718855524410973495

theorem tailTrace_6134826 : CollatzResearch.WordTrace tailWord_6134826 prefixEnd_6134826 350012718855524410973495 := by
  unfold tailWord_6134826
  simp only [CollatzResearch.WordTrace]
  refine ⟨55938871618145155427670083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149170324315053747807120221 55938871618145155427670083)
  ·
    refine ⟨83908307427217733141505125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55938871618145155427670083 83908307427217733141505125)
    ·
      refine ⟨15732807642603324964032211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83908307427217733141505125 15732807642603324964032211)
      ·
        refine ⟨23599211463904987446048317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15732807642603324964032211 23599211463904987446048317)
        ·
          refine ⟨8849704298964370292268119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23599211463904987446048317 8849704298964370292268119)
          ·
            refine ⟨13274556448446555438402179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8849704298964370292268119 13274556448446555438402179)
            ·
              refine ⟨19911834672669833157603269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13274556448446555438402179 19911834672669833157603269)
              ·
                refine ⟨3733469001125593717050613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19911834672669833157603269 3733469001125593717050613)
                ·
                  refine ⟨350012718855524410973495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3733469001125593717050613 350012718855524410973495)
                  ·
                    rfl

theorem cell23_6134826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_6134826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134826 prefixEnd_6134826 := by exact prefixLift 6134826
  have htrace : WordTrace (prefixWord ++ tailWord_6134826) baseStart_6134826 baseEnd_6134826 := by
    simpa [prefixWord, tailWord_6134826, baseEnd_6134826] using wordTrace_append hprefix tailTrace_6134826
  have hstable : (prefixWord ++ tailWord_6134826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134826).length < 2 ^ (prefixWord ++ tailWord_6134826).sum := by decide
  have hdescent : baseEnd_6134826 < baseStart_6134826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134835 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 8]
def baseStart_6134835 : Nat := 118140960795 + 6134835 * 2 ^ 59
def prefixEnd_6134835 : Nat := 4983230072969 + 3 ^ 40 * 6134835 * 2
def baseEnd_6134835 : Nat := 1050039697008536721182971

theorem tailTrace_6134835 : CollatzResearch.WordTrace tailWord_6134835 prefixEnd_6134835 1050039697008536721182971 := by
  unfold tailWord_6134835
  simp only [CollatzResearch.WordTrace]
  refine ⟨223755814729548016247757959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149170543153032010831838639 223755814729548016247757959)
  ·
    refine ⟨335633722094322024371636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223755814729548016247757959 335633722094322024371636939)
    ·
      refine ⟨503450583141483036557455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335633722094322024371636939 503450583141483036557455409)
      ·
        refine ⟨377587937356112277418091557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503450583141483036557455409 377587937356112277418091557)
        ·
          refine ⟨70797738254271052015892167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377587937356112277418091557 70797738254271052015892167)
          ·
            refine ⟨106196607381406578023838251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70797738254271052015892167 106196607381406578023838251)
            ·
              refine ⟨159294911072109867035757377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106196607381406578023838251 159294911072109867035757377)
              ·
                refine ⟨119471183304082400276818033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159294911072109867035757377 119471183304082400276818033)
                ·
                  refine ⟨89603387478061800207613525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119471183304082400276818033 89603387478061800207613525)
                  ·
                    refine ⟨1050039697008536721182971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89603387478061800207613525 1050039697008536721182971)
                    ·
                      rfl

theorem cell23_6134835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_6134835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134835 prefixEnd_6134835 := by exact prefixLift 6134835
  have htrace : WordTrace (prefixWord ++ tailWord_6134835) baseStart_6134835 baseEnd_6134835 := by
    simpa [prefixWord, tailWord_6134835, baseEnd_6134835] using wordTrace_append hprefix tailTrace_6134835
  have hstable : (prefixWord ++ tailWord_6134835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134835).length < 2 ^ (prefixWord ++ tailWord_6134835).sum := by decide
  have hdescent : baseEnd_6134835 < baseStart_6134835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134836 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6134836 : Nat := 118140960795 + 6134836 * 2 ^ 59
def prefixEnd_6134836 : Nat := 4983230072969 + 3 ^ 40 * 6134836 * 2
def baseEnd_6134836 : Nat := 3150119604506264659636409

theorem tailTrace_6134836 : CollatzResearch.WordTrace tailWord_6134836 prefixEnd_6134836 3150119604506264659636409 := by
  unfold tailWord_6134836
  simp only [CollatzResearch.WordTrace]
  refine ⟨111877925601272196709272181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149170567468362928945696241 111877925601272196709272181)
  ·
    refine ⟨10488555525119268441494267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111877925601272196709272181 10488555525119268441494267)
    ·
      refine ⟨15732833287678902662241401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10488555525119268441494267 15732833287678902662241401)
      ·
        refine ⟨11799624965759176996681051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15732833287678902662241401 11799624965759176996681051)
        ·
          refine ⟨17699437448638765495021577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799624965759176996681051 17699437448638765495021577)
          ·
            refine ⟨13274578086479074121266183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17699437448638765495021577 13274578086479074121266183)
            ·
              refine ⟨19911867129718611181899275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13274578086479074121266183 19911867129718611181899275)
              ·
                refine ⟨29867800694577916772848913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19911867129718611181899275 29867800694577916772848913)
                ·
                  refine ⟨22400850520933437579636685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29867800694577916772848913 22400850520933437579636685)
                  ·
                    refine ⟨8400318945350039092363757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22400850520933437579636685 8400318945350039092363757)
                    ·
                      refine ⟨3150119604506264659636409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8400318945350039092363757 3150119604506264659636409)
                      ·
                        rfl

theorem cell23_6134836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6134836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134836 prefixEnd_6134836 := by exact prefixLift 6134836
  have htrace : WordTrace (prefixWord ++ tailWord_6134836) baseStart_6134836 baseEnd_6134836 := by
    simpa [prefixWord, tailWord_6134836, baseEnd_6134836] using wordTrace_append hprefix tailTrace_6134836
  have hstable : (prefixWord ++ tailWord_6134836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134836).length < 2 ^ (prefixWord ++ tailWord_6134836).sum := by decide
  have hdescent : baseEnd_6134836 < baseStart_6134836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134842 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_6134842 : Nat := 118140960795 + 6134842 * 2 ^ 59
def prefixEnd_6134842 : Nat := 4983230072969 + 3 ^ 40 * 6134842 * 2
def baseEnd_6134842 : Nat := 3150122685390191636161381

theorem tailTrace_6134842 : CollatzResearch.WordTrace tailWord_6134842 prefixEnd_6134842 3150122685390191636161381 := by
  unfold tailWord_6134842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55939017510130664110815695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149170713360348437628841853 55939017510130664110815695)
  ·
    refine ⟨83908526265195996166223543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55939017510130664110815695 83908526265195996166223543)
    ·
      refine ⟨125862789397793994249335315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83908526265195996166223543 125862789397793994249335315)
      ·
        refine ⟨188794184096690991374002973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125862789397793994249335315 188794184096690991374002973)
        ·
          refine ⟨70797819036259121765251115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188794184096690991374002973 70797819036259121765251115)
          ·
            refine ⟨106196728554388682647876673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70797819036259121765251115 106196728554388682647876673)
            ·
              refine ⟨79647546415791511985907505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106196728554388682647876673 79647546415791511985907505)
              ·
                refine ⟨59735659811843633989430629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79647546415791511985907505 59735659811843633989430629)
                ·
                  refine ⟨11200436214720681373018243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59735659811843633989430629 11200436214720681373018243)
                  ·
                    refine ⟨16800654322081022059527365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11200436214720681373018243 16800654322081022059527365)
                    ·
                      refine ⟨3150122685390191636161381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16800654322081022059527365 3150122685390191636161381)
                      ·
                        rfl

theorem cell23_6134842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_6134842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134842 prefixEnd_6134842 := by exact prefixLift 6134842
  have htrace : WordTrace (prefixWord ++ tailWord_6134842) baseStart_6134842 baseEnd_6134842 := by
    simpa [prefixWord, tailWord_6134842, baseEnd_6134842] using wordTrace_append hprefix tailTrace_6134842
  have hstable : (prefixWord ++ tailWord_6134842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134842).length < 2 ^ (prefixWord ++ tailWord_6134842).sum := by decide
  have hdescent : baseEnd_6134842 < baseStart_6134842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134912 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_6134912 : Nat := 118140960795 + 6134912 * 2 ^ 59
def prefixEnd_6134912 : Nat := 4983230072969 + 3 ^ 40 * 6134912 * 2
def baseEnd_6134912 : Nat := 1050052876345335454095353

theorem tailTrace_6134912 : CollatzResearch.WordTrace tailWord_6134912 prefixEnd_6134912 1050052876345335454095353 := by
  unfold tailWord_6134912
  simp only [CollatzResearch.WordTrace]
  refine ⟨111879311575134529199155495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149172415433512705598873993 111879311575134529199155495)
  ·
    refine ⟨167818967362701793798733243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111879311575134529199155495 167818967362701793798733243)
    ·
      refine ⟨251728451044052690698099865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167818967362701793798733243 251728451044052690698099865)
      ·
        refine ⟨188796338283039518023574899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251728451044052690698099865 188796338283039518023574899)
        ·
          refine ⟨283194507424559277035362349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188796338283039518023574899 283194507424559277035362349)
          ·
            refine ⟨106197940284209728888260881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283194507424559277035362349 106197940284209728888260881)
            ·
              refine ⟨79648455213157296666195661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106197940284209728888260881 79648455213157296666195661)
              ·
                refine ⟨29868170704933986249823373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79648455213157296666195661 29868170704933986249823373)
                ·
                  refine ⟨11200564014350244843683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29868170704933986249823373 11200564014350244843683765)
                  ·
                    refine ⟨1050052876345335454095353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11200564014350244843683765 1050052876345335454095353)
                    ·
                      rfl

theorem cell23_6134912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_6134912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134912 prefixEnd_6134912 := by exact prefixLift 6134912
  have htrace : WordTrace (prefixWord ++ tailWord_6134912) baseStart_6134912 baseEnd_6134912 := by
    simpa [prefixWord, tailWord_6134912, baseEnd_6134912] using wordTrace_append hprefix tailTrace_6134912
  have hstable : (prefixWord ++ tailWord_6134912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134912).length < 2 ^ (prefixWord ++ tailWord_6134912).sum := by decide
  have hdescent : baseEnd_6134912 < baseStart_6134912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134920 : List Nat := [2, 1, 3, 4, 2, 2, 1, 3, 1, 4]
def baseStart_6134920 : Nat := 118140960795 + 6134920 * 2 ^ 59
def prefixEnd_6134920 : Nat := 4983230072969 + 3 ^ 40 * 6134920 * 2
def baseEnd_6134920 : Nat := 1050054245627080776995341

theorem tailTrace_6134920 : CollatzResearch.WordTrace tailWord_6134920 prefixEnd_6134920 1050054245627080776995341 := by
  unfold tailWord_6134920
  simp only [CollatzResearch.WordTrace]
  refine ⟨111879457467120037882301107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149172609956160050509734809 111879457467120037882301107)
  ·
    refine ⟨167819186200680056823451661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111879457467120037882301107 167819186200680056823451661)
    ·
      refine ⟨62932194825255021308794373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167819186200680056823451661 62932194825255021308794373)
      ·
        refine ⟨11799786529735316495398945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62932194825255021308794373 11799786529735316495398945)
        ·
          refine ⟨8849839897301487371549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11799786529735316495398945 8849839897301487371549209)
          ·
            refine ⟨6637379922976115528661907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8849839897301487371549209 6637379922976115528661907)
            ·
              refine ⟨9956069884464173292992861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637379922976115528661907 9956069884464173292992861)
              ·
                refine ⟨3733526206674064984872323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9956069884464173292992861 3733526206674064984872323)
                ·
                  refine ⟨5600289310011097477308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733526206674064984872323 5600289310011097477308485)
                  ·
                    refine ⟨1050054245627080776995341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600289310011097477308485 1050054245627080776995341)
                    ·
                      rfl

theorem cell23_6134920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_6134920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134920 prefixEnd_6134920 := by exact prefixLift 6134920
  have htrace : WordTrace (prefixWord ++ tailWord_6134920) baseStart_6134920 baseEnd_6134920 := by
    simpa [prefixWord, tailWord_6134920, baseEnd_6134920] using wordTrace_append hprefix tailTrace_6134920
  have hstable : (prefixWord ++ tailWord_6134920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134920).length < 2 ^ (prefixWord ++ tailWord_6134920).sum := by decide
  have hdescent : baseEnd_6134920 < baseStart_6134920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134936 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6134936 : Nat := 118140960795 + 6134936 * 2 ^ 59
def prefixEnd_6134936 : Nat := 4983230072969 + 3 ^ 40 * 6134936 * 2
def baseEnd_6134936 : Nat := 3150170952571714268385949

theorem tailTrace_6134936 : CollatzResearch.WordTrace tailWord_6134936 prefixEnd_6134936 3150170952571714268385949 := by
  unfold tailWord_6134936
  simp only [CollatzResearch.WordTrace]
  refine ⟨111879749251091055248592331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149172999001454740331456441 111879749251091055248592331)
  ·
    refine ⟨167819623876636582872888497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111879749251091055248592331 167819623876636582872888497)
    ·
      refine ⟨125864717907477437154666373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167819623876636582872888497 125864717907477437154666373)
      ·
        refine ⟨23599634607652019466499945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125864717907477437154666373 23599634607652019466499945)
        ·
          refine ⟨17699725955739014599874959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23599634607652019466499945 17699725955739014599874959)
          ·
            refine ⟨26549588933608521899812439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17699725955739014599874959 26549588933608521899812439)
            ·
              refine ⟨39824383400412782849718659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26549588933608521899812439 39824383400412782849718659)
              ·
                refine ⟨59736575100619174274577989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39824383400412782849718659 59736575100619174274577989)
                ·
                  refine ⟨11200607831366095176483373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59736575100619174274577989 11200607831366095176483373)
                  ·
                    refine ⟨4200227936762285691181265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11200607831366095176483373 4200227936762285691181265)
                    ·
                      refine ⟨3150170952571714268385949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200227936762285691181265 3150170952571714268385949)
                      ·
                        rfl

theorem cell23_6134936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6134936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134936 prefixEnd_6134936 := by exact prefixLift 6134936
  have htrace : WordTrace (prefixWord ++ tailWord_6134936) baseStart_6134936 baseEnd_6134936 := by
    simpa [prefixWord, tailWord_6134936, baseEnd_6134936] using wordTrace_append hprefix tailTrace_6134936
  have hstable : (prefixWord ++ tailWord_6134936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134936).length < 2 ^ (prefixWord ++ tailWord_6134936).sum := by decide
  have hdescent : baseEnd_6134936 < baseStart_6134936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6134986 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_6134986 : Nat := 118140960795 + 6134986 * 2 ^ 59
def prefixEnd_6134986 : Nat := 4983230072969 + 3 ^ 40 * 6134986 * 2
def baseEnd_6134986 : Nat := 3150196626604439072760719

theorem tailTrace_6134986 : CollatzResearch.WordTrace tailWord_6134986 prefixEnd_6134986 3150196626604439072760719 := by
  unfold tailWord_6134986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55940330538000242259126203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149174214768000646024336541 55940330538000242259126203)
  ·
    refine ⟨83910495807000363388689305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55940330538000242259126203 83910495807000363388689305)
    ·
      refine ⟨62932871855250272541516979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83910495807000363388689305 62932871855250272541516979)
      ·
        refine ⟨94399307782875408812275469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62932871855250272541516979 94399307782875408812275469)
        ·
          refine ⟨35399740418578278304603301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94399307782875408812275469 35399740418578278304603301)
          ·
            refine ⟨6637451328483427182113119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35399740418578278304603301 6637451328483427182113119)
            ·
              refine ⟨9956176992725140773169679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637451328483427182113119 9956176992725140773169679)
              ·
                refine ⟨14934265489087711159754519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956176992725140773169679 14934265489087711159754519)
                ·
                  refine ⟨22401398233631566739631779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14934265489087711159754519 22401398233631566739631779)
                  ·
                    refine ⟨33602097350447350109447669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22401398233631566739631779 33602097350447350109447669)
                    ·
                      refine ⟨3150196626604439072760719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33602097350447350109447669 3150196626604439072760719)
                      ·
                        rfl

theorem cell23_6134986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_6134986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6134986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6134986 prefixEnd_6134986 := by exact prefixLift 6134986
  have htrace : WordTrace (prefixWord ++ tailWord_6134986) baseStart_6134986 baseEnd_6134986 := by
    simpa [prefixWord, tailWord_6134986, baseEnd_6134986] using wordTrace_append hprefix tailTrace_6134986
  have hstable : (prefixWord ++ tailWord_6134986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6134986).length < 2 ^ (prefixWord ++ tailWord_6134986).sum := by decide
  have hdescent : baseEnd_6134986 < baseStart_6134986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6134986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135016 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6135016 : Nat := 118140960795 + 6135016 * 2 ^ 59
def prefixEnd_6135016 : Nat := 4983230072969 + 3 ^ 40 * 6135016 * 2
def baseEnd_6135016 : Nat := 3150212031024073955385581

theorem tailTrace_6135016 : CollatzResearch.WordTrace tailWord_6135016 prefixEnd_6135016 3150212031024073955385581 := by
  unfold tailWord_6135016
  simp only [CollatzResearch.WordTrace]
  refine ⟨111881208170946142080048451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149174944227928189440064601 111881208170946142080048451)
  ·
    refine ⟨167821812256419213120072677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111881208170946142080048451 167821812256419213120072677)
    ·
      refine ⟨31466589798078602460013627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167821812256419213120072677 31466589798078602460013627)
      ·
        refine ⟨47199884697117903690020441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31466589798078602460013627 47199884697117903690020441)
        ·
          refine ⟨35399913522838427767515331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47199884697117903690020441 35399913522838427767515331)
          ·
            refine ⟨53099870284257641651272997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35399913522838427767515331 53099870284257641651272997)
            ·
              refine ⟨9956225678298307809613687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53099870284257641651272997 9956225678298307809613687)
              ·
                refine ⟨14934338517447461714420531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956225678298307809613687 14934338517447461714420531)
                ·
                  refine ⟨22401507776171192571630797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14934338517447461714420531 22401507776171192571630797)
                  ·
                    refine ⟨8400565416064197214361549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22401507776171192571630797 8400565416064197214361549)
                    ·
                      refine ⟨3150212031024073955385581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8400565416064197214361549 3150212031024073955385581)
                      ·
                        rfl

theorem cell23_6135016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6135016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135016 prefixEnd_6135016 := by exact prefixLift 6135016
  have htrace : WordTrace (prefixWord ++ tailWord_6135016) baseStart_6135016 baseEnd_6135016 := by
    simpa [prefixWord, tailWord_6135016, baseEnd_6135016] using wordTrace_append hprefix tailTrace_6135016
  have hstable : (prefixWord ++ tailWord_6135016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135016).length < 2 ^ (prefixWord ++ tailWord_6135016).sum := by decide
  have hdescent : baseEnd_6135016 < baseStart_6135016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135043 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 1, 3, 2]
def baseStart_6135043 : Nat := 118140960795 + 6135043 * 2 ^ 59
def prefixEnd_6135043 : Nat := 4983230072969 + 3 ^ 40 * 6135043 * 2
def baseEnd_6135043 : Nat := 3150225895001745349747957

theorem tailTrace_6135043 : CollatzResearch.WordTrace tailWord_6135043 prefixEnd_6135043 3150225895001745349747957 := by
  unfold tailWord_6135043
  simp only [CollatzResearch.WordTrace]
  refine ⟨223763401112794467771329783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149175600741862978514219855 223763401112794467771329783)
  ·
    refine ⟨335645101669191701656994675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223763401112794467771329783 335645101669191701656994675)
    ·
      refine ⟨503467652503787552485492013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335645101669191701656994675 503467652503787552485492013)
      ·
        refine ⟨188800369688920332182059505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503467652503787552485492013 188800369688920332182059505)
        ·
          refine ⟨141600277266690249136544629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188800369688920332182059505 141600277266690249136544629)
          ·
            refine ⟨13275025993752210856551059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141600277266690249136544629 13275025993752210856551059)
            ·
              refine ⟨19912538990628316284826589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275025993752210856551059 19912538990628316284826589)
              ·
                refine ⟨7467202121485618606809971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19912538990628316284826589 7467202121485618606809971)
                ·
                  refine ⟨11200803182228427910214957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7467202121485618606809971 11200803182228427910214957)
                  ·
                    refine ⟨4200301193335660466330609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11200803182228427910214957 4200301193335660466330609)
                    ·
                      refine ⟨3150225895001745349747957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200301193335660466330609 3150225895001745349747957)
                      ·
                        rfl

theorem cell23_6135043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_6135043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135043 prefixEnd_6135043 := by exact prefixLift 6135043
  have htrace : WordTrace (prefixWord ++ tailWord_6135043) baseStart_6135043 baseEnd_6135043 := by
    simpa [prefixWord, tailWord_6135043, baseEnd_6135043] using wordTrace_append hprefix tailTrace_6135043
  have hstable : (prefixWord ++ tailWord_6135043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135043).length < 2 ^ (prefixWord ++ tailWord_6135043).sum := by decide
  have hdescent : baseEnd_6135043 < baseStart_6135043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135129 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_6135129 : Nat := 118140960795 + 6135129 * 2 ^ 59
def prefixEnd_6135129 : Nat := 4983230072969 + 3 ^ 40 * 6135129 * 2
def baseEnd_6135129 : Nat := 3150270054338032013272561

theorem tailTrace_6135129 : CollatzResearch.WordTrace tailWord_6135129 prefixEnd_6135129 3150270054338032013272561 := by
  unfold tailWord_6135129
  simp only [CollatzResearch.WordTrace]
  refine ⟨223766537790482904458960441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149177691860321936305973627 223766537790482904458960441)
  ·
    refine ⟨167824903342862178344220331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223766537790482904458960441 167824903342862178344220331)
    ·
      refine ⟨251737355014293267516330497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167824903342862178344220331 251737355014293267516330497)
      ·
        refine ⟨188803016260719950637247873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251737355014293267516330497 188803016260719950637247873)
        ·
          refine ⟨141602262195539962977935905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188803016260719950637247873 141602262195539962977935905)
          ·
            refine ⟨106201696646654972233451929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141602262195539962977935905 106201696646654972233451929)
            ·
              refine ⟨79651272484991229175088947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106201696646654972233451929 79651272484991229175088947)
              ·
                refine ⟨119476908727486843762633421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79651272484991229175088947 119476908727486843762633421)
                ·
                  refine ⟨44803840772807566410987533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119476908727486843762633421 44803840772807566410987533)
                  ·
                    refine ⟨16801440289802837404120325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44803840772807566410987533 16801440289802837404120325)
                    ·
                      refine ⟨3150270054338032013272561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16801440289802837404120325 3150270054338032013272561)
                      ·
                        rfl

theorem cell23_6135129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_6135129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135129 prefixEnd_6135129 := by exact prefixLift 6135129
  have htrace : WordTrace (prefixWord ++ tailWord_6135129) baseStart_6135129 baseEnd_6135129 := by
    simpa [prefixWord, tailWord_6135129, baseEnd_6135129] using wordTrace_append hprefix tailTrace_6135129
  have hstable : (prefixWord ++ tailWord_6135129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135129).length < 2 ^ (prefixWord ++ tailWord_6135129).sum := by decide
  have hdescent : baseEnd_6135129 < baseStart_6135129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135143 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 2, 5]
def baseStart_6135143 : Nat := 118140960795 + 6135143 * 2 ^ 59
def prefixEnd_6135143 : Nat := 4983230072969 + 3 ^ 40 * 6135143 * 2
def baseEnd_6135143 : Nat := 1050092414355731652832499

theorem tailTrace_6135143 : CollatzResearch.WordTrace tailWord_6135143 prefixEnd_6135143 1050092414355731652832499 := by
  unfold tailWord_6135143
  simp only [CollatzResearch.WordTrace]
  refine ⟨223767048412432184849970083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149178032274954789899980055 223767048412432184849970083)
  ·
    refine ⟨335650572618648277274955125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223767048412432184849970083 335650572618648277274955125)
    ·
      refine ⟨31467241182998275994527043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 335650572618648277274955125 31467241182998275994527043)
      ·
        refine ⟨47200861774497413991790565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31467241182998275994527043 47200861774497413991790565)
        ·
          refine ⟨8850161582718265123460731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47200861774497413991790565 8850161582718265123460731)
          ·
            refine ⟨13275242374077397685191097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850161582718265123460731 13275242374077397685191097)
            ·
              refine ⟨9956431780558048263893323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13275242374077397685191097 9956431780558048263893323)
              ·
                refine ⟨14934647670837072395839985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956431780558048263893323 14934647670837072395839985)
                ·
                  refine ⟨11200985753127804296879989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14934647670837072395839985 11200985753127804296879989)
                  ·
                    refine ⟨1050092414355731652832499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11200985753127804296879989 1050092414355731652832499)
                    ·
                      rfl

theorem cell23_6135143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_6135143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135143 prefixEnd_6135143 := by exact prefixLift 6135143
  have htrace : WordTrace (prefixWord ++ tailWord_6135143) baseStart_6135143 baseEnd_6135143 := by
    simpa [prefixWord, tailWord_6135143, baseEnd_6135143] using wordTrace_append hprefix tailTrace_6135143
  have hstable : (prefixWord ++ tailWord_6135143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135143).length < 2 ^ (prefixWord ++ tailWord_6135143).sum := by decide
  have hdescent : baseEnd_6135143 < baseStart_6135143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135159 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_6135159 : Nat := 118140960795 + 6135159 * 2 ^ 59
def prefixEnd_6135159 : Nat := 4983230072969 + 3 ^ 40 * 6135159 * 2
def baseEnd_6135159 : Nat := 3150285458757666895897423

theorem tailTrace_6135159 : CollatzResearch.WordTrace tailWord_6135159 prefixEnd_6135159 3150285458757666895897423 := by
  unfold tailWord_6135159
  simp only [CollatzResearch.WordTrace]
  refine ⟨223767631980374219582552531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149178421320249479721701687 223767631980374219582552531)
  ·
    refine ⟨335651447970561329373828797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223767631980374219582552531 335651447970561329373828797)
    ·
      refine ⟨125869292988960498515185799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335651447970561329373828797 125869292988960498515185799)
      ·
        refine ⟨188803939483440747772778699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125869292988960498515185799 188803939483440747772778699)
        ·
          refine ⟨283205909225161121659168049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188803939483440747772778699 283205909225161121659168049)
          ·
            refine ⟨212404431918870841244376037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283205909225161121659168049 212404431918870841244376037)
            ·
              refine ⟨39825830984788282733320507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212404431918870841244376037 39825830984788282733320507)
              ·
                refine ⟨59738746477182424099980761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39825830984788282733320507 59738746477182424099980761)
                ·
                  refine ⟨44804059857886818074985571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59738746477182424099980761 44804059857886818074985571)
                  ·
                    refine ⟨67206089786830227112478357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44804059857886818074985571 67206089786830227112478357)
                    ·
                      refine ⟨3150285458757666895897423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67206089786830227112478357 3150285458757666895897423)
                      ·
                        rfl

theorem cell23_6135159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_6135159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135159 prefixEnd_6135159 := by exact prefixLift 6135159
  have htrace : WordTrace (prefixWord ++ tailWord_6135159) baseStart_6135159 baseEnd_6135159 := by
    simpa [prefixWord, tailWord_6135159, baseEnd_6135159] using wordTrace_append hprefix tailTrace_6135159
  have hstable : (prefixWord ++ tailWord_6135159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135159).length < 2 ^ (prefixWord ++ tailWord_6135159).sum := by decide
  have hdescent : baseEnd_6135159 < baseStart_6135159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135209 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_6135209 : Nat := 118140960795 + 6135209 * 2 ^ 59
def prefixEnd_6135209 : Nat := 4983230072969 + 3 ^ 40 * 6135209 * 2
def baseEnd_6135209 : Nat := 3150311132790391700272193

theorem tailTrace_6135209 : CollatzResearch.WordTrace tailWord_6135209 prefixEnd_6135209 3150311132790391700272193 := by
  unfold tailWord_6135209
  simp only [CollatzResearch.WordTrace]
  refine ⟨223769455630193078121872681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149179637086795385414581787 223769455630193078121872681)
  ·
    refine ⟨167827091722644808591404511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223769455630193078121872681 167827091722644808591404511)
    ·
      refine ⟨251740637583967212887106767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167827091722644808591404511 251740637583967212887106767)
      ·
        refine ⟨377610956375950819330660151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251740637583967212887106767 377610956375950819330660151)
        ·
          refine ⟨566416434563926228995990227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377610956375950819330660151 566416434563926228995990227)
          ·
            refine ⟨849624651845889343493985341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566416434563926228995990227 849624651845889343493985341)
            ·
              refine ⟨318609244442208503810244503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849624651845889343493985341 318609244442208503810244503)
              ·
                refine ⟨477913866663312755715366755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318609244442208503810244503 477913866663312755715366755)
                ·
                  refine ⟨716870799994969133573050133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477913866663312755715366755 716870799994969133573050133)
                  ·
                    refine ⟨33603318749764178136236725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 716870799994969133573050133 33603318749764178136236725)
                    ·
                      refine ⟨3150311132790391700272193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33603318749764178136236725 3150311132790391700272193)
                      ·
                        rfl

theorem cell23_6135209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_6135209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135209 prefixEnd_6135209 := by exact prefixLift 6135209
  have htrace : WordTrace (prefixWord ++ tailWord_6135209) baseStart_6135209 baseEnd_6135209 := by
    simpa [prefixWord, tailWord_6135209, baseEnd_6135209] using wordTrace_append hprefix tailTrace_6135209
  have hstable : (prefixWord ++ tailWord_6135209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135209).length < 2 ^ (prefixWord ++ tailWord_6135209).sum := by decide
  have hdescent : baseEnd_6135209 < baseStart_6135209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135223 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_6135223 : Nat := 118140960795 + 6135223 * 2 ^ 59
def prefixEnd_6135223 : Nat := 4983230072969 + 3 ^ 40 * 6135223 * 2
def baseEnd_6135223 : Nat := 3150318321519554645497129

theorem tailTrace_6135223 : CollatzResearch.WordTrace tailWord_6135223 prefixEnd_6135223 3150318321519554645497129 := by
  unfold tailWord_6135223
  simp only [CollatzResearch.WordTrace]
  refine ⟨223769966252142358512882323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149179977501428239008588215 223769966252142358512882323)
  ·
    refine ⟨335654949378213537769323485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223769966252142358512882323 335654949378213537769323485)
    ·
      refine ⟨125870606016830076663496307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335654949378213537769323485 125870606016830076663496307)
      ·
        refine ⟨188805909025245114995244461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125870606016830076663496307 188805909025245114995244461)
        ·
          refine ⟨70802215884466918123216673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188805909025245114995244461 70802215884466918123216673)
          ·
            refine ⟨53101661913350188592412505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70802215884466918123216673 53101661913350188592412505)
            ·
              refine ⟨39826246435012641444309379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53101661913350188592412505 39826246435012641444309379)
              ·
                refine ⟨59739369652518962166464069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39826246435012641444309379 59739369652518962166464069)
                ·
                  refine ⟨11201131809847305406212013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59739369652518962166464069 11201131809847305406212013)
                  ·
                    refine ⟨4200424428692739527329505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11201131809847305406212013 4200424428692739527329505)
                    ·
                      refine ⟨3150318321519554645497129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200424428692739527329505 3150318321519554645497129)
                      ·
                        rfl

theorem cell23_6135223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_6135223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135223 prefixEnd_6135223 := by exact prefixLift 6135223
  have htrace : WordTrace (prefixWord ++ tailWord_6135223) baseStart_6135223 baseEnd_6135223 := by
    simpa [prefixWord, tailWord_6135223, baseEnd_6135223] using wordTrace_append hprefix tailTrace_6135223
  have hstable : (prefixWord ++ tailWord_6135223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135223).length < 2 ^ (prefixWord ++ tailWord_6135223).sum := by decide
  have hdescent : baseEnd_6135223 < baseStart_6135223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135253 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6135253 : Nat := 118140960795 + 6135253 * 2 ^ 59
def prefixEnd_6135253 : Nat := 4983230072969 + 3 ^ 40 * 6135253 * 2
def baseEnd_6135253 : Nat := 3150333725939189528121991

theorem tailTrace_6135253 : CollatzResearch.WordTrace tailWord_6135253 prefixEnd_6135253 3150333725939189528121991 := by
  unfold tailWord_6135253
  simp only [CollatzResearch.WordTrace]
  refine ⟨223771060442033673636474413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149180706961355782424316275 223771060442033673636474413)
  ·
    refine ⟨83914147665762627613677905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223771060442033673636474413 83914147665762627613677905)
    ·
      refine ⟨62935610749321970710258429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83914147665762627613677905 62935610749321970710258429)
      ·
        refine ⟨23600854030995739016346911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62935610749321970710258429 23600854030995739016346911)
        ·
          refine ⟨35401281046493608524520367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23600854030995739016346911 35401281046493608524520367)
          ·
            refine ⟨53101921569740412786780551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35401281046493608524520367 53101921569740412786780551)
            ·
              refine ⟨79652882354610619180170827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53101921569740412786780551 79652882354610619180170827)
              ·
                refine ⟨119479323531915928770256241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79652882354610619180170827 119479323531915928770256241)
                ·
                  refine ⟨89609492648936946577692181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119479323531915928770256241 89609492648936946577692181)
                  ·
                    refine ⟨4200444967918919370829321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89609492648936946577692181 4200444967918919370829321)
                    ·
                      refine ⟨3150333725939189528121991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200444967918919370829321 3150333725939189528121991)
                      ·
                        rfl

theorem cell23_6135253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6135253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135253 prefixEnd_6135253 := by exact prefixLift 6135253
  have htrace : WordTrace (prefixWord ++ tailWord_6135253) baseStart_6135253 baseEnd_6135253 := by
    simpa [prefixWord, tailWord_6135253, baseEnd_6135253] using wordTrace_append hprefix tailTrace_6135253
  have hstable : (prefixWord ++ tailWord_6135253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135253).length < 2 ^ (prefixWord ++ tailWord_6135253).sum := by decide
  have hdescent : baseEnd_6135253 < baseStart_6135253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135307 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 3]
def baseStart_6135307 : Nat := 118140960795 + 6135307 * 2 ^ 59
def prefixEnd_6135307 : Nat := 4983230072969 + 3 ^ 40 * 6135307 * 2
def baseEnd_6135307 : Nat := 3150361453894532316846743

theorem tailTrace_6135307 : CollatzResearch.WordTrace tailWord_6135307 prefixEnd_6135307 3150361453894532316846743 := by
  unfold tailWord_6135307
  simp only [CollatzResearch.WordTrace]
  refine ⟨223773029983838040858940175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149182019989225360572626783 223773029983838040858940175)
  ·
    refine ⟨335659544975757061288410263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223773029983838040858940175 335659544975757061288410263)
    ·
      refine ⟨503489317463635591932615395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335659544975757061288410263 503489317463635591932615395)
      ·
        refine ⟨755233976195453387898923093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503489317463635591932615395 755233976195453387898923093)
        ·
          refine ⟨8850398158540469389440505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 755233976195453387898923093 8850398158540469389440505)
          ·
            refine ⟨6637798618905352042080379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8850398158540469389440505 6637798618905352042080379)
            ·
              refine ⟨9956697928358028063120569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637798618905352042080379 9956697928358028063120569)
              ·
                refine ⟨7467523446268521047340427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9956697928358028063120569 7467523446268521047340427)
                ·
                  refine ⟨11201285169402781571010641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7467523446268521047340427 11201285169402781571010641)
                  ·
                    refine ⟨8400963877052086178257981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11201285169402781571010641 8400963877052086178257981)
                    ·
                      refine ⟨3150361453894532316846743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8400963877052086178257981 3150361453894532316846743)
                      ·
                        rfl

theorem cell23_6135307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 3].length) (baseStart_6135307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135307 prefixEnd_6135307 := by exact prefixLift 6135307
  have htrace : WordTrace (prefixWord ++ tailWord_6135307) baseStart_6135307 baseEnd_6135307 := by
    simpa [prefixWord, tailWord_6135307, baseEnd_6135307] using wordTrace_append hprefix tailTrace_6135307
  have hstable : (prefixWord ++ tailWord_6135307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135307).length < 2 ^ (prefixWord ++ tailWord_6135307).sum := by decide
  have hdescent : baseEnd_6135307 < baseStart_6135307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135320 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6135320 : Nat := 118140960795 + 6135320 * 2 ^ 59
def prefixEnd_6135320 : Nat := 4983230072969 + 3 ^ 40 * 6135320 * 2
def baseEnd_6135320 : Nat := 3150368129143040765984183

theorem tailTrace_6135320 : CollatzResearch.WordTrace tailWord_6135320 prefixEnd_6135320 3150368129143040765984183 := by
  unfold tailWord_6135320
  simp only [CollatzResearch.WordTrace]
  refine ⟨111886752066395472039581707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149182336088527296052775609 111886752066395472039581707)
  ·
    refine ⟨167830128099593208059372561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111886752066395472039581707 167830128099593208059372561)
    ·
      refine ⟨125872596074694906044529421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167830128099593208059372561 125872596074694906044529421)
      ·
        refine ⟨47202223528010589766698533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125872596074694906044529421 47202223528010589766698533)
        ·
          refine ⟨8850416911501985581255975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47202223528010589766698533 8850416911501985581255975)
          ·
            refine ⟨13275625367252978371883963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850416911501985581255975 13275625367252978371883963)
            ·
              refine ⟨19913438050879467557825945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275625367252978371883963 19913438050879467557825945)
              ·
                refine ⟨14935078538159600668369459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19913438050879467557825945 14935078538159600668369459)
                ·
                  refine ⟨22402617807239401002554189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14935078538159600668369459 22402617807239401002554189)
                  ·
                    refine ⟨8400981677714775375957821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22402617807239401002554189 8400981677714775375957821)
                    ·
                      refine ⟨3150368129143040765984183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8400981677714775375957821 3150368129143040765984183)
                      ·
                        rfl

theorem cell23_6135320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6135320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135320 prefixEnd_6135320 := by exact prefixLift 6135320
  have htrace : WordTrace (prefixWord ++ tailWord_6135320) baseStart_6135320 baseEnd_6135320 := by
    simpa [prefixWord, tailWord_6135320, baseEnd_6135320] using wordTrace_append hprefix tailTrace_6135320
  have hstable : (prefixWord ++ tailWord_6135320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135320).length < 2 ^ (prefixWord ++ tailWord_6135320).sum := by decide
  have hdescent : baseEnd_6135320 < baseStart_6135320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135353 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_6135353 : Nat := 118140960795 + 6135353 * 2 ^ 59
def prefixEnd_6135353 : Nat := 4983230072969 + 3 ^ 40 * 6135353 * 2
def baseEnd_6135353 : Nat := 1050128358001546378957177

theorem tailTrace_6135353 : CollatzResearch.WordTrace tailWord_6135353 prefixEnd_6135353 1050128358001546378957177 := by
  unfold tailWord_6135353
  simp only [CollatzResearch.WordTrace]
  refine ⟨223774707741671390715114713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149183138494447593810076475 223774707741671390715114713)
  ·
    refine ⟨167831030806253543036336035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223774707741671390715114713 167831030806253543036336035)
    ·
      refine ⟨251746546209380314554504053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167831030806253543036336035 251746546209380314554504053)
      ·
        refine ⟨23601238707129404489484755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251746546209380314554504053 23601238707129404489484755)
        ·
          refine ⟨35401858060694106734227133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23601238707129404489484755 35401858060694106734227133)
          ·
            refine ⟨13275696772760290025335175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35401858060694106734227133 13275696772760290025335175)
            ·
              refine ⟨19913545159140435038002763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13275696772760290025335175 19913545159140435038002763)
              ·
                refine ⟨29870317738710652557004145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19913545159140435038002763 29870317738710652557004145)
                ·
                  refine ⟨22402738304032989417753109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29870317738710652557004145 22402738304032989417753109)
                  ·
                    refine ⟨1050128358001546378957177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22402738304032989417753109 1050128358001546378957177)
                    ·
                      rfl

theorem cell23_6135353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_6135353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135353 prefixEnd_6135353 := by exact prefixLift 6135353
  have htrace : WordTrace (prefixWord ++ tailWord_6135353) baseStart_6135353 baseEnd_6135353 := by
    simpa [prefixWord, tailWord_6135353, baseEnd_6135353] using wordTrace_append hprefix tailTrace_6135353
  have hstable : (prefixWord ++ tailWord_6135353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135353).length < 2 ^ (prefixWord ++ tailWord_6135353).sum := by decide
  have hdescent : baseEnd_6135353 < baseStart_6135353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135360 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2]
def baseStart_6135360 : Nat := 118140960795 + 6135360 * 2 ^ 59
def prefixEnd_6135360 : Nat := 4983230072969 + 3 ^ 40 * 6135360 * 2
def baseEnd_6135360 : Nat := 3150388668369220609483999

theorem tailTrace_6135360 : CollatzResearch.WordTrace tailWord_6135360 prefixEnd_6135360 3150388668369220609483999 := by
  unfold tailWord_6135360
  simp only [CollatzResearch.WordTrace]
  refine ⟨111887481526323015455309767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149183308701764020607079689 111887481526323015455309767)
  ·
    refine ⟨167831222289484523182964651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111887481526323015455309767 167831222289484523182964651)
    ·
      refine ⟨251746833434226784774446977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167831222289484523182964651 251746833434226784774446977)
      ·
        refine ⟨188810125075670088580835233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251746833434226784774446977 188810125075670088580835233)
        ·
          refine ⟨141607593806752566435626425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188810125075670088580835233 141607593806752566435626425)
          ·
            refine ⟨106205695355064424826719819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141607593806752566435626425 106205695355064424826719819)
            ·
              refine ⟨159308543032596637240079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106205695355064424826719819 159308543032596637240079729)
              ·
                refine ⟨119481407274447477930059797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159308543032596637240079729 119481407274447477930059797)
                ·
                  refine ⟨5600690965989725527971553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119481407274447477930059797 5600690965989725527971553)
                  ·
                    refine ⟨4200518224492294145978665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5600690965989725527971553 4200518224492294145978665)
                    ·
                      refine ⟨3150388668369220609483999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200518224492294145978665 3150388668369220609483999)
                      ·
                        rfl

theorem cell23_6135360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_6135360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135360 prefixEnd_6135360 := by exact prefixLift 6135360
  have htrace : WordTrace (prefixWord ++ tailWord_6135360) baseStart_6135360 baseEnd_6135360 := by
    simpa [prefixWord, tailWord_6135360, baseEnd_6135360] using wordTrace_append hprefix tailTrace_6135360
  have hstable : (prefixWord ++ tailWord_6135360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135360).length < 2 ^ (prefixWord ++ tailWord_6135360).sum := by decide
  have hdescent : baseEnd_6135360 < baseStart_6135360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135393 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_6135393 : Nat := 118140960795 + 6135393 * 2 ^ 59
def prefixEnd_6135393 : Nat := 4983230072969 + 3 ^ 40 * 6135393 * 2
def baseEnd_6135393 : Nat := 3150405613230818980371347

theorem tailTrace_6135393 : CollatzResearch.WordTrace tailWord_6135393 prefixEnd_6135393 3150405613230818980371347 := by
  unfold tailWord_6135393
  simp only [CollatzResearch.WordTrace]
  refine ⟨223776166661526477546570833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149184111107684318364380555 223776166661526477546570833)
  ·
    refine ⟨167832124996144858159928125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223776166661526477546570833 167832124996144858159928125)
    ·
      refine ⟨62937046873554321809973047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167832124996144858159928125 62937046873554321809973047)
      ·
        refine ⟨94405570310331482714959571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62937046873554321809973047 94405570310331482714959571)
        ·
          refine ⟨141608355465497224072439357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94405570310331482714959571 141608355465497224072439357)
          ·
            refine ⟨53103133299561459027164759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141608355465497224072439357 53103133299561459027164759)
            ·
              refine ⟨79654699949342188540747139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53103133299561459027164759 79654699949342188540747139)
              ·
                refine ⟨119482049924013282811120709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79654699949342188540747139 119482049924013282811120709)
                ·
                  refine ⟨22402884360752490527085133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119482049924013282811120709 22402884360752490527085133)
                  ·
                    refine ⟨8401081635282183947656925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22402884360752490527085133 8401081635282183947656925)
                    ·
                      refine ⟨3150405613230818980371347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8401081635282183947656925 3150405613230818980371347)
                      ·
                        rfl

theorem cell23_6135393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_6135393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135393 prefixEnd_6135393 := by exact prefixLift 6135393
  have htrace : WordTrace (prefixWord ++ tailWord_6135393) baseStart_6135393 baseEnd_6135393 := by
    simpa [prefixWord, tailWord_6135393, baseEnd_6135393] using wordTrace_append hprefix tailTrace_6135393
  have hstable : (prefixWord ++ tailWord_6135393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135393).length < 2 ^ (prefixWord ++ tailWord_6135393).sum := by decide
  have hdescent : baseEnd_6135393 < baseStart_6135393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135400 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 7]
def baseStart_6135400 : Nat := 118140960795 + 6135400 * 2 ^ 59
def prefixEnd_6135400 : Nat := 4983230072969 + 3 ^ 40 * 6135400 * 2
def baseEnd_6135400 : Nat := 350045467510600050331535

theorem tailTrace_6135400 : CollatzResearch.WordTrace tailWord_6135400 prefixEnd_6135400 350045467510600050331535 := by
  unfold tailWord_6135400
  simp only [CollatzResearch.WordTrace]
  refine ⟨111888210986250558871037827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149184281315000745161383769 111888210986250558871037827)
  ·
    refine ⟨167832316479375838306556741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111888210986250558871037827 167832316479375838306556741)
    ·
      refine ⟨31468559339882969682479389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167832316479375838306556741 31468559339882969682479389)
      ·
        refine ⟨11800709752456113630929771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31468559339882969682479389 11800709752456113630929771)
        ·
          refine ⟨17701064628684170446394657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800709752456113630929771 17701064628684170446394657)
          ·
            refine ⟨13275798471513127834795993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17701064628684170446394657 13275798471513127834795993)
            ·
              refine ⟨9956848853634845876096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13275798471513127834795993 9956848853634845876096995)
              ·
                refine ⟨14935273280452268814145493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956848853634845876096995 14935273280452268814145493)
                ·
                  refine ⟨350045467510600050331535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14935273280452268814145493 350045467510600050331535)
                  ·
                    rfl

theorem cell23_6135400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_6135400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135400 prefixEnd_6135400 := by exact prefixLift 6135400
  have htrace : WordTrace (prefixWord ++ tailWord_6135400) baseStart_6135400 baseEnd_6135400 := by
    simpa [prefixWord, tailWord_6135400, baseEnd_6135400] using wordTrace_append hprefix tailTrace_6135400
  have hstable : (prefixWord ++ tailWord_6135400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135400).length < 2 ^ (prefixWord ++ tailWord_6135400).sum := by decide
  have hdescent : baseEnd_6135400 < baseStart_6135400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135410 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6135410 : Nat := 118140960795 + 6135410 * 2 ^ 59
def prefixEnd_6135410 : Nat := 4983230072969 + 3 ^ 40 * 6135410 * 2
def baseEnd_6135410 : Nat := 3150414342401945413858769

theorem tailTrace_6135410 : CollatzResearch.WordTrace tailWord_6135410 prefixEnd_6135410 3150414342401945413858769 := by
  unfold tailWord_6135410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55944196675616222362484921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149184524468309926299959789 55944196675616222362484921)
  ·
    refine ⟨41958147506712166771863691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55944196675616222362484921 41958147506712166771863691)
    ·
      refine ⟨62937221260068250157795537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41958147506712166771863691 62937221260068250157795537)
      ·
        refine ⟨47202915945051187618346653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62937221260068250157795537 47202915945051187618346653)
        ·
          refine ⟨17701093479394195356879995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47202915945051187618346653 17701093479394195356879995)
          ·
            refine ⟨26551640219091293035319993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17701093479394195356879995 26551640219091293035319993)
            ·
              refine ⟨19913730164318469776489995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26551640219091293035319993 19913730164318469776489995)
              ·
                refine ⟨29870595246477704664734993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19913730164318469776489995 29870595246477704664734993)
                ·
                  refine ⟨22402946434858278498551245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29870595246477704664734993 22402946434858278498551245)
                  ·
                    refine ⟨8401104913071854436956717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22402946434858278498551245 8401104913071854436956717)
                    ·
                      refine ⟨3150414342401945413858769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8401104913071854436956717 3150414342401945413858769)
                      ·
                        rfl

theorem cell23_6135410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6135410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135410 prefixEnd_6135410 := by exact prefixLift 6135410
  have htrace : WordTrace (prefixWord ++ tailWord_6135410) baseStart_6135410 baseEnd_6135410 := by
    simpa [prefixWord, tailWord_6135410, baseEnd_6135410] using wordTrace_append hprefix tailTrace_6135410
  have hstable : (prefixWord ++ tailWord_6135410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135410).length < 2 ^ (prefixWord ++ tailWord_6135410).sum := by decide
  have hdescent : baseEnd_6135410 < baseStart_6135410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135433 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_6135433 : Nat := 118140960795 + 6135433 * 2 ^ 59
def prefixEnd_6135433 : Nat := 4983230072969 + 3 ^ 40 * 6135433 * 2
def baseEnd_6135433 : Nat := 3150426152456998823871163

theorem tailTrace_6135433 : CollatzResearch.WordTrace tailWord_6135433 prefixEnd_6135433 3150426152456998823871163 := by
  unfold tailWord_6135433
  simp only [CollatzResearch.WordTrace]
  refine ⟨223777625581381564378026953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149185083720921042918684635 223777625581381564378026953)
  ·
    refine ⟨167833219186036173283520215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223777625581381564378026953 167833219186036173283520215)
    ·
      refine ⟨251749828779054259925280323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167833219186036173283520215 251749828779054259925280323)
      ·
        refine ⟨377624743168581389887920485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251749828779054259925280323 377624743168581389887920485)
        ·
          refine ⟨70804639344109010603985091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377624743168581389887920485 70804639344109010603985091)
          ·
            refine ⟨106206959016163515905977637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70804639344109010603985091 106206959016163515905977637)
            ·
              refine ⟨19913804815530659232370807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106206959016163515905977637 19913804815530659232370807)
              ·
                refine ⟨29870707223295988848556211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19913804815530659232370807 29870707223295988848556211)
                ·
                  refine ⟨44806060834943983272834317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29870707223295988848556211 44806060834943983272834317)
                  ·
                    refine ⟨16802272813103993727312869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44806060834943983272834317 16802272813103993727312869)
                    ·
                      refine ⟨3150426152456998823871163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16802272813103993727312869 3150426152456998823871163)
                      ·
                        rfl

theorem cell23_6135433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_6135433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135433 prefixEnd_6135433 := by exact prefixLift 6135433
  have htrace : WordTrace (prefixWord ++ tailWord_6135433) baseStart_6135433 baseEnd_6135433 := by
    simpa [prefixWord, tailWord_6135433, baseEnd_6135433] using wordTrace_append hprefix tailTrace_6135433
  have hstable : (prefixWord ++ tailWord_6135433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135433).length < 2 ^ (prefixWord ++ tailWord_6135433).sum := by decide
  have hdescent : baseEnd_6135433 < baseStart_6135433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135483 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3]
def baseStart_6135483 : Nat := 118140960795 + 6135483 * 2 ^ 59
def prefixEnd_6135483 : Nat := 4983230072969 + 3 ^ 40 * 6135483 * 2
def baseEnd_6135483 : Nat := 3150451826489723628245933

theorem tailTrace_6135483 : CollatzResearch.WordTrace tailWord_6135483 prefixEnd_6135483 3150451826489723628245933 := by
  unfold tailWord_6135483
  simp only [CollatzResearch.WordTrace]
  refine ⟨223779449231200422917347103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149186299487466948611564735 223779449231200422917347103)
  ·
    refine ⟨335669173846800634376020655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223779449231200422917347103 335669173846800634376020655)
    ·
      refine ⟨503503760770200951564030983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335669173846800634376020655 503503760770200951564030983)
      ·
        refine ⟨755255641155301427346046475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503503760770200951564030983 755255641155301427346046475)
        ·
          refine ⟨1132883461732952141019069713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755255641155301427346046475 1132883461732952141019069713)
          ·
            refine ⟨849662596299714105764302285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132883461732952141019069713 849662596299714105764302285)
            ·
              refine ⟨318623473612392789661613357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849662596299714105764302285 318623473612392789661613357)
              ·
                refine ⟨119483802604647296123105009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318623473612392789661613357 119483802604647296123105009)
                ·
                  refine ⟨89612851953485472092328757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119483802604647296123105009 89612851953485472092328757)
                  ·
                    refine ⟨8401204870639263008655821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89612851953485472092328757 8401204870639263008655821)
                    ·
                      refine ⟨3150451826489723628245933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8401204870639263008655821 3150451826489723628245933)
                      ·
                        rfl

theorem cell23_6135483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 3].length) (baseStart_6135483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135483 prefixEnd_6135483 := by exact prefixLift 6135483
  have htrace : WordTrace (prefixWord ++ tailWord_6135483) baseStart_6135483 baseEnd_6135483 := by
    simpa [prefixWord, tailWord_6135483, baseEnd_6135483] using wordTrace_append hprefix tailTrace_6135483
  have hstable : (prefixWord ++ tailWord_6135483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135483).length < 2 ^ (prefixWord ++ tailWord_6135483).sum := by decide
  have hdescent : baseEnd_6135483 < baseStart_6135483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135558 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_6135558 : Nat := 118140960795 + 6135558 * 2 ^ 59
def prefixEnd_6135558 : Nat := 4983230072969 + 3 ^ 40 * 6135558 * 2
def baseEnd_6135558 : Nat := 350054481948756759423121

theorem tailTrace_6135558 : CollatzResearch.WordTrace tailWord_6135558 prefixEnd_6135558 350054481948756759423121 := by
  unfold tailWord_6135558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993193272060272210197729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149188123137285807150884885 6993193272060272210197729)
  ·
    refine ⟨5244894954045204157648297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6993193272060272210197729 5244894954045204157648297)
    ·
      refine ⟨3933671215533903118236223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244894954045204157648297 3933671215533903118236223)
      ·
        refine ⟨5900506823300854677354335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933671215533903118236223 5900506823300854677354335)
        ·
          refine ⟨8850760234951282016031503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900506823300854677354335 8850760234951282016031503)
          ·
            refine ⟨13276140352426923024047255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850760234951282016031503 13276140352426923024047255)
            ·
              refine ⟨19914210528640384536070883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13276140352426923024047255 19914210528640384536070883)
              ·
                refine ⟨29871315792960576804106325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19914210528640384536070883 29871315792960576804106325)
                ·
                  refine ⟨350054481948756759423121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29871315792960576804106325 350054481948756759423121)
                  ·
                    rfl

theorem cell23_6135558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_6135558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135558 prefixEnd_6135558 := by exact prefixLift 6135558
  have htrace : WordTrace (prefixWord ++ tailWord_6135558) baseStart_6135558 baseEnd_6135558 := by
    simpa [prefixWord, tailWord_6135558, baseEnd_6135558] using wordTrace_append hprefix tailTrace_6135558
  have hstable : (prefixWord ++ tailWord_6135558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135558).length < 2 ^ (prefixWord ++ tailWord_6135558).sum := by decide
  have hdescent : baseEnd_6135558 < baseStart_6135558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135560 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6135560 : Nat := 118140960795 + 6135560 * 2 ^ 59
def prefixEnd_6135560 : Nat := 4983230072969 + 3 ^ 40 * 6135560 * 2
def baseEnd_6135560 : Nat := 3150491364500119826983079

theorem tailTrace_6135560 : CollatzResearch.WordTrace tailWord_6135560 prefixEnd_6135560 3150491364500119826983079 := by
  unfold tailWord_6135560
  simp only [CollatzResearch.WordTrace]
  refine ⟨111891128825960732533950067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149188171767947643378600089 111891128825960732533950067)
  ·
    refine ⟨167836693238941098800925101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111891128825960732533950067 167836693238941098800925101)
    ·
      refine ⟨62938759964602912050346913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167836693238941098800925101 62938759964602912050346913)
      ·
        refine ⟨47204069973452184037760185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62938759964602912050346913 47204069973452184037760185)
        ·
          refine ⟨35403052480089138028320139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47204069973452184037760185 35403052480089138028320139)
          ·
            refine ⟨53104578720133707042480209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35403052480089138028320139 53104578720133707042480209)
            ·
              refine ⟨39828434040100280281860157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53104578720133707042480209 39828434040100280281860157)
              ·
                refine ⟨14935662765037605105697559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39828434040100280281860157 14935662765037605105697559)
                ·
                  refine ⟨22403494147556407658546339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14935662765037605105697559 22403494147556407658546339)
                  ·
                    refine ⟨33605241221334611487819509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22403494147556407658546339 33605241221334611487819509)
                    ·
                      refine ⟨3150491364500119826983079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33605241221334611487819509 3150491364500119826983079)
                      ·
                        rfl

theorem cell23_6135560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6135560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135560 prefixEnd_6135560 := by exact prefixLift 6135560
  have htrace : WordTrace (prefixWord ++ tailWord_6135560) baseStart_6135560 baseEnd_6135560 := by
    simpa [prefixWord, tailWord_6135560, baseEnd_6135560] using wordTrace_append hprefix tailTrace_6135560
  have hstable : (prefixWord ++ tailWord_6135560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135560).length < 2 ^ (prefixWord ++ tailWord_6135560).sum := by decide
  have hdescent : baseEnd_6135560 < baseStart_6135560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135584 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_6135584 : Nat := 118140960795 + 6135584 * 2 ^ 59
def prefixEnd_6135584 : Nat := 4983230072969 + 3 ^ 40 * 6135584 * 2
def baseEnd_6135584 : Nat := 1050167896011942577694323

theorem tailTrace_6135584 : CollatzResearch.WordTrace tailWord_6135584 prefixEnd_6135584 1050167896011942577694323 := by
  unfold tailWord_6135584
  simp only [CollatzResearch.WordTrace]
  refine ⟨111891566501917258583386903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149188755335889678111182537 111891566501917258583386903)
  ·
    refine ⟨167837349752875887875080355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111891566501917258583386903 167837349752875887875080355)
    ·
      refine ⟨251756024629313831812620533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167837349752875887875080355 251756024629313831812620533)
      ·
        refine ⟨23602127308998171732433175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251756024629313831812620533 23602127308998171732433175)
        ·
          refine ⟨35403190963497257598649763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23602127308998171732433175 35403190963497257598649763)
          ·
            refine ⟨53104786445245886397974645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35403190963497257598649763 53104786445245886397974645)
            ·
              refine ⟨4978573729241801849810123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53104786445245886397974645 4978573729241801849810123)
              ·
                refine ⟨7467860593862702774715185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978573729241801849810123 7467860593862702774715185)
                ·
                  refine ⟨5600895445397027081036389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7467860593862702774715185 5600895445397027081036389)
                  ·
                    refine ⟨1050167896011942577694323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5600895445397027081036389 1050167896011942577694323)
                    ·
                      rfl

theorem cell23_6135584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_6135584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135584 prefixEnd_6135584 := by exact prefixLift 6135584
  have htrace : WordTrace (prefixWord ++ tailWord_6135584) baseStart_6135584 baseEnd_6135584 := by
    simpa [prefixWord, tailWord_6135584, baseEnd_6135584] using wordTrace_append hprefix tailTrace_6135584
  have hstable : (prefixWord ++ tailWord_6135584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135584).length < 2 ^ (prefixWord ++ tailWord_6135584).sum := by decide
  have hdescent : baseEnd_6135584 < baseStart_6135584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135608 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_6135608 : Nat := 118140960795 + 6135608 * 2 ^ 59
def prefixEnd_6135608 : Nat := 4983230072969 + 3 ^ 40 * 6135608 * 2
def baseEnd_6135608 : Nat := 3150516011571535639182859

theorem tailTrace_6135608 : CollatzResearch.WordTrace tailWord_6135608 prefixEnd_6135608 3150516011571535639182859 := by
  unfold tailWord_6135608
  simp only [CollatzResearch.WordTrace]
  refine ⟨111892004177873784632823739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149189338903831712843764985 111892004177873784632823739)
  ·
    refine ⟨167838006266810676949235609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111892004177873784632823739 167838006266810676949235609)
    ·
      refine ⟨125878504700108007711926707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167838006266810676949235609 125878504700108007711926707)
      ·
        refine ⟨188817757050162011567890061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125878504700108007711926707 188817757050162011567890061)
        ·
          refine ⟨70806658893810754337958773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188817757050162011567890061 70806658893810754337958773)
          ·
            refine ⟨6638124271294758219183635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70806658893810754337958773 6638124271294758219183635)
            ·
              refine ⟨9957186406942137328775453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638124271294758219183635 9957186406942137328775453)
              ·
                refine ⟨3733944902603301498290795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957186406942137328775453 3733944902603301498290795)
                ·
                  refine ⟨5600917353904952247436193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733944902603301498290795 5600917353904952247436193)
                  ·
                    refine ⟨4200688015428714185577145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5600917353904952247436193 4200688015428714185577145)
                    ·
                      refine ⟨3150516011571535639182859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200688015428714185577145 3150516011571535639182859)
                      ·
                        rfl

theorem cell23_6135608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_6135608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135608 prefixEnd_6135608 := by exact prefixLift 6135608
  have htrace : WordTrace (prefixWord ++ tailWord_6135608) baseStart_6135608 baseEnd_6135608 := by
    simpa [prefixWord, tailWord_6135608, baseEnd_6135608] using wordTrace_append hprefix tailTrace_6135608
  have hstable : (prefixWord ++ tailWord_6135608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135608).length < 2 ^ (prefixWord ++ tailWord_6135608).sum := by decide
  have hdescent : baseEnd_6135608 < baseStart_6135608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135698 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6135698 : Nat := 118140960795 + 6135698 * 2 ^ 59
def prefixEnd_6135698 : Nat := 4983230072969 + 3 ^ 40 * 6135698 * 2
def baseEnd_6135698 : Nat := 3150562224830440287057445

theorem tailTrace_6135698 : CollatzResearch.WordTrace tailWord_6135698 prefixEnd_6135698 3150562224830440287057445 := by
  unfold tailWord_6135698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55946822731355378659105937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149191527283614343090949165 55946822731355378659105937)
  ·
    refine ⟨41960117048516533994329453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55946822731355378659105937 41960117048516533994329453)
    ·
      refine ⟨15735043893193700247873545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41960117048516533994329453 15735043893193700247873545)
      ·
        refine ⟨11801282919895275185905159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15735043893193700247873545 11801282919895275185905159)
        ·
          refine ⟨17701924379842912778857739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801282919895275185905159 17701924379842912778857739)
          ·
            refine ⟨26552886569764369168286609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17701924379842912778857739 26552886569764369168286609)
            ·
              refine ⟨19914664927323276876214957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26552886569764369168286609 19914664927323276876214957)
              ·
                refine ⟨7467999347746228828580609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19914664927323276876214957 7467999347746228828580609)
                ·
                  refine ⟨5600999510809671621435457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7467999347746228828580609 5600999510809671621435457)
                  ·
                    refine ⟨4200749633107253716076593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5600999510809671621435457 4200749633107253716076593)
                    ·
                      refine ⟨3150562224830440287057445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200749633107253716076593 3150562224830440287057445)
                      ·
                        rfl

theorem cell23_6135698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6135698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135698 prefixEnd_6135698 := by exact prefixLift 6135698
  have htrace : WordTrace (prefixWord ++ tailWord_6135698) baseStart_6135698 baseEnd_6135698 := by
    simpa [prefixWord, tailWord_6135698, baseEnd_6135698] using wordTrace_append hprefix tailTrace_6135698
  have hstable : (prefixWord ++ tailWord_6135698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135698).length < 2 ^ (prefixWord ++ tailWord_6135698).sum := by decide
  have hdescent : baseEnd_6135698 < baseStart_6135698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135704 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 7]
def baseStart_6135704 : Nat := 118140960795 + 6135704 * 2 ^ 59
def prefixEnd_6135704 : Nat := 4983230072969 + 3 ^ 40 * 6135704 * 2
def baseEnd_6135704 : Nat := 350062811746040807064713

theorem tailTrace_6135704 : CollatzResearch.WordTrace tailWord_6135704 prefixEnd_6135704 350062811746040807064713 := by
  unfold tailWord_6135704
  simp only [CollatzResearch.WordTrace]
  refine ⟨111893754881699888830571083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149191673175599851774094777 111893754881699888830571083)
  ·
    refine ⟨167840632322549833245856625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111893754881699888830571083 167840632322549833245856625)
    ·
      refine ⟨125880474241912374934392469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167840632322549833245856625 125880474241912374934392469)
      ·
        refine ⟨5900647230089642575049647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125880474241912374934392469 5900647230089642575049647)
        ·
          refine ⟨8850970845134463862574471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900647230089642575049647 8850970845134463862574471)
          ·
            refine ⟨13276456267701695793861707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8850970845134463862574471 13276456267701695793861707)
            ·
              refine ⟨19914684401552543690792561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13276456267701695793861707 19914684401552543690792561)
              ·
                refine ⟨14936013301164407768094421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19914684401552543690792561 14936013301164407768094421)
                ·
                  refine ⟨350062811746040807064713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14936013301164407768094421 350062811746040807064713)
                  ·
                    rfl

theorem cell23_6135704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_6135704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135704 prefixEnd_6135704 := by exact prefixLift 6135704
  have htrace : WordTrace (prefixWord ++ tailWord_6135704) baseStart_6135704 baseEnd_6135704 := by
    simpa [prefixWord, tailWord_6135704, baseEnd_6135704] using wordTrace_append hprefix tailTrace_6135704
  have hstable : (prefixWord ++ tailWord_6135704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135704).length < 2 ^ (prefixWord ++ tailWord_6135704).sum := by decide
  have hdescent : baseEnd_6135704 < baseStart_6135704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135730 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_6135730 : Nat := 118140960795 + 6135730 * 2 ^ 59
def prefixEnd_6135730 : Nat := 4983230072969 + 3 ^ 40 * 6135730 * 2
def baseEnd_6135730 : Nat := 1050192885403794720619099

theorem tailTrace_6135730 : CollatzResearch.WordTrace tailWord_6135730 prefixEnd_6135730 1050192885403794720619099 := by
  unfold tailWord_6135730
  simp only [CollatzResearch.WordTrace]
  refine ⟨55947114515326396025397161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149192305374203722734392429 55947114515326396025397161)
  ·
    refine ⟨41960335886494797019047871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55947114515326396025397161 41960335886494797019047871)
    ·
      refine ⟨62940503829742195528571807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41960335886494797019047871 62940503829742195528571807)
      ·
        refine ⟨94410755744613293292857711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62940503829742195528571807 94410755744613293292857711)
        ·
          refine ⟨141616133616919939939286567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94410755744613293292857711 141616133616919939939286567)
          ·
            refine ⟨212424200425379909908929851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141616133616919939939286567 212424200425379909908929851)
            ·
              refine ⟨318636300638069864863394777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212424200425379909908929851 318636300638069864863394777)
              ·
                refine ⟨238977225478552398647546083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318636300638069864863394777 238977225478552398647546083)
                ·
                  refine ⟨358465838217828597971319125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238977225478552398647546083 358465838217828597971319125)
                  ·
                    refine ⟨1050192885403794720619099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 358465838217828597971319125 1050192885403794720619099)
                    ·
                      rfl

theorem cell23_6135730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_6135730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135730 prefixEnd_6135730 := by exact prefixLift 6135730
  have htrace : WordTrace (prefixWord ++ tailWord_6135730) baseStart_6135730 baseEnd_6135730 := by
    simpa [prefixWord, tailWord_6135730, baseEnd_6135730] using wordTrace_append hprefix tailTrace_6135730
  have hstable : (prefixWord ++ tailWord_6135730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135730).length < 2 ^ (prefixWord ++ tailWord_6135730).sum := by decide
  have hdescent : baseEnd_6135730 < baseStart_6135730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135732 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6135732 : Nat := 118140960795 + 6135732 * 2 ^ 59
def prefixEnd_6135732 : Nat := 4983230072969 + 3 ^ 40 * 6135732 * 2
def baseEnd_6135732 : Nat := 3150579683172693154032289

theorem tailTrace_6135732 : CollatzResearch.WordTrace tailWord_6135732 prefixEnd_6135732 3150579683172693154032289 := by
  unfold tailWord_6135732
  simp only [CollatzResearch.WordTrace]
  refine ⟨111894265503649169221580725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149192354004865558962107633 111894265503649169221580725)
  ·
    refine ⟨10490087390967109614523193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111894265503649169221580725 10490087390967109614523193)
    ·
      refine ⟨7867565543225332210892395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10490087390967109614523193 7867565543225332210892395)
      ·
        refine ⟨11801348314837998316338593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867565543225332210892395 11801348314837998316338593)
        ·
          refine ⟨8851011236128498737253945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11801348314837998316338593 8851011236128498737253945)
          ·
            refine ⟨6638258427096374052940459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8851011236128498737253945 6638258427096374052940459)
            ·
              refine ⟨9957387640644561079410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638258427096374052940459 9957387640644561079410689)
              ·
                refine ⟨7468040730483420809558017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9957387640644561079410689 7468040730483420809558017)
                ·
                  refine ⟨5601030547862565607168513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468040730483420809558017 5601030547862565607168513)
                  ·
                    refine ⟨4200772910896924205376385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601030547862565607168513 4200772910896924205376385)
                    ·
                      refine ⟨3150579683172693154032289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200772910896924205376385 3150579683172693154032289)
                      ·
                        rfl

theorem cell23_6135732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6135732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135732 prefixEnd_6135732 := by exact prefixLift 6135732
  have htrace : WordTrace (prefixWord ++ tailWord_6135732) baseStart_6135732 baseEnd_6135732 := by
    simpa [prefixWord, tailWord_6135732, baseEnd_6135732] using wordTrace_append hprefix tailTrace_6135732
  have hstable : (prefixWord ++ tailWord_6135732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135732).length < 2 ^ (prefixWord ++ tailWord_6135732).sum := by decide
  have hdescent : baseEnd_6135732 < baseStart_6135732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135737 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6135737 : Nat := 118140960795 + 6135737 * 2 ^ 59
def prefixEnd_6135737 : Nat := 4983230072969 + 3 ^ 40 * 6135737 * 2
def baseEnd_6135737 : Nat := 3150582250575965634469765

theorem tailTrace_6135737 : CollatzResearch.WordTrace tailWord_6135737 prefixEnd_6135737 3150582250575965634469765 := by
  unfold tailWord_6135737
  simp only [CollatzResearch.WordTrace]
  refine ⟨223788713372280224297093465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149192475581520149531395643 223788713372280224297093465)
  ·
    refine ⟨167841535029210168222820099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223788713372280224297093465 167841535029210168222820099)
    ·
      refine ⟨251762302543815252334230149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167841535029210168222820099 251762302543815252334230149)
      ·
        refine ⟨47205431726965359812668153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251762302543815252334230149 47205431726965359812668153)
        ·
          refine ⟨35404073795224019859501115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47205431726965359812668153 35404073795224019859501115)
          ·
            refine ⟨53106110692836029789251673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35404073795224019859501115 53106110692836029789251673)
            ·
              refine ⟨39829583019627022341938755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53106110692836029789251673 39829583019627022341938755)
              ·
                refine ⟨59744374529440533512908133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39829583019627022341938755 59744374529440533512908133)
                ·
                  refine ⟨11202070224270100033670275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59744374529440533512908133 11202070224270100033670275)
                  ·
                    refine ⟨16803105336405150050505413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11202070224270100033670275 16803105336405150050505413)
                    ·
                      refine ⟨3150582250575965634469765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16803105336405150050505413 3150582250575965634469765)
                      ·
                        rfl

theorem cell23_6135737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6135737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135737 prefixEnd_6135737 := by exact prefixLift 6135737
  have htrace : WordTrace (prefixWord ++ tailWord_6135737) baseStart_6135737 baseEnd_6135737 := by
    simpa [prefixWord, tailWord_6135737, baseEnd_6135737] using wordTrace_append hprefix tailTrace_6135737
  have hstable : (prefixWord ++ tailWord_6135737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135737).length < 2 ^ (prefixWord ++ tailWord_6135737).sum := by decide
  have hdescent : baseEnd_6135737 < baseStart_6135737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135754 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_6135754 : Nat := 118140960795 + 6135754 * 2 ^ 59
def prefixEnd_6135754 : Nat := 4983230072969 + 3 ^ 40 * 6135754 * 2
def baseEnd_6135754 : Nat := 3150590979747092067957187

theorem tailTrace_6135754 : CollatzResearch.WordTrace tailWord_6135754 prefixEnd_6135754 3150590979747092067957187 := by
  unfold tailWord_6135754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55947333353304659050115579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149192888942145757466974877 55947333353304659050115579)
  ·
    refine ⟨83921000029956988575173369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55947333353304659050115579 83921000029956988575173369)
    ·
      refine ⟨62940750022467741431380027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83921000029956988575173369 62940750022467741431380027)
      ·
        refine ⟨94411125033701612147070041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62940750022467741431380027 94411125033701612147070041)
        ·
          refine ⟨70808343775276209110302531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94411125033701612147070041 70808343775276209110302531)
          ·
            refine ⟨106212515662914313665453797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70808343775276209110302531 106212515662914313665453797)
            ·
              refine ⟨19914846686796433812272587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106212515662914313665453797 19914846686796433812272587)
              ·
                refine ⟨29872270030194650718408881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19914846686796433812272587 29872270030194650718408881)
                ·
                  refine ⟨22404202522645988038806661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29872270030194650718408881 22404202522645988038806661)
                  ·
                    refine ⟨4200787972996122757276249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22404202522645988038806661 4200787972996122757276249)
                    ·
                      refine ⟨3150590979747092067957187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200787972996122757276249 3150590979747092067957187)
                      ·
                        rfl

theorem cell23_6135754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_6135754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135754 prefixEnd_6135754 := by exact prefixLift 6135754
  have htrace : WordTrace (prefixWord ++ tailWord_6135754) baseStart_6135754 baseEnd_6135754 := by
    simpa [prefixWord, tailWord_6135754, baseEnd_6135754] using wordTrace_append hprefix tailTrace_6135754
  have hstable : (prefixWord ++ tailWord_6135754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135754).length < 2 ^ (prefixWord ++ tailWord_6135754).sum := by decide
  have hdescent : baseEnd_6135754 < baseStart_6135754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135764 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_6135764 : Nat := 118140960795 + 6135764 * 2 ^ 59
def prefixEnd_6135764 : Nat := 4983230072969 + 3 ^ 40 * 6135764 * 2
def baseEnd_6135764 : Nat := 1050198704851212342944047

theorem tailTrace_6135764 : CollatzResearch.WordTrace tailWord_6135764 prefixEnd_6135764 1050198704851212342944047 := by
  unfold tailWord_6135764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111894849071591203954163173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149193132095454938605550897 111894849071591203954163173)
  ·
    refine ⟨20980284200923350741405595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111894849071591203954163173 20980284200923350741405595)
    ·
      refine ⟨31470426301385026112108393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20980284200923350741405595 31470426301385026112108393)
      ·
        refine ⟨23602819726038769584081295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31470426301385026112108393 23602819726038769584081295)
        ·
          refine ⟨35404229589058154376121943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23602819726038769584081295 35404229589058154376121943)
          ·
            refine ⟨53106344383587231564182915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35404229589058154376121943 53106344383587231564182915)
            ·
              refine ⟨79659516575380847346274373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53106344383587231564182915 79659516575380847346274373)
              ·
                refine ⟨14936159357883908877426445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79659516575380847346274373 14936159357883908877426445)
                ·
                  refine ⟨5601059759206465829034917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936159357883908877426445 5601059759206465829034917)
                  ·
                    refine ⟨1050198704851212342944047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601059759206465829034917 1050198704851212342944047)
                    ·
                      rfl

theorem cell23_6135764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_6135764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135764 prefixEnd_6135764 := by exact prefixLift 6135764
  have htrace : WordTrace (prefixWord ++ tailWord_6135764) baseStart_6135764 baseEnd_6135764 := by
    simpa [prefixWord, tailWord_6135764, baseEnd_6135764] using wordTrace_append hprefix tailTrace_6135764
  have hstable : (prefixWord ++ tailWord_6135764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135764).length < 2 ^ (prefixWord ++ tailWord_6135764).sum := by decide
  have hdescent : baseEnd_6135764 < baseStart_6135764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135772 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 5]
def baseStart_6135772 : Nat := 118140960795 + 6135772 * 2 ^ 59
def prefixEnd_6135772 : Nat := 4983230072969 + 3 ^ 40 * 6135772 * 2
def baseEnd_6135772 : Nat := 350066691377652555281345

theorem tailTrace_6135772 : CollatzResearch.WordTrace tailWord_6135772 prefixEnd_6135772 350066691377652555281345 := by
  unfold tailWord_6135772
  simp only [CollatzResearch.WordTrace]
  refine ⟨111894994963576712637308785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149193326618102283516411713 111894994963576712637308785)
  ·
    refine ⟨83921246222682534477981589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111894994963576712637308785 83921246222682534477981589)
    ·
      refine ⟨3933808416688243803655387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83921246222682534477981589 3933808416688243803655387)
      ·
        refine ⟨5900712625032365705483081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933808416688243803655387 5900712625032365705483081)
        ·
          refine ⟨4425534468774274279112311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900712625032365705483081 4425534468774274279112311)
          ·
            refine ⟨6638301703161411418668467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425534468774274279112311 6638301703161411418668467)
            ·
              refine ⟨9957452554742117128002701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638301703161411418668467 9957452554742117128002701)
              ·
                refine ⟨3734044708028293923001013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9957452554742117128002701 3734044708028293923001013)
                ·
                  refine ⟨350066691377652555281345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3734044708028293923001013 350066691377652555281345)
                  ·
                    rfl

theorem cell23_6135772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_6135772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135772 prefixEnd_6135772 := by exact prefixLift 6135772
  have htrace : WordTrace (prefixWord ++ tailWord_6135772) baseStart_6135772 baseEnd_6135772 := by
    simpa [prefixWord, tailWord_6135772, baseEnd_6135772] using wordTrace_append hprefix tailTrace_6135772
  have hstable : (prefixWord ++ tailWord_6135772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135772).length < 2 ^ (prefixWord ++ tailWord_6135772).sum := by decide
  have hdescent : baseEnd_6135772 < baseStart_6135772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135798 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_6135798 : Nat := 118140960795 + 6135798 * 2 ^ 59
def prefixEnd_6135798 : Nat := 4983230072969 + 3 ^ 40 * 6135798 * 2
def baseEnd_6135798 : Nat := 1050204524298629965268995

theorem tailTrace_6135798 : CollatzResearch.WordTrace tailWord_6135798 prefixEnd_6135798 1050204524298629965268995 := by
  unfold tailWord_6135798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986933639066201982191503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149193958816706154476709365 13986933639066201982191503)
  ·
    refine ⟨20980400458599302973287255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13986933639066201982191503 20980400458599302973287255)
    ·
      refine ⟨31470600687898954459930883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20980400458599302973287255 31470600687898954459930883)
      ·
        refine ⟨47205901031848431689896325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31470600687898954459930883 47205901031848431689896325)
        ·
          refine ⟨8851106443471580941855561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47205901031848431689896325 8851106443471580941855561)
          ·
            refine ⟨6638329832603685706391671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8851106443471580941855561 6638329832603685706391671)
            ·
              refine ⟨9957494748905528559587507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638329832603685706391671 9957494748905528559587507)
              ·
                refine ⟨14936242123358292839381261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957494748905528559587507 14936242123358292839381261)
                ·
                  refine ⟨5601090796259359814767973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936242123358292839381261 5601090796259359814767973)
                  ·
                    refine ⟨1050204524298629965268995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601090796259359814767973 1050204524298629965268995)
                    ·
                      rfl

theorem cell23_6135798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_6135798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135798 prefixEnd_6135798 := by exact prefixLift 6135798
  have htrace : WordTrace (prefixWord ++ tailWord_6135798) baseStart_6135798 baseEnd_6135798 := by
    simpa [prefixWord, tailWord_6135798, baseEnd_6135798] using wordTrace_append hprefix tailTrace_6135798
  have hstable : (prefixWord ++ tailWord_6135798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135798).length < 2 ^ (prefixWord ++ tailWord_6135798).sum := by decide
  have hdescent : baseEnd_6135798 < baseStart_6135798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135878 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6135878 : Nat := 118140960795 + 6135878 * 2 ^ 59
def prefixEnd_6135878 : Nat := 4983230072969 + 3 ^ 40 * 6135878 * 2
def baseEnd_6135878 : Nat := 3150654651348249582806617

theorem tailTrace_6135878 : CollatzResearch.WordTrace tailWord_6135878 prefixEnd_6135878 3150654651348249582806617 := by
  unfold tailWord_6135878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993558002024043918061759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149195904043179603585317525 6993558002024043918061759)
  ·
    refine ⟨10490337003036065877092639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993558002024043918061759 10490337003036065877092639)
    ·
      refine ⟨15735505504554098815638959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10490337003036065877092639 15735505504554098815638959)
      ·
        refine ⟨23603258256831148223458439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15735505504554098815638959 23603258256831148223458439)
        ·
          refine ⟨35404887385246722335187659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23603258256831148223458439 35404887385246722335187659)
          ·
            refine ⟨53107331077870083502781489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35404887385246722335187659 53107331077870083502781489)
            ·
              refine ⟨39830498308402562627086117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53107331077870083502781489 39830498308402562627086117)
              ·
                refine ⟨7468218432825480492578647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39830498308402562627086117 7468218432825480492578647)
                ·
                  refine ⟨11202327649238220738867971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468218432825480492578647 11202327649238220738867971)
                  ·
                    refine ⟨16803491473857331108301957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11202327649238220738867971 16803491473857331108301957)
                    ·
                      refine ⟨3150654651348249582806617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16803491473857331108301957 3150654651348249582806617)
                      ·
                        rfl

theorem cell23_6135878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6135878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135878 prefixEnd_6135878 := by exact prefixLift 6135878
  have htrace : WordTrace (prefixWord ++ tailWord_6135878) baseStart_6135878 baseEnd_6135878 := by
    simpa [prefixWord, tailWord_6135878, baseEnd_6135878] using wordTrace_append hprefix tailTrace_6135878
  have hstable : (prefixWord ++ tailWord_6135878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135878).length < 2 ^ (prefixWord ++ tailWord_6135878).sum := by decide
  have hdescent : baseEnd_6135878 < baseStart_6135878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135911 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_6135911 : Nat := 118140960795 + 6135911 * 2 ^ 59
def prefixEnd_6135911 : Nat := 4983230072969 + 3 ^ 40 * 6135911 * 2
def baseEnd_6135911 : Nat := 3150671596209847953693965

theorem tailTrace_6135911 : CollatzResearch.WordTrace tailWord_6135911 prefixEnd_6135911 3150671596209847953693965 := by
  unfold tailWord_6135911
  simp only [CollatzResearch.WordTrace]
  refine ⟨223795059673649852013927587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149196706449099901342618391 223795059673649852013927587)
  ·
    refine ⟨335692589510474778020891381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223795059673649852013927587 335692589510474778020891381)
    ·
      refine ⟨31471180266607010439458567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 335692589510474778020891381 31471180266607010439458567)
      ·
        refine ⟨47206770399910515659187851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31471180266607010439458567 47206770399910515659187851)
        ·
          refine ⟨70810155599865773488781777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47206770399910515659187851 70810155599865773488781777)
          ·
            refine ⟨53107616699899330116586333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70810155599865773488781777 53107616699899330116586333)
            ·
              refine ⟨19915356262462248793719875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53107616699899330116586333 19915356262462248793719875)
              ·
                refine ⟨29873034393693373190579813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19915356262462248793719875 29873034393693373190579813)
                ·
                  refine ⟨5601193948817507473233715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29873034393693373190579813 5601193948817507473233715)
                  ·
                    refine ⟨8401790923226261209850573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601193948817507473233715 8401790923226261209850573)
                    ·
                      refine ⟨3150671596209847953693965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8401790923226261209850573 3150671596209847953693965)
                      ·
                        rfl

theorem cell23_6135911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_6135911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135911 prefixEnd_6135911 := by exact prefixLift 6135911
  have htrace : WordTrace (prefixWord ++ tailWord_6135911) baseStart_6135911 baseEnd_6135911 := by
    simpa [prefixWord, tailWord_6135911, baseEnd_6135911] using wordTrace_append hprefix tailTrace_6135911
  have hstable : (prefixWord ++ tailWord_6135911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135911).length < 2 ^ (prefixWord ++ tailWord_6135911).sum := by decide
  have hdescent : baseEnd_6135911 < baseStart_6135911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135968 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2]
def baseStart_6135968 : Nat := 118140960795 + 6135968 * 2 ^ 59
def prefixEnd_6135968 : Nat := 4983230072969 + 3 ^ 40 * 6135968 * 2
def baseEnd_6135968 : Nat := 3150700864607154230681203

theorem tailTrace_6135968 : CollatzResearch.WordTrace tailWord_6135968 prefixEnd_6135968 3150700864607154230681203 := by
  unfold tailWord_6135968
  simp only [CollatzResearch.WordTrace]
  refine ⟨111898569317221675374376279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149198092422962233832501705 111898569317221675374376279)
  ·
    refine ⟨167847853975832513061564419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111898569317221675374376279 167847853975832513061564419)
    ·
      refine ⟨251771780963748769592346629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167847853975832513061564419 251771780963748769592346629)
      ·
        refine ⟨47207208930702894298564993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251771780963748769592346629 47207208930702894298564993)
        ·
          refine ⟨35405406698027170723923745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47207208930702894298564993 35405406698027170723923745)
          ·
            refine ⟨26554055023520378042942809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35405406698027170723923745 26554055023520378042942809)
            ·
              refine ⟨19915541267640283532207107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26554055023520378042942809 19915541267640283532207107)
              ·
                refine ⟨29873311901460425298310661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19915541267640283532207107 29873311901460425298310661)
                ·
                  refine ⟨5601245981523829743433249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29873311901460425298310661 5601245981523829743433249)
                  ·
                    refine ⟨4200934486142872307574937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601245981523829743433249 4200934486142872307574937)
                    ·
                      refine ⟨3150700864607154230681203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200934486142872307574937 3150700864607154230681203)
                      ·
                        rfl

theorem cell23_6135968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_6135968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135968 prefixEnd_6135968 := by exact prefixLift 6135968
  have htrace : WordTrace (prefixWord ++ tailWord_6135968) baseStart_6135968 baseEnd_6135968 := by
    simpa [prefixWord, tailWord_6135968, baseEnd_6135968] using wordTrace_append hprefix tailTrace_6135968
  have hstable : (prefixWord ++ tailWord_6135968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135968).length < 2 ^ (prefixWord ++ tailWord_6135968).sum := by decide
  have hdescent : baseEnd_6135968 < baseStart_6135968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6135989 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6135989 : Nat := 118140960795 + 6135989 * 2 ^ 59
def prefixEnd_6135989 : Nat := 4983230072969 + 3 ^ 40 * 6135989 * 2
def baseEnd_6135989 : Nat := 3150711647700898648518607

theorem tailTrace_6135989 : CollatzResearch.WordTrace tailWord_6135989 prefixEnd_6135989 3150711647700898648518607 := by
  unfold tailWord_6135989
  simp only [CollatzResearch.WordTrace]
  refine ⟨223797904567367271335267021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149198603044911514223511347 223797904567367271335267021)
  ·
    refine ⟨83924214212762726750725133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223797904567367271335267021 83924214212762726750725133)
    ·
      refine ⟨31471580329786022531521925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83924214212762726750725133 31471580329786022531521925)
      ·
        refine ⟨5900921311834879224660361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31471580329786022531521925 5900921311834879224660361)
        ·
          refine ⟨4425690983876159418495271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900921311834879224660361 4425690983876159418495271)
          ·
            refine ⟨6638536475814239127742907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425690983876159418495271 6638536475814239127742907)
            ·
              refine ⟨9957804713721358691614361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638536475814239127742907 9957804713721358691614361)
              ·
                refine ⟨7468353535291019018710771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9957804713721358691614361 7468353535291019018710771)
                ·
                  refine ⟨11202530302936528528066157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468353535291019018710771 11202530302936528528066157)
                  ·
                    refine ⟨4200948863601198198024809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11202530302936528528066157 4200948863601198198024809)
                    ·
                      refine ⟨3150711647700898648518607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200948863601198198024809 3150711647700898648518607)
                      ·
                        rfl

theorem cell23_6135989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6135989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6135989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6135989 prefixEnd_6135989 := by exact prefixLift 6135989
  have htrace : WordTrace (prefixWord ++ tailWord_6135989) baseStart_6135989 baseEnd_6135989 := by
    simpa [prefixWord, tailWord_6135989, baseEnd_6135989] using wordTrace_append hprefix tailTrace_6135989
  have hstable : (prefixWord ++ tailWord_6135989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6135989).length < 2 ^ (prefixWord ++ tailWord_6135989).sum := by decide
  have hdescent : baseEnd_6135989 < baseStart_6135989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6135989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136002 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6136002 : Nat := 118140960795 + 6136002 * 2 ^ 59
def prefixEnd_6136002 : Nat := 4983230072969 + 3 ^ 40 * 6136002 * 2
def baseEnd_6136002 : Nat := 3150718322949407097656047

theorem tailTrace_6136002 : CollatzResearch.WordTrace tailWord_6136002 prefixEnd_6136002 3150718322949407097656047 := by
  unfold tailWord_6136002
  simp only [CollatzResearch.WordTrace]
  refine ⟨55949594679080043638872565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149198919144213449703660173 55949594679080043638872565)
  ·
    refine ⟨5245274501163754091144303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55949594679080043638872565 5245274501163754091144303)
    ·
      refine ⟨7867911751745631136716455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245274501163754091144303 7867911751745631136716455)
      ·
        refine ⟨11801867627618446705074683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867911751745631136716455 11801867627618446705074683)
        ·
          refine ⟨17702801441427670057612025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801867627618446705074683 17702801441427670057612025)
          ·
            refine ⟨13277101081070752543209019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17702801441427670057612025 13277101081070752543209019)
            ·
              refine ⟨19915651621606128814813529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13277101081070752543209019 19915651621606128814813529)
              ·
                refine ⟨14936738716204596611110147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19915651621606128814813529 14936738716204596611110147)
                ·
                  refine ⟨22405108074306894916665221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14936738716204596611110147 22405108074306894916665221)
                  ·
                    refine ⟨4200957763932542796874729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22405108074306894916665221 4200957763932542796874729)
                    ·
                      refine ⟨3150718322949407097656047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200957763932542796874729 3150718322949407097656047)
                      ·
                        rfl

theorem cell23_6136002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6136002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136002 prefixEnd_6136002 := by exact prefixLift 6136002
  have htrace : WordTrace (prefixWord ++ tailWord_6136002) baseStart_6136002 baseEnd_6136002 := by
    simpa [prefixWord, tailWord_6136002, baseEnd_6136002] using wordTrace_append hprefix tailTrace_6136002
  have hstable : (prefixWord ++ tailWord_6136002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136002).length < 2 ^ (prefixWord ++ tailWord_6136002).sum := by decide
  have hdescent : baseEnd_6136002 < baseStart_6136002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136041 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 4, 2]
def baseStart_6136041 : Nat := 118140960795 + 6136041 * 2 ^ 59
def prefixEnd_6136041 : Nat := 4983230072969 + 3 ^ 40 * 6136041 * 2
def baseEnd_6136041 : Nat := 3150738348694932445068367

theorem tailTrace_6136041 : CollatzResearch.WordTrace tailWord_6136041 prefixEnd_6136041 3150738348694932445068367 := by
  unfold tailWord_6136041
  simp only [CollatzResearch.WordTrace]
  refine ⟨223799801163178884216159977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149199867442119256144106651 223799801163178884216159977)
  ·
    refine ⟨167849850872384163162119983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223799801163178884216159977 167849850872384163162119983)
    ·
      refine ⟨251774776308576244743179975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167849850872384163162119983 251774776308576244743179975)
      ·
        refine ⟨377662164462864367114769963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251774776308576244743179975 377662164462864367114769963)
        ·
          refine ⟨566493246694296550672154945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377662164462864367114769963 566493246694296550672154945)
          ·
            refine ⟨424869935020722413004116209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566493246694296550672154945 424869935020722413004116209)
            ·
              refine ⟨318652451265541809753087157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424869935020722413004116209 318652451265541809753087157)
              ·
                refine ⟨29873667306144544664351921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318652451265541809753087157 29873667306144544664351921)
                ·
                  refine ⟨22405250479608408498263941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29873667306144544664351921 22405250479608408498263941)
                  ·
                    refine ⟨4200984464926576593424489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22405250479608408498263941 4200984464926576593424489)
                    ·
                      refine ⟨3150738348694932445068367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4200984464926576593424489 3150738348694932445068367)
                      ·
                        rfl

theorem cell23_6136041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4, 2].length) (baseStart_6136041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136041 prefixEnd_6136041 := by exact prefixLift 6136041
  have htrace : WordTrace (prefixWord ++ tailWord_6136041) baseStart_6136041 baseEnd_6136041 := by
    simpa [prefixWord, tailWord_6136041, baseEnd_6136041] using wordTrace_append hprefix tailTrace_6136041
  have hstable : (prefixWord ++ tailWord_6136041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136041).length < 2 ^ (prefixWord ++ tailWord_6136041).sum := by decide
  have hdescent : baseEnd_6136041 < baseStart_6136041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136051 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 3, 4]
def baseStart_6136051 : Nat := 118140960795 + 6136051 * 2 ^ 59
def prefixEnd_6136051 : Nat := 4983230072969 + 3 ^ 40 * 6136051 * 2
def baseEnd_6136051 : Nat := 1050247827833825801981107

theorem tailTrace_6136051 : CollatzResearch.WordTrace tailWord_6136051 prefixEnd_6136051 1050247827833825801981107 := by
  unfold tailWord_6136051
  simp only [CollatzResearch.WordTrace]
  refine ⟨223800165893142655924024007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149200110595428437282682671 223800165893142655924024007)
  ·
    refine ⟨335700248839713983886036011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223800165893142655924024007 335700248839713983886036011)
    ·
      refine ⟨503550373259570975829054017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335700248839713983886036011 503550373259570975829054017)
      ·
        refine ⟨377662779944678231871790513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503550373259570975829054017 377662779944678231871790513)
        ·
          refine ⟨283247084958508673903842885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377662779944678231871790513 283247084958508673903842885)
          ·
            refine ⟨53108828429720376356970541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283247084958508673903842885 53108828429720376356970541)
            ·
              refine ⟨19915810661145141133863953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53108828429720376356970541 19915810661145141133863953)
              ·
                refine ⟨14936857995858855850397965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19915810661145141133863953 14936857995858855850397965)
                ·
                  refine ⟨5601321748447070943899237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936857995858855850397965 5601321748447070943899237)
                  ·
                    refine ⟨1050247827833825801981107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601321748447070943899237 1050247827833825801981107)
                    ·
                      rfl

theorem cell23_6136051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 4].length) (baseStart_6136051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136051 prefixEnd_6136051 := by exact prefixLift 6136051
  have htrace : WordTrace (prefixWord ++ tailWord_6136051) baseStart_6136051 baseEnd_6136051 := by
    simpa [prefixWord, tailWord_6136051, baseEnd_6136051] using wordTrace_append hprefix tailTrace_6136051
  have hstable : (prefixWord ++ tailWord_6136051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136051).length < 2 ^ (prefixWord ++ tailWord_6136051).sum := by decide
  have hdescent : baseEnd_6136051 < baseStart_6136051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136058 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_6136058 : Nat := 118140960795 + 6136058 * 2 ^ 59
def prefixEnd_6136058 : Nat := 4983230072969 + 3 ^ 40 * 6136058 * 2
def baseEnd_6136058 : Nat := 3150747077866058878555789

theorem tailTrace_6136058 : CollatzResearch.WordTrace tailWord_6136058 prefixEnd_6136058 3150747077866058878555789 := by
  unfold tailWord_6136058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55950105301029324029882207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149200280802744864079685885 55950105301029324029882207)
  ·
    refine ⟨83925157951543986044823311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55950105301029324029882207 83925157951543986044823311)
    ·
      refine ⟨125887736927315979067234967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83925157951543986044823311 125887736927315979067234967)
      ·
        refine ⟨188831605390973968600852451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125887736927315979067234967 188831605390973968600852451)
        ·
          refine ⟨283247408086460952901278677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188831605390973968600852451 283247408086460952901278677)
          ·
            refine ⟨6638611127026428583623719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 283247408086460952901278677 6638611127026428583623719)
            ·
              refine ⟨9957916690539642875435579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638611127026428583623719 9957916690539642875435579)
              ·
                refine ⟨14936875035809464313153369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957916690539642875435579 14936875035809464313153369)
                ·
                  refine ⟨11202656276857098234865027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14936875035809464313153369 11202656276857098234865027)
                  ·
                    refine ⟨16803984415285647352297541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11202656276857098234865027 16803984415285647352297541)
                    ·
                      refine ⟨3150747077866058878555789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16803984415285647352297541 3150747077866058878555789)
                      ·
                        rfl

theorem cell23_6136058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_6136058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136058 prefixEnd_6136058 := by exact prefixLift 6136058
  have htrace : WordTrace (prefixWord ++ tailWord_6136058) baseStart_6136058 baseEnd_6136058 := by
    simpa [prefixWord, tailWord_6136058, baseEnd_6136058] using wordTrace_append hprefix tailTrace_6136058
  have hstable : (prefixWord ++ tailWord_6136058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136058).length < 2 ^ (prefixWord ++ tailWord_6136058).sum := by decide
  have hdescent : baseEnd_6136058 < baseStart_6136058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136081 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 6]
def baseStart_6136081 : Nat := 118140960795 + 6136081 * 2 ^ 59
def prefixEnd_6136081 : Nat := 4983230072969 + 3 ^ 40 * 6136081 * 2
def baseEnd_6136081 : Nat := 350084320880123587618687

theorem tailTrace_6136081 : CollatzResearch.WordTrace tailWord_6136081 prefixEnd_6136081 350084320880123587618687 := by
  unfold tailWord_6136081
  simp only [CollatzResearch.WordTrace]
  refine ⟨223801260083033971047616097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149200840055355980698410731 223801260083033971047616097)
  ·
    refine ⟨167850945062275478285712073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223801260083033971047616097 167850945062275478285712073)
    ·
      refine ⟨125888208796706608714284055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167850945062275478285712073 125888208796706608714284055)
      ·
        refine ⟨188832313195059913071426083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125888208796706608714284055 188832313195059913071426083)
        ·
          refine ⟨283248469792589869607139125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188832313195059913071426083 283248469792589869607139125)
          ·
            refine ⟨26554544043055300275669293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283248469792589869607139125 26554544043055300275669293)
            ·
              refine ⟨9957954016145737603375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26554544043055300275669293 9957954016145737603375985)
              ·
                refine ⟨7468465512109303202531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9957954016145737603375985 7468465512109303202531989)
                ·
                  refine ⟨350084320880123587618687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7468465512109303202531989 350084320880123587618687)
                  ·
                    rfl

theorem cell23_6136081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_6136081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136081 prefixEnd_6136081 := by exact prefixLift 6136081
  have htrace : WordTrace (prefixWord ++ tailWord_6136081) baseStart_6136081 baseEnd_6136081 := by
    simpa [prefixWord, tailWord_6136081, baseEnd_6136081] using wordTrace_append hprefix tailTrace_6136081
  have hstable : (prefixWord ++ tailWord_6136081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136081).length < 2 ^ (prefixWord ++ tailWord_6136081).sum := by decide
  have hdescent : baseEnd_6136081 < baseStart_6136081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136108 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_6136108 : Nat := 118140960795 + 6136108 * 2 ^ 59
def prefixEnd_6136108 : Nat := 4983230072969 + 3 ^ 40 * 6136108 * 2
def baseEnd_6136108 : Nat := 3150772751898783682930559

theorem tailTrace_6136108 : CollatzResearch.WordTrace tailWord_6136108 prefixEnd_6136108 3150772751898783682930559 := by
  unfold tailWord_6136108
  simp only [CollatzResearch.WordTrace]
  refine ⟨111901122426968077329424489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149201496569290769772565985 111901122426968077329424489)
  ·
    refine ⟨83925841820226057997068367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111901122426968077329424489 83925841820226057997068367)
    ·
      refine ⟨125888762730339086995602551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83925841820226057997068367 125888762730339086995602551)
      ·
        refine ⟨188833144095508630493403827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125888762730339086995602551 188833144095508630493403827)
        ·
          refine ⟨283249716143262945740105741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188833144095508630493403827 283249716143262945740105741)
          ·
            refine ⟨106218643553723604652539653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283249716143262945740105741 106218643553723604652539653)
            ·
              refine ⟨19915995666323175872351185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106218643553723604652539653 19915995666323175872351185)
              ·
                refine ⟨14936996749742381904263389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19915995666323175872351185 14936996749742381904263389)
                ·
                  refine ⟨5601373781153393214098771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14936996749742381904263389 5601373781153393214098771)
                  ·
                    refine ⟨8402060671730089821148157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601373781153393214098771 8402060671730089821148157)
                    ·
                      refine ⟨3150772751898783682930559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402060671730089821148157 3150772751898783682930559)
                      ·
                        rfl

theorem cell23_6136108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_6136108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136108 prefixEnd_6136108 := by exact prefixLift 6136108
  have htrace : WordTrace (prefixWord ++ tailWord_6136108) baseStart_6136108 baseEnd_6136108 := by
    simpa [prefixWord, tailWord_6136108, baseEnd_6136108] using wordTrace_append hprefix tailTrace_6136108
  have hstable : (prefixWord ++ tailWord_6136108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136108).length < 2 ^ (prefixWord ++ tailWord_6136108).sum := by decide
  have hdescent : baseEnd_6136108 < baseStart_6136108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136111 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 1, 5]
def baseStart_6136111 : Nat := 118140960795 + 6136111 * 2 ^ 59
def prefixEnd_6136111 : Nat := 4983230072969 + 3 ^ 40 * 6136111 * 2
def baseEnd_6136111 : Nat := 1050258097446915723731015

theorem tailTrace_6136111 : CollatzResearch.WordTrace tailWord_6136111 prefixEnd_6136111 1050258097446915723731015 := by
  unfold tailWord_6136111
  simp only [CollatzResearch.WordTrace]
  refine ⟨223802354272925286171208187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149201569515283524114138791 223802354272925286171208187)
  ·
    refine ⟨335703531409387929256812281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223802354272925286171208187 335703531409387929256812281)
    ·
      refine ⟨251777648557040946942609211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335703531409387929256812281 251777648557040946942609211)
      ·
        refine ⟨377666472835561420413913817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251777648557040946942609211 377666472835561420413913817)
        ·
          refine ⟨283249854626671065310435363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377666472835561420413913817 283249854626671065310435363)
          ·
            refine ⟨424874781940006597965653045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283249854626671065310435363 424874781940006597965653045)
            ·
              refine ⟨39832010806875618559279973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 424874781940006597965653045 39832010806875618559279973)
              ·
                refine ⟨7468502026289178479864995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39832010806875618559279973 7468502026289178479864995)
                ·
                  refine ⟨11202753039433767719797493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468502026289178479864995 11202753039433767719797493)
                  ·
                    refine ⟨1050258097446915723731015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11202753039433767719797493 1050258097446915723731015)
                    ·
                      rfl

theorem cell23_6136111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_6136111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136111 prefixEnd_6136111 := by exact prefixLift 6136111
  have htrace : WordTrace (prefixWord ++ tailWord_6136111) baseStart_6136111 baseEnd_6136111 := by
    simpa [prefixWord, tailWord_6136111, baseEnd_6136111] using wordTrace_append hprefix tailTrace_6136111
  have hstable : (prefixWord ++ tailWord_6136111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136111).length < 2 ^ (prefixWord ++ tailWord_6136111).sum := by decide
  have hdescent : baseEnd_6136111 < baseStart_6136111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136151 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_6136151 : Nat := 118140960795 + 6136151 * 2 ^ 59
def prefixEnd_6136151 : Nat := 4983230072969 + 3 ^ 40 * 6136151 * 2
def baseEnd_6136151 : Nat := 3150794831566927014692861

theorem tailTrace_6136151 : CollatzResearch.WordTrace tailWord_6136151 prefixEnd_6136151 3150794831566927014692861 := by
  unfold tailWord_6136151
  simp only [CollatzResearch.WordTrace]
  refine ⟨223803813192780373002664307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149202542128520248668442871 223803813192780373002664307)
  ·
    refine ⟨335705719789170559503996461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223803813192780373002664307 335705719789170559503996461)
    ·
      refine ⟨125889644920938959813998673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335705719789170559503996461 125889644920938959813998673)
      ·
        refine ⟨94417233690704219860499005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125889644920938959813998673 94417233690704219860499005)
        ·
          refine ⟨35406462634014082447687127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94417233690704219860499005 35406462634014082447687127)
          ·
            refine ⟨53109693951021123671530691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35406462634014082447687127 53109693951021123671530691)
            ·
              refine ⟨79664540926531685507296037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53109693951021123671530691 79664540926531685507296037)
              ·
                refine ⟨14937101423724691032618007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79664540926531685507296037 14937101423724691032618007)
                ·
                  refine ⟨22405652135587036548927011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14937101423724691032618007 22405652135587036548927011)
                  ·
                    refine ⟨33608478203380554823390517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22405652135587036548927011 33608478203380554823390517)
                    ·
                      refine ⟨3150794831566927014692861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33608478203380554823390517 3150794831566927014692861)
                      ·
                        rfl

theorem cell23_6136151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_6136151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136151 prefixEnd_6136151 := by exact prefixLift 6136151
  have htrace : WordTrace (prefixWord ++ tailWord_6136151) baseStart_6136151 baseEnd_6136151 := by
    simpa [prefixWord, tailWord_6136151, baseEnd_6136151] using wordTrace_append hprefix tailTrace_6136151
  have hstable : (prefixWord ++ tailWord_6136151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136151).length < 2 ^ (prefixWord ++ tailWord_6136151).sum := by decide
  have hdescent : baseEnd_6136151 < baseStart_6136151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136165 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_6136165 : Nat := 118140960795 + 6136165 * 2 ^ 59
def prefixEnd_6136165 : Nat := 4983230072969 + 3 ^ 40 * 6136165 * 2
def baseEnd_6136165 : Nat := 3150802020296089959917797

theorem tailTrace_6136165 : CollatzResearch.WordTrace tailWord_6136165 prefixEnd_6136165 3150802020296089959917797 := by
  unfold tailWord_6136165
  simp only [CollatzResearch.WordTrace]
  refine ⟨223804323814729653393673949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149202882543153102262449299 223804323814729653393673949)
  ·
    refine ⟨83926621430523620022627731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223804323814729653393673949 83926621430523620022627731)
    ·
      refine ⟨125889932145785430033941597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83926621430523620022627731 125889932145785430033941597)
      ·
        refine ⟨47208724554669536262728099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125889932145785430033941597 47208724554669536262728099)
        ·
          refine ⟨70813086832004304394092149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47208724554669536262728099 70813086832004304394092149)
          ·
            refine ⟨6638726890500403536946139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70813086832004304394092149 6638726890500403536946139)
            ·
              refine ⟨9958090335750605305419209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6638726890500403536946139 9958090335750605305419209)
              ·
                refine ⟨7468567751812953979064407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9958090335750605305419209 7468567751812953979064407)
                ·
                  refine ⟨11202851627719430968596611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468567751812953979064407 11202851627719430968596611)
                  ·
                    refine ⟨16804277441579146452894917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11202851627719430968596611 16804277441579146452894917)
                    ·
                      refine ⟨3150802020296089959917797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16804277441579146452894917 3150802020296089959917797)
                      ·
                        rfl

theorem cell23_6136165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_6136165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136165 prefixEnd_6136165 := by exact prefixLift 6136165
  have htrace : WordTrace (prefixWord ++ tailWord_6136165) baseStart_6136165 baseEnd_6136165 := by
    simpa [prefixWord, tailWord_6136165, baseEnd_6136165] using wordTrace_append hprefix tailTrace_6136165
  have hstable : (prefixWord ++ tailWord_6136165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136165).length < 2 ^ (prefixWord ++ tailWord_6136165).sum := by decide
  have hdescent : baseEnd_6136165 < baseStart_6136165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136178 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6136178 : Nat := 118140960795 + 6136178 * 2 ^ 59
def prefixEnd_6136178 : Nat := 4983230072969 + 3 ^ 40 * 6136178 * 2
def baseEnd_6136178 : Nat := 3150808695544598409055237

theorem tailTrace_6136178 : CollatzResearch.WordTrace tailWord_6136178 prefixEnd_6136178 3150808695544598409055237 := by
  unfold tailWord_6136178
  simp only [CollatzResearch.WordTrace]
  refine ⟨55951199490920639153474297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149203198642455037742598125 55951199490920639153474297)
  ·
    refine ⟨41963399618190479365105723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55951199490920639153474297 41963399618190479365105723)
    ·
      refine ⟨62945099427285719047658585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41963399618190479365105723 62945099427285719047658585)
      ·
        refine ⟨47208824570464289285743939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62945099427285719047658585 47208824570464289285743939)
        ·
          refine ⟨70813236855696433928615909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47208824570464289285743939 70813236855696433928615909)
          ·
            refine ⟨13277481910443081361615483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70813236855696433928615909 13277481910443081361615483)
            ·
              refine ⟨19916222865664622042423225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13277481910443081361615483 19916222865664622042423225)
              ·
                refine ⟨14937167149248466531817419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19916222865664622042423225 14937167149248466531817419)
                ·
                  refine ⟨22405750723872699797726129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14937167149248466531817419 22405750723872699797726129)
                  ·
                    refine ⟨16804313042904524848294597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22405750723872699797726129 16804313042904524848294597)
                    ·
                      refine ⟨3150808695544598409055237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16804313042904524848294597 3150808695544598409055237)
                      ·
                        rfl

theorem cell23_6136178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6136178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136178 prefixEnd_6136178 := by exact prefixLift 6136178
  have htrace : WordTrace (prefixWord ++ tailWord_6136178) baseStart_6136178 baseEnd_6136178 := by
    simpa [prefixWord, tailWord_6136178, baseEnd_6136178] using wordTrace_append hprefix tailTrace_6136178
  have hstable : (prefixWord ++ tailWord_6136178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136178).length < 2 ^ (prefixWord ++ tailWord_6136178).sum := by decide
  have hdescent : baseEnd_6136178 < baseStart_6136178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136201 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_6136201 : Nat := 118140960795 + 6136201 * 2 ^ 59
def prefixEnd_6136201 : Nat := 4983230072969 + 3 ^ 40 * 6136201 * 2
def baseEnd_6136201 : Nat := 1050273501866550606355877

theorem tailTrace_6136201 : CollatzResearch.WordTrace tailWord_6136201 prefixEnd_6136201 1050273501866550606355877 := by
  unfold tailWord_6136201
  simp only [CollatzResearch.WordTrace]
  refine ⟨223805636842599231541984457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149203757895066154361322971 223805636842599231541984457)
  ·
    refine ⟨167854227631949423656488343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223805636842599231541984457 167854227631949423656488343)
    ·
      refine ⟨251781341447924135484732515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167854227631949423656488343 251781341447924135484732515)
      ·
        refine ⟨377672012171886203227098773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251781341447924135484732515 377672012171886203227098773)
        ·
          refine ⟨17703375570557165776270255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 377672012171886203227098773 17703375570557165776270255)
          ·
            refine ⟨26555063355835748664405383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17703375570557165776270255 26555063355835748664405383)
            ·
              refine ⟨39832595033753622996608075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26555063355835748664405383 39832595033753622996608075)
              ·
                refine ⟨59748892550630434494912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39832595033753622996608075 59748892550630434494912113)
                ·
                  refine ⟨44811669412972825871184085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59748892550630434494912113 44811669412972825871184085)
                  ·
                    refine ⟨1050273501866550606355877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44811669412972825871184085 1050273501866550606355877)
                    ·
                      rfl

theorem cell23_6136201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_6136201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136201 prefixEnd_6136201 := by exact prefixLift 6136201
  have htrace : WordTrace (prefixWord ++ tailWord_6136201) baseStart_6136201 baseEnd_6136201 := by
    simpa [prefixWord, tailWord_6136201, baseEnd_6136201] using wordTrace_append hprefix tailTrace_6136201
  have hstable : (prefixWord ++ tailWord_6136201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136201).length < 2 ^ (prefixWord ++ tailWord_6136201).sum := by decide
  have hdescent : baseEnd_6136201 < baseStart_6136201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136215 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_6136215 : Nat := 118140960795 + 6136215 * 2 ^ 59
def prefixEnd_6136215 : Nat := 4983230072969 + 3 ^ 40 * 6136215 * 2
def baseEnd_6136215 : Nat := 3150827694328814764292567

theorem tailTrace_6136215 : CollatzResearch.WordTrace tailWord_6136215 prefixEnd_6136215 3150827694328814764292567 := by
  unfold tailWord_6136215
  simp only [CollatzResearch.WordTrace]
  refine ⟨223806147464548511932994099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149204098309699007955329399 223806147464548511932994099)
  ·
    refine ⟨335709221196822767899491149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223806147464548511932994099 335709221196822767899491149)
    ·
      refine ⟨125890957948808537962309181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335709221196822767899491149 125890957948808537962309181)
      ·
        refine ⟨47209109230803201735865943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125890957948808537962309181 47209109230803201735865943)
        ·
          refine ⟨70813663846204802603798915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47209109230803201735865943 70813663846204802603798915)
          ·
            refine ⟨106220495769307203905698373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70813663846204802603798915 106220495769307203905698373)
            ·
              refine ⟨19916342956745100732318445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106220495769307203905698373 19916342956745100732318445)
              ·
                refine ⟨7468628608779412774619417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19916342956745100732318445 7468628608779412774619417)
                ·
                  refine ⟨5601471456584559580964563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7468628608779412774619417 5601471456584559580964563)
                  ·
                    refine ⟨8402207184876839371446845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601471456584559580964563 8402207184876839371446845)
                    ·
                      refine ⟨3150827694328814764292567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402207184876839371446845 3150827694328814764292567)
                      ·
                        rfl

theorem cell23_6136215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_6136215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136215 prefixEnd_6136215 := by exact prefixLift 6136215
  have htrace : WordTrace (prefixWord ++ tailWord_6136215) baseStart_6136215 baseEnd_6136215 := by
    simpa [prefixWord, tailWord_6136215, baseEnd_6136215] using wordTrace_append hprefix tailTrace_6136215
  have hstable : (prefixWord ++ tailWord_6136215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136215).length < 2 ^ (prefixWord ++ tailWord_6136215).sum := by decide
  have hdescent : baseEnd_6136215 < baseStart_6136215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136328 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6136328 : Nat := 118140960795 + 6136328 * 2 ^ 59
def prefixEnd_6136328 : Nat := 4983230072969 + 3 ^ 40 * 6136328 * 2
def baseEnd_6136328 : Nat := 3150885717642772822179547

theorem tailTrace_6136328 : CollatzResearch.WordTrace tailWord_6136328 prefixEnd_6136328 3150885717642772822179547 := by
  unfold tailWord_6136328
  simp only [CollatzResearch.WordTrace]
  refine ⟨111905134456569566115928819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149206845942092754821238425 111905134456569566115928819)
  ·
    refine ⟨167857701684854349173893229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111905134456569566115928819 167857701684854349173893229)
    ·
      refine ⟨62946638131820380940209961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167857701684854349173893229 62946638131820380940209961)
      ·
        refine ⟨47209978598865285705157471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62946638131820380940209961 47209978598865285705157471)
        ·
          refine ⟨70814967898297928557736207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47209978598865285705157471 70814967898297928557736207)
          ·
            refine ⟨106222451847446892836604311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70814967898297928557736207 106222451847446892836604311)
            ·
              refine ⟨159333677771170339254906467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106222451847446892836604311 159333677771170339254906467)
              ·
                refine ⟨239000516656755508882359701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159333677771170339254906467 239000516656755508882359701)
                ·
                  refine ⟨11203149218285414478860611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239000516656755508882359701 11203149218285414478860611)
                  ·
                    refine ⟨16804723827428121718290917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11203149218285414478860611 16804723827428121718290917)
                    ·
                      refine ⟨3150885717642772822179547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16804723827428121718290917 3150885717642772822179547)
                      ·
                        rfl

theorem cell23_6136328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6136328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136328 prefixEnd_6136328 := by exact prefixLift 6136328
  have htrace : WordTrace (prefixWord ++ tailWord_6136328) baseStart_6136328 baseEnd_6136328 := by
    simpa [prefixWord, tailWord_6136328, baseEnd_6136328] using wordTrace_append hprefix tailTrace_6136328
  have hstable : (prefixWord ++ tailWord_6136328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136328).length < 2 ^ (prefixWord ++ tailWord_6136328).sum := by decide
  have hdescent : baseEnd_6136328 < baseStart_6136328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136368 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 6]
def baseStart_6136368 : Nat := 118140960795 + 6136368 * 2 ^ 59
def prefixEnd_6136368 : Nat := 4983230072969 + 3 ^ 40 * 6136368 * 2
def baseEnd_6136368 : Nat := 350100695207661407297707

theorem tailTrace_6136368 : CollatzResearch.WordTrace tailWord_6136368 prefixEnd_6136368 350100695207661407297707 := by
  unfold tailWord_6136368
  simp only [CollatzResearch.WordTrace]
  refine ⟨111905863916497109531656879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149207818555329479375542505 111905863916497109531656879)
  ·
    refine ⟨167858795874745664297485319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111905863916497109531656879 167858795874745664297485319)
    ·
      refine ⟨251788193812118496446227979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167858795874745664297485319 251788193812118496446227979)
      ·
        refine ⟨377682290718177744669341969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251788193812118496446227979 377682290718177744669341969)
        ·
          refine ⟨283261718038633308502006477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377682290718177744669341969 283261718038633308502006477)
          ·
            refine ⟨106223144264487490688252429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283261718038633308502006477 106223144264487490688252429)
            ·
              refine ⟨39833679099182809008094661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106223144264487490688252429 39833679099182809008094661)
              ·
                refine ⟨7468814831096776689017749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39833679099182809008094661 7468814831096776689017749)
                ·
                  refine ⟨350100695207661407297707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7468814831096776689017749 350100695207661407297707)
                  ·
                    rfl

theorem cell23_6136368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_6136368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136368 prefixEnd_6136368 := by exact prefixLift 6136368
  have htrace : WordTrace (prefixWord ++ tailWord_6136368) baseStart_6136368 baseEnd_6136368 := by
    simpa [prefixWord, tailWord_6136368, baseEnd_6136368] using wordTrace_append hprefix tailTrace_6136368
  have hstable : (prefixWord ++ tailWord_6136368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136368).length < 2 ^ (prefixWord ++ tailWord_6136368).sum := by decide
  have hdescent : baseEnd_6136368 < baseStart_6136368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136385 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 6]
def baseStart_6136385 : Nat := 118140960795 + 6136385 * 2 ^ 59
def prefixEnd_6136385 : Nat := 4983230072969 + 3 ^ 40 * 6136385 * 2
def baseEnd_6136385 : Nat := 350101665115564344351865

theorem tailTrace_6136385 : CollatzResearch.WordTrace tailWord_6136385 prefixEnd_6136385 350101665115564344351865 := by
  unfold tailWord_6136385
  simp only [CollatzResearch.WordTrace]
  refine ⟨223812347873932630966682609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149208231915955087311121739 223812347873932630966682609)
  ·
    refine ⟨167859260905449473225011957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223812347873932630966682609 167859260905449473225011957)
    ·
      refine ⟨15736805709885888114844871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167859260905449473225011957 15736805709885888114844871)
      ·
        refine ⟨23605208564828832172267307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736805709885888114844871 23605208564828832172267307)
        ·
          refine ⟨35407812847243248258400961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23605208564828832172267307 35407812847243248258400961)
          ·
            refine ⟨26555859635432436193800721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35407812847243248258400961 26555859635432436193800721)
            ·
              refine ⟨19916894726574327145350541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26555859635432436193800721 19916894726574327145350541)
              ·
                refine ⟨7468835522465372679506453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19916894726574327145350541 7468835522465372679506453)
                ·
                  refine ⟨350101665115564344351865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7468835522465372679506453 350101665115564344351865)
                  ·
                    rfl

theorem cell23_6136385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_6136385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136385 prefixEnd_6136385 := by exact prefixLift 6136385
  have htrace : WordTrace (prefixWord ++ tailWord_6136385) baseStart_6136385 baseEnd_6136385 := by
    simpa [prefixWord, tailWord_6136385, baseEnd_6136385] using wordTrace_append hprefix tailTrace_6136385
  have hstable : (prefixWord ++ tailWord_6136385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136385).length < 2 ^ (prefixWord ++ tailWord_6136385).sum := by decide
  have hdescent : baseEnd_6136385 < baseStart_6136385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136395 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 3]
def baseStart_6136395 : Nat := 118140960795 + 6136395 * 2 ^ 59
def prefixEnd_6136395 : Nat := 4983230072969 + 3 ^ 40 * 6136395 * 2
def baseEnd_6136395 : Nat := 3150920120846624060041739

theorem tailTrace_6136395 : CollatzResearch.WordTrace tailWord_6136395 prefixEnd_6136395 3150920120846624060041739 := by
  unfold tailWord_6136395
  simp only [CollatzResearch.WordTrace]
  refine ⟨223812712603896402674546639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149208475069264268449697759 223812712603896402674546639)
  ·
    refine ⟨335719068905844604011819959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223812712603896402674546639 335719068905844604011819959)
    ·
      refine ⟨503578603358766906017729939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335719068905844604011819959 503578603358766906017729939)
      ·
        refine ⟨755367905038150359026594909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503578603358766906017729939 755367905038150359026594909)
        ·
          refine ⟨283262964389306384634973091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755367905038150359026594909 283262964389306384634973091)
          ·
            refine ⟨424894446583959576952459637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283262964389306384634973091 424894446583959576952459637)
            ·
              refine ⟨39833854367246210339293091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 424894446583959576952459637 39833854367246210339293091)
              ·
                refine ⟨59750781550869315508939637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39833854367246210339293091 59750781550869315508939637)
                ·
                  refine ⟨5601635770393998328963091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59750781550869315508939637 5601635770393998328963091)
                  ·
                    refine ⟨8402453655590997493444637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601635770393998328963091 8402453655590997493444637)
                    ·
                      refine ⟨3150920120846624060041739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402453655590997493444637 3150920120846624060041739)
                      ·
                        rfl

theorem cell23_6136395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 3].length) (baseStart_6136395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136395 prefixEnd_6136395 := by exact prefixLift 6136395
  have htrace : WordTrace (prefixWord ++ tailWord_6136395) baseStart_6136395 baseEnd_6136395 := by
    simpa [prefixWord, tailWord_6136395, baseEnd_6136395] using wordTrace_append hprefix tailTrace_6136395
  have hstable : (prefixWord ++ tailWord_6136395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136395).length < 2 ^ (prefixWord ++ tailWord_6136395).sum := by decide
  have hdescent : baseEnd_6136395 < baseStart_6136395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136428 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_6136428 : Nat := 118140960795 + 6136428 * 2 ^ 59
def prefixEnd_6136428 : Nat := 4983230072969 + 3 ^ 40 * 6136428 * 2
def baseEnd_6136428 : Nat := 1050312355236074143643029

theorem tailTrace_6136428 : CollatzResearch.WordTrace tailWord_6136428 prefixEnd_6136428 1050312355236074143643029 := by
  unfold tailWord_6136428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111906958106388424655248969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149209277475184566206998625 111906958106388424655248969)
  ·
    refine ⟨83930218579791318491436727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111906958106388424655248969 83930218579791318491436727)
    ·
      refine ⟨125895327869686977737155091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83930218579791318491436727 125895327869686977737155091)
      ·
        refine ⟨188842991804530466605732637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125895327869686977737155091 188842991804530466605732637)
        ·
          refine ⟨70816121926698924977149739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188842991804530466605732637 70816121926698924977149739)
          ·
            refine ⟨106224182890048387465724609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70816121926698924977149739 106224182890048387465724609)
            ·
              refine ⟨79668137167536290599293457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106224182890048387465724609 79668137167536290599293457)
              ·
                refine ⟨59751102875652217949470093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79668137167536290599293457 59751102875652217949470093)
                ·
                  refine ⟨22406663578369581731051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59751102875652217949470093 22406663578369581731051285)
                  ·
                    refine ⟨1050312355236074143643029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22406663578369581731051285 1050312355236074143643029)
                    ·
                      rfl

theorem cell23_6136428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_6136428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136428 prefixEnd_6136428 := by exact prefixLift 6136428
  have htrace : WordTrace (prefixWord ++ tailWord_6136428) baseStart_6136428 baseEnd_6136428 := by
    simpa [prefixWord, tailWord_6136428, baseEnd_6136428] using wordTrace_append hprefix tailTrace_6136428
  have hstable : (prefixWord ++ tailWord_6136428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136428).length < 2 ^ (prefixWord ++ tailWord_6136428).sum := by decide
  have hdescent : baseEnd_6136428 < baseStart_6136428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136429 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6136429 : Nat := 118140960795 + 6136429 * 2 ^ 59
def prefixEnd_6136429 : Nat := 4983230072969 + 3 ^ 40 * 6136429 * 2
def baseEnd_6136429 : Nat := 3150937579188876927016583

theorem tailTrace_6136429 : CollatzResearch.WordTrace tailWord_6136429 prefixEnd_6136429 3150937579188876927016583 := by
  unfold tailWord_6136429
  simp only [CollatzResearch.WordTrace]
  refine ⟨223813952685773226481284341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149209301790515484320856227 223813952685773226481284341)
  ·
    refine ⟨20982558064291239982620407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223813952685773226481284341 20982558064291239982620407)
    ·
      refine ⟨31473837096436859973930611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20982558064291239982620407 31473837096436859973930611)
      ·
        refine ⟨47210755644655289960895917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31473837096436859973930611 47210755644655289960895917)
        ·
          refine ⟨17704033366745733735335969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47210755644655289960895917 17704033366745733735335969)
          ·
            refine ⟨13278025025059300301501977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17704033366745733735335969 13278025025059300301501977)
            ·
              refine ⟨9958518768794475226126483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13278025025059300301501977 9958518768794475226126483)
              ·
                refine ⟨14937778153191712839189725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958518768794475226126483 14937778153191712839189725)
                ·
                  refine ⟨5601666807446892314696147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14937778153191712839189725 5601666807446892314696147)
                  ·
                    refine ⟨8402500211170338472044221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5601666807446892314696147 8402500211170338472044221)
                    ·
                      refine ⟨3150937579188876927016583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402500211170338472044221 3150937579188876927016583)
                      ·
                        rfl

theorem cell23_6136429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6136429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136429 prefixEnd_6136429 := by exact prefixLift 6136429
  have htrace : WordTrace (prefixWord ++ tailWord_6136429) baseStart_6136429 baseEnd_6136429 := by
    simpa [prefixWord, tailWord_6136429, baseEnd_6136429] using wordTrace_append hprefix tailTrace_6136429
  have hstable : (prefixWord ++ tailWord_6136429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136429).length < 2 ^ (prefixWord ++ tailWord_6136429).sum := by decide
  have hdescent : baseEnd_6136429 < baseStart_6136429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136452 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_6136452 : Nat := 118140960795 + 6136452 * 2 ^ 59
def prefixEnd_6136452 : Nat := 4983230072969 + 3 ^ 40 * 6136452 * 2
def baseEnd_6136452 : Nat := 3150949389243930337028977

theorem tailTrace_6136452 : CollatzResearch.WordTrace tailWord_6136452 prefixEnd_6136452 3150949389243930337028977 := by
  unfold tailWord_6136452
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907395782344950704685805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149209861043126600939581073 111907395782344950704685805)
  ·
    refine ⟨41965273418379356514257177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111907395782344950704685805 41965273418379356514257177)
    ·
      refine ⟨31473955063784517385692883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41965273418379356514257177 31473955063784517385692883)
      ·
        refine ⟨47210932595676776078539325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31473955063784517385692883 47210932595676776078539325)
        ·
          refine ⟨17704099723378791029452247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47210932595676776078539325 17704099723378791029452247)
          ·
            refine ⟨26556149585068186544178371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704099723378791029452247 26556149585068186544178371)
            ·
              refine ⟨39834224377602279816267557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26556149585068186544178371 39834224377602279816267557)
              ·
                refine ⟨7468917070800427465550167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39834224377602279816267557 7468917070800427465550167)
                ·
                  refine ⟨11203375606200641198325251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468917070800427465550167 11203375606200641198325251)
                  ·
                    refine ⟨16805063409300961797487877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11203375606200641198325251 16805063409300961797487877)
                    ·
                      refine ⟨3150949389243930337028977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16805063409300961797487877 3150949389243930337028977)
                      ·
                        rfl

theorem cell23_6136452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_6136452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136452 prefixEnd_6136452 := by exact prefixLift 6136452
  have htrace : WordTrace (prefixWord ++ tailWord_6136452) baseStart_6136452 baseEnd_6136452 := by
    simpa [prefixWord, tailWord_6136452, baseEnd_6136452] using wordTrace_append hprefix tailTrace_6136452
  have hstable : (prefixWord ++ tailWord_6136452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136452).length < 2 ^ (prefixWord ++ tailWord_6136452).sum := by decide
  have hdescent : baseEnd_6136452 < baseStart_6136452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136472 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6136472 : Nat := 118140960795 + 6136472 * 2 ^ 59
def prefixEnd_6136472 : Nat := 4983230072969 + 3 ^ 40 * 6136472 * 2
def baseEnd_6136472 : Nat := 3150959658857020258778885

theorem tailTrace_6136472 : CollatzResearch.WordTrace tailWord_6136472 prefixEnd_6136472 3150959658857020258778885 := by
  unfold tailWord_6136472
  simp only [CollatzResearch.WordTrace]
  refine ⟨111907760512308722412549835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149210347349744963216733113 111907760512308722412549835)
  ·
    refine ⟨167861640768463083618824753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111907760512308722412549835 167861640768463083618824753)
    ·
      refine ⟨125896230576347312714118565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167861640768463083618824753 125896230576347312714118565)
      ·
        refine ⟨23605543233065121133897231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125896230576347312714118565 23605543233065121133897231)
        ·
          refine ⟨35408314849597681700845847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23605543233065121133897231 35408314849597681700845847)
          ·
            refine ⟨53112472274396522551268771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35408314849597681700845847 53112472274396522551268771)
            ·
              refine ⟨79668708411594783826903157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53112472274396522551268771 79668708411594783826903157)
              ·
                refine ⟨7468941413587010983772171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79668708411594783826903157 7468941413587010983772171)
                ·
                  refine ⟨11203412120380516475658257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468941413587010983772171 11203412120380516475658257)
                  ·
                    refine ⟨8402559090285387356743693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11203412120380516475658257 8402559090285387356743693)
                    ·
                      refine ⟨3150959658857020258778885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402559090285387356743693 3150959658857020258778885)
                      ·
                        rfl

theorem cell23_6136472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6136472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136472 prefixEnd_6136472 := by exact prefixLift 6136472
  have htrace : WordTrace (prefixWord ++ tailWord_6136472) baseStart_6136472 baseEnd_6136472 := by
    simpa [prefixWord, tailWord_6136472, baseEnd_6136472] using wordTrace_append hprefix tailTrace_6136472
  have hstable : (prefixWord ++ tailWord_6136472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136472).length < 2 ^ (prefixWord ++ tailWord_6136472).sum := by decide
  have hdescent : baseEnd_6136472 < baseStart_6136472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136552 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6136552 : Nat := 118140960795 + 6136552 * 2 ^ 59
def prefixEnd_6136552 : Nat := 4983230072969 + 3 ^ 40 * 6136552 * 2
def baseEnd_6136552 : Nat := 1050333579103126648592839

theorem tailTrace_6136552 : CollatzResearch.WordTrace tailWord_6136552 prefixEnd_6136552 1050333579103126648592839 := by
  unfold tailWord_6136552
  simp only [CollatzResearch.WordTrace]
  refine ⟨111909219432163809244005955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149212292576218412325341273 111909219432163809244005955)
  ·
    refine ⟨167863829148245713866008933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111909219432163809244005955 167863829148245713866008933)
    ·
      refine ⟨31474467965296071349876675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167863829148245713866008933 31474467965296071349876675)
      ·
        refine ⟨47211701947944107024815013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31474467965296071349876675 47211701947944107024815013)
        ·
          refine ⟨8852194115239520067152815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47211701947944107024815013 8852194115239520067152815)
          ·
            refine ⟨13278291172859280100729223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852194115239520067152815 13278291172859280100729223)
            ·
              refine ⟨19917436759288920151093835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13278291172859280100729223 19917436759288920151093835)
              ·
                refine ⟨29876155138933380226640753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19917436759288920151093835 29876155138933380226640753)
                ·
                  refine ⟨22407116354200035169980565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29876155138933380226640753 22407116354200035169980565)
                  ·
                    refine ⟨1050333579103126648592839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22407116354200035169980565 1050333579103126648592839)
                    ·
                      rfl

theorem cell23_6136552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6136552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136552 prefixEnd_6136552 := by exact prefixLift 6136552
  have htrace : WordTrace (prefixWord ++ tailWord_6136552) baseStart_6136552 baseEnd_6136552 := by
    simpa [prefixWord, tailWord_6136552, baseEnd_6136552] using wordTrace_append hprefix tailTrace_6136552
  have hstable : (prefixWord ++ tailWord_6136552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136552).length < 2 ^ (prefixWord ++ tailWord_6136552).sum := by decide
  have hdescent : baseEnd_6136552 < baseStart_6136552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136559 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 4, 2]
def baseStart_6136559 : Nat := 118140960795 + 6136559 * 2 ^ 59
def prefixEnd_6136559 : Nat := 4983230072969 + 3 ^ 40 * 6136559 * 2
def baseEnd_6136559 : Nat := 3151004331673961418390985

theorem tailTrace_6136559 : CollatzResearch.WordTrace tailWord_6136559 prefixEnd_6136559 3151004331673961418390985 := by
  unfold tailWord_6136559
  simp only [CollatzResearch.WordTrace]
  refine ⟨223818694175302258683516731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149212462783534839122344487 223818694175302258683516731)
  ·
    refine ⟨335728041262953388025275097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223818694175302258683516731 335728041262953388025275097)
    ·
      refine ⟨251796030947215041018956323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335728041262953388025275097 251796030947215041018956323)
      ·
        refine ⟨377694046420822561528434485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251796030947215041018956323 377694046420822561528434485)
        ·
          refine ⟨35408816851952115143290733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 377694046420822561528434485 35408816851952115143290733)
          ·
            refine ⟨13278306319482043178734025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35408816851952115143290733 13278306319482043178734025)
            ·
              refine ⟨9958729739611532384050519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13278306319482043178734025 9958729739611532384050519)
              ·
                refine ⟨14938094609417298576075779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958729739611532384050519 14938094609417298576075779)
                ·
                  refine ⟨22407141914125947864113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14938094609417298576075779 22407141914125947864113669)
                  ·
                    refine ⟨4201339108898615224521313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22407141914125947864113669 4201339108898615224521313)
                    ·
                      refine ⟨3151004331673961418390985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201339108898615224521313 3151004331673961418390985)
                      ·
                        rfl

theorem cell23_6136559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4, 2].length) (baseStart_6136559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136559 prefixEnd_6136559 := by exact prefixLift 6136559
  have htrace : WordTrace (prefixWord ++ tailWord_6136559) baseStart_6136559 baseEnd_6136559 := by
    simpa [prefixWord, tailWord_6136559, baseEnd_6136559] using wordTrace_append hprefix tailTrace_6136559
  have hstable : (prefixWord ++ tailWord_6136559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136559).length < 2 ^ (prefixWord ++ tailWord_6136559).sum := by decide
  have hdescent : baseEnd_6136559 < baseStart_6136559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136575 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_6136575 : Nat := 118140960795 + 6136575 * 2 ^ 59
def prefixEnd_6136575 : Nat := 4983230072969 + 3 ^ 40 * 6136575 * 2
def baseEnd_6136575 : Nat := 3151012547364433355790911

theorem tailTrace_6136575 : CollatzResearch.WordTrace tailWord_6136575 prefixEnd_6136575 3151012547364433355790911 := by
  unfold tailWord_6136575
  simp only [CollatzResearch.WordTrace]
  refine ⟨223819277743244293416099179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149212851828829528944066119 223819277743244293416099179)
  ·
    refine ⟨335728916614866440124148769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223819277743244293416099179 335728916614866440124148769)
    ·
      refine ⟨251796687461149830093111577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335728916614866440124148769 251796687461149830093111577)
      ·
        refine ⟨188847515595862372569833683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251796687461149830093111577 188847515595862372569833683)
        ·
          refine ⟨283271273393793558854750525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188847515595862372569833683 283271273393793558854750525)
          ·
            refine ⟨106226727522672584570531447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283271273393793558854750525 106226727522672584570531447)
            ·
              refine ⟨159340091284008876855797171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106226727522672584570531447 159340091284008876855797171)
              ·
                refine ⟨239010136926013315283695757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159340091284008876855797171 239010136926013315283695757)
                ·
                  refine ⟨89628801347254993231385909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239010136926013315283695757 89628801347254993231385909)
                  ·
                    refine ⟨8402700126305155615442429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89628801347254993231385909 8402700126305155615442429)
                    ·
                      refine ⟨3151012547364433355790911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8402700126305155615442429 3151012547364433355790911)
                      ·
                        rfl

theorem cell23_6136575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_6136575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136575 prefixEnd_6136575 := by exact prefixLift 6136575
  have htrace : WordTrace (prefixWord ++ tailWord_6136575) baseStart_6136575 baseEnd_6136575 := by
    simpa [prefixWord, tailWord_6136575, baseEnd_6136575] using wordTrace_append hprefix tailTrace_6136575
  have hstable : (prefixWord ++ tailWord_6136575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136575).length < 2 ^ (prefixWord ++ tailWord_6136575).sum := by decide
  have hdescent : baseEnd_6136575 < baseStart_6136575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136595 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 4, 5]
def baseStart_6136595 : Nat := 118140960795 + 6136595 * 2 ^ 59
def prefixEnd_6136595 : Nat := 4983230072969 + 3 ^ 40 * 6136595 * 2
def baseEnd_6136595 : Nat := 1050340938992507759180273

theorem tailTrace_6136595 : CollatzResearch.WordTrace tailWord_6136595 prefixEnd_6136595 1050340938992507759180273 := by
  unfold tailWord_6136595
  simp only [CollatzResearch.WordTrace]
  refine ⟨223820007203171836831827239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149213338135447891221218159 223820007203171836831827239)
  ·
    refine ⟨335730010804757755247740859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223820007203171836831827239 335730010804757755247740859)
    ·
      refine ⟨503595016207136632871611289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335730010804757755247740859 503595016207136632871611289)
      ·
        refine ⟨377696262155352474653708467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503595016207136632871611289 377696262155352474653708467)
        ·
          refine ⟨566544393233028711980562701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377696262155352474653708467 566544393233028711980562701)
          ·
            refine ⟨212454147462385766992711013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566544393233028711980562701 212454147462385766992711013)
            ·
              refine ⟨39835152649197331311133315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212454147462385766992711013 39835152649197331311133315)
              ·
                refine ⟨59752728973795996966699973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39835152649197331311133315 59752728973795996966699973)
                ·
                  refine ⟨11203636682586749431256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59752728973795996966699973 11203636682586749431256245)
                  ·
                    refine ⟨1050340938992507759180273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11203636682586749431256245 1050340938992507759180273)
                    ·
                      rfl

theorem cell23_6136595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 5].length) (baseStart_6136595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136595 prefixEnd_6136595 := by exact prefixLift 6136595
  have htrace : WordTrace (prefixWord ++ tailWord_6136595) baseStart_6136595 baseEnd_6136595 := by
    simpa [prefixWord, tailWord_6136595, baseEnd_6136595] using wordTrace_append hprefix tailTrace_6136595
  have hstable : (prefixWord ++ tailWord_6136595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136595).length < 2 ^ (prefixWord ++ tailWord_6136595).sum := by decide
  have hdescent : baseEnd_6136595 < baseStart_6136595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136625 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_6136625 : Nat := 118140960795 + 6136625 * 2 ^ 59
def prefixEnd_6136625 : Nat := 4983230072969 + 3 ^ 40 * 6136625 * 2
def baseEnd_6136625 : Nat := 1050346073799052720055227

theorem tailTrace_6136625 : CollatzResearch.WordTrace tailWord_6136625 prefixEnd_6136625 1050346073799052720055227 := by
  unfold tailWord_6136625
  simp only [CollatzResearch.WordTrace]
  refine ⟨223821101393063151955419329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149214067595375434636946219 223821101393063151955419329)
  ·
    refine ⟨167865826044797363966564497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223821101393063151955419329 167865826044797363966564497)
    ·
      refine ⟨125899369533598022974923373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167865826044797363966564497 125899369533598022974923373)
      ·
        refine ⟨47212263575099258615596265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125899369533598022974923373 47212263575099258615596265)
        ·
          refine ⟨35409197681324443961697199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47212263575099258615596265 35409197681324443961697199)
          ·
            refine ⟨53113796521986665942545799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35409197681324443961697199 53113796521986665942545799)
            ·
              refine ⟨79670694782979998913818699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53113796521986665942545799 79670694782979998913818699)
              ·
                refine ⟨119506042174469998370728049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79670694782979998913818699 119506042174469998370728049)
                ·
                  refine ⟨89629531630852498778046037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119506042174469998370728049 89629531630852498778046037)
                  ·
                    refine ⟨1050346073799052720055227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89629531630852498778046037 1050346073799052720055227)
                    ·
                      rfl

theorem cell23_6136625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_6136625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136625 prefixEnd_6136625 := by exact prefixLift 6136625
  have htrace : WordTrace (prefixWord ++ tailWord_6136625) baseStart_6136625 baseEnd_6136625 := by
    simpa [prefixWord, tailWord_6136625, baseEnd_6136625] using wordTrace_append hprefix tailTrace_6136625
  have hstable : (prefixWord ++ tailWord_6136625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136625).length < 2 ^ (prefixWord ++ tailWord_6136625).sum := by decide
  have hdescent : baseEnd_6136625 < baseStart_6136625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136632 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_6136632 : Nat := 118140960795 + 6136632 * 2 ^ 59
def prefixEnd_6136632 : Nat := 4983230072969 + 3 ^ 40 * 6136632 * 2
def baseEnd_6136632 : Nat := 3151041815761739632778149

theorem tailTrace_6136632 : CollatzResearch.WordTrace tailWord_6136632 prefixEnd_6136632 3151041815761739632778149 := by
  unfold tailWord_6136632
  simp only [CollatzResearch.WordTrace]
  refine ⟨111910678352018896075462075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149214237802691861433949433 111910678352018896075462075)
  ·
    refine ⟨167866017528028344113193113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111910678352018896075462075 167866017528028344113193113)
    ·
      refine ⟨125899513146021258084894835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167866017528028344113193113 125899513146021258084894835)
      ·
        refine ⟨188849269719031887127342253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125899513146021258084894835 188849269719031887127342253)
        ·
          refine ⟨70818476144636957672753345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188849269719031887127342253 70818476144636957672753345)
          ·
            refine ⟨53113857108477718254565009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70818476144636957672753345 53113857108477718254565009)
            ·
              refine ⟨39835392831358288690923757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53113857108477718254565009 39835392831358288690923757)
              ·
                refine ⟨14938272311759358259096409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39835392831358288690923757 14938272311759358259096409)
                ·
                  refine ⟨11203704233819518694322307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14938272311759358259096409 11203704233819518694322307)
                  ·
                    refine ⟨16805556350729278041483461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11203704233819518694322307 16805556350729278041483461)
                    ·
                      refine ⟨3151041815761739632778149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16805556350729278041483461 3151041815761739632778149)
                      ·
                        rfl

theorem cell23_6136632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_6136632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136632 prefixEnd_6136632 := by exact prefixLift 6136632
  have htrace : WordTrace (prefixWord ++ tailWord_6136632) baseStart_6136632 baseEnd_6136632 := by
    simpa [prefixWord, tailWord_6136632, baseEnd_6136632] using wordTrace_append hprefix tailTrace_6136632
  have hstable : (prefixWord ++ tailWord_6136632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136632).length < 2 ^ (prefixWord ++ tailWord_6136632).sum := by decide
  have hdescent : baseEnd_6136632 < baseStart_6136632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136645 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_6136645 : Nat := 118140960795 + 6136645 * 2 ^ 59
def prefixEnd_6136645 : Nat := 4983230072969 + 3 ^ 40 * 6136645 * 2
def baseEnd_6136645 : Nat := 3151048491010248081915589

theorem tailTrace_6136645 : CollatzResearch.WordTrace tailWord_6136645 prefixEnd_6136645 3151048491010248081915589 := by
  unfold tailWord_6136645
  simp only [CollatzResearch.WordTrace]
  refine ⟨223821830852990695371147389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149214553901993796914098259 223821830852990695371147389)
  ·
    refine ⟨83933186569871510764180271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223821830852990695371147389 83933186569871510764180271)
    ·
      refine ⟨125899779854807266146270407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83933186569871510764180271 125899779854807266146270407)
      ·
        refine ⟨188849669782210899219405611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125899779854807266146270407 188849669782210899219405611)
        ·
          refine ⟨283274504673316348829108417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188849669782210899219405611 283274504673316348829108417)
          ·
            refine ⟨212455878504987261621831313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283274504673316348829108417 212455878504987261621831313)
            ·
              refine ⟨159341908878740446216373485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212455878504987261621831313 159341908878740446216373485)
              ·
                refine ⟨59753215829527667331140057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159341908878740446216373485 59753215829527667331140057)
                ·
                  refine ⟨44814911872145750498355043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59753215829527667331140057 44814911872145750498355043)
                  ·
                    refine ⟨67222367808218625747532565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44814911872145750498355043 67222367808218625747532565)
                    ·
                      refine ⟨3151048491010248081915589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67222367808218625747532565 3151048491010248081915589)
                      ·
                        rfl

theorem cell23_6136645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_6136645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136645 prefixEnd_6136645 := by exact prefixLift 6136645
  have htrace : WordTrace (prefixWord ++ tailWord_6136645) baseStart_6136645 baseEnd_6136645 := by
    simpa [prefixWord, tailWord_6136645, baseEnd_6136645] using wordTrace_append hprefix tailTrace_6136645
  have hstable : (prefixWord ++ tailWord_6136645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136645).length < 2 ^ (prefixWord ++ tailWord_6136645).sum := by decide
  have hdescent : baseEnd_6136645 < baseStart_6136645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136659 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 1, 4]
def baseStart_6136659 : Nat := 118140960795 + 6136659 * 2 ^ 59
def prefixEnd_6136659 : Nat := 4983230072969 + 3 ^ 40 * 6136659 * 2
def baseEnd_6136659 : Nat := 1050351893246470342380175

theorem tailTrace_6136659 : CollatzResearch.WordTrace tailWord_6136659 prefixEnd_6136659 1050351893246470342380175 := by
  unfold tailWord_6136659
  simp only [CollatzResearch.WordTrace]
  refine ⟨223822341474939975762157031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149214894316626650508104687 223822341474939975762157031)
  ·
    refine ⟨335733512212409963643235547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223822341474939975762157031 335733512212409963643235547)
    ·
      refine ⟨503600268318614945464853321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335733512212409963643235547 503600268318614945464853321)
      ·
        refine ⟨377700201238961209098639991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503600268318614945464853321 377700201238961209098639991)
        ·
          refine ⟨566550301858441813647959987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377700201238961209098639991 566550301858441813647959987)
          ·
            refine ⟨849825452787662720471939981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566550301858441813647959987 849825452787662720471939981)
            ·
              refine ⟨318684544795373520176977493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849825452787662720471939981 318684544795373520176977493)
              ·
                refine ⟨3734584509320783439573955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 318684544795373520176977493 3734584509320783439573955)
                ·
                  refine ⟨5601876763981175159360933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734584509320783439573955 5601876763981175159360933)
                  ·
                    refine ⟨1050351893246470342380175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5601876763981175159360933 1050351893246470342380175)
                    ·
                      rfl

theorem cell23_6136659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 1, 4].length) (baseStart_6136659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136659 prefixEnd_6136659 := by exact prefixLift 6136659
  have htrace : WordTrace (prefixWord ++ tailWord_6136659) baseStart_6136659 baseEnd_6136659 := by
    simpa [prefixWord, tailWord_6136659, baseEnd_6136659] using wordTrace_append hprefix tailTrace_6136659
  have hstable : (prefixWord ++ tailWord_6136659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136659).length < 2 ^ (prefixWord ++ tailWord_6136659).sum := by decide
  have hdescent : baseEnd_6136659 < baseStart_6136659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136672 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 6]
def baseStart_6136672 : Nat := 118140960795 + 6136672 * 2 ^ 59
def prefixEnd_6136672 : Nat := 4983230072969 + 3 ^ 40 * 6136672 * 2
def baseEnd_6136672 : Nat := 350118039443102164030885

theorem tailTrace_6136672 : CollatzResearch.WordTrace tailWord_6136672 prefixEnd_6136672 350118039443102164030885 := by
  unfold tailWord_6136672
  simp only [CollatzResearch.WordTrace]
  refine ⟨111911407811946439491190135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149215210415928585988253513 111911407811946439491190135)
  ·
    refine ⟨167867111717919659236785203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111911407811946439491190135 167867111717919659236785203)
    ·
      refine ⟨251800667576879488855177805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167867111717919659236785203 251800667576879488855177805)
      ·
        refine ⟨94425250341329808320691677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251800667576879488855177805 94425250341329808320691677)
        ·
          refine ⟨35409468877998678120259379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94425250341329808320691677 35409468877998678120259379)
          ·
            refine ⟨53114203316998017180389069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35409468877998678120259379 53114203316998017180389069)
            ·
              refine ⟨19917826243874256442645901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53114203316998017180389069 19917826243874256442645901)
              ·
                refine ⟨7469184841452846165992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19917826243874256442645901 7469184841452846165992213)
                ·
                  refine ⟨350118039443102164030885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7469184841452846165992213 350118039443102164030885)
                  ·
                    rfl

theorem cell23_6136672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_6136672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136672 prefixEnd_6136672 := by exact prefixLift 6136672
  have htrace : WordTrace (prefixWord ++ tailWord_6136672) baseStart_6136672 baseEnd_6136672 := by
    simpa [prefixWord, tailWord_6136672, baseEnd_6136672] using wordTrace_append hprefix tailTrace_6136672
  have hstable : (prefixWord ++ tailWord_6136672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136672).length < 2 ^ (prefixWord ++ tailWord_6136672).sum := by decide
  have hdescent : baseEnd_6136672 < baseStart_6136672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136695 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_6136695 : Nat := 118140960795 + 6136695 * 2 ^ 59
def prefixEnd_6136695 : Nat := 4983230072969 + 3 ^ 40 * 6136695 * 2
def baseEnd_6136695 : Nat := 3151074165042972886290359

theorem tailTrace_6136695 : CollatzResearch.WordTrace tailWord_6136695 prefixEnd_6136695 3151074165042972886290359 := by
  unfold tailWord_6136695
  simp only [CollatzResearch.WordTrace]
  refine ⟨223823654502809553910467539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149215769668539702606978359 223823654502809553910467539)
  ·
    refine ⟨335735481754214330865701309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223823654502809553910467539 335735481754214330865701309)
    ·
      refine ⟨125900805657830374074637991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335735481754214330865701309 125900805657830374074637991)
      ·
        refine ⟨188851208486745561111956987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125900805657830374074637991 188851208486745561111956987)
        ·
          refine ⟨283276812730118341667935481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188851208486745561111956987 283276812730118341667935481)
          ·
            refine ⟨212457609547588756250951611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283276812730118341667935481 212457609547588756250951611)
            ·
              refine ⟨318686414321383134376427417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212457609547588756250951611 318686414321383134376427417)
              ·
                refine ⟨239014810741037350782320563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318686414321383134376427417 239014810741037350782320563)
                ·
                  refine ⟨358522216111556026173480845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239014810741037350782320563 358522216111556026173480845)
                  ·
                    refine ⟨134445831041833509815055317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358522216111556026173480845 134445831041833509815055317)
                    ·
                      refine ⟨3151074165042972886290359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134445831041833509815055317 3151074165042972886290359)
                      ·
                        rfl

theorem cell23_6136695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_6136695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136695 prefixEnd_6136695 := by exact prefixLift 6136695
  have htrace : WordTrace (prefixWord ++ tailWord_6136695) baseStart_6136695 baseEnd_6136695 := by
    simpa [prefixWord, tailWord_6136695, baseEnd_6136695] using wordTrace_append hprefix tailTrace_6136695
  have hstable : (prefixWord ++ tailWord_6136695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136695).length < 2 ^ (prefixWord ++ tailWord_6136695).sum := by decide
  have hdescent : baseEnd_6136695 < baseStart_6136695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136753 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_6136753 : Nat := 118140960795 + 6136753 * 2 ^ 59
def prefixEnd_6136753 : Nat := 4983230072969 + 3 ^ 40 * 6136753 * 2
def baseEnd_6136753 : Nat := 1050367982306977886455031

theorem tailTrace_6136753 : CollatzResearch.WordTrace tailWord_6136753 prefixEnd_6136753 1050367982306977886455031 := by
  unfold tailWord_6136753
  simp only [CollatzResearch.WordTrace]
  refine ⟨223825769936599429816078913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149217179957732953210719275 223825769936599429816078913)
  ·
    refine ⟨167869327452449572362059185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223825769936599429816078913 167869327452449572362059185)
    ·
      refine ⟨125901995589337179271544389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167869327452449572362059185 125901995589337179271544389)
      ·
        refine ⟨23606624173000721113414573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125901995589337179271544389 23606624173000721113414573)
        ·
          refine ⟨8852484064875270417530465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23606624173000721113414573 8852484064875270417530465)
          ·
            refine ⟨6639363048656452813147849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852484064875270417530465 6639363048656452813147849)
            ·
              refine ⟨4979522286492339609860887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639363048656452813147849 4979522286492339609860887)
              ·
                refine ⟨7469283429738509414791331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979522286492339609860887 7469283429738509414791331)
                ·
                  refine ⟨11203925144607764122186997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7469283429738509414791331 11203925144607764122186997)
                  ·
                    refine ⟨1050367982306977886455031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11203925144607764122186997 1050367982306977886455031)
                    ·
                      rfl

theorem cell23_6136753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_6136753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136753 prefixEnd_6136753 := by exact prefixLift 6136753
  have htrace : WordTrace (prefixWord ++ tailWord_6136753) baseStart_6136753 baseEnd_6136753 := by
    simpa [prefixWord, tailWord_6136753, baseEnd_6136753] using wordTrace_append hprefix tailTrace_6136753
  have hstable : (prefixWord ++ tailWord_6136753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136753).length < 2 ^ (prefixWord ++ tailWord_6136753).sum := by decide
  have hdescent : baseEnd_6136753 < baseStart_6136753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136786 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6136786 : Nat := 118140960795 + 6136786 * 2 ^ 59
def prefixEnd_6136786 : Nat := 4983230072969 + 3 ^ 40 * 6136786 * 2
def baseEnd_6136786 : Nat := 3151120891782532030252441

theorem tailTrace_6136786 : CollatzResearch.WordTrace tailWord_6136786 prefixEnd_6136786 3151120891782532030252441 := by
  unfold tailWord_6136786
  simp only [CollatzResearch.WordTrace]
  refine ⟨55956743386369969113007553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149217982363653250968020141 55956743386369969113007553)
  ·
    refine ⟨41967557539777476834755665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55956743386369969113007553 41967557539777476834755665)
    ·
      refine ⟨31475668154833107626066749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41967557539777476834755665 31475668154833107626066749)
      ·
        refine ⟨11803375558062415359775031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31475668154833107626066749 11803375558062415359775031)
        ·
          refine ⟨17705063337093623039662547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803375558062415359775031 17705063337093623039662547)
          ·
            refine ⟨26557595005640434559493821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17705063337093623039662547 26557595005640434559493821)
            ·
              refine ⟨9959098127115162959810183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26557595005640434559493821 9959098127115162959810183)
              ·
                refine ⟨14938647190672744439715275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959098127115162959810183 14938647190672744439715275)
                ·
                  refine ⟨22407970786009116659572913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14938647190672744439715275 22407970786009116659572913)
                  ·
                    refine ⟨16805978089506837494679685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22407970786009116659572913 16805978089506837494679685)
                    ·
                      refine ⟨3151120891782532030252441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16805978089506837494679685 3151120891782532030252441)
                      ·
                        rfl

theorem cell23_6136786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6136786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136786 prefixEnd_6136786 := by exact prefixLift 6136786
  have htrace : WordTrace (prefixWord ++ tailWord_6136786) baseStart_6136786 baseEnd_6136786 := by
    simpa [prefixWord, tailWord_6136786, baseEnd_6136786] using wordTrace_append hprefix tailTrace_6136786
  have hstable : (prefixWord ++ tailWord_6136786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136786).length < 2 ^ (prefixWord ++ tailWord_6136786).sum := by decide
  have hdescent : baseEnd_6136786 < baseStart_6136786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136790 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6136790 : Nat := 118140960795 + 6136790 * 2 ^ 59
def prefixEnd_6136790 : Nat := 4983230072969 + 3 ^ 40 * 6136790 * 2
def baseEnd_6136790 : Nat := 3151122945705150014602423

theorem tailTrace_6136790 : CollatzResearch.WordTrace tailWord_6136790 prefixEnd_6136790 3151122945705150014602423 := by
  unfold tailWord_6136790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989194964841586570948489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149218079624976923423450549 13989194964841586570948489)
  ·
    refine ⟨10491896223631189928211367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13989194964841586570948489 10491896223631189928211367)
    ·
      refine ⟨15737844335446784892317051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10491896223631189928211367 15737844335446784892317051)
      ·
        refine ⟨23606766503170177338475577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15737844335446784892317051 23606766503170177338475577)
        ·
          refine ⟨17705074877377633003856683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23606766503170177338475577 17705074877377633003856683)
          ·
            refine ⟨26557612316066449505785025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17705074877377633003856683 26557612316066449505785025)
            ·
              refine ⟨19918209237049837129338769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26557612316066449505785025 19918209237049837129338769)
              ·
                refine ⟨14938656927787377847004077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19918209237049837129338769 14938656927787377847004077)
                ·
                  refine ⟨5601996347920266692626529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14938656927787377847004077 5601996347920266692626529)
                  ·
                    refine ⟨4201497260940200019469897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5601996347920266692626529 4201497260940200019469897)
                    ·
                      refine ⟨3151122945705150014602423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201497260940200019469897 3151122945705150014602423)
                      ·
                        rfl

theorem cell23_6136790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6136790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136790 prefixEnd_6136790 := by exact prefixLift 6136790
  have htrace : WordTrace (prefixWord ++ tailWord_6136790) baseStart_6136790 baseEnd_6136790 := by
    simpa [prefixWord, tailWord_6136790, baseEnd_6136790] using wordTrace_append hprefix tailTrace_6136790
  have hstable : (prefixWord ++ tailWord_6136790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136790).length < 2 ^ (prefixWord ++ tailWord_6136790).sum := by decide
  have hdescent : baseEnd_6136790 < baseStart_6136790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136807 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6136807 : Nat := 118140960795 + 6136807 * 2 ^ 59
def prefixEnd_6136807 : Nat := 4983230072969 + 3 ^ 40 * 6136807 * 2
def baseEnd_6136807 : Nat := 3151131674876276448089845

theorem tailTrace_6136807 : CollatzResearch.WordTrace tailWord_6136807 prefixEnd_6136807 3151131674876276448089845 := by
  unfold tailWord_6136807
  simp only [CollatzResearch.WordTrace]
  refine ⟨223827739478403797038544675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149218492985602531359029783 223827739478403797038544675)
  ·
    refine ⟨335741609217605695557817013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223827739478403797038544675 335741609217605695557817013)
    ·
      refine ⟨31475775864150533958545345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 335741609217605695557817013 31475775864150533958545345)
      ·
        refine ⟨23606831898112900468909009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31475775864150533958545345 23606831898112900468909009)
        ·
          refine ⟨17705123923584675351681757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23606831898112900468909009 17705123923584675351681757)
          ·
            refine ⟨6639421471344253256880659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17705123923584675351681757 6639421471344253256880659)
            ·
              refine ⟨9959132207016379885320989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639421471344253256880659 9959132207016379885320989)
              ·
                refine ⟨3734674577631142456995371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9959132207016379885320989 3734674577631142456995371)
                ·
                  refine ⟨5602011866446713685493057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734674577631142456995371 5602011866446713685493057)
                  ·
                    refine ⟨4201508899835035264119793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5602011866446713685493057 4201508899835035264119793)
                    ·
                      refine ⟨3151131674876276448089845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201508899835035264119793 3151131674876276448089845)
                      ·
                        rfl

theorem cell23_6136807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6136807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136807 prefixEnd_6136807 := by exact prefixLift 6136807
  have htrace : WordTrace (prefixWord ++ tailWord_6136807) baseStart_6136807 baseEnd_6136807 := by
    simpa [prefixWord, tailWord_6136807, baseEnd_6136807] using wordTrace_append hprefix tailTrace_6136807
  have hstable : (prefixWord ++ tailWord_6136807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136807).length < 2 ^ (prefixWord ++ tailWord_6136807).sum := by decide
  have hdescent : baseEnd_6136807 < baseStart_6136807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136812 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_6136812 : Nat := 118140960795 + 6136812 * 2 ^ 59
def prefixEnd_6136812 : Nat := 4983230072969 + 3 ^ 40 * 6136812 * 2
def baseEnd_6136812 : Nat := 3151134242279548928527321

theorem tailTrace_6136812 : CollatzResearch.WordTrace tailWord_6136812 prefixEnd_6136812 3151134242279548928527321 := by
  unfold tailWord_6136812
  simp only [CollatzResearch.WordTrace]
  refine ⟨111913960921692841446238345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149218614562257121928317793 111913960921692841446238345)
  ·
    refine ⟨83935470691269631084678759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111913960921692841446238345 83935470691269631084678759)
    ·
      refine ⟨125903206036904446627018139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83935470691269631084678759 125903206036904446627018139)
      ·
        refine ⟨188854809055356669940527209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125903206036904446627018139 188854809055356669940527209)
        ·
          refine ⟨141641106791517502455395407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188854809055356669940527209 141641106791517502455395407)
          ·
            refine ⟨212461660187276253683093111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141641106791517502455395407 212461660187276253683093111)
            ·
              refine ⟨318692490280914380524639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212461660187276253683093111 318692490280914380524639667)
              ·
                refine ⟨478038735421371570786959501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318692490280914380524639667 478038735421371570786959501)
                ·
                  refine ⟨179264525783014339045109813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478038735421371570786959501 179264525783014339045109813)
                  ·
                    refine ⟨16806049292157594285479045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179264525783014339045109813 16806049292157594285479045)
                    ·
                      refine ⟨3151134242279548928527321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16806049292157594285479045 3151134242279548928527321)
                      ·
                        rfl

theorem cell23_6136812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_6136812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136812 prefixEnd_6136812 := by exact prefixLift 6136812
  have htrace : WordTrace (prefixWord ++ tailWord_6136812) baseStart_6136812 baseEnd_6136812 := by
    simpa [prefixWord, tailWord_6136812, baseEnd_6136812] using wordTrace_append hprefix tailTrace_6136812
  have hstable : (prefixWord ++ tailWord_6136812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136812).length < 2 ^ (prefixWord ++ tailWord_6136812).sum := by decide
  have hdescent : baseEnd_6136812 < baseStart_6136812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136834 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6136834 : Nat := 118140960795 + 6136834 * 2 ^ 59
def prefixEnd_6136834 : Nat := 4983230072969 + 3 ^ 40 * 6136834 * 2
def baseEnd_6136834 : Nat := 1050381846284649280817407

theorem tailTrace_6136834 : CollatzResearch.WordTrace tailWord_6136834 prefixEnd_6136834 1050381846284649280817407 := by
  unfold tailWord_6136834
  simp only [CollatzResearch.WordTrace]
  refine ⟨55957181062326495162444389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149219149499537320433185037 55957181062326495162444389)
  ·
    refine ⟨10491971449186217842958323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55957181062326495162444389 10491971449186217842958323)
    ·
      refine ⟨15737957173779326764437485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10491971449186217842958323 15737957173779326764437485)
      ·
        refine ⟨5901733940167247536664057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15737957173779326764437485 5901733940167247536664057)
        ·
          refine ⟨4426300455125435652498043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5901733940167247536664057 4426300455125435652498043)
          ·
            refine ⟨6639450682688153478747065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426300455125435652498043 6639450682688153478747065)
            ·
              refine ⟨4979588012016115109060299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639450682688153478747065 4979588012016115109060299)
              ·
                refine ⟨7469382018024172663590449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979588012016115109060299 7469382018024172663590449)
                ·
                  refine ⟨5602036513518129497692837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7469382018024172663590449 5602036513518129497692837)
                  ·
                    refine ⟨1050381846284649280817407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602036513518129497692837 1050381846284649280817407)
                    ·
                      rfl

theorem cell23_6136834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6136834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136834 prefixEnd_6136834 := by exact prefixLift 6136834
  have htrace : WordTrace (prefixWord ++ tailWord_6136834) baseStart_6136834 baseEnd_6136834 := by
    simpa [prefixWord, tailWord_6136834, baseEnd_6136834] using wordTrace_append hprefix tailTrace_6136834
  have hstable : (prefixWord ++ tailWord_6136834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136834).length < 2 ^ (prefixWord ++ tailWord_6136834).sum := by decide
  have hdescent : baseEnd_6136834 < baseStart_6136834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136840 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_6136840 : Nat := 118140960795 + 6136840 * 2 ^ 59
def prefixEnd_6136840 : Nat := 4983230072969 + 3 ^ 40 * 6136840 * 2
def baseEnd_6136840 : Nat := 3151148619737874818977193

theorem tailTrace_6136840 : CollatzResearch.WordTrace tailWord_6136840 prefixEnd_6136840 3151148619737874818977193 := by
  unfold tailWord_6136840
  simp only [CollatzResearch.WordTrace]
  refine ⟨111914471543642121837247987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149219295391522829116330649 111914471543642121837247987)
  ·
    refine ⟨167871707315463182755871981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111914471543642121837247987 167871707315463182755871981)
    ·
      refine ⟨62951890243298693533451993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167871707315463182755871981 62951890243298693533451993)
      ·
        refine ⟨47213917682474020150088995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62951890243298693533451993 47213917682474020150088995)
        ·
          refine ⟨70820876523711030225133493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47213917682474020150088995 70820876523711030225133493)
          ·
            refine ⟨6639457174097909083606265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70820876523711030225133493 6639457174097909083606265)
            ·
              refine ⟨4979592880573431812704699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6639457174097909083606265 4979592880573431812704699)
              ·
                refine ⟨7469389320860147719057049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979592880573431812704699 7469389320860147719057049)
                ·
                  refine ⟨5602041990645110789292787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7469389320860147719057049 5602041990645110789292787)
                  ·
                    refine ⟨8403062985967666183939181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602041990645110789292787 8403062985967666183939181)
                    ·
                      refine ⟨3151148619737874818977193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8403062985967666183939181 3151148619737874818977193)
                      ·
                        rfl

theorem cell23_6136840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_6136840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136840 prefixEnd_6136840 := by exact prefixLift 6136840
  have htrace : WordTrace (prefixWord ++ tailWord_6136840) baseStart_6136840 baseEnd_6136840 := by
    simpa [prefixWord, tailWord_6136840, baseEnd_6136840] using wordTrace_append hprefix tailTrace_6136840
  have hstable : (prefixWord ++ tailWord_6136840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136840).length < 2 ^ (prefixWord ++ tailWord_6136840).sum := by decide
  have hdescent : baseEnd_6136840 < baseStart_6136840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136916 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_6136916 : Nat := 118140960795 + 6136916 * 2 ^ 59
def prefixEnd_6136916 : Nat := 4983230072969 + 3 ^ 40 * 6136916 * 2
def baseEnd_6136916 : Nat := 1050395881422538840542281

theorem tailTrace_6136916 : CollatzResearch.WordTrace tailWord_6136916 prefixEnd_6136916 1050395881422538840542281 := by
  unfold tailWord_6136916
  simp only [CollatzResearch.WordTrace]
  refine ⟨111915857517504454327131301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149221143356672605769508401 111915857517504454327131301)
  ·
    refine ⟨20984223284532085186337119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111915857517504454327131301 20984223284532085186337119)
    ·
      refine ⟨31476334926798127779505679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984223284532085186337119 31476334926798127779505679)
      ·
        refine ⟨47214502390197191669258519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476334926798127779505679 47214502390197191669258519)
        ·
          refine ⟨70821753585295787503887779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47214502390197191669258519 70821753585295787503887779)
          ·
            refine ⟨106232630377943681255831669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70821753585295787503887779 106232630377943681255831669)
            ·
              refine ⟨9959309097932220117734219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106232630377943681255831669 9959309097932220117734219)
              ·
                refine ⟨14938963646898330176601329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959309097932220117734219 14938963646898330176601329)
                ·
                  refine ⟨11204222735173747632450997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14938963646898330176601329 11204222735173747632450997)
                  ·
                    refine ⟨1050395881422538840542281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11204222735173747632450997 1050395881422538840542281)
                    ·
                      rfl

theorem cell23_6136916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_6136916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136916 prefixEnd_6136916 := by exact prefixLift 6136916
  have htrace : WordTrace (prefixWord ++ tailWord_6136916) baseStart_6136916 baseEnd_6136916 := by
    simpa [prefixWord, tailWord_6136916, baseEnd_6136916] using wordTrace_append hprefix tailTrace_6136916
  have hstable : (prefixWord ++ tailWord_6136916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136916).length < 2 ^ (prefixWord ++ tailWord_6136916).sum := by decide
  have hdescent : baseEnd_6136916 < baseStart_6136916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6136990 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_6136990 : Nat := 118140960795 + 6136990 * 2 ^ 59
def prefixEnd_6136990 : Nat := 4983230072969 + 3 ^ 40 * 6136990 * 2
def baseEnd_6136990 : Nat := 3151225641836049232101503

theorem tailTrace_6136990 : CollatzResearch.WordTrace tailWord_6136990 prefixEnd_6136990 3151225641836049232101503 := by
  unfold tailWord_6136990
  simp only [CollatzResearch.WordTrace]
  refine ⟨27979301754592602411557053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149222942691160546194970949 27979301754592602411557053)
  ·
    refine ⟨10492238157972225904333895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27979301754592602411557053 10492238157972225904333895)
    ·
      refine ⟨15738357236958338856500843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10492238157972225904333895 15738357236958338856500843)
      ·
        refine ⟨23607535855437508284751265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15738357236958338856500843 23607535855437508284751265)
        ·
          refine ⟨17705651891578131213563449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23607535855437508284751265 17705651891578131213563449)
          ·
            refine ⟨13279238918683598410172587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17705651891578131213563449 13279238918683598410172587)
            ·
              refine ⟨19918858378025397615258881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13279238918683598410172587 19918858378025397615258881)
              ·
                refine ⟨14939143783519048211444161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19918858378025397615258881 14939143783519048211444161)
                ·
                  refine ⟨11204357837639286158583121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14939143783519048211444161 11204357837639286158583121)
                  ·
                    refine ⟨8403268378229464618937341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11204357837639286158583121 8403268378229464618937341)
                    ·
                      refine ⟨3151225641836049232101503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8403268378229464618937341 3151225641836049232101503)
                      ·
                        rfl

theorem cell23_6136990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_6136990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6136990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6136990 prefixEnd_6136990 := by exact prefixLift 6136990
  have htrace : WordTrace (prefixWord ++ tailWord_6136990) baseStart_6136990 baseEnd_6136990 := by
    simpa [prefixWord, tailWord_6136990, baseEnd_6136990] using wordTrace_append hprefix tailTrace_6136990
  have hstable : (prefixWord ++ tailWord_6136990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6136990).length < 2 ^ (prefixWord ++ tailWord_6136990).sum := by decide
  have hdescent : baseEnd_6136990 < baseStart_6136990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6136990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137039 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_6137039 : Nat := 118140960795 + 6137039 * 2 ^ 59
def prefixEnd_6137039 : Nat := 4983230072969 + 3 ^ 40 * 6137039 * 2
def baseEnd_6137039 : Nat := 3151250802388119540388777

theorem tailTrace_6137039 : CollatzResearch.WordTrace tailWord_6137039 prefixEnd_6137039 3151250802388119540388777 := by
  unfold tailWord_6137039
  simp only [CollatzResearch.WordTrace]
  refine ⟨223836201213563300660990171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149224134142375533773993447 223836201213563300660990171)
  ·
    refine ⟨335754301820344950991485257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223836201213563300660990171 335754301820344950991485257)
    ·
      refine ⟨251815726365258713243613943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335754301820344950991485257 251815726365258713243613943)
      ·
        refine ⟨377723589547888069865420915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251815726365258713243613943 377723589547888069865420915)
        ·
          refine ⟨566585384321832104798131373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377723589547888069865420915 566585384321832104798131373)
          ·
            refine ⟨212469519120687039299299265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566585384321832104798131373 212469519120687039299299265)
            ·
              refine ⟨159352139340515279474474449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212469519120687039299299265 159352139340515279474474449)
              ·
                refine ⟨119514104505386459605855837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159352139340515279474474449 119514104505386459605855837)
                ·
                  refine ⟨44817789189519922352195939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119514104505386459605855837 44817789189519922352195939)
                  ·
                    refine ⟨67226683784279883528293909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44817789189519922352195939 67226683784279883528293909)
                    ·
                      refine ⟨3151250802388119540388777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67226683784279883528293909 3151250802388119540388777)
                      ·
                        rfl

theorem cell23_6137039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_6137039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137039 prefixEnd_6137039 := by exact prefixLift 6137039
  have htrace : WordTrace (prefixWord ++ tailWord_6137039) baseStart_6137039 baseEnd_6137039 := by
    simpa [prefixWord, tailWord_6137039, baseEnd_6137039] using wordTrace_append hprefix tailTrace_6137039
  have hstable : (prefixWord ++ tailWord_6137039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137039).length < 2 ^ (prefixWord ++ tailWord_6137039).sum := by decide
  have hdescent : baseEnd_6137039 < baseStart_6137039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 5, 2, 2]
def baseStart_6137043 : Nat := 118140960795 + 6137043 * 2 ^ 59
def prefixEnd_6137043 : Nat := 4983230072969 + 3 ^ 40 * 6137043 * 2
def baseEnd_6137043 : Nat := 3151252856310737524738759

theorem tailTrace_6137043 : CollatzResearch.WordTrace tailWord_6137043 prefixEnd_6137043 3151252856310737524738759 := by
  unfold tailWord_6137043
  simp only [CollatzResearch.WordTrace]
  refine ⟨223836347105548809344135783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149224231403699206229423855 223836347105548809344135783)
  ·
    refine ⟨335754520658323214016203675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223836347105548809344135783 335754520658323214016203675)
    ·
      refine ⟨503631780987484821024305513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335754520658323214016203675 503631780987484821024305513)
      ·
        refine ⟨377723835740613615768229135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503631780987484821024305513 377723835740613615768229135)
        ·
          refine ⟨566585753610920423652343703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377723835740613615768229135 566585753610920423652343703)
          ·
            refine ⟨849878630416380635478515555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566585753610920423652343703 849878630416380635478515555)
            ·
              refine ⟨1274817945624570953217773333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849878630416380635478515555 1274817945624570953217773333)
              ·
                refine ⟨59757091201151763432083125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1274817945624570953217773333 59757091201151763432083125)
                ·
                  refine ⟨5602227300107977821757793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59757091201151763432083125 5602227300107977821757793)
                  ·
                    refine ⟨4201670475080983366318345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5602227300107977821757793 4201670475080983366318345)
                    ·
                      refine ⟨3151252856310737524738759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201670475080983366318345 3151252856310737524738759)
                      ·
                        rfl

theorem cell23_6137043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2, 2].length) (baseStart_6137043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137043 prefixEnd_6137043 := by exact prefixLift 6137043
  have htrace : WordTrace (prefixWord ++ tailWord_6137043) baseStart_6137043 baseEnd_6137043 := by
    simpa [prefixWord, tailWord_6137043, baseEnd_6137043] using wordTrace_append hprefix tailTrace_6137043
  have hstable : (prefixWord ++ tailWord_6137043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137043).length < 2 ^ (prefixWord ++ tailWord_6137043).sum := by decide
  have hdescent : baseEnd_6137043 < baseStart_6137043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137066 : List Nat := [3, 1, 3, 1, 1, 3, 3, 8]
def baseStart_6137066 : Nat := 118140960795 + 6137066 * 2 ^ 59
def prefixEnd_6137066 : Nat := 4983230072969 + 3 ^ 40 * 6137066 * 2
def baseEnd_6137066 : Nat := 116713506161695960546339

theorem tailTrace_6137066 : CollatzResearch.WordTrace tailWord_6137066 prefixEnd_6137066 116713506161695960546339 := by
  unfold tailWord_6137066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55959296496116371068055763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149224790656310322848148701 55959296496116371068055763)
  ·
    refine ⟨83938944744174556602083645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55959296496116371068055763 83938944744174556602083645)
    ·
      refine ⟨31477104279065458725781367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83938944744174556602083645 31477104279065458725781367)
      ·
        refine ⟨47215656418598188088672051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31477104279065458725781367 47215656418598188088672051)
        ·
          refine ⟨70823484627897282133008077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47215656418598188088672051 70823484627897282133008077)
          ·
            refine ⟨26558806735461480799878029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70823484627897282133008077 26558806735461480799878029)
            ·
              refine ⟨9959552525798055299954261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26558806735461480799878029 9959552525798055299954261)
              ·
                refine ⟨116713506161695960546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9959552525798055299954261 116713506161695960546339)
                ·
                  rfl

theorem cell23_6137066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_6137066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137066 prefixEnd_6137066 := by exact prefixLift 6137066
  have htrace : WordTrace (prefixWord ++ tailWord_6137066) baseStart_6137066 baseEnd_6137066 := by
    simpa [prefixWord, tailWord_6137066, baseEnd_6137066] using wordTrace_append hprefix tailTrace_6137066
  have hstable : (prefixWord ++ tailWord_6137066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137066).length < 2 ^ (prefixWord ++ tailWord_6137066).sum := by decide
  have hdescent : baseEnd_6137066 < baseStart_6137066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137093 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_6137093 : Nat := 118140960795 + 6137093 * 2 ^ 59
def prefixEnd_6137093 : Nat := 4983230072969 + 3 ^ 40 * 6137093 * 2
def baseEnd_6137093 : Nat := 3151278530343462329113529

theorem tailTrace_6137093 : CollatzResearch.WordTrace tailWord_6137093 prefixEnd_6137093 3151278530343462329113529 := by
  unfold tailWord_6137093
  simp only [CollatzResearch.WordTrace]
  refine ⟨223838170755367667883455933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149225447170245111922303955 223838170755367667883455933)
  ·
    refine ⟨83939314033262875456295975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223838170755367667883455933 83939314033262875456295975)
    ·
      refine ⟨125908971049894313184443963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83939314033262875456295975 125908971049894313184443963)
      ·
        refine ⟨188863456574841469776665945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125908971049894313184443963 188863456574841469776665945)
        ·
          refine ⟨141647592431131102332499459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188863456574841469776665945 141647592431131102332499459)
          ·
            refine ⟨212471388646696653498749189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141647592431131102332499459 212471388646696653498749189)
            ·
              refine ⟨39838385371255622531015473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212471388646696653498749189 39838385371255622531015473)
              ·
                refine ⟨29878789028441716898261605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39838385371255622531015473 29878789028441716898261605)
                ·
                  refine ⟨5602272942832821918424051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29878789028441716898261605 5602272942832821918424051)
                  ·
                    refine ⟨8403409414249232877636077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602272942832821918424051 8403409414249232877636077)
                    ·
                      refine ⟨3151278530343462329113529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8403409414249232877636077 3151278530343462329113529)
                      ·
                        rfl

theorem cell23_6137093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_6137093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137093 prefixEnd_6137093 := by exact prefixLift 6137093
  have htrace : WordTrace (prefixWord ++ tailWord_6137093) baseStart_6137093 baseEnd_6137093 := by
    simpa [prefixWord, tailWord_6137093, baseEnd_6137093] using wordTrace_append hprefix tailTrace_6137093
  have hstable : (prefixWord ++ tailWord_6137093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137093).length < 2 ^ (prefixWord ++ tailWord_6137093).sum := by decide
  have hdescent : baseEnd_6137093 < baseStart_6137093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137116 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6137116 : Nat := 118140960795 + 6137116 * 2 ^ 59
def prefixEnd_6137116 : Nat := 4983230072969 + 3 ^ 40 * 6137116 * 2
def baseEnd_6137116 : Nat := 3151290340398515739125923

theorem tailTrace_6137116 : CollatzResearch.WordTrace tailWord_6137116 prefixEnd_6137116 3151290340398515739125923 := by
  unfold tailWord_6137116
  simp only [CollatzResearch.WordTrace]
  refine ⟨111919504817142171405771601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149226006422856228541028801 111919504817142171405771601)
  ·
    refine ⟨83939628612856628554328701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111919504817142171405771601 83939628612856628554328701)
    ·
      refine ⟨31477360729821235707873263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83939628612856628554328701 31477360729821235707873263)
      ·
        refine ⟨47216041094731853561809895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31477360729821235707873263 47216041094731853561809895)
        ·
          refine ⟨70824061642097780342714843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47216041094731853561809895 70824061642097780342714843)
          ·
            refine ⟨106236092463146670514072265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70824061642097780342714843 106236092463146670514072265)
            ·
              refine ⟨79677069347360002885554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106236092463146670514072265 79677069347360002885554199)
              ·
                refine ⟨119515604021040004328331299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79677069347360002885554199 119515604021040004328331299)
                ·
                  refine ⟨179273406031560006492496949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119515604021040004328331299 179273406031560006492496949)
                  ·
                    refine ⟨16806881815458750608671589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179273406031560006492496949 16806881815458750608671589)
                    ·
                      refine ⟨3151290340398515739125923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16806881815458750608671589 3151290340398515739125923)
                      ·
                        rfl

theorem cell23_6137116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6137116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137116 prefixEnd_6137116 := by exact prefixLift 6137116
  have htrace : WordTrace (prefixWord ++ tailWord_6137116) baseStart_6137116 baseEnd_6137116 := by
    simpa [prefixWord, tailWord_6137116, baseEnd_6137116] using wordTrace_append hprefix tailTrace_6137116
  have hstable : (prefixWord ++ tailWord_6137116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137116).length < 2 ^ (prefixWord ++ tailWord_6137116).sum := by decide
  have hdescent : baseEnd_6137116 < baseStart_6137116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137136 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_6137136 : Nat := 118140960795 + 6137136 * 2 ^ 59
def prefixEnd_6137136 : Nat := 4983230072969 + 3 ^ 40 * 6137136 * 2
def baseEnd_6137136 : Nat := 3151300610011605660875831

theorem tailTrace_6137136 : CollatzResearch.WordTrace tailWord_6137136 prefixEnd_6137136 3151300610011605660875831 := by
  unfold tailWord_6137136
  simp only [CollatzResearch.WordTrace]
  refine ⟨111919869547105943113635631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149226492729474590818180841 111919869547105943113635631)
  ·
    refine ⟨167879804320658914670453447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111919869547105943113635631 167879804320658914670453447)
    ·
      refine ⟨251819706480988372005680171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167879804320658914670453447 251819706480988372005680171)
      ·
        refine ⟨377729559721482558008520257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251819706480988372005680171 377729559721482558008520257)
        ·
          refine ⟨283297169791111918506390193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377729559721482558008520257 283297169791111918506390193)
          ·
            refine ⟨212472877343333938879792645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283297169791111918506390193 212472877343333938879792645)
            ·
              refine ⟨39838664501875113539961121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212472877343333938879792645 39838664501875113539961121)
              ·
                refine ⟨29878998376406335154970841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39838664501875113539961121 29878998376406335154970841)
                ·
                  refine ⟨22409248782304751366228131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29878998376406335154970841 22409248782304751366228131)
                  ·
                    refine ⟨33613873173457127049342197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22409248782304751366228131 33613873173457127049342197)
                    ·
                      refine ⟨3151300610011605660875831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33613873173457127049342197 3151300610011605660875831)
                      ·
                        rfl

theorem cell23_6137136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_6137136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137136 prefixEnd_6137136 := by exact prefixLift 6137136
  have htrace : WordTrace (prefixWord ++ tailWord_6137136) baseStart_6137136 baseEnd_6137136 := by
    simpa [prefixWord, tailWord_6137136, baseEnd_6137136] using wordTrace_append hprefix tailTrace_6137136
  have hstable : (prefixWord ++ tailWord_6137136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137136).length < 2 ^ (prefixWord ++ tailWord_6137136).sum := by decide
  have hdescent : baseEnd_6137136 < baseStart_6137136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137137 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_6137137 : Nat := 118140960795 + 6137137 * 2 ^ 59
def prefixEnd_6137137 : Nat := 4983230072969 + 3 ^ 40 * 6137137 * 2
def baseEnd_6137137 : Nat := 3151301123492260156963327

theorem tailTrace_6137137 : CollatzResearch.WordTrace tailWord_6137137 prefixEnd_6137137 3151301123492260156963327 := by
  unfold tailWord_6137137
  simp only [CollatzResearch.WordTrace]
  refine ⟨223839775567208263398057665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149226517044805508932038443 223839775567208263398057665)
  ·
    refine ⟨167879831675406197548543249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223839775567208263398057665 167879831675406197548543249)
    ·
      refine ⟨125909873756554648161407437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167879831675406197548543249 125909873756554648161407437)
      ·
        refine ⟨47216202658707993060527789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125909873756554648161407437 47216202658707993060527789)
        ·
          refine ⟨17706075997015497397697921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47216202658707993060527789 17706075997015497397697921)
          ·
            refine ⟨13279556997761623048273441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17706075997015497397697921 13279556997761623048273441)
            ·
              refine ⟨9959667748321217286205081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13279556997761623048273441 9959667748321217286205081)
              ·
                refine ⟨7469750811240912964653811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9959667748321217286205081 7469750811240912964653811)
                ·
                  refine ⟨11204626216861369446980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7469750811240912964653811 11204626216861369446980717)
                  ·
                    refine ⟨4201734831323013542617769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11204626216861369446980717 4201734831323013542617769)
                    ·
                      refine ⟨3151301123492260156963327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201734831323013542617769 3151301123492260156963327)
                      ·
                        rfl

theorem cell23_6137137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_6137137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137137 prefixEnd_6137137 := by exact prefixLift 6137137
  have htrace : WordTrace (prefixWord ++ tailWord_6137137) baseStart_6137137 baseEnd_6137137 := by
    simpa [prefixWord, tailWord_6137137, baseEnd_6137137] using wordTrace_append hprefix tailTrace_6137137
  have hstable : (prefixWord ++ tailWord_6137137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137137).length < 2 ^ (prefixWord ++ tailWord_6137137).sum := by decide
  have hdescent : baseEnd_6137137 < baseStart_6137137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137150 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6137150 : Nat := 118140960795 + 6137150 * 2 ^ 59
def prefixEnd_6137150 : Nat := 4983230072969 + 3 ^ 40 * 6137150 * 2
def baseEnd_6137150 : Nat := 3151307798740768606100767

theorem tailTrace_6137150 : CollatzResearch.WordTrace tailWord_6137150 prefixEnd_6137150 3151307798740768606100767 := by
  unfold tailWord_6137150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980031214520145827285113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149226833144107444412187269 27980031214520145827285113)
  ·
    refine ⟨20985023410890109370463835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27980031214520145827285113 20985023410890109370463835)
    ·
      refine ⟨31477535116335164055695753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20985023410890109370463835 31477535116335164055695753)
      ·
        refine ⟨23608151337251373041771815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31477535116335164055695753 23608151337251373041771815)
        ·
          refine ⟨35412227005877059562657723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23608151337251373041771815 35412227005877059562657723)
          ·
            refine ⟨53118340508815589343986585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35412227005877059562657723 53118340508815589343986585)
            ·
              refine ⟨39838755381611692007989939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53118340508815589343986585 39838755381611692007989939)
              ·
                refine ⟨59758133072417538011984909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39838755381611692007989939 59758133072417538011984909)
                ·
                  refine ⟨22409299902156576754494341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59758133072417538011984909 22409299902156576754494341)
                  ·
                    refine ⟨4201743731654358141467689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22409299902156576754494341 4201743731654358141467689)
                    ·
                      refine ⟨3151307798740768606100767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201743731654358141467689 3151307798740768606100767)
                      ·
                        rfl

theorem cell23_6137150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6137150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137150 prefixEnd_6137150 := by exact prefixLift 6137150
  have htrace : WordTrace (prefixWord ++ tailWord_6137150) baseStart_6137150 baseEnd_6137150 := by
    simpa [prefixWord, tailWord_6137150, baseEnd_6137150] using wordTrace_append hprefix tailTrace_6137150
  have hstable : (prefixWord ++ tailWord_6137150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137150).length < 2 ^ (prefixWord ++ tailWord_6137150).sum := by decide
  have hdescent : baseEnd_6137150 < baseStart_6137150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137153 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6137153 : Nat := 118140960795 + 6137153 * 2 ^ 59
def prefixEnd_6137153 : Nat := 4983230072969 + 3 ^ 40 * 6137153 * 2
def baseEnd_6137153 : Nat := 3151309339182732094363253

theorem tailTrace_6137153 : CollatzResearch.WordTrace tailWord_6137153 prefixEnd_6137153 3151309339182732094363253 := by
  unfold tailWord_6137153
  simp only [CollatzResearch.WordTrace]
  refine ⟨223840359135150298130640113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149226906090100198753760075 223840359135150298130640113)
  ·
    refine ⟨167880269351362723597980085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223840359135150298130640113 167880269351362723597980085)
    ·
      refine ⟨15738775251690255337310633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167880269351362723597980085 15738775251690255337310633)
      ·
        refine ⟨11804081438767691502982975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15738775251690255337310633 11804081438767691502982975)
        ·
          refine ⟨17706122158151537254474463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804081438767691502982975 17706122158151537254474463)
          ·
            refine ⟨26559183237227305881711695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706122158151537254474463 26559183237227305881711695)
            ·
              refine ⟨39838774855840958822567543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26559183237227305881711695 39838774855840958822567543)
              ·
                refine ⟨59758162283761438233851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39838774855840958822567543 59758162283761438233851315)
                ·
                  refine ⟨89637243425642157350776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59758162283761438233851315 89637243425642157350776973)
                  ·
                    refine ⟨33613966284615809006541365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89637243425642157350776973 33613966284615809006541365)
                    ·
                      refine ⟨3151309339182732094363253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33613966284615809006541365 3151309339182732094363253)
                      ·
                        rfl

theorem cell23_6137153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6137153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137153 prefixEnd_6137153 := by exact prefixLift 6137153
  have htrace : WordTrace (prefixWord ++ tailWord_6137153) baseStart_6137153 baseEnd_6137153 := by
    simpa [prefixWord, tailWord_6137153, baseEnd_6137153] using wordTrace_append hprefix tailTrace_6137153
  have hstable : (prefixWord ++ tailWord_6137153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137153).length < 2 ^ (prefixWord ++ tailWord_6137153).sum := by decide
  have hdescent : baseEnd_6137153 < baseStart_6137153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137166 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6137166 : Nat := 118140960795 + 6137166 * 2 ^ 59
def prefixEnd_6137166 : Nat := 4983230072969 + 3 ^ 40 * 6137166 * 2
def baseEnd_6137166 : Nat := 3151316014431240543500693

theorem tailTrace_6137166 : CollatzResearch.WordTrace tailWord_6137166 prefixEnd_6137166 3151316014431240543500693 := by
  unfold tailWord_6137166
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980104160512900168857919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149227222189402134233908901 27980104160512900168857919)
  ·
    refine ⟨41970156240769350253286879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27980104160512900168857919 41970156240769350253286879)
    ·
      refine ⟨62955234361154025379930319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41970156240769350253286879 62955234361154025379930319)
      ·
        refine ⟨94432851541731038069895479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62955234361154025379930319 94432851541731038069895479)
        ·
          refine ⟨141649277312596557104843219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94432851541731038069895479 141649277312596557104843219)
          ·
            refine ⟨212473915968894835657264829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141649277312596557104843219 212473915968894835657264829)
            ·
              refine ⟨79677718488335563371474311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212473915968894835657264829 79677718488335563371474311)
              ·
                refine ⟨119516577732503345057211467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79677718488335563371474311 119516577732503345057211467)
                ·
                  refine ⟨179274866598755017585817201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119516577732503345057211467 179274866598755017585817201)
                  ·
                    refine ⟨134456149949066263189362901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179274866598755017585817201 134456149949066263189362901)
                    ·
                      refine ⟨3151316014431240543500693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134456149949066263189362901 3151316014431240543500693)
                      ·
                        rfl

theorem cell23_6137166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6137166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137166 prefixEnd_6137166 := by exact prefixLift 6137166
  have htrace : WordTrace (prefixWord ++ tailWord_6137166) baseStart_6137166 baseEnd_6137166 := by
    simpa [prefixWord, tailWord_6137166, baseEnd_6137166] using wordTrace_append hprefix tailTrace_6137166
  have hstable : (prefixWord ++ tailWord_6137166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137166).length < 2 ^ (prefixWord ++ tailWord_6137166).sum := by decide
  have hdescent : baseEnd_6137166 < baseStart_6137166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137173 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 7]
def baseStart_6137173 : Nat := 118140960795 + 6137173 * 2 ^ 59
def prefixEnd_6137173 : Nat := 4983230072969 + 3 ^ 40 * 6137173 * 2
def baseEnd_6137173 : Nat := 350146623199535779568129

theorem tailTrace_6137173 : CollatzResearch.WordTrace tailWord_6137173 prefixEnd_6137173 350146623199535779568129 := by
  unfold tailWord_6137173
  simp only [CollatzResearch.WordTrace]
  refine ⟨223841088595077841546368173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149227392396718561030912115 223841088595077841546368173)
  ·
    refine ⟨83940408223154190579888065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223841088595077841546368173 83940408223154190579888065)
    ·
      refine ⟨62955306167365642934916049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83940408223154190579888065 62955306167365642934916049)
      ·
        refine ⟨47216479625524232201187037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62955306167365642934916049 47216479625524232201187037)
        ·
          refine ⟨17706179859571587075445139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47216479625524232201187037 17706179859571587075445139)
          ·
            refine ⟨26559269789357380613167709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706179859571587075445139 26559269789357380613167709)
            ·
              refine ⟨9959726171009017729937891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26559269789357380613167709 9959726171009017729937891)
              ·
                refine ⟨14939589256513526594906837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959726171009017729937891 14939589256513526594906837)
                ·
                  refine ⟨350146623199535779568129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14939589256513526594906837 350146623199535779568129)
                  ·
                    rfl

theorem cell23_6137173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_6137173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137173 prefixEnd_6137173 := by exact prefixLift 6137173
  have htrace : WordTrace (prefixWord ++ tailWord_6137173) baseStart_6137173 baseEnd_6137173 := by
    simpa [prefixWord, tailWord_6137173, baseEnd_6137173] using wordTrace_append hprefix tailTrace_6137173
  have hstable : (prefixWord ++ tailWord_6137173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137173).length < 2 ^ (prefixWord ++ tailWord_6137173).sum := by decide
  have hdescent : baseEnd_6137173 < baseStart_6137173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137184 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2]
def baseStart_6137184 : Nat := 118140960795 + 6137184 * 2 ^ 59
def prefixEnd_6137184 : Nat := 4983230072969 + 3 ^ 40 * 6137184 * 2
def baseEnd_6137184 : Nat := 3151325257083021473075611

theorem tailTrace_6137184 : CollatzResearch.WordTrace tailWord_6137184 prefixEnd_6137184 3151325257083021473075611 := by
  unfold tailWord_6137184
  simp only [CollatzResearch.WordTrace]
  refine ⟨111920744899018995212509303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149227659865358660283345737 111920744899018995212509303)
  ·
    refine ⟨167881117348528492818763955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111920744899018995212509303 167881117348528492818763955)
    ·
      refine ⟨251821676022792739228145933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167881117348528492818763955 251821676022792739228145933)
      ·
        refine ⟨94433128508547277210554725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251821676022792739228145933 94433128508547277210554725)
        ·
          refine ⟨17706211595352614476979011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94433128508547277210554725 17706211595352614476979011)
          ·
            refine ⟨26559317393028921715468517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706211595352614476979011 26559317393028921715468517)
            ·
              refine ⟨4979872011192922821650347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26559317393028921715468517 4979872011192922821650347)
              ·
                refine ⟨7469808016789384232475521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979872011192922821650347 7469808016789384232475521)
                ·
                  refine ⟨5602356012592038174356641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7469808016789384232475521 5602356012592038174356641)
                  ·
                    refine ⟨4201767009444028630767481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5602356012592038174356641 4201767009444028630767481)
                    ·
                      refine ⟨3151325257083021473075611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201767009444028630767481 3151325257083021473075611)
                      ·
                        rfl

theorem cell23_6137184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_6137184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137184 prefixEnd_6137184 := by exact prefixLift 6137184
  have htrace : WordTrace (prefixWord ++ tailWord_6137184) baseStart_6137184 baseEnd_6137184 := by
    simpa [prefixWord, tailWord_6137184, baseEnd_6137184] using wordTrace_append hprefix tailTrace_6137184
  have hstable : (prefixWord ++ tailWord_6137184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137184).length < 2 ^ (prefixWord ++ tailWord_6137184).sum := by decide
  have hdescent : baseEnd_6137184 < baseStart_6137184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137193 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 5, 2]
def baseStart_6137193 : Nat := 118140960795 + 6137193 * 2 ^ 59
def prefixEnd_6137193 : Nat := 4983230072969 + 3 ^ 40 * 6137193 * 2
def baseEnd_6137193 : Nat := 3151329878408911937863069

theorem tailTrace_6137193 : CollatzResearch.WordTrace tailWord_6137193 prefixEnd_6137193 3151329878408911937863069 := by
  unfold tailWord_6137193
  simp only [CollatzResearch.WordTrace]
  refine ⟨223841818055005384962096233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149227878703336923308064155 223841818055005384962096233)
  ·
    refine ⟨167881363541254038721572175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223841818055005384962096233 167881363541254038721572175)
    ·
      refine ⟨251822045311881058082358263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167881363541254038721572175 251822045311881058082358263)
      ·
        refine ⟨377733067967821587123537395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251822045311881058082358263 377733067967821587123537395)
        ·
          refine ⟨566599601951732380685306093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377733067967821587123537395 566599601951732380685306093)
          ·
            refine ⟨212474850731899642756989785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566599601951732380685306093 212474850731899642756989785)
            ·
              refine ⟨159356138048924732067742339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212474850731899642756989785 159356138048924732067742339)
              ·
                refine ⟨239034207073387098101613509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159356138048924732067742339 239034207073387098101613509)
                ·
                  refine ⟨44818913826260080894052533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239034207073387098101613509 44818913826260080894052533)
                  ·
                    refine ⟨4201773171211882583817425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44818913826260080894052533 4201773171211882583817425)
                    ·
                      refine ⟨3151329878408911937863069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201773171211882583817425 3151329878408911937863069)
                      ·
                        rfl

theorem cell23_6137193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5, 2].length) (baseStart_6137193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137193 prefixEnd_6137193 := by exact prefixLift 6137193
  have htrace : WordTrace (prefixWord ++ tailWord_6137193) baseStart_6137193 baseEnd_6137193 := by
    simpa [prefixWord, tailWord_6137193, baseEnd_6137193] using wordTrace_append hprefix tailTrace_6137193
  have hstable : (prefixWord ++ tailWord_6137193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137193).length < 2 ^ (prefixWord ++ tailWord_6137193).sum := by decide
  have hdescent : baseEnd_6137193 < baseStart_6137193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137250 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_6137250 : Nat := 118140960795 + 6137250 * 2 ^ 59
def prefixEnd_6137250 : Nat := 4983230072969 + 3 ^ 40 * 6137250 * 2
def baseEnd_6137250 : Nat := 1050453048935406071616769

theorem tailTrace_6137250 : CollatzResearch.WordTrace tailWord_6137250 prefixEnd_6137250 1050453048935406071616769 := by
  unfold tailWord_6137250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55960974253949720924230301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149229264677199255797947469 55960974253949720924230301)
  ·
    refine ⟨20985365345231145346586363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55960974253949720924230301 20985365345231145346586363)
    ·
      refine ⟨31478048017846718019879545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20985365345231145346586363 31478048017846718019879545)
      ·
        refine ⟨23608536013385038514909659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31478048017846718019879545 23608536013385038514909659)
        ·
          refine ⟨35412804020077557772364489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23608536013385038514909659 35412804020077557772364489)
          ·
            refine ⟨26559603015058168329273367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35412804020077557772364489 26559603015058168329273367)
            ·
              refine ⟨39839404522587252493910051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26559603015058168329273367 39839404522587252493910051)
              ·
                refine ⟨59759106783880878740865077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39839404522587252493910051 59759106783880878740865077)
                ·
                  refine ⟨5602416260988832381956101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59759106783880878740865077 5602416260988832381956101)
                  ·
                    refine ⟨1050453048935406071616769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602416260988832381956101 1050453048935406071616769)
                    ·
                      rfl

theorem cell23_6137250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_6137250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137250 prefixEnd_6137250 := by exact prefixLift 6137250
  have htrace : WordTrace (prefixWord ++ tailWord_6137250) baseStart_6137250 baseEnd_6137250 := by
    simpa [prefixWord, tailWord_6137250, baseEnd_6137250] using wordTrace_append hprefix tailTrace_6137250
  have hstable : (prefixWord ++ tailWord_6137250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137250).length < 2 ^ (prefixWord ++ tailWord_6137250).sum := by decide
  have hdescent : baseEnd_6137250 < baseStart_6137250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137260 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_6137260 : Nat := 118140960795 + 6137260 * 2 ^ 59
def prefixEnd_6137260 : Nat := 4983230072969 + 3 ^ 40 * 6137260 * 2
def baseEnd_6137260 : Nat := 3151364281612763175725261

theorem tailTrace_6137260 : CollatzResearch.WordTrace tailWord_6137260 prefixEnd_6137260 3151364281612763175725261 := by
  unfold tailWord_6137260
  simp only [CollatzResearch.WordTrace]
  refine ⟨111922130872881327702392617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149229507830508436936523489 111922130872881327702392617)
  ·
    refine ⟨83941598154660995776794463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111922130872881327702392617 83941598154660995776794463)
    ·
      refine ⟨125912397231991493665191695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83941598154660995776794463 125912397231991493665191695)
      ·
        refine ⟨188868595847987240497787543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125912397231991493665191695 188868595847987240497787543)
        ·
          refine ⟨283302893771980860746681315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188868595847987240497787543 283302893771980860746681315)
          ·
            refine ⟨424954340657971291120021973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283302893771980860746681315 424954340657971291120021973)
            ·
              refine ⟨9959867359171202135625515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 424954340657971291120021973 9959867359171202135625515)
              ·
                refine ⟨14939801038756803203438273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9959867359171202135625515 14939801038756803203438273)
                ·
                  refine ⟨11204850779067602402578705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14939801038756803203438273 11204850779067602402578705)
                  ·
                    refine ⟨8403638084300701801934029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11204850779067602402578705 8403638084300701801934029)
                    ·
                      refine ⟨3151364281612763175725261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8403638084300701801934029 3151364281612763175725261)
                      ·
                        rfl

theorem cell23_6137260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_6137260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137260 prefixEnd_6137260 := by exact prefixLift 6137260
  have htrace : WordTrace (prefixWord ++ tailWord_6137260) baseStart_6137260 baseEnd_6137260 := by
    simpa [prefixWord, tailWord_6137260, baseEnd_6137260] using wordTrace_append hprefix tailTrace_6137260
  have hstable : (prefixWord ++ tailWord_6137260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137260).length < 2 ^ (prefixWord ++ tailWord_6137260).sum := by decide
  have hdescent : baseEnd_6137260 < baseStart_6137260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137284 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_6137284 : Nat := 118140960795 + 6137284 * 2 ^ 59
def prefixEnd_6137284 : Nat := 4983230072969 + 3 ^ 40 * 6137284 * 2
def baseEnd_6137284 : Nat := 1050458868382823693941717

theorem tailTrace_6137284 : CollatzResearch.WordTrace tailWord_6137284 prefixEnd_6137284 1050458868382823693941717 := by
  unfold tailWord_6137284
  simp only [CollatzResearch.WordTrace]
  refine ⟨111922568548837853751829453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149230091398450471669105937 111922568548837853751829453)
  ·
    refine ⟨41970963205814195156936045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111922568548837853751829453 41970963205814195156936045)
    ·
      refine ⟨15739111202180323183851017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41970963205814195156936045 15739111202180323183851017)
      ·
        refine ⟨11804333401635242387888263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15739111202180323183851017 11804333401635242387888263)
        ·
          refine ⟨17706500102452863581832395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804333401635242387888263 17706500102452863581832395)
          ·
            refine ⟨26559750153679295372748593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706500102452863581832395 26559750153679295372748593)
            ·
              refine ⟨19919812615259471529561445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26559750153679295372748593 19919812615259471529561445)
              ·
                refine ⟨3734964865361150911792771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19919812615259471529561445 3734964865361150911792771)
                ·
                  refine ⟨5602447298041726367689157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734964865361150911792771 5602447298041726367689157)
                  ·
                    refine ⟨1050458868382823693941717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602447298041726367689157 1050458868382823693941717)
                    ·
                      rfl

theorem cell23_6137284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_6137284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137284 prefixEnd_6137284 := by exact prefixLift 6137284
  have htrace : WordTrace (prefixWord ++ tailWord_6137284) baseStart_6137284 baseEnd_6137284 := by
    simpa [prefixWord, tailWord_6137284, baseEnd_6137284] using wordTrace_append hprefix tailTrace_6137284
  have hstable : (prefixWord ++ tailWord_6137284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137284).length < 2 ^ (prefixWord ++ tailWord_6137284).sum := by decide
  have hdescent : baseEnd_6137284 < baseStart_6137284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137317 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6137317 : Nat := 118140960795 + 6137317 * 2 ^ 59
def prefixEnd_6137317 : Nat := 4983230072969 + 3 ^ 40 * 6137317 * 2
def baseEnd_6137317 : Nat := 3151393550010069452712499

theorem tailTrace_6137317 : CollatzResearch.WordTrace tailWord_6137317 prefixEnd_6137317 3151393550010069452712499 := by
  unfold tailWord_6137317
  simp only [CollatzResearch.WordTrace]
  refine ⟨223846340706556154139610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149230893804370769426406803 223846340706556154139610205)
  ·
    refine ⟨83942377764958557802353827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223846340706556154139610205 83942377764958557802353827)
    ·
      refine ⟨125913566647437836703530741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83942377764958557802353827 125913566647437836703530741)
      ·
        refine ⟨11804396873197297190956007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125913566647437836703530741 11804396873197297190956007)
        ·
          refine ⟨17706595309795945786434011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804396873197297190956007 17706595309795945786434011)
          ·
            refine ⟨26559892964693918679651017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706595309795945786434011 26559892964693918679651017)
            ·
              refine ⟨19919919723520439009738263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26559892964693918679651017 19919919723520439009738263)
              ·
                refine ⟨29879879585280658514607395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19919919723520439009738263 29879879585280658514607395)
                ·
                  refine ⟨44819819377920987771911093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29879879585280658514607395 44819819377920987771911093)
                  ·
                    refine ⟨4201858066680092603616665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44819819377920987771911093 4201858066680092603616665)
                    ·
                      refine ⟨3151393550010069452712499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201858066680092603616665 3151393550010069452712499)
                      ·
                        rfl

theorem cell23_6137317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6137317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137317 prefixEnd_6137317 := by exact prefixLift 6137317
  have htrace : WordTrace (prefixWord ++ tailWord_6137317) baseStart_6137317 baseEnd_6137317 := by
    simpa [prefixWord, tailWord_6137317, baseEnd_6137317] using wordTrace_append hprefix tailTrace_6137317
  have hstable : (prefixWord ++ tailWord_6137317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137317).length < 2 ^ (prefixWord ++ tailWord_6137317).sum := by decide
  have hdescent : baseEnd_6137317 < baseStart_6137317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137334 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6137334 : Nat := 118140960795 + 6137334 * 2 ^ 59
def prefixEnd_6137334 : Nat := 4983230072969 + 3 ^ 40 * 6137334 * 2
def baseEnd_6137334 : Nat := 3151402279181195886199921

theorem tailTrace_6137334 : CollatzResearch.WordTrace tailWord_6137334 prefixEnd_6137334 3151402279181195886199921 := by
  unfold tailWord_6137334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990435046718410377686191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149231307164996377361986037 13990435046718410377686191)
  ·
    refine ⟨20985652570077615566529287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13990435046718410377686191 20985652570077615566529287)
    ·
      refine ⟨31478478855116423349793931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20985652570077615566529287 31478478855116423349793931)
      ·
        refine ⟨47217718282674635024690897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31478478855116423349793931 47217718282674635024690897)
        ·
          refine ⟨35413288712005976268518173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47217718282674635024690897 35413288712005976268518173)
          ·
            refine ⟨13279983267002241100694315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35413288712005976268518173 13279983267002241100694315)
            ·
              refine ⟨19919974900503361651041473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13279983267002241100694315 19919974900503361651041473)
              ·
                refine ⟨14939981175377521238281105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19919974900503361651041473 14939981175377521238281105)
                ·
                  refine ⟨11204985881533140928710829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14939981175377521238281105 11204985881533140928710829)
                  ·
                    refine ⟨4201869705574927848266561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11204985881533140928710829 4201869705574927848266561)
                    ·
                      refine ⟨3151402279181195886199921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201869705574927848266561 3151402279181195886199921)
                      ·
                        rfl

theorem cell23_6137334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6137334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137334 prefixEnd_6137334 := by exact prefixLift 6137334
  have htrace : WordTrace (prefixWord ++ tailWord_6137334) baseStart_6137334 baseEnd_6137334 := by
    simpa [prefixWord, tailWord_6137334, baseEnd_6137334] using wordTrace_append hprefix tailTrace_6137334
  have hstable : (prefixWord ++ tailWord_6137334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137334).length < 2 ^ (prefixWord ++ tailWord_6137334).sum := by decide
  have hdescent : baseEnd_6137334 < baseStart_6137334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137340 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_6137340 : Nat := 118140960795 + 6137340 * 2 ^ 59
def prefixEnd_6137340 : Nat := 4983230072969 + 3 ^ 40 * 6137340 * 2
def baseEnd_6137340 : Nat := 1050468453355040954241631

theorem tailTrace_6137340 : CollatzResearch.WordTrace tailWord_6137340 prefixEnd_6137340 1050468453355040954241631 := by
  unfold tailWord_6137340
  simp only [CollatzResearch.WordTrace]
  refine ⟨111923589792736414533848737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149231453056981886045131649 111923589792736414533848737)
  ·
    refine ⟨83942692344552310900386553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111923589792736414533848737 83942692344552310900386553)
    ·
      refine ⟨62957019258414233175289915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83942692344552310900386553 62957019258414233175289915)
      ·
        refine ⟨94435528887621349762934873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62957019258414233175289915 94435528887621349762934873)
        ·
          refine ⟨70826646665716012322201155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94435528887621349762934873 70826646665716012322201155)
          ·
            refine ⟨106239969998574018483301733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70826646665716012322201155 106239969998574018483301733)
            ·
              refine ⟨19919994374732628465619075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106239969998574018483301733 19919994374732628465619075)
              ·
                refine ⟨29879991562098942698428613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19919994374732628465619075 29879991562098942698428613)
                ·
                  refine ⟨5602498417893551755955365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29879991562098942698428613 5602498417893551755955365)
                  ·
                    refine ⟨1050468453355040954241631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602498417893551755955365 1050468453355040954241631)
                    ·
                      rfl

theorem cell23_6137340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_6137340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137340 prefixEnd_6137340 := by exact prefixLift 6137340
  have htrace : WordTrace (prefixWord ++ tailWord_6137340) baseStart_6137340 baseEnd_6137340 := by
    simpa [prefixWord, tailWord_6137340, baseEnd_6137340] using wordTrace_append hprefix tailTrace_6137340
  have hstable : (prefixWord ++ tailWord_6137340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137340).length < 2 ^ (prefixWord ++ tailWord_6137340).sum := by decide
  have hdescent : baseEnd_6137340 < baseStart_6137340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137341 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_6137341 : Nat := 118140960795 + 6137341 * 2 ^ 59
def prefixEnd_6137341 : Nat := 4983230072969 + 3 ^ 40 * 6137341 * 2
def baseEnd_6137341 : Nat := 3151405873545777358812389

theorem tailTrace_6137341 : CollatzResearch.WordTrace tailWord_6137341 prefixEnd_6137341 3151405873545777358812389 := by
  unfold tailWord_6137341
  simp only [CollatzResearch.WordTrace]
  refine ⟨223847216058469206238483877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149231477372312804158989251 223847216058469206238483877)
  ·
    refine ⟨41971353010962976169715727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223847216058469206238483877 41971353010962976169715727)
    ·
      refine ⟨62957029516444464254573591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41971353010962976169715727 62957029516444464254573591)
      ·
        refine ⟨94435544274666696381860387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62957029516444464254573591 94435544274666696381860387)
        ·
          refine ⟨141653316412000044572790581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94435544274666696381860387 141653316412000044572790581)
          ·
            refine ⟨13279998413625004178699117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141653316412000044572790581 13279998413625004178699117)
            ·
              refine ⟨4979999405109376567012169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13279998413625004178699117 4979999405109376567012169)
              ·
                refine ⟨3734999553832032425259127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979999405109376567012169 3734999553832032425259127)
                ·
                  refine ⟨5602499330748048637888691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734999553832032425259127 5602499330748048637888691)
                  ·
                    refine ⟨8403748996122072956833037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602499330748048637888691 8403748996122072956833037)
                    ·
                      refine ⟨3151405873545777358812389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8403748996122072956833037 3151405873545777358812389)
                      ·
                        rfl

theorem cell23_6137341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_6137341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137341 prefixEnd_6137341 := by exact prefixLift 6137341
  have htrace : WordTrace (prefixWord ++ tailWord_6137341) baseStart_6137341 baseEnd_6137341 := by
    simpa [prefixWord, tailWord_6137341, baseEnd_6137341] using wordTrace_append hprefix tailTrace_6137341
  have hstable : (prefixWord ++ tailWord_6137341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137341).length < 2 ^ (prefixWord ++ tailWord_6137341).sum := by decide
  have hdescent : baseEnd_6137341 < baseStart_6137341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137343 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_6137343 : Nat := 118140960795 + 6137343 * 2 ^ 59
def prefixEnd_6137343 : Nat := 4983230072969 + 3 ^ 40 * 6137343 * 2
def baseEnd_6137343 : Nat := 3151406900507086350987379

theorem tailTrace_6137343 : CollatzResearch.WordTrace tailWord_6137343 prefixEnd_6137343 3151406900507086350987379 := by
  unfold tailWord_6137343
  simp only [CollatzResearch.WordTrace]
  refine ⟨223847289004461960580056683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149231526002974640386704455 223847289004461960580056683)
  ·
    refine ⟨335770933506692940870085025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223847289004461960580056683 335770933506692940870085025)
    ·
      refine ⟨251828200130019705652563769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335770933506692940870085025 251828200130019705652563769)
      ·
        refine ⟨188871150097514779239422827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251828200130019705652563769 188871150097514779239422827)
        ·
          refine ⟨283306725146272168859134241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188871150097514779239422827 283306725146272168859134241)
          ·
            refine ⟨212480043859704126644350681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283306725146272168859134241 212480043859704126644350681)
            ·
              refine ⟨159360032894778094983263011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212480043859704126644350681 159360032894778094983263011)
              ·
                refine ⟨239040049342167142474894517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159360032894778094983263011 239040049342167142474894517)
                ·
                  refine ⟨22410004625828169607021361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239040049342167142474894517 22410004625828169607021361)
                  ·
                    refine ⟨16807503469371127205266021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22410004625828169607021361 16807503469371127205266021)
                    ·
                      refine ⟨3151406900507086350987379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16807503469371127205266021 3151406900507086350987379)
                      ·
                        rfl

theorem cell23_6137343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_6137343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137343 prefixEnd_6137343 := by exact prefixLift 6137343
  have htrace : WordTrace (prefixWord ++ tailWord_6137343) baseStart_6137343 baseEnd_6137343 := by
    simpa [prefixWord, tailWord_6137343, baseEnd_6137343] using wordTrace_append hprefix tailTrace_6137343
  have hstable : (prefixWord ++ tailWord_6137343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137343).length < 2 ^ (prefixWord ++ tailWord_6137343).sum := by decide
  have hdescent : baseEnd_6137343 < baseStart_6137343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137347 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 3, 2, 2]
def baseStart_6137347 : Nat := 118140960795 + 6137347 * 2 ^ 59
def prefixEnd_6137347 : Nat := 4983230072969 + 3 ^ 40 * 6137347 * 2
def baseEnd_6137347 : Nat := 3151408954429704335337361

theorem tailTrace_6137347 : CollatzResearch.WordTrace tailWord_6137347 prefixEnd_6137347 3151408954429704335337361 := by
  unfold tailWord_6137347
  simp only [CollatzResearch.WordTrace]
  refine ⟨223847434896447469263202295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149231623264298312842134863 223847434896447469263202295)
  ·
    refine ⟨335771152344671203894803443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223847434896447469263202295 335771152344671203894803443)
    ·
      refine ⟨503656728517006805842205165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335771152344671203894803443 503656728517006805842205165)
      ·
        refine ⟨188871273193877552190826937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503656728517006805842205165 188871273193877552190826937)
        ·
          refine ⟨141653454895408164143120203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188871273193877552190826937 141653454895408164143120203)
          ·
            refine ⟨212480182343112246214680305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141653454895408164143120203 212480182343112246214680305)
            ·
              refine ⟨159360136757334184661010229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212480182343112246214680305 159360136757334184661010229)
              ·
                refine ⟨14940012821000079811969709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159360136757334184661010229 14940012821000079811969709)
                ·
                  refine ⟨5602504807875029929488641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14940012821000079811969709 5602504807875029929488641)
                  ·
                    refine ⟨4201878605906272447116481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5602504807875029929488641 4201878605906272447116481)
                    ·
                      refine ⟨3151408954429704335337361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201878605906272447116481 3151408954429704335337361)
                      ·
                        rfl

theorem cell23_6137347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_6137347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137347 prefixEnd_6137347 := by exact prefixLift 6137347
  have htrace : WordTrace (prefixWord ++ tailWord_6137347) baseStart_6137347 baseEnd_6137347 := by
    simpa [prefixWord, tailWord_6137347, baseEnd_6137347] using wordTrace_append hprefix tailTrace_6137347
  have hstable : (prefixWord ++ tailWord_6137347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137347).length < 2 ^ (prefixWord ++ tailWord_6137347).sum := by decide
  have hdescent : baseEnd_6137347 < baseStart_6137347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137353 : List Nat := [1, 2, 1, 1, 3, 1, 6, 8]
def baseStart_6137353 : Nat := 118140960795 + 6137353 * 2 ^ 59
def prefixEnd_6137353 : Nat := 4983230072969 + 3 ^ 40 * 6137353 * 2
def baseEnd_6137353 : Nat := 116718964270875233772679

theorem tailTrace_6137353 : CollatzResearch.WordTrace tailWord_6137353 prefixEnd_6137353 116718964270875233772679 := by
  unfold tailWord_6137353
  simp only [CollatzResearch.WordTrace]
  refine ⟨223847653734425732287920713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149231769156283821525280475 223847653734425732287920713)
  ·
    refine ⟨167885740300819299215940535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223847653734425732287920713 167885740300819299215940535)
    ·
      refine ⟨251828610451228948823910803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167885740300819299215940535 251828610451228948823910803)
      ·
        refine ⟨377742915676843423235866205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251828610451228948823910803 377742915676843423235866205)
        ·
          refine ⟨141653593378816283713449827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377742915676843423235866205 141653593378816283713449827)
          ·
            refine ⟨212480390068224425570174741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141653593378816283713449827 212480390068224425570174741)
            ·
              refine ⟨9960018284448019948601941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212480390068224425570174741 9960018284448019948601941)
              ·
                refine ⟨116718964270875233772679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9960018284448019948601941 116718964270875233772679)
                ·
                  rfl

theorem cell23_6137353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 8].length) (baseStart_6137353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137353 prefixEnd_6137353 := by exact prefixLift 6137353
  have htrace : WordTrace (prefixWord ++ tailWord_6137353) baseStart_6137353 baseEnd_6137353 := by
    simpa [prefixWord, tailWord_6137353, baseEnd_6137353] using wordTrace_append hprefix tailTrace_6137353
  have hstable : (prefixWord ++ tailWord_6137353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137353).length < 2 ^ (prefixWord ++ tailWord_6137353).sum := by decide
  have hdescent : baseEnd_6137353 < baseStart_6137353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137364 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6137364 : Nat := 118140960795 + 6137364 * 2 ^ 59
def prefixEnd_6137364 : Nat := 4983230072969 + 3 ^ 40 * 6137364 * 2
def baseEnd_6137364 : Nat := 3151417683600830768824783

theorem tailTrace_6137364 : CollatzResearch.WordTrace tailWord_6137364 prefixEnd_6137364 3151417683600830768824783 := by
  unfold tailWord_6137364
  simp only [CollatzResearch.WordTrace]
  refine ⟨111924027468692940583285573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149232036624923920777714097 111924027468692940583285573)
  ·
    refine ⟨20985755150379926359366045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111924027468692940583285573 20985755150379926359366045)
    ·
      refine ⟨7869658181392472384762267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20985755150379926359366045 7869658181392472384762267)
      ·
        refine ⟨11804487272088708577143401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869658181392472384762267 11804487272088708577143401)
        ·
          refine ⟨8853365454066531432857551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11804487272088708577143401 8853365454066531432857551)
          ·
            refine ⟨13280048181099797149286327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853365454066531432857551 13280048181099797149286327)
            ·
              refine ⟨19920072271649695723929491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280048181099797149286327 19920072271649695723929491)
              ·
                refine ⟨29880108407474543585894237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19920072271649695723929491 29880108407474543585894237)
                ·
                  refine ⟨11205040652802953844710339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29880108407474543585894237 11205040652802953844710339)
                  ·
                    refine ⟨16807560979204430767065509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11205040652802953844710339 16807560979204430767065509)
                    ·
                      refine ⟨3151417683600830768824783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16807560979204430767065509 3151417683600830768824783)
                      ·
                        rfl

theorem cell23_6137364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6137364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137364 prefixEnd_6137364 := by exact prefixLift 6137364
  have htrace : WordTrace (prefixWord ++ tailWord_6137364) baseStart_6137364 baseEnd_6137364 := by
    simpa [prefixWord, tailWord_6137364, baseEnd_6137364] using wordTrace_append hprefix tailTrace_6137364
  have hstable : (prefixWord ++ tailWord_6137364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137364).length < 2 ^ (prefixWord ++ tailWord_6137364).sum := by decide
  have hdescent : baseEnd_6137364 < baseStart_6137364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137384 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6137384 : Nat := 118140960795 + 6137384 * 2 ^ 59
def prefixEnd_6137384 : Nat := 4983230072969 + 3 ^ 40 * 6137384 * 2
def baseEnd_6137384 : Nat := 3151427953213920690574691

theorem tailTrace_6137384 : CollatzResearch.WordTrace tailWord_6137384 prefixEnd_6137384 3151427953213920690574691 := by
  unfold tailWord_6137384
  simp only [CollatzResearch.WordTrace]
  refine ⟨111924392198656712291149603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149232522931542283054866137 111924392198656712291149603)
  ·
    refine ⟨167886588297985068436724405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111924392198656712291149603 167886588297985068436724405)
    ·
      refine ⟨15739367652936100165942913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167886588297985068436724405 15739367652936100165942913)
      ·
        refine ⟨11804525739702075124457185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15739367652936100165942913 11804525739702075124457185)
        ·
          refine ⟨8853394304776556343342889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11804525739702075124457185 8853394304776556343342889)
          ·
            refine ⟨6640045728582417257507167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8853394304776556343342889 6640045728582417257507167)
            ·
              refine ⟨9960068592873625886260751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640045728582417257507167 9960068592873625886260751)
              ·
                refine ⟨14940102889310438829391127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9960068592873625886260751 14940102889310438829391127)
                ·
                  refine ⟨22410154333965658244086691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14940102889310438829391127 22410154333965658244086691)
                  ·
                    refine ⟨33615231500948487366130037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22410154333965658244086691 33615231500948487366130037)
                    ·
                      refine ⟨3151427953213920690574691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33615231500948487366130037 3151427953213920690574691)
                      ·
                        rfl

theorem cell23_6137384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6137384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137384 prefixEnd_6137384 := by exact prefixLift 6137384
  have htrace : WordTrace (prefixWord ++ tailWord_6137384) baseStart_6137384 baseEnd_6137384 := by
    simpa [prefixWord, tailWord_6137384, baseEnd_6137384] using wordTrace_append hprefix tailTrace_6137384
  have hstable : (prefixWord ++ tailWord_6137384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137384).length < 2 ^ (prefixWord ++ tailWord_6137384).sum := by decide
  have hdescent : baseEnd_6137384 < baseStart_6137384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137407 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 3, 3, 2]
def baseStart_6137407 : Nat := 118140960795 + 6137407 * 2 ^ 59
def prefixEnd_6137407 : Nat := 4983230072969 + 3 ^ 40 * 6137407 * 2
def baseEnd_6137407 : Nat := 3151439763268974100587085

theorem tailTrace_6137407 : CollatzResearch.WordTrace tailWord_6137407 prefixEnd_6137407 3151439763268974100587085 := by
  unfold tailWord_6137407
  simp only [CollatzResearch.WordTrace]
  refine ⟨223849623276230099510386475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149233082184153399673590983 223849623276230099510386475)
  ·
    refine ⟨335774434914345149265579713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223849623276230099510386475 335774434914345149265579713)
    ·
      refine ⟨251830826185758861949184785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335774434914345149265579713 251830826185758861949184785)
      ·
        refine ⟨188873119639319146461888589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251830826185758861949184785 188873119639319146461888589)
        ·
          refine ⟨70827419864744679923208221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188873119639319146461888589 70827419864744679923208221)
          ·
            refine ⟨26560282449279254971203083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70827419864744679923208221 26560282449279254971203083)
            ·
              refine ⟨39840423673918882456804625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26560282449279254971203083 39840423673918882456804625)
              ·
                refine ⟨29880317755439161842603469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39840423673918882456804625 29880317755439161842603469)
                ·
                  refine ⟨11205119158289685690976301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29880317755439161842603469 11205119158289685690976301)
                  ·
                    refine ⟨4201919684358632134116113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11205119158289685690976301 4201919684358632134116113)
                    ·
                      refine ⟨3151439763268974100587085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4201919684358632134116113 3151439763268974100587085)
                      ·
                        rfl

theorem cell23_6137407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_6137407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137407 prefixEnd_6137407 := by exact prefixLift 6137407
  have htrace : WordTrace (prefixWord ++ tailWord_6137407) baseStart_6137407 baseEnd_6137407 := by
    simpa [prefixWord, tailWord_6137407, baseEnd_6137407] using wordTrace_append hprefix tailTrace_6137407
  have hstable : (prefixWord ++ tailWord_6137407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137407).length < 2 ^ (prefixWord ++ tailWord_6137407).sum := by decide
  have hdescent : baseEnd_6137407 < baseStart_6137407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137517 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6137517 : Nat := 118140960795 + 6137517 * 2 ^ 59
def prefixEnd_6137517 : Nat := 4983230072969 + 3 ^ 40 * 6137517 * 2
def baseEnd_6137517 : Nat := 3151496246140968670211579

theorem tailTrace_6137517 : CollatzResearch.WordTrace tailWord_6137517 prefixEnd_6137517 3151496246140968670211579 := by
  unfold tailWord_6137517
  simp only [CollatzResearch.WordTrace]
  refine ⟨223853635305831588296890805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149235756870554392197927203 223853635305831588296890805)
  ·
    refine ⟨20986278309921711402833513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223853635305831588296890805 20986278309921711402833513)
    ·
      refine ⟨15739708732441283552125135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20986278309921711402833513 15739708732441283552125135)
      ·
        refine ⟨23609563098661925328187703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15739708732441283552125135 23609563098661925328187703)
        ·
          refine ⟨35414344647992887992281555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23609563098661925328187703 35414344647992887992281555)
          ·
            refine ⟨53121516971989331988422333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35414344647992887992281555 53121516971989331988422333)
            ·
              refine ⟨19920568864495999495658375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53121516971989331988422333 19920568864495999495658375)
              ·
                refine ⟨29880853296743999243487563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19920568864495999495658375 29880853296743999243487563)
                ·
                  refine ⟨44821279945115998865231345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29880853296743999243487563 44821279945115998865231345)
                  ·
                    refine ⟨33615959958836999148923509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44821279945115998865231345 33615959958836999148923509)
                    ·
                      refine ⟨3151496246140968670211579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33615959958836999148923509 3151496246140968670211579)
                      ·
                        rfl

theorem cell23_6137517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6137517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137517 prefixEnd_6137517 := by exact prefixLift 6137517
  have htrace : WordTrace (prefixWord ++ tailWord_6137517) baseStart_6137517 baseEnd_6137517 := by
    simpa [prefixWord, tailWord_6137517, baseEnd_6137517] using wordTrace_append hprefix tailTrace_6137517
  have hstable : (prefixWord ++ tailWord_6137517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137517).length < 2 ^ (prefixWord ++ tailWord_6137517).sum := by decide
  have hdescent : baseEnd_6137517 < baseStart_6137517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137567 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 6]
def baseStart_6137567 : Nat := 118140960795 + 6137567 * 2 ^ 59
def prefixEnd_6137567 : Nat := 4983230072969 + 3 ^ 40 * 6137567 * 2
def baseEnd_6137567 : Nat := 350169102241521497176261

theorem tailTrace_6137567 : CollatzResearch.WordTrace tailWord_6137567 prefixEnd_6137567 350169102241521497176261 := by
  unfold tailWord_6137567
  simp only [CollatzResearch.WordTrace]
  refine ⟨223855458955650446836210955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149236972637100297890807303 223855458955650446836210955)
  ·
    refine ⟨335783188433475670254316433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223855458955650446836210955 335783188433475670254316433)
    ·
      refine ⟨251837391325106752690737325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335783188433475670254316433 251837391325106752690737325)
      ·
        refine ⟨94439021746915032259026497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251837391325106752690737325 94439021746915032259026497)
        ·
          refine ⟨70829266310186274194269873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94439021746915032259026497 70829266310186274194269873)
          ·
            refine ⟨53121949732639705645702405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70829266310186274194269873 53121949732639705645702405)
            ·
              refine ⟨9960365574869944808569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53121949732639705645702405 9960365574869944808569201)
              ·
                refine ⟨7470274181152458606426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9960365574869944808569201 7470274181152458606426901)
                ·
                  refine ⟨350169102241521497176261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7470274181152458606426901 350169102241521497176261)
                  ·
                    rfl

theorem cell23_6137567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 6].length) (baseStart_6137567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137567 prefixEnd_6137567 := by exact prefixLift 6137567
  have htrace : WordTrace (prefixWord ++ tailWord_6137567) baseStart_6137567 baseEnd_6137567 := by
    simpa [prefixWord, tailWord_6137567, baseEnd_6137567] using wordTrace_append hprefix tailTrace_6137567
  have hstable : (prefixWord ++ tailWord_6137567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137567).length < 2 ^ (prefixWord ++ tailWord_6137567).sum := by decide
  have hdescent : baseEnd_6137567 < baseStart_6137567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137588 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6137588 : Nat := 118140960795 + 6137588 * 2 ^ 59
def prefixEnd_6137588 : Nat := 4983230072969 + 3 ^ 40 * 6137588 * 2
def baseEnd_6137588 : Nat := 1050510901089145964141251

theorem tailTrace_6137588 : CollatzResearch.WordTrace tailWord_6137588 prefixEnd_6137588 1050510901089145964141251 := by
  unfold tailWord_6137588
  simp only [CollatzResearch.WordTrace]
  refine ⟨111928112444287183711362709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149237483259049578281816945 111928112444287183711362709)
  ·
    refine ⟨5246630270825961736470127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111928112444287183711362709 5246630270825961736470127)
    ·
      refine ⟨7869945406238942604705191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246630270825961736470127 7869945406238942604705191)
      ·
        refine ⟨11804918109358413907057787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7869945406238942604705191 11804918109358413907057787)
        ·
          refine ⟨17707377164037620860586681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11804918109358413907057787 17707377164037620860586681)
          ·
            refine ⟨13280532873028215645440011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17707377164037620860586681 13280532873028215645440011)
            ·
              refine ⟨19920799309542323468160017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280532873028215645440011 19920799309542323468160017)
              ·
                refine ⟨14940599482156742601120013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19920799309542323468160017 14940599482156742601120013)
                ·
                  refine ⟨5602724805808778475420005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14940599482156742601120013 5602724805808778475420005)
                  ·
                    refine ⟨1050510901089145964141251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602724805808778475420005 1050510901089145964141251)
                    ·
                      rfl

theorem cell23_6137588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6137588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137588 prefixEnd_6137588 := by exact prefixLift 6137588
  have htrace : WordTrace (prefixWord ++ tailWord_6137588) baseStart_6137588 baseEnd_6137588 := by
    simpa [prefixWord, tailWord_6137588, baseEnd_6137588] using wordTrace_append hprefix tailTrace_6137588
  have hstable : (prefixWord ++ tailWord_6137588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137588).length < 2 ^ (prefixWord ++ tailWord_6137588).sum := by decide
  have hdescent : baseEnd_6137588 < baseStart_6137588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137598 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_6137598 : Nat := 118140960795 + 6137598 * 2 ^ 59
def prefixEnd_6137598 : Nat := 4983230072969 + 3 ^ 40 * 6137598 * 2
def baseEnd_6137598 : Nat := 3151537838073982853298707

theorem tailTrace_6137598 : CollatzResearch.WordTrace tailWord_6137598 prefixEnd_6137598 3151537838073982853298707 := by
  unfold tailWord_6137598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982073702317267391323681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149237726412358759420392965 27982073702317267391323681)
  ·
    refine ⟨20986555276737950543492761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27982073702317267391323681 20986555276737950543492761)
    ·
      refine ⟨15739916457553462907619571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20986555276737950543492761 15739916457553462907619571)
      ·
        refine ⟨23609874686330194361429357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15739916457553462907619571 23609874686330194361429357)
        ·
          refine ⟨8853703007373822885536009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23609874686330194361429357 8853703007373822885536009)
          ·
            refine ⟨6640277255530367164152007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8853703007373822885536009 6640277255530367164152007)
            ·
              refine ⟨9960415883295550746228011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640277255530367164152007 9960415883295550746228011)
              ·
                refine ⟨14940623824943326119342017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9960415883295550746228011 14940623824943326119342017)
                ·
                  refine ⟨11205467868707494589506513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14940623824943326119342017 11205467868707494589506513)
                  ·
                    refine ⟨8404100901530620942129885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11205467868707494589506513 8404100901530620942129885)
                    ·
                      refine ⟨3151537838073982853298707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404100901530620942129885 3151537838073982853298707)
                      ·
                        rfl

theorem cell23_6137598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_6137598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137598 prefixEnd_6137598 := by exact prefixLift 6137598
  have htrace : WordTrace (prefixWord ++ tailWord_6137598) baseStart_6137598 baseEnd_6137598 := by
    simpa [prefixWord, tailWord_6137598, baseEnd_6137598] using wordTrace_append hprefix tailTrace_6137598
  have hstable : (prefixWord ++ tailWord_6137598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137598).length < 2 ^ (prefixWord ++ tailWord_6137598).sum := by decide
  have hdescent : baseEnd_6137598 < baseStart_6137598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137611 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 1, 1, 3]
def baseStart_6137611 : Nat := 118140960795 + 6137611 * 2 ^ 59
def prefixEnd_6137611 : Nat := 4983230072969 + 3 ^ 40 * 6137611 * 2
def baseEnd_6137611 : Nat := 3151544513322491302436147

theorem tailTrace_6137611 : CollatzResearch.WordTrace tailWord_6137611 prefixEnd_6137611 3151544513322491302436147 := by
  unfold tailWord_6137611
  simp only [CollatzResearch.WordTrace]
  refine ⟨223857063767491042350812687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149238042511660694900541791 223857063767491042350812687)
  ·
    refine ⟨335785595651236563526219031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223857063767491042350812687 335785595651236563526219031)
    ·
      refine ⟨503678393476854845289328547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335785595651236563526219031 503678393476854845289328547)
      ·
        refine ⟨755517590215282267933992821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503678393476854845289328547 755517590215282267933992821)
        ·
          refine ⟨70829774082682712618811827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 755517590215282267933992821 70829774082682712618811827)
          ·
            refine ⟨106244661124024068928217741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70829774082682712618811827 106244661124024068928217741)
            ·
              refine ⟨39841747921509025848081653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106244661124024068928217741 39841747921509025848081653)
              ·
                refine ⟨3735163867641471173257655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39841747921509025848081653 3735163867641471173257655)
                ·
                  refine ⟨5602745801462206759886483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735163867641471173257655 5602745801462206759886483)
                  ·
                    refine ⟨8404118702193310139829725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602745801462206759886483 8404118702193310139829725)
                    ·
                      refine ⟨3151544513322491302436147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404118702193310139829725 3151544513322491302436147)
                      ·
                        rfl

theorem cell23_6137611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 1, 3].length) (baseStart_6137611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137611 prefixEnd_6137611 := by exact prefixLift 6137611
  have htrace : WordTrace (prefixWord ++ tailWord_6137611) baseStart_6137611 baseEnd_6137611 := by
    simpa [prefixWord, tailWord_6137611, baseEnd_6137611] using wordTrace_append hprefix tailTrace_6137611
  have hstable : (prefixWord ++ tailWord_6137611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137611).length < 2 ^ (prefixWord ++ tailWord_6137611).sum := by decide
  have hdescent : baseEnd_6137611 < baseStart_6137611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137627 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 4, 4]
def baseStart_6137627 : Nat := 118140960795 + 6137627 * 2 ^ 59
def prefixEnd_6137627 : Nat := 4983230072969 + 3 ^ 40 * 6137627 * 2
def baseEnd_6137627 : Nat := 1050517576337654413278691

theorem tailTrace_6137627 : CollatzResearch.WordTrace tailWord_6137627 prefixEnd_6137627 1050517576337654413278691 := by
  unfold tailWord_6137627
  simp only [CollatzResearch.WordTrace]
  refine ⟨223857647335433077083395135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149238431556955384722263423 223857647335433077083395135)
  ·
    refine ⟨335786471003149615625092703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223857647335433077083395135 335786471003149615625092703)
    ·
      refine ⟨503679706504724423437639055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335786471003149615625092703 503679706504724423437639055)
      ·
        refine ⟨755519559757086635156458583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503679706504724423437639055 755519559757086635156458583)
        ·
          refine ⟨1133279339635629952734687875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755519559757086635156458583 1133279339635629952734687875)
          ·
            refine ⟨1699919009453444929102031813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133279339635629952734687875 1699919009453444929102031813)
            ·
              refine ⟨318734814272520924206630965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1699919009453444929102031813 318734814272520924206630965)
              ·
                refine ⟨29881388838048836644371653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318734814272520924206630965 29881388838048836644371653)
                ·
                  refine ⟨5602760407134156870819685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29881388838048836644371653 5602760407134156870819685)
                  ·
                    refine ⟨1050517576337654413278691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5602760407134156870819685 1050517576337654413278691)
                    ·
                      rfl

theorem cell23_6137627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 4].length) (baseStart_6137627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137627 prefixEnd_6137627 := by exact prefixLift 6137627
  have htrace : WordTrace (prefixWord ++ tailWord_6137627) baseStart_6137627 baseEnd_6137627 := by
    simpa [prefixWord, tailWord_6137627, baseEnd_6137627] using wordTrace_append hprefix tailTrace_6137627
  have hstable : (prefixWord ++ tailWord_6137627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137627).length < 2 ^ (prefixWord ++ tailWord_6137627).sum := by decide
  have hdescent : baseEnd_6137627 < baseStart_6137627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137637 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_6137637 : Nat := 118140960795 + 6137637 * 2 ^ 59
def prefixEnd_6137637 : Nat := 4983230072969 + 3 ^ 40 * 6137637 * 2
def baseEnd_6137637 : Nat := 3151557863819508200711027

theorem tailTrace_6137637 : CollatzResearch.WordTrace tailWord_6137637 prefixEnd_6137637 3151557863819508200711027 := by
  unfold tailWord_6137637
  simp only [CollatzResearch.WordTrace]
  refine ⟨223858012065396848791259165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149238674710264565860839443 223858012065396848791259165)
  ·
    refine ⟨83946754524523818296722187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223858012065396848791259165 83946754524523818296722187)
    ·
      refine ⟨125920131786785727445083281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83946754524523818296722187 125920131786785727445083281)
      ·
        refine ⟨94440098840089295583812461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125920131786785727445083281 94440098840089295583812461)
        ·
          refine ⟨35415037065033485843929673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94440098840089295583812461 35415037065033485843929673)
          ·
            refine ⟨26561277798775114382947255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35415037065033485843929673 26561277798775114382947255)
            ·
              refine ⟨39841916698162671574420883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26561277798775114382947255 39841916698162671574420883)
              ·
                refine ⟨59762875047244007361631325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39841916698162671574420883 59762875047244007361631325)
                ·
                  refine ⟨22411078142716502760611747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59762875047244007361631325 22411078142716502760611747)
                  ·
                    refine ⟨33616617214074754140917621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22411078142716502760611747 33616617214074754140917621)
                    ·
                      refine ⟨3151557863819508200711027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33616617214074754140917621 3151557863819508200711027)
                      ·
                        rfl

theorem cell23_6137637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_6137637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137637 prefixEnd_6137637 := by exact prefixLift 6137637
  have htrace : WordTrace (prefixWord ++ tailWord_6137637) baseStart_6137637 baseEnd_6137637 := by
    simpa [prefixWord, tailWord_6137637, baseEnd_6137637] using wordTrace_append hprefix tailTrace_6137637
  have hstable : (prefixWord ++ tailWord_6137637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137637).length < 2 ^ (prefixWord ++ tailWord_6137637).sum := by decide
  have hdescent : baseEnd_6137637 < baseStart_6137637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137644 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_6137644 : Nat := 118140960795 + 6137644 * 2 ^ 59
def prefixEnd_6137644 : Nat := 4983230072969 + 3 ^ 40 * 6137644 * 2
def baseEnd_6137644 : Nat := 1050520486061363224441165

theorem tailTrace_6137644 : CollatzResearch.WordTrace tailWord_6137644 prefixEnd_6137644 1050520486061363224441165 := by
  unfold tailWord_6137644
  simp only [CollatzResearch.WordTrace]
  refine ⟨111929133688185744493381993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149238844917580992657842657 111929133688185744493381993)
  ·
    refine ⟨83946850266139308370036495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111929133688185744493381993 83946850266139308370036495)
    ·
      refine ⟨125920275399208962555054743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83946850266139308370036495 125920275399208962555054743)
      ·
        refine ⟨188880413098813443832582115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125920275399208962555054743 188880413098813443832582115)
        ·
          refine ⟨283320619648220165748873173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188880413098813443832582115 283320619648220165748873173)
          ·
            refine ⟨6640327023005160134739215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 283320619648220165748873173 6640327023005160134739215)
            ·
              refine ⟨9960490534507740202108823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640327023005160134739215 9960490534507740202108823)
              ·
                refine ⟨14940735801761610303163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9960490534507740202108823 14940735801761610303163235)
                ·
                  refine ⟨22411103702642415454744853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14940735801761610303163235 22411103702642415454744853)
                  ·
                    refine ⟨1050520486061363224441165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22411103702642415454744853 1050520486061363224441165)
                    ·
                      rfl

theorem cell23_6137644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_6137644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137644 prefixEnd_6137644 := by exact prefixLift 6137644
  have htrace : WordTrace (prefixWord ++ tailWord_6137644) baseStart_6137644 baseEnd_6137644 := by
    simpa [prefixWord, tailWord_6137644, baseEnd_6137644] using wordTrace_append hprefix tailTrace_6137644
  have hstable : (prefixWord ++ tailWord_6137644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137644).length < 2 ^ (prefixWord ++ tailWord_6137644).sum := by decide
  have hdescent : baseEnd_6137644 < baseStart_6137644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137651 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 4]
def baseStart_6137651 : Nat := 118140960795 + 6137651 * 2 ^ 59
def prefixEnd_6137651 : Nat := 4983230072969 + 3 ^ 40 * 6137651 * 2
def baseEnd_6137651 : Nat := 3151565052548671145935963

theorem tailTrace_6137651 : CollatzResearch.WordTrace tailWord_6137651 prefixEnd_6137651 3151565052548671145935963 := by
  unfold tailWord_6137651
  simp only [CollatzResearch.WordTrace]
  refine ⟨223858522687346129182268807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149239015124897419454845871 223858522687346129182268807)
  ·
    refine ⟨335787784031019193773403211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223858522687346129182268807 335787784031019193773403211)
    ·
      refine ⟨503681676046528790660104817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335787784031019193773403211 503681676046528790660104817)
      ·
        refine ⟨377761257034896592995078613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503681676046528790660104817 377761257034896592995078613)
        ·
          refine ⟨8853779461755388898322155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 377761257034896592995078613 8853779461755388898322155)
          ·
            refine ⟨13280669192633083347483233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853779461755388898322155 13280669192633083347483233)
            ·
              refine ⟨9960501894474812510612425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13280669192633083347483233 9960501894474812510612425)
              ·
                refine ⟨7470376420856109382959319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9960501894474812510612425 7470376420856109382959319)
                ·
                  refine ⟨11205564631284164074438979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7470376420856109382959319 11205564631284164074438979)
                  ·
                    refine ⟨16808346946926246111658469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11205564631284164074438979 16808346946926246111658469)
                    ·
                      refine ⟨3151565052548671145935963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16808346946926246111658469 3151565052548671145935963)
                      ·
                        rfl

theorem cell23_6137651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_6137651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137651 prefixEnd_6137651 := by exact prefixLift 6137651
  have htrace : WordTrace (prefixWord ++ tailWord_6137651) baseStart_6137651 baseEnd_6137651 := by
    simpa [prefixWord, tailWord_6137651, baseEnd_6137651] using wordTrace_append hprefix tailTrace_6137651
  have hstable : (prefixWord ++ tailWord_6137651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137651).length < 2 ^ (prefixWord ++ tailWord_6137651).sum := by decide
  have hdescent : baseEnd_6137651 < baseStart_6137651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137718 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6137718 : Nat := 118140960795 + 6137718 * 2 ^ 59
def prefixEnd_6137718 : Nat := 4983230072969 + 3 ^ 40 * 6137718 * 2
def baseEnd_6137718 : Nat := 3151599455752522383798155

theorem tailTrace_6137718 : CollatzResearch.WordTrace tailWord_6137718 prefixEnd_6137718 3151599455752522383798155 := by
  unfold tailWord_6137718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991310398631462476559863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149240644252068933083305205 13991310398631462476559863)
  ·
    refine ⟨20986965597947193714839795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13991310398631462476559863 20986965597947193714839795)
    ·
      refine ⟨31480448396920790572259693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20986965597947193714839795 31480448396920790572259693)
      ·
        refine ⟨11805168148845296464597385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31480448396920790572259693 11805168148845296464597385)
        ·
          refine ⟨8853876111633972348448039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11805168148845296464597385 8853876111633972348448039)
          ·
            refine ⟨13280814167450958522672059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853876111633972348448039 13280814167450958522672059)
            ·
              refine ⟨19921221251176437784008089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280814167450958522672059 19921221251176437784008089)
              ·
                refine ⟨14940915938382328338006067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19921221251176437784008089 14940915938382328338006067)
                ·
                  refine ⟨22411373907573492507009101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14940915938382328338006067 22411373907573492507009101)
                  ·
                    refine ⟨8404265215340059690128413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22411373907573492507009101 8404265215340059690128413)
                    ·
                      refine ⟨3151599455752522383798155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404265215340059690128413 3151599455752522383798155)
                      ·
                        rfl

theorem cell23_6137718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6137718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137718 prefixEnd_6137718 := by exact prefixLift 6137718
  have htrace : WordTrace (prefixWord ++ tailWord_6137718) baseStart_6137718 baseEnd_6137718 := by
    simpa [prefixWord, tailWord_6137718, baseEnd_6137718] using wordTrace_append hprefix tailTrace_6137718
  have hstable : (prefixWord ++ tailWord_6137718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137718).length < 2 ^ (prefixWord ++ tailWord_6137718).sum := by decide
  have hdescent : baseEnd_6137718 < baseStart_6137718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137728 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2]
def baseStart_6137728 : Nat := 118140960795 + 6137728 * 2 ^ 59
def prefixEnd_6137728 : Nat := 4983230072969 + 3 ^ 40 * 6137728 * 2
def baseEnd_6137728 : Nat := 3151604590559067344673109

theorem tailTrace_6137728 : CollatzResearch.WordTrace tailWord_6137728 prefixEnd_6137728 3151604590559067344673109 := by
  unfold tailWord_6137728
  simp only [CollatzResearch.WordTrace]
  refine ⟨111930665554033585666410919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149240887405378114221881225 111930665554033585666410919)
  ·
    refine ⟨167895998331050378499616379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111930665554033585666410919 167895998331050378499616379)
    ·
      refine ⟨251843997496575567749424569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167895998331050378499616379 251843997496575567749424569)
      ·
        refine ⟨188882998122431675812068427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251843997496575567749424569 188882998122431675812068427)
        ·
          refine ⟨283324497183647513718102641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188882998122431675812068427 283324497183647513718102641)
          ·
            refine ⟨212493372887735635288576981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283324497183647513718102641 212493372887735635288576981)
            ·
              refine ⟨4980313427056303952076023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212493372887735635288576981 4980313427056303952076023)
              ·
                refine ⟨7470470140584455928114035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4980313427056303952076023 7470470140584455928114035)
                ·
                  refine ⟨11205705210876683892171053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7470470140584455928114035 11205705210876683892171053)
                  ·
                    refine ⟨4202139454078756459564145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11205705210876683892171053 4202139454078756459564145)
                    ·
                      refine ⟨3151604590559067344673109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202139454078756459564145 3151604590559067344673109)
                      ·
                        rfl

theorem cell23_6137728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_6137728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137728 prefixEnd_6137728 := by exact prefixLift 6137728
  have htrace : WordTrace (prefixWord ++ tailWord_6137728) baseStart_6137728 baseEnd_6137728 := by
    simpa [prefixWord, tailWord_6137728, baseEnd_6137728] using wordTrace_append hprefix tailTrace_6137728
  have hstable : (prefixWord ++ tailWord_6137728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137728).length < 2 ^ (prefixWord ++ tailWord_6137728).sum := by decide
  have hdescent : baseEnd_6137728 < baseStart_6137728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137754 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6137754 : Nat := 118140960795 + 6137754 * 2 ^ 59
def prefixEnd_6137754 : Nat := 4983230072969 + 3 ^ 40 * 6137754 * 2
def baseEnd_6137754 : Nat := 3151617941056084242947989

theorem tailTrace_6137754 : CollatzResearch.WordTrace tailWord_6137754 prefixEnd_6137754 3151617941056084242947989 := by
  unfold tailWord_6137754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55965569851493244443317079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149241519603981985182178877 55965569851493244443317079)
  ·
    refine ⟨83948354777239866664975619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55965569851493244443317079 83948354777239866664975619)
    ·
      refine ⟨125922532165859799997463429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83948354777239866664975619 125922532165859799997463429)
      ·
        refine ⟨23610474781098712499524393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125922532165859799997463429 23610474781098712499524393)
        ·
          refine ⟨17707856085824034374643295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23610474781098712499524393 17707856085824034374643295)
          ·
            refine ⟨26561784128736051561964943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17707856085824034374643295 26561784128736051561964943)
            ·
              refine ⟨39842676193104077342947415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26561784128736051561964943 39842676193104077342947415)
              ·
                refine ⟨59764014289656116014421123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39842676193104077342947415 59764014289656116014421123)
                ·
                  refine ⟨89646021434484174021631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59764014289656116014421123 89646021434484174021631685)
                  ·
                    refine ⟨16808629018965782629055941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89646021434484174021631685 16808629018965782629055941)
                    ·
                      refine ⟨3151617941056084242947989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16808629018965782629055941 3151617941056084242947989)
                      ·
                        rfl

theorem cell23_6137754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6137754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137754 prefixEnd_6137754 := by exact prefixLift 6137754
  have htrace : WordTrace (prefixWord ++ tailWord_6137754) baseStart_6137754 baseEnd_6137754 := by
    simpa [prefixWord, tailWord_6137754, baseEnd_6137754] using wordTrace_append hprefix tailTrace_6137754
  have hstable : (prefixWord ++ tailWord_6137754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137754).length < 2 ^ (prefixWord ++ tailWord_6137754).sum := by decide
  have hdescent : baseEnd_6137754 < baseStart_6137754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137764 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 7]
def baseStart_6137764 : Nat := 118140960795 + 6137764 * 2 ^ 59
def prefixEnd_6137764 : Nat := 4983230072969 + 3 ^ 40 * 6137764 * 2
def baseEnd_6137764 : Nat := 350180341762514355980327

theorem tailTrace_6137764 : CollatzResearch.WordTrace tailWord_6137764 prefixEnd_6137764 350180341762514355980327 := by
  unfold tailWord_6137764
  simp only [CollatzResearch.WordTrace]
  refine ⟨111931322067968374740566173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149241762757291166320754897 111931322067968374740566173)
  ·
    refine ⟨41974245775488140527712315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111931322067968374740566173 41974245775488140527712315)
    ·
      refine ⟨62961368663232210791568473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41974245775488140527712315 62961368663232210791568473)
      ·
        refine ⟨47221026497424158093676355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62961368663232210791568473 47221026497424158093676355)
        ·
          refine ⟨70831539746136237140514533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47221026497424158093676355 70831539746136237140514533)
          ·
            refine ⟨13280913702400544463846475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70831539746136237140514533 13280913702400544463846475)
            ·
              refine ⟨19921370553600816695769713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280913702400544463846475 19921370553600816695769713)
              ·
                refine ⟨14941027915200612521827285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19921370553600816695769713 14941027915200612521827285)
                ·
                  refine ⟨350180341762514355980327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14941027915200612521827285 350180341762514355980327)
                  ·
                    rfl

theorem cell23_6137764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_6137764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137764 prefixEnd_6137764 := by exact prefixLift 6137764
  have htrace : WordTrace (prefixWord ++ tailWord_6137764) baseStart_6137764 baseEnd_6137764 := by
    simpa [prefixWord, tailWord_6137764, baseEnd_6137764] using wordTrace_append hprefix tailTrace_6137764
  have hstable : (prefixWord ++ tailWord_6137764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137764).length < 2 ^ (prefixWord ++ tailWord_6137764).sum := by decide
  have hdescent : baseEnd_6137764 < baseStart_6137764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137781 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 5]
def baseStart_6137781 : Nat := 118140960795 + 6137781 * 2 ^ 59
def prefixEnd_6137781 : Nat := 4983230072969 + 3 ^ 40 * 6137781 * 2
def baseEnd_6137781 : Nat := 350181311670417293034485

theorem tailTrace_6137781 : CollatzResearch.WordTrace tailWord_6137781 prefixEnd_6137781 350181311670417293034485 := by
  unfold tailWord_6137781
  simp only [CollatzResearch.WordTrace]
  refine ⟨223863264176875161384501197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149242176117916774256334131 223863264176875161384501197)
  ·
    refine ⟨83948724066328185519187949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223863264176875161384501197 83948724066328185519187949)
    ·
      refine ⟨31480771524873069569695481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83948724066328185519187949 31480771524873069569695481)
      ·
        refine ⟨23610578643654802177271611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31480771524873069569695481 23610578643654802177271611)
        ·
          refine ⟨35415867965482203265907417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23610578643654802177271611 35415867965482203265907417)
          ·
            refine ⟨26561900974111652449430563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35415867965482203265907417 26561900974111652449430563)
            ·
              refine ⟨39842851461167478674145845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26561900974111652449430563 39842851461167478674145845)
              ·
                refine ⟨3735267324484451125701173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39842851461167478674145845 3735267324484451125701173)
                ·
                  refine ⟨350181311670417293034485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735267324484451125701173 350181311670417293034485)
                  ·
                    rfl

theorem cell23_6137781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_6137781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137781 prefixEnd_6137781 := by exact prefixLift 6137781
  have htrace : WordTrace (prefixWord ++ tailWord_6137781) baseStart_6137781 baseEnd_6137781 := by
    simpa [prefixWord, tailWord_6137781, baseEnd_6137781] using wordTrace_append hprefix tailTrace_6137781
  have hstable : (prefixWord ++ tailWord_6137781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137781).length < 2 ^ (prefixWord ++ tailWord_6137781).sum := by decide
  have hdescent : baseEnd_6137781 < baseStart_6137781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137881 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_6137881 : Nat := 118140960795 + 6137881 * 2 ^ 59
def prefixEnd_6137881 : Nat := 4983230072969 + 3 ^ 40 * 6137881 * 2
def baseEnd_6137881 : Nat := 3151683153099205246059905

theorem tailTrace_6137881 : CollatzResearch.WordTrace tailWord_6137881 prefixEnd_6137881 3151683153099205246059905 := by
  unfold tailWord_6137881
  simp only [CollatzResearch.WordTrace]
  refine ⟨223866911476512878463141497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149244607651008585642094331 223866911476512878463141497)
  ·
    refine ⟨167900183607384658847356123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223866911476512878463141497 167900183607384658847356123)
    ·
      refine ⟨251850275411076988271034185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167900183607384658847356123 251850275411076988271034185)
      ·
        refine ⟨188887706558307741203275639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251850275411076988271034185 188887706558307741203275639)
        ·
          refine ⟨283331559837461611804913459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188887706558307741203275639 283331559837461611804913459)
          ·
            refine ⟨424997339756192417707370189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283331559837461611804913459 424997339756192417707370189)
            ·
              refine ⟨159374002408572156640263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424997339756192417707370189 159374002408572156640263821)
              ·
                refine ⟨59765250903214558740098933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159374002408572156640263821 59765250903214558740098933)
                ·
                  refine ⟨5602992272176364881884275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59765250903214558740098933 5602992272176364881884275)
                  ·
                    refine ⟨8404488408264547322826413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602992272176364881884275 8404488408264547322826413)
                    ·
                      refine ⟨3151683153099205246059905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404488408264547322826413 3151683153099205246059905)
                      ·
                        rfl

theorem cell23_6137881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_6137881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137881 prefixEnd_6137881 := by exact prefixLift 6137881
  have htrace : WordTrace (prefixWord ++ tailWord_6137881) baseStart_6137881 baseEnd_6137881 := by
    simpa [prefixWord, tailWord_6137881, baseEnd_6137881] using wordTrace_append hprefix tailTrace_6137881
  have hstable : (prefixWord ++ tailWord_6137881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137881).length < 2 ^ (prefixWord ++ tailWord_6137881).sum := by decide
  have hdescent : baseEnd_6137881 < baseStart_6137881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137914 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_6137914 : Nat := 118140960795 + 6137914 * 2 ^ 59
def prefixEnd_6137914 : Nat := 4983230072969 + 3 ^ 40 * 6137914 * 2
def baseEnd_6137914 : Nat := 1050566699320267872315751

theorem tailTrace_6137914 : CollatzResearch.WordTrace tailWord_6137914 prefixEnd_6137914 1050566699320267872315751 := by
  unfold tailWord_6137914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55967028771348331274773199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149245410056928883399395197 55967028771348331274773199)
  ·
    refine ⟨83950543157022496912159799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55967028771348331274773199 83950543157022496912159799)
    ·
      refine ⟨125925814735533745368239699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83950543157022496912159799 125925814735533745368239699)
      ·
        refine ⟨188888722103300618052359549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125925814735533745368239699 188888722103300618052359549)
        ·
          refine ⟨70833270788737731769634831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188888722103300618052359549 70833270788737731769634831)
          ·
            refine ⟨106249906183106597654452247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70833270788737731769634831 106249906183106597654452247)
            ·
              refine ⟨159374859274659896481678371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106249906183106597654452247 159374859274659896481678371)
              ·
                refine ⟨239062288911989844722517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159374859274659896481678371 239062288911989844722517557)
                ·
                  refine ⟨22412089585499047942736021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239062288911989844722517557 22412089585499047942736021)
                  ·
                    refine ⟨1050566699320267872315751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22412089585499047942736021 1050566699320267872315751)
                    ·
                      rfl

theorem cell23_6137914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_6137914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137914 prefixEnd_6137914 := by exact prefixLift 6137914
  have htrace : WordTrace (prefixWord ++ tailWord_6137914) baseStart_6137914 baseEnd_6137914 := by
    simpa [prefixWord, tailWord_6137914, baseEnd_6137914] using wordTrace_append hprefix tailTrace_6137914
  have hstable : (prefixWord ++ tailWord_6137914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137914).length < 2 ^ (prefixWord ++ tailWord_6137914).sum := by decide
  have hdescent : baseEnd_6137914 < baseStart_6137914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137942 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6137942 : Nat := 118140960795 + 6137942 * 2 ^ 59
def prefixEnd_6137942 : Nat := 4983230072969 + 3 ^ 40 * 6137942 * 2
def baseEnd_6137942 : Nat := 3151714475419129507397125

theorem tailTrace_6137942 : CollatzResearch.WordTrace tailWord_6137942 prefixEnd_6137942 3151714475419129507397125 := by
  unfold tailWord_6137942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991821020580742867569505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149246090886194590587408053 13991821020580742867569505)
  ·
    refine ⟨10493865765435557150677129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13991821020580742867569505 10493865765435557150677129)
    ·
      refine ⟨7870399324076667863007847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10493865765435557150677129 7870399324076667863007847)
      ·
        refine ⟨11805598986115001794511771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870399324076667863007847 11805598986115001794511771)
        ·
          refine ⟨17708398479172502691767657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805598986115001794511771 17708398479172502691767657)
          ·
            refine ⟨13281298859379377018825743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708398479172502691767657 13281298859379377018825743)
            ·
              refine ⟨19921948289069065528238615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13281298859379377018825743 19921948289069065528238615)
              ·
                refine ⟨29882922433603598292357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19921948289069065528238615 29882922433603598292357923)
                ·
                  refine ⟨44824383650405397438536885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29882922433603598292357923 44824383650405397438536885)
                  ·
                    refine ⟨4202285967225506009862833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44824383650405397438536885 4202285967225506009862833)
                    ·
                      refine ⟨3151714475419129507397125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202285967225506009862833 3151714475419129507397125)
                      ·
                        rfl

theorem cell23_6137942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6137942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137942 prefixEnd_6137942 := by exact prefixLift 6137942
  have htrace : WordTrace (prefixWord ++ tailWord_6137942) baseStart_6137942 baseEnd_6137942 := by
    simpa [prefixWord, tailWord_6137942, baseEnd_6137942] using wordTrace_append hprefix tailTrace_6137942
  have hstable : (prefixWord ++ tailWord_6137942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137942).length < 2 ^ (prefixWord ++ tailWord_6137942).sum := by decide
  have hdescent : baseEnd_6137942 < baseStart_6137942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137949 : List Nat := [1, 4, 4, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6137949 : Nat := 118140960795 + 6137949 * 2 ^ 59
def prefixEnd_6137949 : Nat := 4983230072969 + 3 ^ 40 * 6137949 * 2
def baseEnd_6137949 : Nat := 3151718069783710980009593

theorem tailTrace_6137949 : CollatzResearch.WordTrace tailWord_6137949 prefixEnd_6137949 3151718069783710980009593 := by
  unfold tailWord_6137949
  simp only [CollatzResearch.WordTrace]
  refine ⟨223869391640266526076616901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149246261093511017384411267 223869391640266526076616901)
  ·
    refine ⟨41975510932549973639365669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223869391640266526076616901 41975510932549973639365669)
    ·
      refine ⟨7870408299853120057381063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41975510932549973639365669 7870408299853120057381063)
      ·
        refine ⟨11805612449779680086071595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870408299853120057381063 11805612449779680086071595)
        ·
          refine ⟨17708418674669520129107393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805612449779680086071595 17708418674669520129107393)
          ·
            refine ⟨13281314006002140096830545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708418674669520129107393 13281314006002140096830545)
            ·
              refine ⟨9960985504501605072622909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13281314006002140096830545 9960985504501605072622909)
              ·
                refine ⟨3735369564188101902233591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9960985504501605072622909 3735369564188101902233591)
                ·
                  refine ⟨5603054346282152853350387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735369564188101902233591 5603054346282152853350387)
                  ·
                    refine ⟨8404581519423229280025581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603054346282152853350387 8404581519423229280025581)
                    ·
                      refine ⟨3151718069783710980009593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404581519423229280025581 3151718069783710980009593)
                      ·
                        rfl

theorem cell23_6137949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6137949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137949 prefixEnd_6137949 := by exact prefixLift 6137949
  have htrace : WordTrace (prefixWord ++ tailWord_6137949) baseStart_6137949 baseEnd_6137949 := by
    simpa [prefixWord, tailWord_6137949, baseEnd_6137949] using wordTrace_append hprefix tailTrace_6137949
  have hstable : (prefixWord ++ tailWord_6137949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137949).length < 2 ^ (prefixWord ++ tailWord_6137949).sum := by decide
  have hdescent : baseEnd_6137949 < baseStart_6137949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6137985 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6137985 : Nat := 118140960795 + 6137985 * 2 ^ 59
def prefixEnd_6137985 : Nat := 4983230072969 + 3 ^ 40 * 6137985 * 2
def baseEnd_6137985 : Nat := 3151736555087272839159427

theorem tailTrace_6137985 : CollatzResearch.WordTrace tailWord_6137985 prefixEnd_6137985 3151736555087272839159427 := by
  unfold tailWord_6137985
  simp only [CollatzResearch.WordTrace]
  refine ⟨223870704668136104224927409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149247136445424069483284939 223870704668136104224927409)
  ·
    refine ⟨167903028501102078168695557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223870704668136104224927409 167903028501102078168695557)
    ·
      refine ⟨31481817843956639656630417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167903028501102078168695557 31481817843956639656630417)
      ·
        refine ⟨23611363382967479742472813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31481817843956639656630417 23611363382967479742472813)
        ·
          refine ⟨8854261268612804903427305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23611363382967479742472813 8854261268612804903427305)
          ·
            refine ⟨6640695951459603677570479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8854261268612804903427305 6640695951459603677570479)
            ·
              refine ⟨9961043927189405516355719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640695951459603677570479 9961043927189405516355719)
              ·
                refine ⟨14941565890784108274533579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961043927189405516355719 14941565890784108274533579)
                ·
                  refine ⟨22412348836176162411800369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14941565890784108274533579 22412348836176162411800369)
                  ·
                    refine ⟨16809261627132121808850277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22412348836176162411800369 16809261627132121808850277)
                    ·
                      refine ⟨3151736555087272839159427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16809261627132121808850277 3151736555087272839159427)
                      ·
                        rfl

theorem cell23_6137985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6137985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6137985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6137985 prefixEnd_6137985 := by exact prefixLift 6137985
  have htrace : WordTrace (prefixWord ++ tailWord_6137985) baseStart_6137985 baseEnd_6137985 := by
    simpa [prefixWord, tailWord_6137985, baseEnd_6137985] using wordTrace_append hprefix tailTrace_6137985
  have hstable : (prefixWord ++ tailWord_6137985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6137985).length < 2 ^ (prefixWord ++ tailWord_6137985).sum := by decide
  have hdescent : baseEnd_6137985 < baseStart_6137985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6137985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138031 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_6138031 : Nat := 118140960795 + 6138031 * 2 ^ 59
def prefixEnd_6138031 : Nat := 4983230072969 + 3 ^ 40 * 6138031 * 2
def baseEnd_6138031 : Nat := 3151760175197379659184215

theorem tailTrace_6138031 : CollatzResearch.WordTrace tailWord_6138031 prefixEnd_6138031 3151760175197379659184215 := by
  unfold tailWord_6138031
  simp only [CollatzResearch.WordTrace]
  refine ⟨223872382425969454081101947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149248254950646302720734631 223872382425969454081101947)
  ·
    refine ⟨335808573638954181121652921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223872382425969454081101947 335808573638954181121652921)
    ·
      refine ⟨251856430229215635841239691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335808573638954181121652921 251856430229215635841239691)
      ·
        refine ⟨377784645343823453761859537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251856430229215635841239691 377784645343823453761859537)
        ·
          refine ⟨283338484007867590321394653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377784645343823453761859537 283338484007867590321394653)
          ·
            refine ⟨106251931502950346370522995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283338484007867590321394653 106251931502950346370522995)
            ·
              refine ⟨159377897254425519555784493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106251931502950346370522995 159377897254425519555784493)
              ·
                refine ⟨59766711470409569833419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159377897254425519555784493 59766711470409569833419185)
                ·
                  refine ⟨44825033602807177375064389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59766711470409569833419185 44825033602807177375064389)
                  ·
                    refine ⟨8404693800526345757824573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44825033602807177375064389 8404693800526345757824573)
                    ·
                      refine ⟨3151760175197379659184215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8404693800526345757824573 3151760175197379659184215)
                      ·
                        rfl

theorem cell23_6138031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_6138031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138031 prefixEnd_6138031 := by exact prefixLift 6138031
  have htrace : WordTrace (prefixWord ++ tailWord_6138031) baseStart_6138031 baseEnd_6138031 := by
    simpa [prefixWord, tailWord_6138031, baseEnd_6138031] using wordTrace_append hprefix tailTrace_6138031
  have hstable : (prefixWord ++ tailWord_6138031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138031).length < 2 ^ (prefixWord ++ tailWord_6138031).sum := by decide
  have hdescent : baseEnd_6138031 < baseStart_6138031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138041 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6138041 : Nat := 118140960795 + 6138041 * 2 ^ 59
def prefixEnd_6138041 : Nat := 4983230072969 + 3 ^ 40 * 6138041 * 2
def baseEnd_6138041 : Nat := 3151765310003924620059169

theorem tailTrace_6138041 : CollatzResearch.WordTrace tailWord_6138041 prefixEnd_6138041 3151765310003924620059169 := by
  unfold tailWord_6138041
  simp only [CollatzResearch.WordTrace]
  refine ⟨223872747155933225788965977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149248498103955483859310651 223872747155933225788965977)
  ·
    refine ⟨167904560366949919341724483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223872747155933225788965977 167904560366949919341724483)
    ·
      refine ⟨251856840550424879012586725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167904560366949919341724483 251856840550424879012586725)
      ·
        refine ⟨47223157603204664814860011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251856840550424879012586725 47223157603204664814860011)
        ·
          refine ⟨70834736404806997222290017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47223157603204664814860011 70834736404806997222290017)
          ·
            refine ⟨53126052303605247916717513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70834736404806997222290017 53126052303605247916717513)
            ·
              refine ⟨39844539227703935937538135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53126052303605247916717513 39844539227703935937538135)
              ·
                refine ⟨59766808841555903906307203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39844539227703935937538135 59766808841555903906307203)
                ·
                  refine ⟨89650213262333855859460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59766808841555903906307203 89650213262333855859460805)
                  ·
                    refine ⟨16809414986687597973648901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89650213262333855859460805 16809414986687597973648901)
                    ·
                      refine ⟨3151765310003924620059169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16809414986687597973648901 3151765310003924620059169)
                      ·
                        rfl

theorem cell23_6138041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6138041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138041 prefixEnd_6138041 := by exact prefixLift 6138041
  have htrace : WordTrace (prefixWord ++ tailWord_6138041) baseStart_6138041 baseEnd_6138041 := by
    simpa [prefixWord, tailWord_6138041, baseEnd_6138041] using wordTrace_append hprefix tailTrace_6138041
  have hstable : (prefixWord ++ tailWord_6138041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138041).length < 2 ^ (prefixWord ++ tailWord_6138041).sum := by decide
  have hdescent : baseEnd_6138041 < baseStart_6138041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138085 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 5]
def baseStart_6138085 : Nat := 118140960795 + 6138085 * 2 ^ 59
def prefixEnd_6138085 : Nat := 4983230072969 + 3 ^ 40 * 6138085 * 2
def baseEnd_6138085 : Nat := 350198655905858049767663

theorem tailTrace_6138085 : CollatzResearch.WordTrace tailWord_6138085 prefixEnd_6138085 350198655905858049767663 := by
  unfold tailWord_6138085
  simp only [CollatzResearch.WordTrace]
  refine ⟨223874351967773821303567709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149249567978515880869045139 223874351967773821303567709)
  ·
    refine ⟨83952881987915182988837891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223874351967773821303567709 83952881987915182988837891)
    ·
      refine ⟨125929322981872774483256837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83952881987915182988837891 125929322981872774483256837)
      ·
        refine ⟨23611748059101145215610657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125929322981872774483256837 23611748059101145215610657)
        ·
          refine ⟨17708811044325858911707993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23611748059101145215610657 17708811044325858911707993)
          ·
            refine ⟨13281608283244394183780995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708811044325858911707993 13281608283244394183780995)
            ·
              refine ⟨19922412424866591275671493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13281608283244394183780995 19922412424866591275671493)
              ·
                refine ⟨3735452329662485864188405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19922412424866591275671493 3735452329662485864188405)
                ·
                  refine ⟨350198655905858049767663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3735452329662485864188405 350198655905858049767663)
                  ·
                    rfl

theorem cell23_6138085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_6138085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138085 prefixEnd_6138085 := by exact prefixLift 6138085
  have htrace : WordTrace (prefixWord ++ tailWord_6138085) baseStart_6138085 baseEnd_6138085 := by
    simpa [prefixWord, tailWord_6138085, baseEnd_6138085] using wordTrace_append hprefix tailTrace_6138085
  have hstable : (prefixWord ++ tailWord_6138085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138085).length < 2 ^ (prefixWord ++ tailWord_6138085).sum := by decide
  have hdescent : baseEnd_6138085 < baseStart_6138085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138091 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_6138091 : Nat := 118140960795 + 6138091 * 2 ^ 59
def prefixEnd_6138091 : Nat := 4983230072969 + 3 ^ 40 * 6138091 * 2
def baseEnd_6138091 : Nat := 3151790984036649424433939

theorem tailTrace_6138091 : CollatzResearch.WordTrace tailWord_6138091 prefixEnd_6138091 3151790984036649424433939 := by
  unfold tailWord_6138091
  simp only [CollatzResearch.WordTrace]
  refine ⟨223874570805752084328286127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149249713870501389552190751 223874570805752084328286127)
  ·
    refine ⟨335811856208628126492429191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223874570805752084328286127 335811856208628126492429191)
    ·
      refine ⟨503717784312942189738643787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335811856208628126492429191 503717784312942189738643787)
      ·
        refine ⟨755576676469413284607965681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503717784312942189738643787 755576676469413284607965681)
        ·
          refine ⟨566682507352059963455974261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755576676469413284607965681 566682507352059963455974261)
          ·
            refine ⟨53126485064255621573997587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 566682507352059963455974261 53126485064255621573997587)
            ·
              refine ⟨79689727596383432360996381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53126485064255621573997587 79689727596383432360996381)
              ·
                refine ⟨29883647848643787135373643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79689727596383432360996381 29883647848643787135373643)
                ·
                  refine ⟨44825471772965680703060465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29883647848643787135373643 44825471772965680703060465)
                  ·
                    refine ⟨33619103829724260527295349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44825471772965680703060465 33619103829724260527295349)
                    ·
                      refine ⟨3151790984036649424433939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33619103829724260527295349 3151790984036649424433939)
                      ·
                        rfl

theorem cell23_6138091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_6138091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138091 prefixEnd_6138091 := by exact prefixLift 6138091
  have htrace : WordTrace (prefixWord ++ tailWord_6138091) baseStart_6138091 baseEnd_6138091 := by
    simpa [prefixWord, tailWord_6138091, baseEnd_6138091] using wordTrace_append hprefix tailTrace_6138091
  have hstable : (prefixWord ++ tailWord_6138091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138091).length < 2 ^ (prefixWord ++ tailWord_6138091).sum := by decide
  have hdescent : baseEnd_6138091 < baseStart_6138091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138131 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_6138131 : Nat := 118140960795 + 6138131 * 2 ^ 59
def prefixEnd_6138131 : Nat := 4983230072969 + 3 ^ 40 * 6138131 * 2
def baseEnd_6138131 : Nat := 3151811523262829267933755

theorem tailTrace_6138131 : CollatzResearch.WordTrace tailWord_6138131 prefixEnd_6138131 3151811523262829267933755 := by
  unfold tailWord_6138131
  simp only [CollatzResearch.WordTrace]
  refine ⟨223876029725607171159742247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149250686483738114106494831 223876029725607171159742247)
  ·
    refine ⟨335814044588410756739613371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223876029725607171159742247 335814044588410756739613371)
    ·
      refine ⟨503721066882616135109420057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335814044588410756739613371 503721066882616135109420057)
      ·
        refine ⟨377790800161962101332065043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503721066882616135109420057 377790800161962101332065043)
        ·
          refine ⟨566686200242943151998097565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377790800161962101332065043 566686200242943151998097565)
          ·
            refine ⟨212507325091103681999286587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566686200242943151998097565 212507325091103681999286587)
            ·
              refine ⟨318760987636655522998929881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212507325091103681999286587 318760987636655522998929881)
              ·
                refine ⟨239070740727491642249197411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318760987636655522998929881 239070740727491642249197411)
                ·
                  refine ⟨358606111091237463373796117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239070740727491642249197411 358606111091237463373796117)
                  ·
                    refine ⟨16809661457401756095646693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 358606111091237463373796117 16809661457401756095646693)
                    ·
                      refine ⟨3151811523262829267933755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16809661457401756095646693 3151811523262829267933755)
                      ·
                        rfl

theorem cell23_6138131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_6138131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138131 prefixEnd_6138131 := by exact prefixLift 6138131
  have htrace : WordTrace (prefixWord ++ tailWord_6138131) baseStart_6138131 baseEnd_6138131 := by
    simpa [prefixWord, tailWord_6138131, baseEnd_6138131] using wordTrace_append hprefix tailTrace_6138131
  have hstable : (prefixWord ++ tailWord_6138131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138131).length < 2 ^ (prefixWord ++ tailWord_6138131).sum := by decide
  have hdescent : baseEnd_6138131 < baseStart_6138131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138135 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_6138135 : Nat := 118140960795 + 6138135 * 2 ^ 59
def prefixEnd_6138135 : Nat := 4983230072969 + 3 ^ 40 * 6138135 * 2
def baseEnd_6138135 : Nat := 3151813577185447252283737

theorem tailTrace_6138135 : CollatzResearch.WordTrace tailWord_6138135 prefixEnd_6138135 3151813577185447252283737 := by
  unfold tailWord_6138135
  simp only [CollatzResearch.WordTrace]
  refine ⟨223876175617592679842887859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149250783745061786561925239 223876175617592679842887859)
  ·
    refine ⟨335814263426389019764331789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223876175617592679842887859 335814263426389019764331789)
    ·
      refine ⟨125930348784895882411624421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335814263426389019764331789 125930348784895882411624421)
      ·
        refine ⟨23611940397167977952179579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125930348784895882411624421 23611940397167977952179579)
        ·
          refine ⟨35417910595751966928269369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23611940397167977952179579 35417910595751966928269369)
          ·
            refine ⟨26563432946813975196202027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35417910595751966928269369 26563432946813975196202027)
            ·
              refine ⟨39845149420220962794303041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26563432946813975196202027 39845149420220962794303041)
              ·
                refine ⟨29883862065165722095727281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39845149420220962794303041 29883862065165722095727281)
                ·
                  refine ⟨22412896548874291571795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29883862065165722095727281 22412896548874291571795461)
                  ·
                    refine ⟨4202418102913929669711649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22412896548874291571795461 4202418102913929669711649)
                    ·
                      refine ⟨3151813577185447252283737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202418102913929669711649 3151813577185447252283737)
                      ·
                        rfl

theorem cell23_6138135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_6138135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138135 prefixEnd_6138135 := by exact prefixLift 6138135
  have htrace : WordTrace (prefixWord ++ tailWord_6138135) baseStart_6138135 baseEnd_6138135 := by
    simpa [prefixWord, tailWord_6138135, baseEnd_6138135] using wordTrace_append hprefix tailTrace_6138135
  have hstable : (prefixWord ++ tailWord_6138135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138135).length < 2 ^ (prefixWord ++ tailWord_6138135).sum := by decide
  have hdescent : baseEnd_6138135 < baseStart_6138135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138229 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6138229 : Nat := 118140960795 + 6138229 * 2 ^ 59
def prefixEnd_6138229 : Nat := 4983230072969 + 3 ^ 40 * 6138229 * 2
def baseEnd_6138229 : Nat := 3151861844366969884508305

theorem tailTrace_6138229 : CollatzResearch.WordTrace tailWord_6138229 prefixEnd_6138229 3151861844366969884508305 := by
  unfold tailWord_6138229
  simp only [CollatzResearch.WordTrace]
  refine ⟨223879604079252133896809741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149253069386168089264539827 223879604079252133896809741)
  ·
    refine ⟨83954851529719550211303653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223879604079252133896809741 83954851529719550211303653)
    ·
      refine ⟨15741534661822415664619435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83954851529719550211303653 15741534661822415664619435)
      ·
        refine ⟨23612301992733623496929153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15741534661822415664619435 23612301992733623496929153)
        ·
          refine ⟨17709226494550217622696865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23612301992733623496929153 17709226494550217622696865)
          ·
            refine ⟨13281919870912663217022649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17709226494550217622696865 13281919870912663217022649)
            ·
              refine ⟨9961439903184497412766987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13281919870912663217022649 9961439903184497412766987)
              ·
                refine ⟨14942159854776746119150481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961439903184497412766987 14942159854776746119150481)
                ·
                  refine ⟨11206619891082559589362861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14942159854776746119150481 11206619891082559589362861)
                  ·
                    refine ⟨4202482459155959846011073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11206619891082559589362861 4202482459155959846011073)
                    ·
                      refine ⟨3151861844366969884508305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202482459155959846011073 3151861844366969884508305)
                      ·
                        rfl

theorem cell23_6138229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6138229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138229 prefixEnd_6138229 := by exact prefixLift 6138229
  have htrace : WordTrace (prefixWord ++ tailWord_6138229) baseStart_6138229 baseEnd_6138229 := by
    simpa [prefixWord, tailWord_6138229, baseEnd_6138229] using wordTrace_append hprefix tailTrace_6138229
  have hstable : (prefixWord ++ tailWord_6138229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138229).length < 2 ^ (prefixWord ++ tailWord_6138229).sum := by decide
  have hdescent : baseEnd_6138229 < baseStart_6138229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138252 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_6138252 : Nat := 118140960795 + 6138252 * 2 ^ 59
def prefixEnd_6138252 : Nat := 4983230072969 + 3 ^ 40 * 6138252 * 2
def baseEnd_6138252 : Nat := 1050624551474007764840233

theorem tailTrace_6138252 : CollatzResearch.WordTrace tailWord_6138252 prefixEnd_6138252 1050624551474007764840233 := by
  unfold tailWord_6138252
  simp only [CollatzResearch.WordTrace]
  refine ⟨111940221479084404412448505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149253628638779205883264673 111940221479084404412448505)
  ·
    refine ⟨83955166109313303309336379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111940221479084404412448505 83955166109313303309336379)
    ·
      refine ⟨125932749163969954964004569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83955166109313303309336379 125932749163969954964004569)
      ·
        refine ⟨94449561872977466223003427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125932749163969954964004569 94449561872977466223003427)
        ·
          refine ⟨141674342809466199334505141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94449561872977466223003427 141674342809466199334505141)
          ·
            refine ⟨13281969638387456187609857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141674342809466199334505141 13281969638387456187609857)
            ·
              refine ⟨9961477228790592140707393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13281969638387456187609857 9961477228790592140707393)
              ·
                refine ⟨7471107921592944105530545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961477228790592140707393 7471107921592944105530545)
                ·
                  refine ⟨5603330941194708079147909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7471107921592944105530545 5603330941194708079147909)
                  ·
                    refine ⟨1050624551474007764840233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5603330941194708079147909 1050624551474007764840233)
                    ·
                      rfl

theorem cell23_6138252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_6138252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138252 prefixEnd_6138252 := by exact prefixLift 6138252
  have htrace : WordTrace (prefixWord ++ tailWord_6138252) baseStart_6138252 baseEnd_6138252 := by
    simpa [prefixWord, tailWord_6138252, baseEnd_6138252] using wordTrace_append hprefix tailTrace_6138252
  have hstable : (prefixWord ++ tailWord_6138252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138252).length < 2 ^ (prefixWord ++ tailWord_6138252).sum := by decide
  have hdescent : baseEnd_6138252 < baseStart_6138252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138275 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3]
def baseStart_6138275 : Nat := 118140960795 + 6138275 * 2 ^ 59
def prefixEnd_6138275 : Nat := 4983230072969 + 3 ^ 40 * 6138275 * 2
def baseEnd_6138275 : Nat := 3151885464477076704533093

theorem tailTrace_6138275 : CollatzResearch.WordTrace tailWord_6138275 prefixEnd_6138275 3151885464477076704533093 := by
  unfold tailWord_6138275
  simp only [CollatzResearch.WordTrace]
  refine ⟨223881281837085483752984279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149254187891390322501989519 223881281837085483752984279)
  ·
    refine ⟨335821922755628225629476419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223881281837085483752984279 335821922755628225629476419)
    ·
      refine ⟨503732884133442338444214629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335821922755628225629476419 503732884133442338444214629)
      ·
        refine ⟨94449915775020438458290243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 503732884133442338444214629 94449915775020438458290243)
        ·
          refine ⟨141674873662530657687435365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94449915775020438458290243 141674873662530657687435365)
          ·
            refine ⟨26564038811724498316394131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141674873662530657687435365 26564038811724498316394131)
            ·
              refine ⟨39846058217586747474591197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26564038811724498316394131 39846058217586747474591197)
              ·
                refine ⟨14942271831595030302971699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39846058217586747474591197 14942271831595030302971699)
                ·
                  refine ⟨22413407747392545454457549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14942271831595030302971699 22413407747392545454457549)
                  ·
                    refine ⟨8405027905272204545421581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22413407747392545454457549 8405027905272204545421581)
                    ·
                      refine ⟨3151885464477076704533093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405027905272204545421581 3151885464477076704533093)
                      ·
                        rfl

theorem cell23_6138275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_6138275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138275 prefixEnd_6138275 := by exact prefixLift 6138275
  have htrace : WordTrace (prefixWord ++ tailWord_6138275) baseStart_6138275 baseEnd_6138275 := by
    simpa [prefixWord, tailWord_6138275, baseEnd_6138275] using wordTrace_append hprefix tailTrace_6138275
  have hstable : (prefixWord ++ tailWord_6138275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138275).length < 2 ^ (prefixWord ++ tailWord_6138275).sum := by decide
  have hdescent : baseEnd_6138275 < baseStart_6138275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138293 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_6138293 : Nat := 118140960795 + 6138293 * 2 ^ 59
def prefixEnd_6138293 : Nat := 4983230072969 + 3 ^ 40 * 6138293 * 2
def baseEnd_6138293 : Nat := 3151894707128857634108011

theorem tailTrace_6138293 : CollatzResearch.WordTrace tailWord_6138293 prefixEnd_6138293 3151894707128857634108011 := by
  unfold tailWord_6138293
  simp only [CollatzResearch.WordTrace]
  refine ⟨223881938351020272827139533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149254625567346848551426355 223881938351020272827139533)
  ·
    refine ⟨83955726881632602310177325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223881938351020272827139533 83955726881632602310177325)
    ·
      refine ⟨31483397580612225866316497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83955726881632602310177325 31483397580612225866316497)
      ·
        refine ⟨23612548185459169399737373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31483397580612225866316497 23612548185459169399737373)
        ·
          refine ⟨8854705569547188524901515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23612548185459169399737373 8854705569547188524901515)
          ·
            refine ⟨13282058354320782787352273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854705569547188524901515 13282058354320782787352273)
            ·
              refine ⟨9961543765740587090514205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13282058354320782787352273 9961543765740587090514205)
              ·
                refine ⟨3735578912152720158942827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9961543765740587090514205 3735578912152720158942827)
                ·
                  refine ⟨5603368368229080238414241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735578912152720158942827 5603368368229080238414241)
                  ·
                    refine ⟨4202526276171810178810681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5603368368229080238414241 4202526276171810178810681)
                    ·
                      refine ⟨3151894707128857634108011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202526276171810178810681 3151894707128857634108011)
                      ·
                        rfl

theorem cell23_6138293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_6138293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138293 prefixEnd_6138293 := by exact prefixLift 6138293
  have htrace : WordTrace (prefixWord ++ tailWord_6138293) baseStart_6138293 baseEnd_6138293 := by
    simpa [prefixWord, tailWord_6138293, baseEnd_6138293] using wordTrace_append hprefix tailTrace_6138293
  have hstable : (prefixWord ++ tailWord_6138293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138293).length < 2 ^ (prefixWord ++ tailWord_6138293).sum := by decide
  have hdescent : baseEnd_6138293 < baseStart_6138293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138325 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_6138325 : Nat := 118140960795 + 6138325 * 2 ^ 59
def prefixEnd_6138325 : Nat := 4983230072969 + 3 ^ 40 * 6138325 * 2
def baseEnd_6138325 : Nat := 1050637046169933836302621

theorem tailTrace_6138325 : CollatzResearch.WordTrace tailWord_6138325 prefixEnd_6138325 1050637046169933836302621 := by
  unfold tailWord_6138325
  simp only [CollatzResearch.WordTrace]
  refine ⟨223883105486904342292304429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149255403657936228194869619 223883105486904342292304429)
  ·
    refine ⟨83956164557589128359614161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223883105486904342292304429 83956164557589128359614161)
    ·
      refine ⟨62967123418191846269710621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83956164557589128359614161 62967123418191846269710621)
      ·
        refine ⟨23612671281821942351141483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62967123418191846269710621 23612671281821942351141483)
        ·
          refine ⟨35419006922732913526712225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23612671281821942351141483 35419006922732913526712225)
          ·
            refine ⟨26564255192049685145034169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35419006922732913526712225 26564255192049685145034169)
            ·
              refine ⟨19923191394037263858775627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26564255192049685145034169 19923191394037263858775627)
              ·
                refine ⟨29884787091055895788163441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19923191394037263858775627 29884787091055895788163441)
                ·
                  refine ⟨22413590318291921841122581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29884787091055895788163441 22413590318291921841122581)
                  ·
                    refine ⟨1050637046169933836302621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22413590318291921841122581 1050637046169933836302621)
                    ·
                      rfl

theorem cell23_6138325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_6138325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138325 prefixEnd_6138325 := by exact prefixLift 6138325
  have htrace : WordTrace (prefixWord ++ tailWord_6138325) baseStart_6138325 baseEnd_6138325 := by
    simpa [prefixWord, tailWord_6138325, baseEnd_6138325] using wordTrace_append hprefix tailTrace_6138325
  have hstable : (prefixWord ++ tailWord_6138325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138325).length < 2 ^ (prefixWord ++ tailWord_6138325).sum := by decide
  have hdescent : baseEnd_6138325 < baseStart_6138325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_6138368 : Nat := 118140960795 + 6138368 * 2 ^ 59
def prefixEnd_6138368 : Nat := 4983230072969 + 3 ^ 40 * 6138368 * 2
def baseEnd_6138368 : Nat := 1050644406059314946890055

theorem tailTrace_6138368 : CollatzResearch.WordTrace tailWord_6138368 prefixEnd_6138368 1050644406059314946890055 := by
  unfold tailWord_6138368
  simp only [CollatzResearch.WordTrace]
  refine ⟨111942336912874280318059879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149256449217165707090746505 111942336912874280318059879)
  ·
    refine ⟨167913505369311420477089819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111942336912874280318059879 167913505369311420477089819)
    ·
      refine ⟨251870258053967130715634729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167913505369311420477089819 251870258053967130715634729)
      ·
        refine ⟨188902693540475348036726047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251870258053967130715634729 188902693540475348036726047)
        ·
          refine ⟨283354040310713022055089071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188902693540475348036726047 283354040310713022055089071)
          ·
            refine ⟨425031060466069533082633607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283354040310713022055089071 425031060466069533082633607)
            ·
              refine ⟨637546590699104299623950411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425031060466069533082633607 637546590699104299623950411)
              ·
                refine ⟨956319886048656449435925617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637546590699104299623950411 956319886048656449435925617)
                ·
                  refine ⟨717239914536492337076944213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956319886048656449435925617 717239914536492337076944213)
                  ·
                    refine ⟨1050644406059314946890055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 717239914536492337076944213 1050644406059314946890055)
                    ·
                      rfl

theorem cell23_6138368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_6138368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138368 prefixEnd_6138368 := by exact prefixLift 6138368
  have htrace : WordTrace (prefixWord ++ tailWord_6138368) baseStart_6138368 baseEnd_6138368 := by
    simpa [prefixWord, tailWord_6138368, baseEnd_6138368] using wordTrace_append hprefix tailTrace_6138368
  have hstable : (prefixWord ++ tailWord_6138368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138368).length < 2 ^ (prefixWord ++ tailWord_6138368).sum := by decide
  have hdescent : baseEnd_6138368 < baseStart_6138368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138372 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 7]
def baseStart_6138372 : Nat := 118140960795 + 6138372 * 2 ^ 59
def prefixEnd_6138372 : Nat := 4983230072969 + 3 ^ 40 * 6138372 * 2
def baseEnd_6138372 : Nat := 350215030233395869446683

theorem tailTrace_6138372 : CollatzResearch.WordTrace tailWord_6138372 prefixEnd_6138372 350215030233395869446683 := by
  unfold tailWord_6138372
  simp only [CollatzResearch.WordTrace]
  refine ⟨111942409858867034659632685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149256546478489379546176913 111942409858867034659632685)
  ·
    refine ⟨41978403697075137997362257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111942409858867034659632685 41978403697075137997362257)
    ·
      refine ⟨31483802772806353498021693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41978403697075137997362257 31483802772806353498021693)
      ·
        refine ⟨11806426039802382561758135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31483802772806353498021693 11806426039802382561758135)
        ·
          refine ⟨17709639059703573842637203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806426039802382561758135 17709639059703573842637203)
          ·
            refine ⟨26564458589555360763955805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17709639059703573842637203 26564458589555360763955805)
            ·
              refine ⟨9961671971083260286483427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26564458589555360763955805 9961671971083260286483427)
              ·
                refine ⟨14942507956624890429725141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961671971083260286483427 14942507956624890429725141)
                ·
                  refine ⟨350215030233395869446683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14942507956624890429725141 350215030233395869446683)
                  ·
                    rfl

theorem cell23_6138372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_6138372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138372 prefixEnd_6138372 := by exact prefixLift 6138372
  have htrace : WordTrace (prefixWord ++ tailWord_6138372) baseStart_6138372 baseEnd_6138372 := by
    simpa [prefixWord, tailWord_6138372, baseEnd_6138372] using wordTrace_append hprefix tailTrace_6138372
  have hstable : (prefixWord ++ tailWord_6138372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138372).length < 2 ^ (prefixWord ++ tailWord_6138372).sum := by decide
  have hdescent : baseEnd_6138372 < baseStart_6138372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138405 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_6138405 : Nat := 118140960795 + 6138405 * 2 ^ 59
def prefixEnd_6138405 : Nat := 4983230072969 + 3 ^ 40 * 6138405 * 2
def baseEnd_6138405 : Nat := 3151952216962161195907495

theorem tailTrace_6138405 : CollatzResearch.WordTrace tailWord_6138405 prefixEnd_6138405 3151952216962161195907495 := by
  unfold tailWord_6138405
  simp only [CollatzResearch.WordTrace]
  refine ⟨223886023326614515955216669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149257348884409677303477779 223886023326614515955216669)
  ·
    refine ⟨83957258747480443483206251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223886023326614515955216669 83957258747480443483206251)
    ·
      refine ⟨125935888121220665224809377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83957258747480443483206251 125935888121220665224809377)
      ·
        refine ⟨94451916090915498918607033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125935888121220665224809377 94451916090915498918607033)
        ·
          refine ⟨70838937068186624188955275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94451916090915498918607033 70838937068186624188955275)
          ·
            refine ⟨106258405602279936283432913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70838937068186624188955275 106258405602279936283432913)
            ·
              refine ⟨79693804201709952212574685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106258405602279936283432913 79693804201709952212574685)
              ·
                refine ⟨29885176575641232079715507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79693804201709952212574685 29885176575641232079715507)
                ·
                  refine ⟨44827764863461848119573261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29885176575641232079715507 44827764863461848119573261)
                  ·
                    refine ⟨16810411823798193044839973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44827764863461848119573261 16810411823798193044839973)
                    ·
                      refine ⟨3151952216962161195907495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16810411823798193044839973 3151952216962161195907495)
                      ·
                        rfl

theorem cell23_6138405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_6138405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138405 prefixEnd_6138405 := by exact prefixLift 6138405
  have htrace : WordTrace (prefixWord ++ tailWord_6138405) baseStart_6138405 baseEnd_6138405 := by
    simpa [prefixWord, tailWord_6138405, baseEnd_6138405] using wordTrace_append hprefix tailTrace_6138405
  have hstable : (prefixWord ++ tailWord_6138405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138405).length < 2 ^ (prefixWord ++ tailWord_6138405).sum := by decide
  have hdescent : baseEnd_6138405 < baseStart_6138405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138425 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6138425 : Nat := 118140960795 + 6138425 * 2 ^ 59
def prefixEnd_6138425 : Nat := 4983230072969 + 3 ^ 40 * 6138425 * 2
def baseEnd_6138425 : Nat := 3151962486575251117657403

theorem tailTrace_6138425 : CollatzResearch.WordTrace tailWord_6138425 prefixEnd_6138425 3151962486575251117657403 := by
  unfold tailWord_6138425
  simp only [CollatzResearch.WordTrace]
  refine ⟨223886752786542059370944729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149257835191028039580629819 223886752786542059370944729)
  ·
    refine ⟨167915064589906544528208547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223886752786542059370944729 167915064589906544528208547)
    ·
      refine ⟨251872596884859816792312821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167915064589906544528208547 251872596884859816792312821)
      ·
        refine ⟨23613055957955607824279327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251872596884859816792312821 23613055957955607824279327)
        ·
          refine ⟨35419583936933411736418991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23613055957955607824279327 35419583936933411736418991)
          ·
            refine ⟨53129375905400117604628487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35419583936933411736418991 53129375905400117604628487)
            ·
              refine ⟨79694063858100176406942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53129375905400117604628487 79694063858100176406942731)
              ·
                refine ⟨119541095787150264610414097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79694063858100176406942731 119541095787150264610414097)
                ·
                  refine ⟨89655821840362698457810573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119541095787150264610414097 89655821840362698457810573)
                  ·
                    refine ⟨33620933190136011921678965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89655821840362698457810573 33620933190136011921678965)
                    ·
                      refine ⟨3151962486575251117657403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33620933190136011921678965 3151962486575251117657403)
                      ·
                        rfl

theorem cell23_6138425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6138425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138425 prefixEnd_6138425 := by exact prefixLift 6138425
  have htrace : WordTrace (prefixWord ++ tailWord_6138425) baseStart_6138425 baseEnd_6138425 := by
    simpa [prefixWord, tailWord_6138425, baseEnd_6138425] using wordTrace_append hprefix tailTrace_6138425
  have hstable : (prefixWord ++ tailWord_6138425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138425).length < 2 ^ (prefixWord ++ tailWord_6138425).sum := by decide
  have hdescent : baseEnd_6138425 < baseStart_6138425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138439 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_6138439 : Nat := 118140960795 + 6138439 * 2 ^ 59
def prefixEnd_6138439 : Nat := 4983230072969 + 3 ^ 40 * 6138439 * 2
def baseEnd_6138439 : Nat := 3151969675304414062882339

theorem tailTrace_6138439 : CollatzResearch.WordTrace tailWord_6138439 prefixEnd_6138439 3151969675304414062882339 := by
  unfold tailWord_6138439
  simp only [CollatzResearch.WordTrace]
  refine ⟨223887263408491339761954371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149258175605660893174636247 223887263408491339761954371)
  ·
    refine ⟨335830895112737009642931557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223887263408491339761954371 335830895112737009642931557)
    ·
      refine ⟨62968292833638189308049667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335830895112737009642931557 62968292833638189308049667)
      ·
        refine ⟨94452439250457283962074501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62968292833638189308049667 94452439250457283962074501)
        ·
          refine ⟨17709832359460740742888969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94452439250457283962074501 17709832359460740742888969)
          ·
            refine ⟨13282374269595555557166727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17709832359460740742888969 13282374269595555557166727)
            ·
              refine ⟨19923561404393333335750091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282374269595555557166727 19923561404393333335750091)
              ·
                refine ⟨29885342106590000003625137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19923561404393333335750091 29885342106590000003625137)
                ·
                  refine ⟨22414006579942500002718853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29885342106590000003625137 22414006579942500002718853)
                  ·
                    refine ⟨4202626233739218750509785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22414006579942500002718853 4202626233739218750509785)
                    ·
                      refine ⟨3151969675304414062882339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202626233739218750509785 3151969675304414062882339)
                      ·
                        rfl

theorem cell23_6138439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_6138439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138439 prefixEnd_6138439 := by exact prefixLift 6138439
  have htrace : WordTrace (prefixWord ++ tailWord_6138439) baseStart_6138439 baseEnd_6138439 := by
    simpa [prefixWord, tailWord_6138439, baseEnd_6138439] using wordTrace_append hprefix tailTrace_6138439
  have hstable : (prefixWord ++ tailWord_6138439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138439).length < 2 ^ (prefixWord ++ tailWord_6138439).sum := by decide
  have hdescent : baseEnd_6138439 < baseStart_6138439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138475 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 5, 5]
def baseStart_6138475 : Nat := 118140960795 + 6138475 * 2 ^ 59
def prefixEnd_6138475 : Nat := 4983230072969 + 3 ^ 40 * 6138475 * 2
def baseEnd_6138475 : Nat := 1050662720202658640677391

theorem tailTrace_6138475 : CollatzResearch.WordTrace tailWord_6138475 prefixEnd_6138475 1050662720202658640677391 := by
  unfold tailWord_6138475
  simp only [CollatzResearch.WordTrace]
  refine ⟨223888576436360917910264879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149259050957573945273509919 223888576436360917910264879)
  ·
    refine ⟨335832864654541376865397319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223888576436360917910264879 335832864654541376865397319)
    ·
      refine ⟨503749296981812065298095979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335832864654541376865397319 503749296981812065298095979)
      ·
        refine ⟨755623945472718097947143969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503749296981812065298095979 755623945472718097947143969)
        ·
          refine ⟨566717959104538573460357977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755623945472718097947143969 566717959104538573460357977)
          ·
            refine ⟨425038469328403930095268483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566717959104538573460357977 425038469328403930095268483)
            ·
              refine ⟨637557703992605895142902725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425038469328403930095268483 637557703992605895142902725)
              ·
                refine ⟨119542069498613605339294261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637557703992605895142902725 119542069498613605339294261)
                ·
                  refine ⟨11207069015495025500558837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119542069498613605339294261 11207069015495025500558837)
                  ·
                    refine ⟨1050662720202658640677391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11207069015495025500558837 1050662720202658640677391)
                    ·
                      rfl

theorem cell23_6138475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 5].length) (baseStart_6138475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138475 prefixEnd_6138475 := by exact prefixLift 6138475
  have htrace : WordTrace (prefixWord ++ tailWord_6138475) baseStart_6138475 baseEnd_6138475 := by
    simpa [prefixWord, tailWord_6138475, baseEnd_6138475] using wordTrace_append hprefix tailTrace_6138475
  have hstable : (prefixWord ++ tailWord_6138475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138475).length < 2 ^ (prefixWord ++ tailWord_6138475).sum := by decide
  have hdescent : baseEnd_6138475 < baseStart_6138475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138489 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_6138489 : Nat := 118140960795 + 6138489 * 2 ^ 59
def prefixEnd_6138489 : Nat := 4983230072969 + 3 ^ 40 * 6138489 * 2
def baseEnd_6138489 : Nat := 3151995349337138867257109

theorem tailTrace_6138489 : CollatzResearch.WordTrace tailWord_6138489 prefixEnd_6138489 3151995349337138867257109 := by
  unfold tailWord_6138489
  simp only [CollatzResearch.WordTrace]
  refine ⟨223889087058310198301274521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149259391372206798867516347 223889087058310198301274521)
  ·
    refine ⟨167916815293732648725955891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223889087058310198301274521 167916815293732648725955891)
    ·
      refine ⟨251875222940598973088933837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167916815293732648725955891 251875222940598973088933837)
      ·
        refine ⟨94453208602724614908350189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251875222940598973088933837 94453208602724614908350189)
        ·
          refine ⟨35419953226021730590631321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94453208602724614908350189 35419953226021730590631321)
          ·
            refine ⟨26564964919516297942973491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35419953226021730590631321 26564964919516297942973491)
            ·
              refine ⟨39847447379274446914460237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26564964919516297942973491 39847447379274446914460237)
              ·
                refine ⟨14942792767227917592922589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39847447379274446914460237 14942792767227917592922589)
                ·
                  refine ⟨5603547287710469097345971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14942792767227917592922589 5603547287710469097345971)
                  ·
                    refine ⟨8405320931565703646018957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603547287710469097345971 8405320931565703646018957)
                    ·
                      refine ⟨3151995349337138867257109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405320931565703646018957 3151995349337138867257109)
                      ·
                        rfl

theorem cell23_6138489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_6138489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138489 prefixEnd_6138489 := by exact prefixLift 6138489
  have htrace : WordTrace (prefixWord ++ tailWord_6138489) baseStart_6138489 baseEnd_6138489 := by
    simpa [prefixWord, tailWord_6138489, baseEnd_6138489] using wordTrace_append hprefix tailTrace_6138489
  have hstable : (prefixWord ++ tailWord_6138489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138489).length < 2 ^ (prefixWord ++ tailWord_6138489).sum := by decide
  have hdescent : baseEnd_6138489 < baseStart_6138489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138495 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_6138495 : Nat := 118140960795 + 6138495 * 2 ^ 59
def prefixEnd_6138495 : Nat := 4983230072969 + 3 ^ 40 * 6138495 * 2
def baseEnd_6138495 : Nat := 3151998430221065843782081

theorem tailTrace_6138495 : CollatzResearch.WordTrace tailWord_6138495 prefixEnd_6138495 3151998430221065843782081 := by
  unfold tailWord_6138495
  simp only [CollatzResearch.WordTrace]
  refine ⟨223889305896288461325992939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149259537264192307550661959 223889305896288461325992939)
  ·
    refine ⟨335833958844432691988989409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223889305896288461325992939 335833958844432691988989409)
    ·
      refine ⟨251875469133324518991742057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335833958844432691988989409 251875469133324518991742057)
      ·
        refine ⟨188906601849993389243806543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251875469133324518991742057 188906601849993389243806543)
        ·
          refine ⟨283359902774990083865709815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188906601849993389243806543 283359902774990083865709815)
          ·
            refine ⟨425039854162485125798564723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283359902774990083865709815 425039854162485125798564723)
            ·
              refine ⟨637559781243727688697847085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425039854162485125798564723 637559781243727688697847085)
              ·
                refine ⟨239084917966397883261692657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637559781243727688697847085 239084917966397883261692657)
                ·
                  refine ⟨179313688474798412446269493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239084917966397883261692657 179313688474798412446269493)
                  ·
                    refine ⟨16810658294512351166837765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179313688474798412446269493 16810658294512351166837765)
                    ·
                      refine ⟨3151998430221065843782081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16810658294512351166837765 3151998430221065843782081)
                      ·
                        rfl

theorem cell23_6138495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_6138495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138495 prefixEnd_6138495 := by exact prefixLift 6138495
  have htrace : WordTrace (prefixWord ++ tailWord_6138495) baseStart_6138495 baseEnd_6138495 := by
    simpa [prefixWord, tailWord_6138495, baseEnd_6138495] using wordTrace_append hprefix tailTrace_6138495
  have hstable : (prefixWord ++ tailWord_6138495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138495).length < 2 ^ (prefixWord ++ tailWord_6138495).sum := by decide
  have hdescent : baseEnd_6138495 < baseStart_6138495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138516 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_6138516 : Nat := 118140960795 + 6138516 * 2 ^ 59
def prefixEnd_6138516 : Nat := 4983230072969 + 3 ^ 40 * 6138516 * 2
def baseEnd_6138516 : Nat := 3152009213314810261619485

theorem tailTrace_6138516 : CollatzResearch.WordTrace tailWord_6138516 prefixEnd_6138516 3152009213314810261619485 := by
  unfold tailWord_6138516
  simp only [CollatzResearch.WordTrace]
  refine ⟨111945035914606190956253701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149260047886141587941671601 111945035914606190956253701)
  ·
    refine ⟨20989694233988660804297569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111945035914606190956253701 20989694233988660804297569)
    ·
      refine ⟨15742270675491495603223177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20989694233988660804297569 15742270675491495603223177)
      ·
        refine ⟨11806703006618621702417383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15742270675491495603223177 11806703006618621702417383)
        ·
          refine ⟨17710054509927932553626075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806703006618621702417383 17710054509927932553626075)
          ·
            refine ⟨26565081764891898830439113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710054509927932553626075 26565081764891898830439113)
            ·
              refine ⟨19923811323668924122829335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26565081764891898830439113 19923811323668924122829335)
              ·
                refine ⟨29885716985503386184244003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19923811323668924122829335 29885716985503386184244003)
                ·
                  refine ⟨44828575478255079276366005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29885716985503386184244003 44828575478255079276366005)
                  ·
                    refine ⟨4202678951086413682159313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44828575478255079276366005 4202678951086413682159313)
                    ·
                      refine ⟨3152009213314810261619485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202678951086413682159313 3152009213314810261619485)
                      ·
                        rfl

theorem cell23_6138516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_6138516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138516 prefixEnd_6138516 := by exact prefixLift 6138516
  have htrace : WordTrace (prefixWord ++ tailWord_6138516) baseStart_6138516 baseEnd_6138516 := by
    simpa [prefixWord, tailWord_6138516, baseEnd_6138516] using wordTrace_append hprefix tailTrace_6138516
  have hstable : (prefixWord ++ tailWord_6138516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138516).length < 2 ^ (prefixWord ++ tailWord_6138516).sum := by decide
  have hdescent : baseEnd_6138516 < baseStart_6138516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138549 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6138549 : Nat := 118140960795 + 6138549 * 2 ^ 59
def prefixEnd_6138549 : Nat := 4983230072969 + 3 ^ 40 * 6138549 * 2
def baseEnd_6138549 : Nat := 3152026158176408632506833

theorem tailTrace_6138549 : CollatzResearch.WordTrace tailWord_6138549 prefixEnd_6138549 3152026158176408632506833 := by
  unfold tailWord_6138549
  simp only [CollatzResearch.WordTrace]
  refine ⟨223891275438092828548458701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149260850292061885698972467 223891275438092828548458701)
  ·
    refine ⟨83959228289284810705672013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223891275438092828548458701 83959228289284810705672013)
    ·
      refine ⟨31484710608481804014627005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83959228289284810705672013 31484710608481804014627005)
      ·
        refine ⟨11806766478180676505485127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31484710608481804014627005 11806766478180676505485127)
        ·
          refine ⟨17710149717271014758227691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806766478180676505485127 17710149717271014758227691)
          ·
            refine ⟨26565224575906522137341537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710149717271014758227691 26565224575906522137341537)
            ·
              refine ⟨19923918431929891603006153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26565224575906522137341537 19923918431929891603006153)
              ·
                refine ⟨14942938823947418702254615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19923918431929891603006153 14942938823947418702254615)
                ·
                  refine ⟨22414408235921128053381923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14942938823947418702254615 22414408235921128053381923)
                  ·
                    refine ⟨33621612353881692080072885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22414408235921128053381923 33621612353881692080072885)
                    ·
                      refine ⟨3152026158176408632506833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33621612353881692080072885 3152026158176408632506833)
                      ·
                        rfl

theorem cell23_6138549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6138549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138549 prefixEnd_6138549 := by exact prefixLift 6138549
  have htrace : WordTrace (prefixWord ++ tailWord_6138549) baseStart_6138549 baseEnd_6138549 := by
    simpa [prefixWord, tailWord_6138549, baseEnd_6138549] using wordTrace_append hprefix tailTrace_6138549
  have hstable : (prefixWord ++ tailWord_6138549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138549).length < 2 ^ (prefixWord ++ tailWord_6138549).sum := by decide
  have hdescent : baseEnd_6138549 < baseStart_6138549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138596 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_6138596 : Nat := 118140960795 + 6138596 * 2 ^ 59
def prefixEnd_6138596 : Nat := 4983230072969 + 3 ^ 40 * 6138596 * 2
def baseEnd_6138596 : Nat := 3152050291767169948619117

theorem tailTrace_6138596 : CollatzResearch.WordTrace tailWord_6138596 prefixEnd_6138596 3152050291767169948619117 := by
  unfold tailWord_6138596
  simp only [CollatzResearch.WordTrace]
  refine ⟨111946494834461277787709821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149261993112615037050279761 111946494834461277787709821)
  ·
    refine ⟨41979935562922979170391183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111946494834461277787709821 41979935562922979170391183)
    ·
      refine ⟨62969903344384468755586775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41979935562922979170391183 62969903344384468755586775)
      ·
        refine ⟨94454855016576703133380163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62969903344384468755586775 94454855016576703133380163)
        ·
          refine ⟨141682282524865054700070245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94454855016576703133380163 141682282524865054700070245)
          ·
            refine ⟨26565427973412197756263171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141682282524865054700070245 26565427973412197756263171)
            ·
              refine ⟨39848141960118296634394757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26565427973412197756263171 39848141960118296634394757)
              ·
                refine ⟨7471526617522180618949017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39848141960118296634394757 7471526617522180618949017)
                ·
                  refine ⟨5603644963141635464211763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7471526617522180618949017 5603644963141635464211763)
                  ·
                    refine ⟨8405467444712453196317645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603644963141635464211763 8405467444712453196317645)
                    ·
                      refine ⟨3152050291767169948619117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405467444712453196317645 3152050291767169948619117)
                      ·
                        rfl

theorem cell23_6138596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_6138596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138596 prefixEnd_6138596 := by exact prefixLift 6138596
  have htrace : WordTrace (prefixWord ++ tailWord_6138596) baseStart_6138596 baseEnd_6138596 := by
    simpa [prefixWord, tailWord_6138596, baseEnd_6138596] using wordTrace_append hprefix tailTrace_6138596
  have hstable : (prefixWord ++ tailWord_6138596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138596).length < 2 ^ (prefixWord ++ tailWord_6138596).sum := by decide
  have hdescent : baseEnd_6138596 < baseStart_6138596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138597 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6138597 : Nat := 118140960795 + 6138597 * 2 ^ 59
def prefixEnd_6138597 : Nat := 4983230072969 + 3 ^ 40 * 6138597 * 2
def baseEnd_6138597 : Nat := 3152050805247824444706613

theorem tailTrace_6138597 : CollatzResearch.WordTrace tailWord_6138597 prefixEnd_6138597 3152050805247824444706613 := by
  unfold tailWord_6138597
  simp only [CollatzResearch.WordTrace]
  refine ⟨223893026141918932746206045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149262017427945955164137363 223893026141918932746206045)
  ·
    refine ⟨83959884803219599779827267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223893026141918932746206045 83959884803219599779827267)
    ·
      refine ⟨125939827204829399669740901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83959884803219599779827267 125939827204829399669740901)
      ·
        refine ⟨23613717600905512438076419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125939827204829399669740901 23613717600905512438076419)
        ·
          refine ⟨35420576401358268657114629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23613717600905512438076419 35420576401358268657114629)
          ·
            refine ⟨6641358075254675373208993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35420576401358268657114629 6641358075254675373208993)
            ·
              refine ⟨4981018556441006529906745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6641358075254675373208993 4981018556441006529906745)
              ·
                refine ⟨3735763917330754897430059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981018556441006529906745 3735763917330754897430059)
                ·
                  refine ⟨5603645875996132346145089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735763917330754897430059 5603645875996132346145089)
                  ·
                    refine ⟨4202734406997099259608817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5603645875996132346145089 4202734406997099259608817)
                    ·
                      refine ⟨3152050805247824444706613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202734406997099259608817 3152050805247824444706613)
                      ·
                        rfl

theorem cell23_6138597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6138597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138597 prefixEnd_6138597 := by exact prefixLift 6138597
  have htrace : WordTrace (prefixWord ++ tailWord_6138597) baseStart_6138597 baseEnd_6138597 := by
    simpa [prefixWord, tailWord_6138597, baseEnd_6138597] using wordTrace_append hprefix tailTrace_6138597
  have hstable : (prefixWord ++ tailWord_6138597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138597).length < 2 ^ (prefixWord ++ tailWord_6138597).sum := by decide
  have hdescent : baseEnd_6138597 < baseStart_6138597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138606 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_6138606 : Nat := 118140960795 + 6138606 * 2 ^ 59
def prefixEnd_6138606 : Nat := 4983230072969 + 3 ^ 40 * 6138606 * 2
def baseEnd_6138606 : Nat := 3152055426573714909494071

theorem tailTrace_6138606 : CollatzResearch.WordTrace tailWord_6138606 prefixEnd_6138606 3152055426573714909494071 := by
  unfold tailWord_6138606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986669299860790910410459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149262236265924218188855781 27986669299860790910410459)
  ·
    refine ⟨41980003949791186365615689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986669299860790910410459 41980003949791186365615689)
    ·
      refine ⟨31485002962343389774211767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41980003949791186365615689 31485002962343389774211767)
      ·
        refine ⟨47227504443515084661317651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31485002962343389774211767 47227504443515084661317651)
        ·
          refine ⟨70841256665272626991976477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47227504443515084661317651 70841256665272626991976477)
          ·
            refine ⟨26565471249477235121991179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70841256665272626991976477 26565471249477235121991179)
            ·
              refine ⟨39848206874215852682986769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26565471249477235121991179 39848206874215852682986769)
              ·
                refine ⟨29886155155661889512240077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39848206874215852682986769 29886155155661889512240077)
                ·
                  refine ⟨11207308183373208567090029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29886155155661889512240077 11207308183373208567090029)
                  ·
                    refine ⟨4202740568764953212658761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11207308183373208567090029 4202740568764953212658761)
                    ·
                      refine ⟨3152055426573714909494071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202740568764953212658761 3152055426573714909494071)
                      ·
                        rfl

theorem cell23_6138606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_6138606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138606 prefixEnd_6138606 := by exact prefixLift 6138606
  have htrace : WordTrace (prefixWord ++ tailWord_6138606) baseStart_6138606 baseEnd_6138606 := by
    simpa [prefixWord, tailWord_6138606, baseEnd_6138606] using wordTrace_append hprefix tailTrace_6138606
  have hstable : (prefixWord ++ tailWord_6138606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138606).length < 2 ^ (prefixWord ++ tailWord_6138606).sum := by decide
  have hdescent : baseEnd_6138606 < baseStart_6138606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138636 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_6138636 : Nat := 118140960795 + 6138636 * 2 ^ 59
def prefixEnd_6138636 : Nat := 4983230072969 + 3 ^ 40 * 6138636 * 2
def baseEnd_6138636 : Nat := 3152070830993349792118933

theorem tailTrace_6138636 : CollatzResearch.WordTrace tailWord_6138636 prefixEnd_6138636 3152070830993349792118933 := by
  unfold tailWord_6138636
  simp only [CollatzResearch.WordTrace]
  refine ⟨111947224294388821203437881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149262965725851761604583841 111947224294388821203437881)
  ·
    refine ⟨83960418220791615902578411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111947224294388821203437881 83960418220791615902578411)
    ·
      refine ⟨125940627331187423853867617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83960418220791615902578411 125940627331187423853867617)
      ·
        refine ⟨94455470498390567890400713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125940627331187423853867617 94455470498390567890400713)
        ·
          refine ⟨70841602873792925917800535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94455470498390567890400713 70841602873792925917800535)
          ·
            refine ⟨106262404310689388876700803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70841602873792925917800535 106262404310689388876700803)
            ·
              refine ⟨159393606466034083315051205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106262404310689388876700803 159393606466034083315051205)
              ·
                refine ⟨29886301212381390621572101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159393606466034083315051205 29886301212381390621572101)
                ·
                  refine ⟨5603681477321510741544769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29886301212381390621572101 5603681477321510741544769)
                  ·
                    refine ⟨4202761107991133056158577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5603681477321510741544769 4202761107991133056158577)
                    ·
                      refine ⟨3152070830993349792118933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202761107991133056158577 3152070830993349792118933)
                      ·
                        rfl

theorem cell23_6138636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_6138636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138636 prefixEnd_6138636 := by exact prefixLift 6138636
  have htrace : WordTrace (prefixWord ++ tailWord_6138636) baseStart_6138636 baseEnd_6138636 := by
    simpa [prefixWord, tailWord_6138636, baseEnd_6138636] using wordTrace_append hprefix tailTrace_6138636
  have hstable : (prefixWord ++ tailWord_6138636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138636).length < 2 ^ (prefixWord ++ tailWord_6138636).sum := by decide
  have hdescent : baseEnd_6138636 < baseStart_6138636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138670 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6138670 : Nat := 118140960795 + 6138670 * 2 ^ 59
def prefixEnd_6138670 : Nat := 4983230072969 + 3 ^ 40 * 6138670 * 2
def baseEnd_6138670 : Nat := 3152088289335602659093777

theorem tailTrace_6138670 : CollatzResearch.WordTrace tailWord_6138670 prefixEnd_6138670 3152088289335602659093777 := by
  unfold tailWord_6138670
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986961083831808276701683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149263792447102977475742309 27986961083831808276701683)
  ·
    refine ⟨41980441625747712415052525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986961083831808276701683 41980441625747712415052525)
    ·
      refine ⟨15742665609655392155644697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41980441625747712415052525 15742665609655392155644697)
      ·
        refine ⟨11806999207241544116733523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15742665609655392155644697 11806999207241544116733523)
        ·
          refine ⟨17710498810862316175100285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806999207241544116733523 17710498810862316175100285)
          ·
            refine ⟨6641437054073368565662607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17710498810862316175100285 6641437054073368565662607)
            ·
              refine ⟨9962155581110052848493911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641437054073368565662607 9962155581110052848493911)
              ·
                refine ⟨14943233371665079272740867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962155581110052848493911 14943233371665079272740867)
                ·
                  refine ⟨22414850057497618909111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14943233371665079272740867 22414850057497618909111301)
                  ·
                    refine ⟨4202784385780803545458369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22414850057497618909111301 4202784385780803545458369)
                    ·
                      refine ⟨3152088289335602659093777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202784385780803545458369 3152088289335602659093777)
                      ·
                        rfl

theorem cell23_6138670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6138670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138670 prefixEnd_6138670 := by exact prefixLift 6138670
  have htrace : WordTrace (prefixWord ++ tailWord_6138670) baseStart_6138670 baseEnd_6138670 := by
    simpa [prefixWord, tailWord_6138670, baseEnd_6138670] using wordTrace_append hprefix tailTrace_6138670
  have hstable : (prefixWord ++ tailWord_6138670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138670).length < 2 ^ (prefixWord ++ tailWord_6138670).sum := by decide
  have hdescent : baseEnd_6138670 < baseStart_6138670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138716 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6138716 : Nat := 118140960795 + 6138716 * 2 ^ 59
def prefixEnd_6138716 : Nat := 4983230072969 + 3 ^ 40 * 6138716 * 2
def baseEnd_6138716 : Nat := 3152111909445709479118565

theorem tailTrace_6138716 : CollatzResearch.WordTrace tailWord_6138716 prefixEnd_6138716 3152111909445709479118565 := by
  unfold tailWord_6138716
  simp only [CollatzResearch.WordTrace]
  refine ⟨111948683214243908034894001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149264910952325210713192001 111948683214243908034894001)
  ·
    refine ⟨83961512410682931026170501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111948683214243908034894001 83961512410682931026170501)
    ·
      refine ⟨15742783577003049567406969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83961512410682931026170501 15742783577003049567406969)
      ·
        refine ⟨11807087682752287175555227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15742783577003049567406969 11807087682752287175555227)
        ·
          refine ⟨17710631524128430763332841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807087682752287175555227 17710631524128430763332841)
          ·
            refine ⟨13282973643096323072499631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17710631524128430763332841 13282973643096323072499631)
            ·
              refine ⟨19924460464644484608749447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282973643096323072499631 19924460464644484608749447)
              ·
                refine ⟨29886690696966726913124171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19924460464644484608749447 29886690696966726913124171)
                ·
                  refine ⟨44830036045450090369686257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29886690696966726913124171 44830036045450090369686257)
                  ·
                    refine ⟨33622527034087567777264693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44830036045450090369686257 33622527034087567777264693)
                    ·
                      refine ⟨3152111909445709479118565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33622527034087567777264693 3152111909445709479118565)
                      ·
                        rfl

theorem cell23_6138716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6138716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138716 prefixEnd_6138716 := by exact prefixLift 6138716
  have htrace : WordTrace (prefixWord ++ tailWord_6138716) baseStart_6138716 baseEnd_6138716 := by
    simpa [prefixWord, tailWord_6138716, baseEnd_6138716] using wordTrace_append hprefix tailTrace_6138716
  have hstable : (prefixWord ++ tailWord_6138716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138716).length < 2 ^ (prefixWord ++ tailWord_6138716).sum := by decide
  have hdescent : baseEnd_6138716 < baseStart_6138716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138797 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6138797 : Nat := 118140960795 + 6138797 * 2 ^ 59
def prefixEnd_6138797 : Nat := 4983230072969 + 3 ^ 40 * 6138797 * 2
def baseEnd_6138797 : Nat := 3152153501378723662205693

theorem tailTrace_6138797 : CollatzResearch.WordTrace tailWord_6138797 prefixEnd_6138797 3152153501378723662205693 := by
  unfold tailWord_6138797
  simp only [CollatzResearch.WordTrace]
  refine ⟨223900320741194366903486645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149266880494129577935657763 223900320741194366903486645)
  ·
    refine ⟨20990655069486971897201873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223900320741194366903486645 20990655069486971897201873)
    ·
      refine ⟨15742991302115228922901405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20990655069486971897201873 15742991302115228922901405)
      ·
        refine ⟨5903621738293210846088027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15742991302115228922901405 5903621738293210846088027)
        ·
          refine ⟨8855432607439816269132041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903621738293210846088027 8855432607439816269132041)
          ·
            refine ⟨6641574455579862201849031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8855432607439816269132041 6641574455579862201849031)
            ·
              refine ⟨9962361683369793302773547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641574455579862201849031 9962361683369793302773547)
              ·
                refine ⟨14943542525054689954160321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962361683369793302773547 14943542525054689954160321)
                ·
                  refine ⟨11207656893791017465620241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14943542525054689954160321 11207656893791017465620241)
                  ·
                    refine ⟨8405742670343263099215181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11207656893791017465620241 8405742670343263099215181)
                    ·
                      refine ⟨3152153501378723662205693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405742670343263099215181 3152153501378723662205693)
                      ·
                        rfl

theorem cell23_6138797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6138797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138797 prefixEnd_6138797 := by exact prefixLift 6138797
  have htrace : WordTrace (prefixWord ++ tailWord_6138797) baseStart_6138797 baseEnd_6138797 := by
    simpa [prefixWord, tailWord_6138797, baseEnd_6138797] using wordTrace_append hprefix tailTrace_6138797
  have hstable : (prefixWord ++ tailWord_6138797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138797).length < 2 ^ (prefixWord ++ tailWord_6138797).sum := by decide
  have hdescent : baseEnd_6138797 < baseStart_6138797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138810 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_6138810 : Nat := 118140960795 + 6138810 * 2 ^ 59
def prefixEnd_6138810 : Nat := 4983230072969 + 3 ^ 40 * 6138810 * 2
def baseEnd_6138810 : Nat := 3152160176627232111343133

theorem tailTrace_6138810 : CollatzResearch.WordTrace tailWord_6138810 prefixEnd_6138810 3152160176627232111343133 := by
  unfold tailWord_6138810
  simp only [CollatzResearch.WordTrace]
  refine ⟨55975198722536817530927471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149267196593431513415806589 55975198722536817530927471)
  ·
    refine ⟨83962798083805226296391207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55975198722536817530927471 83962798083805226296391207)
    ·
      refine ⟨125944197125707839444586811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83962798083805226296391207 125944197125707839444586811)
      ·
        refine ⟨188916295688561759166880217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125944197125707839444586811 188916295688561759166880217)
        ·
          refine ⟨141687221766421319375160163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188916295688561759166880217 141687221766421319375160163)
          ·
            refine ⟨212530832649631979062740245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141687221766421319375160163 212530832649631979062740245)
            ·
              refine ⟨9962382780451499018565949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212530832649631979062740245 9962382780451499018565949)
              ·
                refine ⟨3735893542669312131962231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9962382780451499018565949 3735893542669312131962231)
                ·
                  refine ⟨5603840314003968197943347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735893542669312131962231 5603840314003968197943347)
                  ·
                    refine ⟨8405760471005952296915021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603840314003968197943347 8405760471005952296915021)
                    ·
                      refine ⟨3152160176627232111343133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405760471005952296915021 3152160176627232111343133)
                      ·
                        rfl

theorem cell23_6138810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_6138810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138810 prefixEnd_6138810 := by exact prefixLift 6138810
  have htrace : WordTrace (prefixWord ++ tailWord_6138810) baseStart_6138810 baseEnd_6138810 := by
    simpa [prefixWord, tailWord_6138810, baseEnd_6138810] using wordTrace_append hprefix tailTrace_6138810
  have hstable : (prefixWord ++ tailWord_6138810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138810).length < 2 ^ (prefixWord ++ tailWord_6138810).sum := by decide
  have hdescent : baseEnd_6138810 < baseStart_6138810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138813 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_6138813 : Nat := 118140960795 + 6138813 * 2 ^ 59
def prefixEnd_6138813 : Nat := 4983230072969 + 3 ^ 40 * 6138813 * 2
def baseEnd_6138813 : Nat := 1050720572356398533201873

theorem tailTrace_6138813 : CollatzResearch.WordTrace tailWord_6138813 prefixEnd_6138813 1050720572356398533201873 := by
  unfold tailWord_6138813
  simp only [CollatzResearch.WordTrace]
  refine ⟨223900904309136401636069093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149267269539424267757379395 223900904309136401636069093)
  ·
    refine ⟨41981419557963075306762955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223900904309136401636069093 41981419557963075306762955)
    ·
      refine ⟨62972129336944612960144433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41981419557963075306762955 62972129336944612960144433)
      ·
        refine ⟨47229097002708459720108325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62972129336944612960144433 47229097002708459720108325)
        ·
          refine ⟨8855455688007836197520311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47229097002708459720108325 8855455688007836197520311)
          ·
            refine ⟨13283183532011754296280467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8855455688007836197520311 13283183532011754296280467)
            ·
              refine ⟨19924775298017631444420701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283183532011754296280467 19924775298017631444420701)
              ·
                refine ⟨7471790736756611791657763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19924775298017631444420701 7471790736756611791657763)
                ·
                  refine ⟨11207686105134917687486645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471790736756611791657763 11207686105134917687486645)
                  ·
                    refine ⟨1050720572356398533201873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11207686105134917687486645 1050720572356398533201873)
                    ·
                      rfl

theorem cell23_6138813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_6138813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138813 prefixEnd_6138813 := by exact prefixLift 6138813
  have htrace : WordTrace (prefixWord ++ tailWord_6138813) baseStart_6138813 baseEnd_6138813 := by
    simpa [prefixWord, tailWord_6138813, baseEnd_6138813] using wordTrace_append hprefix tailTrace_6138813
  have hstable : (prefixWord ++ tailWord_6138813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138813).length < 2 ^ (prefixWord ++ tailWord_6138813).sum := by decide
  have hdescent : baseEnd_6138813 < baseStart_6138813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138836 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6138836 : Nat := 118140960795 + 6138836 * 2 ^ 59
def prefixEnd_6138836 : Nat := 4983230072969 + 3 ^ 40 * 6138836 * 2
def baseEnd_6138836 : Nat := 3152173527124249009618013

theorem tailTrace_6138836 : CollatzResearch.WordTrace tailWord_6138836 prefixEnd_6138836 3152173527124249009618013 := by
  unfold tailWord_6138836
  simp only [CollatzResearch.WordTrace]
  refine ⟨111950871594026538282078181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149267828792035384376104241 111950871594026538282078181)
  ·
    refine ⟨20990788423879975927889659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111950871594026538282078181 20990788423879975927889659)
    ·
      refine ⟨31486182635819963891834489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20990788423879975927889659 31486182635819963891834489)
      ·
        refine ⟨23614636976864972918875867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31486182635819963891834489 23614636976864972918875867)
        ·
          refine ⟨35421955465297459378313801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23614636976864972918875867 35421955465297459378313801)
          ·
            refine ⟨26566466598973094533735351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35421955465297459378313801 26566466598973094533735351)
            ·
              refine ⟨39849699898459641800603027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26566466598973094533735351 39849699898459641800603027)
              ·
                refine ⟨59774549847689462700904541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39849699898459641800603027 59774549847689462700904541)
                ·
                  refine ⟨22415456192883548512839203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59774549847689462700904541 22415456192883548512839203)
                  ·
                    refine ⟨33623184289325322769258805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22415456192883548512839203 33623184289325322769258805)
                    ·
                      refine ⟨3152173527124249009618013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33623184289325322769258805 3152173527124249009618013)
                      ·
                        rfl

theorem cell23_6138836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6138836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138836 prefixEnd_6138836 := by exact prefixLift 6138836
  have htrace : WordTrace (prefixWord ++ tailWord_6138836) baseStart_6138836 baseEnd_6138836 := by
    simpa [prefixWord, tailWord_6138836, baseEnd_6138836] using wordTrace_append hprefix tailTrace_6138836
  have hstable : (prefixWord ++ tailWord_6138836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138836).length < 2 ^ (prefixWord ++ tailWord_6138836).sum := by decide
  have hdescent : baseEnd_6138836 < baseStart_6138836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138850 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6138850 : Nat := 118140960795 + 6138850 * 2 ^ 59
def prefixEnd_6138850 : Nat := 4983230072969 + 3 ^ 40 * 6138850 * 2
def baseEnd_6138850 : Nat := 3152180715853411954842949

theorem tailTrace_6138850 : CollatzResearch.WordTrace tailWord_6138850 prefixEnd_6138850 3152180715853411954842949 := by
  unfold tailWord_6138850
  simp only [CollatzResearch.WordTrace]
  refine ⟨55975563452500589238791501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149268169206668237970110669 55975563452500589238791501)
  ·
    refine ⟨20990836294687720964546813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55975563452500589238791501 20990836294687720964546813)
    ·
      refine ⟨7871563610507895361705055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20990836294687720964546813 7871563610507895361705055)
      ·
        refine ⟨11807345415761843042557583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7871563610507895361705055 11807345415761843042557583)
        ·
          refine ⟨17711018123642764563836375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807345415761843042557583 17711018123642764563836375)
          ·
            refine ⟨26566527185464146845754563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17711018123642764563836375 26566527185464146845754563)
            ·
              refine ⟨39849790778196220268631845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26566527185464146845754563 39849790778196220268631845)
              ·
                refine ⟨7471835770911791300368471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39849790778196220268631845 7471835770911791300368471)
                ·
                  refine ⟨11207753656367686950552707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471835770911791300368471 11207753656367686950552707)
                  ·
                    refine ⟨16811630484551530425829061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11207753656367686950552707 16811630484551530425829061)
                    ·
                      refine ⟨3152180715853411954842949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16811630484551530425829061 3152180715853411954842949)
                      ·
                        rfl

theorem cell23_6138850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6138850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138850 prefixEnd_6138850 := by exact prefixLift 6138850
  have htrace : WordTrace (prefixWord ++ tailWord_6138850) baseStart_6138850 baseEnd_6138850 := by
    simpa [prefixWord, tailWord_6138850, baseEnd_6138850] using wordTrace_append hprefix tailTrace_6138850
  have hstable : (prefixWord ++ tailWord_6138850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138850).length < 2 ^ (prefixWord ++ tailWord_6138850).sum := by decide
  have hdescent : baseEnd_6138850 < baseStart_6138850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138856 : List Nat := [2, 1, 4, 1, 1, 1, 6, 7]
def baseStart_6138856 : Nat := 118140960795 + 6138856 * 2 ^ 59
def prefixEnd_6138856 : Nat := 4983230072969 + 3 ^ 40 * 6138856 * 2
def baseEnd_6138856 : Nat := 116747548027308849309923

theorem tailTrace_6138856 : CollatzResearch.WordTrace tailWord_6138856 prefixEnd_6138856 116747548027308849309923 := by
  unfold tailWord_6138856
  simp only [CollatzResearch.WordTrace]
  refine ⟨111951236323990309989942211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149268315098653746653256281 111951236323990309989942211)
  ·
    refine ⟨167926854485985464984913317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111951236323990309989942211 167926854485985464984913317)
    ·
      refine ⟨31486285216122274684671247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167926854485985464984913317 31486285216122274684671247)
      ·
        refine ⟨47229427824183412027006871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31486285216122274684671247 47229427824183412027006871)
        ·
          refine ⟨70844141736275118040510307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47229427824183412027006871 70844141736275118040510307)
          ·
            refine ⟨106266212604412677060765461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70844141736275118040510307 106266212604412677060765461)
            ·
              refine ⟨4981228715831844237223381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106266212604412677060765461 4981228715831844237223381)
              ·
                refine ⟨116747548027308849309923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4981228715831844237223381 116747548027308849309923)
                ·
                  rfl

theorem cell23_6138856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 7].length) (baseStart_6138856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138856 prefixEnd_6138856 := by exact prefixLift 6138856
  have htrace : WordTrace (prefixWord ++ tailWord_6138856) baseStart_6138856 baseEnd_6138856 := by
    simpa [prefixWord, tailWord_6138856, baseEnd_6138856] using wordTrace_append hprefix tailTrace_6138856
  have hstable : (prefixWord ++ tailWord_6138856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138856).length < 2 ^ (prefixWord ++ tailWord_6138856).sum := by decide
  have hdescent : baseEnd_6138856 < baseStart_6138856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138870 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6138870 : Nat := 118140960795 + 6138870 * 2 ^ 59
def prefixEnd_6138870 : Nat := 4983230072969 + 3 ^ 40 * 6138870 * 2
def baseEnd_6138870 : Nat := 3152190985466501876592857

theorem tailTrace_6138870 : CollatzResearch.WordTrace tailWord_6138870 prefixEnd_6138870 3152190985466501876592857 := by
  unfold tailWord_6138870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993936454370618773180879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149268655513286600247262709 13993936454370618773180879)
  ·
    refine ⟨20990904681555928159771319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13993936454370618773180879 20990904681555928159771319)
    ·
      refine ⟨31486357022333892239656979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20990904681555928159771319 31486357022333892239656979)
      ·
        refine ⟨47229535533500838359485469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31486357022333892239656979 47229535533500838359485469)
        ·
          refine ⟨17711075825062814384807051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47229535533500838359485469 17711075825062814384807051)
          ·
            refine ⟨26566613737594221577210577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17711075825062814384807051 26566613737594221577210577)
            ·
              refine ⟨19924960303195666182907933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26566613737594221577210577 19924960303195666182907933)
              ·
                refine ⟨7471860113698374818590475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19924960303195666182907933 7471860113698374818590475)
                ·
                  refine ⟨11207790170547562227885713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471860113698374818590475 11207790170547562227885713)
                  ·
                    refine ⟨8405842627910671670914285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11207790170547562227885713 8405842627910671670914285)
                    ·
                      refine ⟨3152190985466501876592857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8405842627910671670914285 3152190985466501876592857)
                      ·
                        rfl

theorem cell23_6138870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6138870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138870 prefixEnd_6138870 := by exact prefixLift 6138870
  have htrace : WordTrace (prefixWord ++ tailWord_6138870) baseStart_6138870 baseEnd_6138870 := by
    simpa [prefixWord, tailWord_6138870, baseEnd_6138870] using wordTrace_append hprefix tailTrace_6138870
  have hstable : (prefixWord ++ tailWord_6138870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138870).length < 2 ^ (prefixWord ++ tailWord_6138870).sum := by decide
  have hdescent : baseEnd_6138870 < baseStart_6138870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138899 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 8]
def baseStart_6138899 : Nat := 118140960795 + 6138899 * 2 ^ 59
def prefixEnd_6138899 : Nat := 4983230072969 + 3 ^ 40 * 6138899 * 2
def baseEnd_6138899 : Nat := 1050735292135160754376741

theorem tailTrace_6138899 : CollatzResearch.WordTrace tailWord_6138899 prefixEnd_6138899 1050735292135160754376741 := by
  unfold tailWord_6138899
  simp only [CollatzResearch.WordTrace]
  refine ⟨223904040986824838323699751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149269360657883225549133167 223904040986824838323699751)
  ·
    refine ⟨335856061480237257485549627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223904040986824838323699751 335856061480237257485549627)
    ·
      refine ⟨503784092220355886228324441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335856061480237257485549627 503784092220355886228324441)
      ·
        refine ⟨377838069165266914671243331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503784092220355886228324441 377838069165266914671243331)
        ·
          refine ⟨566757103747900372006864997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377838069165266914671243331 566757103747900372006864997)
          ·
            refine ⟨106266956952731319751287187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 566757103747900372006864997 106266956952731319751287187)
            ·
              refine ⟨159400435429096979626930781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106266956952731319751287187 159400435429096979626930781)
              ·
                refine ⟨59775163285911367360099043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159400435429096979626930781 59775163285911367360099043)
                ·
                  refine ⟨89662744928867051040148565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59775163285911367360099043 89662744928867051040148565)
                  ·
                    refine ⟨1050735292135160754376741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89662744928867051040148565 1050735292135160754376741)
                    ·
                      rfl

theorem cell23_6138899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_6138899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138899 prefixEnd_6138899 := by exact prefixLift 6138899
  have htrace : WordTrace (prefixWord ++ tailWord_6138899) baseStart_6138899 baseEnd_6138899 := by
    simpa [prefixWord, tailWord_6138899, baseEnd_6138899] using wordTrace_append hprefix tailTrace_6138899
  have hstable : (prefixWord ++ tailWord_6138899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138899).length < 2 ^ (prefixWord ++ tailWord_6138899).sum := by decide
  have hdescent : baseEnd_6138899 < baseStart_6138899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138923 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 4, 2]
def baseStart_6138923 : Nat := 118140960795 + 6138923 * 2 ^ 59
def prefixEnd_6138923 : Nat := 4983230072969 + 3 ^ 40 * 6138923 * 2
def baseEnd_6138923 : Nat := 3152218199941190169230113

theorem tailTrace_6138923 : CollatzResearch.WordTrace tailWord_6138923 prefixEnd_6138923 3152218199941190169230113 := by
  unfold tailWord_6138923
  simp only [CollatzResearch.WordTrace]
  refine ⟨223904916338737890422573423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149269944225825260281715615 223904916338737890422573423)
  ·
    refine ⟨335857374508106835633860135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223904916338737890422573423 335857374508106835633860135)
    ·
      refine ⟨503786061762160253450790203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335857374508106835633860135 503786061762160253450790203)
      ·
        refine ⟨755679092643240380176185305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503786061762160253450790203 755679092643240380176185305)
        ·
          refine ⟨566759319482430285132138979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755679092643240380176185305 566759319482430285132138979)
          ·
            refine ⟨850138979223645427698208469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566759319482430285132138979 850138979223645427698208469)
            ·
              refine ⟨19925132325554189711676761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 850138979223645427698208469 19925132325554189711676761)
              ·
                refine ⟨14943849244165642283757571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19925132325554189711676761 14943849244165642283757571)
                ·
                  refine ⟨22415773866248463425636357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14943849244165642283757571 22415773866248463425636357)
                  ·
                    refine ⟨4202957599921586892306817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22415773866248463425636357 4202957599921586892306817)
                    ·
                      refine ⟨3152218199941190169230113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202957599921586892306817 3152218199941190169230113)
                      ·
                        rfl

theorem cell23_6138923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4, 2].length) (baseStart_6138923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138923 prefixEnd_6138923 := by exact prefixLift 6138923
  have htrace : WordTrace (prefixWord ++ tailWord_6138923) baseStart_6138923 baseEnd_6138923 := by
    simpa [prefixWord, tailWord_6138923, baseEnd_6138923] using wordTrace_append hprefix tailTrace_6138923
  have hstable : (prefixWord ++ tailWord_6138923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138923).length < 2 ^ (prefixWord ++ tailWord_6138923).sum := by decide
  have hdescent : baseEnd_6138923 < baseStart_6138923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138950 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6138950 : Nat := 118140960795 + 6138950 * 2 ^ 59
def prefixEnd_6138950 : Nat := 4983230072969 + 3 ^ 40 * 6138950 * 2
def baseEnd_6138950 : Nat := 1050744021306287187864163

theorem tailTrace_6138950 : CollatzResearch.WordTrace tailWord_6138950 prefixEnd_6138950 1050744021306287187864163 := by
  unfold tailWord_6138950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997059409676252313556447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149270600739760049355870869 6997059409676252313556447)
  ·
    refine ⟨10495589114514378470334671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6997059409676252313556447 10495589114514378470334671)
    ·
      refine ⟨15743383671771567705502007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495589114514378470334671 15743383671771567705502007)
      ·
        refine ⟨23615075507657351558253011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15743383671771567705502007 23615075507657351558253011)
        ·
          refine ⟨35422613261486027337379517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23615075507657351558253011 35422613261486027337379517)
          ·
            refine ⟨13283479973057260251517319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35422613261486027337379517 13283479973057260251517319)
            ·
              refine ⟨19925219959585890377275979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283479973057260251517319 19925219959585890377275979)
              ·
                refine ⟨29887829939378835565913969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19925219959585890377275979 29887829939378835565913969)
                ·
                  refine ⟨22415872454534126674435477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29887829939378835565913969 22415872454534126674435477)
                  ·
                    refine ⟨1050744021306287187864163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22415872454534126674435477 1050744021306287187864163)
                    ·
                      rfl

theorem cell23_6138950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6138950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138950 prefixEnd_6138950 := by exact prefixLift 6138950
  have htrace : WordTrace (prefixWord ++ tailWord_6138950) baseStart_6138950 baseEnd_6138950 := by
    simpa [prefixWord, tailWord_6138950, baseEnd_6138950] using wordTrace_append hprefix tailTrace_6138950
  have hstable : (prefixWord ++ tailWord_6138950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138950).length < 2 ^ (prefixWord ++ tailWord_6138950).sum := by decide
  have hdescent : baseEnd_6138950 < baseStart_6138950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138957 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6138957 : Nat := 118140960795 + 6138957 * 2 ^ 59
def prefixEnd_6138957 : Nat := 4983230072969 + 3 ^ 40 * 6138957 * 2
def baseEnd_6138957 : Nat := 3152235658283443036204957

theorem tailTrace_6138957 : CollatzResearch.WordTrace tailWord_6138957 prefixEnd_6138957 3152235658283443036204957 := by
  unfold tailWord_6138957
  simp only [CollatzResearch.WordTrace]
  refine ⟨223906156420614714229311125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149270770947076476152874083 223906156420614714229311125)
  ·
    refine ⟨10495601082216314729498959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 223906156420614714229311125 10495601082216314729498959)
    ·
      refine ⟨15743401623324472094248439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495601082216314729498959 15743401623324472094248439)
      ·
        refine ⟨23615102434986708141372659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15743401623324472094248439 23615102434986708141372659)
        ·
          refine ⟨35422653652480062212058989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23615102434986708141372659 35422653652480062212058989)
          ·
            refine ⟨13283495119680023329522121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35422653652480062212058989 13283495119680023329522121)
            ·
              refine ⟨9962621339760017497141591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13283495119680023329522121 9962621339760017497141591)
              ·
                refine ⟨14943932009640026245712387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962621339760017497141591 14943932009640026245712387)
                ·
                  refine ⟨22415898014460039368568581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14943932009640026245712387 22415898014460039368568581)
                  ·
                    refine ⟨4202980877711257381606609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22415898014460039368568581 4202980877711257381606609)
                    ·
                      refine ⟨3152235658283443036204957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202980877711257381606609 3152235658283443036204957)
                      ·
                        rfl

theorem cell23_6138957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6138957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138957 prefixEnd_6138957 := by exact prefixLift 6138957
  have htrace : WordTrace (prefixWord ++ tailWord_6138957) baseStart_6138957 baseEnd_6138957 := by
    simpa [prefixWord, tailWord_6138957, baseEnd_6138957] using wordTrace_append hprefix tailTrace_6138957
  have hstable : (prefixWord ++ tailWord_6138957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138957).length < 2 ^ (prefixWord ++ tailWord_6138957).sum := by decide
  have hdescent : baseEnd_6138957 < baseStart_6138957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138974 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6138974 : Nat := 118140960795 + 6138974 * 2 ^ 59
def prefixEnd_6138974 : Nat := 4983230072969 + 3 ^ 40 * 6138974 * 2
def baseEnd_6138974 : Nat := 3152244387454569469692379

theorem tailTrace_6138974 : CollatzResearch.WordTrace tailWord_6138974 prefixEnd_6138974 3152244387454569469692379 := by
  unfold tailWord_6138974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27988347057694140766584997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149271184307702084088453317 27988347057694140766584997)
  ·
    refine ⟨5247815073317651393734687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27988347057694140766584997 5247815073317651393734687)
    ·
      refine ⟨7871722609976477090602031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247815073317651393734687 7871722609976477090602031)
      ·
        refine ⟨11807583914964715635903047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7871722609976477090602031 11807583914964715635903047)
        ·
          refine ⟨17711375872447073453854571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807583914964715635903047 17711375872447073453854571)
          ·
            refine ⟨26567063808670610180781857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17711375872447073453854571 26567063808670610180781857)
            ·
              refine ⟨19925297856502957635586393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26567063808670610180781857 19925297856502957635586393)
              ·
                refine ⟨14943973392377218226689795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19925297856502957635586393 14943973392377218226689795)
                ·
                  refine ⟨22415960088565827340034693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14943973392377218226689795 22415960088565827340034693)
                  ·
                    refine ⟨4202992516606092626256505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22415960088565827340034693 4202992516606092626256505)
                    ·
                      refine ⟨3152244387454569469692379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4202992516606092626256505 3152244387454569469692379)
                      ·
                        rfl

theorem cell23_6138974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6138974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138974 prefixEnd_6138974 := by exact prefixLift 6138974
  have htrace : WordTrace (prefixWord ++ tailWord_6138974) baseStart_6138974 baseEnd_6138974 := by
    simpa [prefixWord, tailWord_6138974, baseEnd_6138974] using wordTrace_append hprefix tailTrace_6138974
  have hstable : (prefixWord ++ tailWord_6138974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138974).length < 2 ^ (prefixWord ++ tailWord_6138974).sum := by decide
  have hdescent : baseEnd_6138974 < baseStart_6138974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6138976 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 7]
def baseStart_6138976 : Nat := 118140960795 + 6138976 * 2 ^ 59
def prefixEnd_6138976 : Nat := 4983230072969 + 3 ^ 40 * 6138976 * 2
def baseEnd_6138976 : Nat := 1050748471471959487289123

theorem tailTrace_6138976 : CollatzResearch.WordTrace tailWord_6138976 prefixEnd_6138976 1050748471471959487289123 := by
  unfold tailWord_6138976
  simp only [CollatzResearch.WordTrace]
  refine ⟨111953424703772940237126391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149271232938363920316168521 111953424703772940237126391)
  ·
    refine ⟨167930137055659410355689587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111953424703772940237126391 167930137055659410355689587)
    ·
      refine ⟨251895205583489115533534381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167930137055659410355689587 251895205583489115533534381)
      ·
        refine ⟨94460702093808418325075393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251895205583489115533534381 94460702093808418325075393)
        ·
          refine ⟨70845526570356313743806545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94460702093808418325075393 70845526570356313743806545)
          ·
            refine ⟨53134144927767235307854909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70845526570356313743806545 53134144927767235307854909)
            ·
              refine ⟨19925304347912713240445591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53134144927767235307854909 19925304347912713240445591)
              ·
                refine ⟨29887956521869069860668387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19925304347912713240445591 29887956521869069860668387)
                ·
                  refine ⟨44831934782803604791002581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29887956521869069860668387 44831934782803604791002581)
                  ·
                    refine ⟨1050748471471959487289123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44831934782803604791002581 1050748471471959487289123)
                    ·
                      rfl

theorem cell23_6138976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_6138976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6138976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6138976 prefixEnd_6138976 := by exact prefixLift 6138976
  have htrace : WordTrace (prefixWord ++ tailWord_6138976) baseStart_6138976 baseEnd_6138976 := by
    simpa [prefixWord, tailWord_6138976, baseEnd_6138976] using wordTrace_append hprefix tailTrace_6138976
  have hstable : (prefixWord ++ tailWord_6138976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6138976).length < 2 ^ (prefixWord ++ tailWord_6138976).sum := by decide
  have hdescent : baseEnd_6138976 < baseStart_6138976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6138976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139057 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_6139057 : Nat := 118140960795 + 6139057 * 2 ^ 59
def prefixEnd_6139057 : Nat := 4983230072969 + 3 ^ 40 * 6139057 * 2
def baseEnd_6139057 : Nat := 1050762335449630881651499

theorem tailTrace_6139057 : CollatzResearch.WordTrace tailWord_6139057 prefixEnd_6139057 1050762335449630881651499 := by
  unfold tailWord_6139057
  simp only [CollatzResearch.WordTrace]
  refine ⟨223909803720252431307951425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149273202480168287538634283 223909803720252431307951425)
  ·
    refine ⟨167932352790189323480963569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223909803720252431307951425 167932352790189323480963569)
    ·
      refine ⟨125949264592641992610722677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167932352790189323480963569 125949264592641992610722677)
      ·
        refine ⟨11807743555560186807255251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125949264592641992610722677 11807743555560186807255251)
        ·
          refine ⟨17711615333340280210882877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807743555560186807255251 17711615333340280210882877)
          ·
            refine ⟨6641855750002605079081079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17711615333340280210882877 6641855750002605079081079)
            ·
              refine ⟨9962783625003907618621619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641855750002605079081079 9962783625003907618621619)
              ·
                refine ⟨14944175437505861427932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962783625003907618621619 14944175437505861427932429)
                ·
                  refine ⟨5604065789064698035474661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14944175437505861427932429 5604065789064698035474661)
                  ·
                    refine ⟨1050762335449630881651499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604065789064698035474661 1050762335449630881651499)
                    ·
                      rfl

theorem cell23_6139057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_6139057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139057 prefixEnd_6139057 := by exact prefixLift 6139057
  have htrace : WordTrace (prefixWord ++ tailWord_6139057) baseStart_6139057 baseEnd_6139057 := by
    simpa [prefixWord, tailWord_6139057, baseEnd_6139057] using wordTrace_append hprefix tailTrace_6139057
  have hstable : (prefixWord ++ tailWord_6139057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139057).length < 2 ^ (prefixWord ++ tailWord_6139057).sum := by decide
  have hdescent : baseEnd_6139057 < baseStart_6139057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139066 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_6139066 : Nat := 118140960795 + 6139066 * 2 ^ 59
def prefixEnd_6139066 : Nat := 4983230072969 + 3 ^ 40 * 6139066 * 2
def baseEnd_6139066 : Nat := 1050763875891594369913985

theorem tailTrace_6139066 : CollatzResearch.WordTrace tailWord_6139066 prefixEnd_6139066 1050763875891594369913985 := by
  unfold tailWord_6139066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55977532994304956461257263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149273421318146550563352701 55977532994304956461257263)
  ·
    refine ⟨83966299491457434691885895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55977532994304956461257263 83966299491457434691885895)
    ·
      refine ⟨125949449237186152037828843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83966299491457434691885895 125949449237186152037828843)
      ·
        refine ⟨188924173855779228056743265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125949449237186152037828843 188924173855779228056743265)
        ·
          refine ⟨141693130391834421042557449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188924173855779228056743265 141693130391834421042557449)
          ·
            refine ⟨106269847793875815781918087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141693130391834421042557449 106269847793875815781918087)
            ·
              refine ⟨159404771690813723672877131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106269847793875815781918087 159404771690813723672877131)
              ·
                refine ⟨239107157536220585509315697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159404771690813723672877131 239107157536220585509315697)
                ·
                  refine ⟨179330368152165439131986773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239107157536220585509315697 179330368152165439131986773)
                  ·
                    refine ⟨1050763875891594369913985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179330368152165439131986773 1050763875891594369913985)
                    ·
                      rfl

theorem cell23_6139066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_6139066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139066 prefixEnd_6139066 := by exact prefixLift 6139066
  have htrace : WordTrace (prefixWord ++ tailWord_6139066) baseStart_6139066 baseEnd_6139066 := by
    simpa [prefixWord, tailWord_6139066, baseEnd_6139066] using wordTrace_append hprefix tailTrace_6139066
  have hstable : (prefixWord ++ tailWord_6139066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139066).length < 2 ^ (prefixWord ++ tailWord_6139066).sum := by decide
  have hdescent : baseEnd_6139066 < baseStart_6139066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139070 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_6139070 : Nat := 118140960795 + 6139070 * 2 ^ 59
def prefixEnd_6139070 : Nat := 4983230072969 + 3 ^ 40 * 6139070 * 2
def baseEnd_6139070 : Nat := 350254853510822343787993

theorem tailTrace_6139070 : CollatzResearch.WordTrace tailWord_6139070 prefixEnd_6139070 350254853510822343787993 := by
  unfold tailWord_6139070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27988784733650666816021833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149273518579470223018783109 27988784733650666816021833)
  ·
    refine ⟨20991588550238000112016375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27988784733650666816021833 20991588550238000112016375)
    ·
      refine ⟨31487382825357000168024563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991588550238000112016375 31487382825357000168024563)
      ·
        refine ⟨47231074238035500252036845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31487382825357000168024563 47231074238035500252036845)
        ·
          refine ⟨17711652839263312594513817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47231074238035500252036845 17711652839263312594513817)
          ·
            refine ⟨13283739629447484445885363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17711652839263312594513817 13283739629447484445885363)
            ·
              refine ⟨19925609444171226668828045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283739629447484445885363 19925609444171226668828045)
              ·
                refine ⟨7472103541564210000810517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19925609444171226668828045 7472103541564210000810517)
                ·
                  refine ⟨350254853510822343787993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7472103541564210000810517 350254853510822343787993)
                  ·
                    rfl

theorem cell23_6139070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_6139070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139070 prefixEnd_6139070 := by exact prefixLift 6139070
  have htrace : WordTrace (prefixWord ++ tailWord_6139070) baseStart_6139070 baseEnd_6139070 := by
    simpa [prefixWord, tailWord_6139070, baseEnd_6139070] using wordTrace_append hprefix tailTrace_6139070
  have hstable : (prefixWord ++ tailWord_6139070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139070).length < 2 ^ (prefixWord ++ tailWord_6139070).sum := by decide
  have hdescent : baseEnd_6139070 < baseStart_6139070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139080 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_6139080 : Nat := 118140960795 + 6139080 * 2 ^ 59
def prefixEnd_6139080 : Nat := 4983230072969 + 3 ^ 40 * 6139080 * 2
def baseEnd_6139080 : Nat := 3152298816403946054966891

theorem tailTrace_6139080 : CollatzResearch.WordTrace tailWord_6139080 prefixEnd_6139080 3152298816403946054966891 := by
  unfold tailWord_6139080
  simp only [CollatzResearch.WordTrace]
  refine ⟨111955321299584553118019347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149273761732779404157359129 111955321299584553118019347)
  ·
    refine ⟨167932981949376829677029021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111955321299584553118019347 167932981949376829677029021)
    ·
      refine ⟨62974868231016311128885883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167932981949376829677029021 62974868231016311128885883)
      ·
        refine ⟨94462302346524466693328825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62974868231016311128885883 94462302346524466693328825)
        ·
          refine ⟨70846726759893350019996619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94462302346524466693328825 70846726759893350019996619)
          ·
            refine ⟨106270090139840025029994929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70846726759893350019996619 106270090139840025029994929)
            ·
              refine ⟨79702567604880018772496197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106270090139840025029994929 79702567604880018772496197)
              ·
                refine ⟨14944231425915003519843037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79702567604880018772496197 14944231425915003519843037)
                ·
                  refine ⟨5604086784718126319941139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14944231425915003519843037 5604086784718126319941139)
                  ·
                    refine ⟨8406130177077189479911709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604086784718126319941139 8406130177077189479911709)
                    ·
                      refine ⟨3152298816403946054966891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406130177077189479911709 3152298816403946054966891)
                      ·
                        rfl

theorem cell23_6139080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_6139080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139080 prefixEnd_6139080 := by exact prefixLift 6139080
  have htrace : WordTrace (prefixWord ++ tailWord_6139080) baseStart_6139080 baseEnd_6139080 := by
    simpa [prefixWord, tailWord_6139080, baseEnd_6139080] using wordTrace_append hprefix tailTrace_6139080
  have hstable : (prefixWord ++ tailWord_6139080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139080).length < 2 ^ (prefixWord ++ tailWord_6139080).sum := by decide
  have hdescent : baseEnd_6139080 < baseStart_6139080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139083 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 1, 5]
def baseStart_6139083 : Nat := 118140960795 + 6139083 * 2 ^ 59
def prefixEnd_6139083 : Nat := 4983230072969 + 3 ^ 40 * 6139083 * 2
def baseEnd_6139083 : Nat := 1050766785615303181076459

theorem tailTrace_6139083 : CollatzResearch.WordTrace tailWord_6139083 prefixEnd_6139083 1050766785615303181076459 := by
  unfold tailWord_6139083
  simp only [CollatzResearch.WordTrace]
  refine ⟨223910752018158237748397903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149273834678772158498931935 223910752018158237748397903)
  ·
    refine ⟨335866128027237356622596855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223910752018158237748397903 335866128027237356622596855)
    ·
      refine ⟨503799192040856034933895283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335866128027237356622596855 503799192040856034933895283)
      ·
        refine ⟨755698788061284052400842925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503799192040856034933895283 755698788061284052400842925)
        ·
          refine ⟨283387045522981519650316097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755698788061284052400842925 283387045522981519650316097)
          ·
            refine ⟨212540284142236139737737073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283387045522981519650316097 212540284142236139737737073)
            ·
              refine ⟨159405213106677104803302805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212540284142236139737737073 159405213106677104803302805)
              ·
                refine ⟨7472119364375489287654819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159405213106677104803302805 7472119364375489287654819)
                ·
                  refine ⟨11208179046563233931482229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472119364375489287654819 11208179046563233931482229)
                  ·
                    refine ⟨1050766785615303181076459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11208179046563233931482229 1050766785615303181076459)
                    ·
                      rfl

theorem cell23_6139083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 5].length) (baseStart_6139083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139083 prefixEnd_6139083 := by exact prefixLift 6139083
  have htrace : WordTrace (prefixWord ++ tailWord_6139083) baseStart_6139083 baseEnd_6139083 := by
    simpa [prefixWord, tailWord_6139083, baseEnd_6139083] using wordTrace_append hprefix tailTrace_6139083
  have hstable : (prefixWord ++ tailWord_6139083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139083).length < 2 ^ (prefixWord ++ tailWord_6139083).sum := by decide
  have hdescent : baseEnd_6139083 < baseStart_6139083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 1, 1, 3]
def baseStart_6139097 : Nat := 118140960795 + 6139097 * 2 ^ 59
def prefixEnd_6139097 : Nat := 4983230072969 + 3 ^ 40 * 6139097 * 2
def baseEnd_6139097 : Nat := 3152307545575072488454313

theorem tailTrace_6139097 : CollatzResearch.WordTrace tailWord_6139097 prefixEnd_6139097 3152307545575072488454313 := by
  unfold tailWord_6139097
  simp only [CollatzResearch.WordTrace]
  refine ⟨223911262640107518139407545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149274175093405012092938363 223911262640107518139407545)
  ·
    refine ⟨167933446980080638604555659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223911262640107518139407545 167933446980080638604555659)
    ·
      refine ⟨251900170470120957906833489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167933446980080638604555659 251900170470120957906833489)
      ·
        refine ⟨188925127852590718430125117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251900170470120957906833489 188925127852590718430125117)
        ·
          refine ⟨70846922944721519411296919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188925127852590718430125117 70846922944721519411296919)
          ·
            refine ⟨106270384417082279116945379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70846922944721519411296919 106270384417082279116945379)
            ·
              refine ⟨159405576625623418675418069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106270384417082279116945379 159405576625623418675418069)
              ·
                refine ⟨3736068202163048875205111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159405576625623418675418069 3736068202163048875205111)
                ·
                  refine ⟨5604102303244573312807667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736068202163048875205111 5604102303244573312807667)
                  ·
                    refine ⟨8406153454866859969211501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604102303244573312807667 8406153454866859969211501)
                    ·
                      refine ⟨3152307545575072488454313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406153454866859969211501 3152307545575072488454313)
                      ·
                        rfl

theorem cell23_6139097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_6139097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139097 prefixEnd_6139097 := by exact prefixLift 6139097
  have htrace : WordTrace (prefixWord ++ tailWord_6139097) baseStart_6139097 baseEnd_6139097 := by
    simpa [prefixWord, tailWord_6139097, baseEnd_6139097] using wordTrace_append hprefix tailTrace_6139097
  have hstable : (prefixWord ++ tailWord_6139097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139097).length < 2 ^ (prefixWord ++ tailWord_6139097).sum := by decide
  have hdescent : baseEnd_6139097 < baseStart_6139097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139114 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_6139114 : Nat := 118140960795 + 6139114 * 2 ^ 59
def prefixEnd_6139114 : Nat := 4983230072969 + 3 ^ 40 * 6139114 * 2
def baseEnd_6139114 : Nat := 3152316274746198921941735

theorem tailTrace_6139114 : CollatzResearch.WordTrace tailWord_6139114 prefixEnd_6139114 3152316274746198921941735 := by
  unfold tailWord_6139114
  simp only [CollatzResearch.WordTrace]
  refine ⟨55977970670261482510694099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149274588454030620028517597 55977970670261482510694099)
  ·
    refine ⟨83966956005392223766041149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55977970670261482510694099 83966956005392223766041149)
    ·
      refine ⟨31487608502022083912265431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83966956005392223766041149 31487608502022083912265431)
      ·
        refine ⟨47231412753033125868398147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31487608502022083912265431 47231412753033125868398147)
        ·
          refine ⟨70847119129549688802597221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47231412753033125868398147 70847119129549688802597221)
          ·
            refine ⟨13283834836790566650486979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70847119129549688802597221 13283834836790566650486979)
            ·
              refine ⟨19925752255185849975730469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283834836790566650486979 19925752255185849975730469)
              ·
                refine ⟨3736078547847346870449463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19925752255185849975730469 3736078547847346870449463)
                ·
                  refine ⟨5604117821771020305674195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736078547847346870449463 5604117821771020305674195)
                  ·
                    refine ⟨8406176732656530458511293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604117821771020305674195 8406176732656530458511293)
                    ·
                      refine ⟨3152316274746198921941735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406176732656530458511293 3152316274746198921941735)
                      ·
                        rfl

theorem cell23_6139114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_6139114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139114 prefixEnd_6139114 := by exact prefixLift 6139114
  have htrace : WordTrace (prefixWord ++ tailWord_6139114) baseStart_6139114 baseEnd_6139114 := by
    simpa [prefixWord, tailWord_6139114, baseEnd_6139114] using wordTrace_append hprefix tailTrace_6139114
  have hstable : (prefixWord ++ tailWord_6139114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139114).length < 2 ^ (prefixWord ++ tailWord_6139114).sum := by decide
  have hdescent : baseEnd_6139114 < baseStart_6139114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139130 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_6139130 : Nat := 118140960795 + 6139130 * 2 ^ 59
def prefixEnd_6139130 : Nat := 4983230072969 + 3 ^ 40 * 6139130 * 2
def baseEnd_6139130 : Nat := 1050774830145556953113887

theorem tailTrace_6139130 : CollatzResearch.WordTrace tailWord_6139130 prefixEnd_6139130 1050774830145556953113887 := by
  unfold tailWord_6139130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55978116562246991193839711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149274977499325309850239229 55978116562246991193839711)
  ·
    refine ⟨83967174843370486790759567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55978116562246991193839711 83967174843370486790759567)
    ·
      refine ⟨125950762265055730186139351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83967174843370486790759567 125950762265055730186139351)
      ·
        refine ⟨188926143397583595279209027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125950762265055730186139351 188926143397583595279209027)
        ·
          refine ⟨283389215096375392918813541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188926143397583595279209027 283389215096375392918813541)
          ·
            refine ⟨53135477830570386172277539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283389215096375392918813541 53135477830570386172277539)
            ·
              refine ⟨79703216745855579258416309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53135477830570386172277539 79703216745855579258416309)
              ·
                refine ⟨7472176569923960555476529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79703216745855579258416309 7472176569923960555476529)
                ·
                  refine ⟨5604132427442970416607397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472176569923960555476529 5604132427442970416607397)
                  ·
                    refine ⟨1050774830145556953113887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604132427442970416607397 1050774830145556953113887)
                    ·
                      rfl

theorem cell23_6139130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_6139130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139130 prefixEnd_6139130 := by exact prefixLift 6139130
  have htrace : WordTrace (prefixWord ++ tailWord_6139130) baseStart_6139130 baseEnd_6139130 := by
    simpa [prefixWord, tailWord_6139130, baseEnd_6139130] using wordTrace_append hprefix tailTrace_6139130
  have hstable : (prefixWord ++ tailWord_6139130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139130).length < 2 ^ (prefixWord ++ tailWord_6139130).sum := by decide
  have hdescent : baseEnd_6139130 < baseStart_6139130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139137 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6139137 : Nat := 118140960795 + 6139137 * 2 ^ 59
def prefixEnd_6139137 : Nat := 4983230072969 + 3 ^ 40 * 6139137 * 2
def baseEnd_6139137 : Nat := 3152328084801252331954129

theorem tailTrace_6139137 : CollatzResearch.WordTrace tailWord_6139137 prefixEnd_6139137 3152328084801252331954129 := by
  unfold tailWord_6139137
  simp only [CollatzResearch.WordTrace]
  refine ⟨223912721559962604970863665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149275147706641736647242443 223912721559962604970863665)
  ·
    refine ⟨167934541169971953728147749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223912721559962604970863665 167934541169971953728147749)
    ·
      refine ⟨31487726469369741324027703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167934541169971953728147749 31487726469369741324027703)
      ·
        refine ⟨47231589704054611986041555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31487726469369741324027703 47231589704054611986041555)
        ·
          refine ⟨70847384556081917979062333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47231589704054611986041555 70847384556081917979062333)
          ·
            refine ⟨26567769208530719242148375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70847384556081917979062333 26567769208530719242148375)
            ·
              refine ⟨39851653812796078863222563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26567769208530719242148375 39851653812796078863222563)
              ·
                refine ⟨59777480719194118294833845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39851653812796078863222563 59777480719194118294833845)
                ·
                  refine ⟨5604138817424448590140673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59777480719194118294833845 5604138817424448590140673)
                  ·
                    refine ⟨4203104113068336442605505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604138817424448590140673 4203104113068336442605505)
                    ·
                      refine ⟨3152328084801252331954129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203104113068336442605505 3152328084801252331954129)
                      ·
                        rfl

theorem cell23_6139137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6139137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139137 prefixEnd_6139137 := by exact prefixLift 6139137
  have htrace : WordTrace (prefixWord ++ tailWord_6139137) baseStart_6139137 baseEnd_6139137 := by
    simpa [prefixWord, tailWord_6139137, baseEnd_6139137] using wordTrace_append hprefix tailTrace_6139137
  have hstable : (prefixWord ++ tailWord_6139137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139137).length < 2 ^ (prefixWord ++ tailWord_6139137).sum := by decide
  have hdescent : baseEnd_6139137 < baseStart_6139137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139150 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6139150 : Nat := 118140960795 + 6139150 * 2 ^ 59
def prefixEnd_6139150 : Nat := 4983230072969 + 3 ^ 40 * 6139150 * 2
def baseEnd_6139150 : Nat := 3152334760049760781091569

theorem tailTrace_6139150 : CollatzResearch.WordTrace tailWord_6139150 prefixEnd_6139150 3152334760049760781091569 := by
  unfold tailWord_6139150
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989149463614438523885863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149275463805943672127391269 27989149463614438523885863)
  ·
    refine ⟨41983724195421657785828795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27989149463614438523885863 41983724195421657785828795)
    ·
      refine ⟨62975586293132486678743193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41983724195421657785828795 62975586293132486678743193)
      ·
        refine ⟨47231689719849365009057395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62975586293132486678743193 47231689719849365009057395)
        ·
          refine ⟨70847534579774047513586093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47231689719849365009057395 70847534579774047513586093)
          ·
            refine ⟨26567825467415267817594785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70847534579774047513586093 26567825467415267817594785)
            ·
              refine ⟨19925869100561450863196089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26567825467415267817594785 19925869100561450863196089)
              ·
                refine ⟨14944401825421088147397067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19925869100561450863196089 14944401825421088147397067)
                ·
                  refine ⟨22416602738131632221095601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14944401825421088147397067 22416602738131632221095601)
                  ·
                    refine ⟨16812452053598724165821701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22416602738131632221095601 16812452053598724165821701)
                    ·
                      refine ⟨3152334760049760781091569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16812452053598724165821701 3152334760049760781091569)
                      ·
                        rfl

theorem cell23_6139150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6139150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139150 prefixEnd_6139150 := by exact prefixLift 6139150
  have htrace : WordTrace (prefixWord ++ tailWord_6139150) baseStart_6139150 baseEnd_6139150 := by
    simpa [prefixWord, tailWord_6139150, baseEnd_6139150] using wordTrace_append hprefix tailTrace_6139150
  have hstable : (prefixWord ++ tailWord_6139150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139150).length < 2 ^ (prefixWord ++ tailWord_6139150).sum := by decide
  have hdescent : baseEnd_6139150 < baseStart_6139150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139181 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6139181 : Nat := 118140960795 + 6139181 * 2 ^ 59
def prefixEnd_6139181 : Nat := 4983230072969 + 3 ^ 40 * 6139181 * 2
def baseEnd_6139181 : Nat := 1050783559316683386601309

theorem tailTrace_6139181 : CollatzResearch.WordTrace tailWord_6139181 prefixEnd_6139181 1050783559316683386601309 := by
  unfold tailWord_6139181
  simp only [CollatzResearch.WordTrace]
  refine ⟨223914326371803200485465397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149276217581202133656976931 223914326371803200485465397)
  ·
    refine ⟨20991968097356550045512381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 223914326371803200485465397 20991968097356550045512381)
    ·
      refine ⟨7871988036508706267067143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20991968097356550045512381 7871988036508706267067143)
      ·
        refine ⟨11807982054763059400600715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7871988036508706267067143 11807982054763059400600715)
        ·
          refine ⟨17711973082144589100901073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807982054763059400600715 17711973082144589100901073)
          ·
            refine ⟨13283979811608441825675805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17711973082144589100901073 13283979811608441825675805)
            ·
              refine ⟨4981492429353165684628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13283979811608441825675805 4981492429353165684628427)
              ·
                refine ⟨7472238644029748526942641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981492429353165684628427 7472238644029748526942641)
                ·
                  refine ⟨5604178983022311395206981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472238644029748526942641 5604178983022311395206981)
                  ·
                    refine ⟨1050783559316683386601309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604178983022311395206981 1050783559316683386601309)
                    ·
                      rfl

theorem cell23_6139181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6139181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139181 prefixEnd_6139181 := by exact prefixLift 6139181
  have htrace : WordTrace (prefixWord ++ tailWord_6139181) baseStart_6139181 baseEnd_6139181 := by
    simpa [prefixWord, tailWord_6139181, baseEnd_6139181] using wordTrace_append hprefix tailTrace_6139181
  have hstable : (prefixWord ++ tailWord_6139181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139181).length < 2 ^ (prefixWord ++ tailWord_6139181).sum := by decide
  have hdescent : baseEnd_6139181 < baseStart_6139181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139187 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 3]
def baseStart_6139187 : Nat := 118140960795 + 6139187 * 2 ^ 59
def prefixEnd_6139187 : Nat := 4983230072969 + 3 ^ 40 * 6139187 * 2
def baseEnd_6139187 : Nat := 3152353758833977136328899

theorem tailTrace_6139187 : CollatzResearch.WordTrace tailWord_6139187 prefixEnd_6139187 3152353758833977136328899 := by
  unfold tailWord_6139187
  simp only [CollatzResearch.WordTrace]
  refine ⟨223914545209781463510183815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149276363473187642340122543 223914545209781463510183815)
  ·
    refine ⟨335871817814672195265275723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223914545209781463510183815 335871817814672195265275723)
    ·
      refine ⟨503807726722008292897913585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335871817814672195265275723 503807726722008292897913585)
      ·
        refine ⟨377855795041506219673435189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503807726722008292897913585 377855795041506219673435189)
        ·
          refine ⟨35423980785141208094384549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 377855795041506219673435189 35423980785141208094384549)
          ·
            refine ⟨6641996397213976517697103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35423980785141208094384549 6641996397213976517697103)
            ·
              refine ⟨9962994595820964776545655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641996397213976517697103 9962994595820964776545655)
              ·
                refine ⟨14944491893731447164818483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962994595820964776545655 14944491893731447164818483)
                ·
                  refine ⟨22416737840597170747227725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14944491893731447164818483 22416737840597170747227725)
                  ·
                    refine ⟨8406276690223939030210397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22416737840597170747227725 8406276690223939030210397)
                    ·
                      refine ⟨3152353758833977136328899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406276690223939030210397 3152353758833977136328899)
                      ·
                        rfl

theorem cell23_6139187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_6139187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139187 prefixEnd_6139187 := by exact prefixLift 6139187
  have htrace : WordTrace (prefixWord ++ tailWord_6139187) baseStart_6139187 baseEnd_6139187 := by
    simpa [prefixWord, tailWord_6139187, baseEnd_6139187] using wordTrace_append hprefix tailTrace_6139187
  have hstable : (prefixWord ++ tailWord_6139187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139187).length < 2 ^ (prefixWord ++ tailWord_6139187).sum := by decide
  have hdescent : baseEnd_6139187 < baseStart_6139187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139204 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6139204 : Nat := 118140960795 + 6139204 * 2 ^ 59
def prefixEnd_6139204 : Nat := 4983230072969 + 3 ^ 40 * 6139204 * 2
def baseEnd_6139204 : Nat := 3152362488005103569816321

theorem tailTrace_6139204 : CollatzResearch.WordTrace tailWord_6139204 prefixEnd_6139204 3152362488005103569816321 := by
  unfold tailWord_6139204
  simp only [CollatzResearch.WordTrace]
  refine ⟨111957582625359937706776333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149276776833813250275701777 111957582625359937706776333)
  ·
    refine ⟨41984093484509976640041125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111957582625359937706776333 41984093484509976640041125)
    ·
      refine ⟨7872017528345620620007711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41984093484509976640041125 7872017528345620620007711)
      ·
        refine ⟨11808026292518430930011567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872017528345620620007711 11808026292518430930011567)
        ·
          refine ⟨17712039438777646395017351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808026292518430930011567 17712039438777646395017351)
          ·
            refine ⟨26568059158166469592526027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17712039438777646395017351 26568059158166469592526027)
            ·
              refine ⟨39852088737249704388789041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26568059158166469592526027 39852088737249704388789041)
              ·
                refine ⟨29889066552937278291591781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39852088737249704388789041 29889066552937278291591781)
                ·
                  refine ⟨5604199978675739679673459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29889066552937278291591781 5604199978675739679673459)
                  ·
                    refine ⟨8406299968013609519510189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604199978675739679673459 8406299968013609519510189)
                    ·
                      refine ⟨3152362488005103569816321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406299968013609519510189 3152362488005103569816321)
                      ·
                        rfl

theorem cell23_6139204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6139204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139204 prefixEnd_6139204 := by exact prefixLift 6139204
  have htrace : WordTrace (prefixWord ++ tailWord_6139204) baseStart_6139204 baseEnd_6139204 := by
    simpa [prefixWord, tailWord_6139204, baseEnd_6139204] using wordTrace_append hprefix tailTrace_6139204
  have hstable : (prefixWord ++ tailWord_6139204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139204).length < 2 ^ (prefixWord ++ tailWord_6139204).sum := by decide
  have hdescent : baseEnd_6139204 < baseStart_6139204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139222 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6139222 : Nat := 118140960795 + 6139222 * 2 ^ 59
def prefixEnd_6139222 : Nat := 4983230072969 + 3 ^ 40 * 6139222 * 2
def baseEnd_6139222 : Nat := 3152371730656884499391239

theorem tailTrace_6139222 : CollatzResearch.WordTrace tailWord_6139222 prefixEnd_6139222 3152371730656884499391239 := by
  unfold tailWord_6139222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994738860290916530481745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149277214509769776325138613 13994738860290916530481745)
  ·
    refine ⟨10496054145218187397861309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13994738860290916530481745 10496054145218187397861309)
    ·
      refine ⟨3936020304456820274197991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10496054145218187397861309 3936020304456820274197991)
      ·
        refine ⟨5904030456685230411296987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936020304456820274197991 5904030456685230411296987)
        ·
          refine ⟨8856045685027845616945481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904030456685230411296987 8856045685027845616945481)
          ·
            refine ⟨6642034263770884212709111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8856045685027845616945481 6642034263770884212709111)
            ·
              refine ⟨9963051395656326319063667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642034263770884212709111 9963051395656326319063667)
              ·
                refine ⟨14944577093484489478595501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963051395656326319063667 14944577093484489478595501)
                ·
                  refine ⟨5604216410056683554473313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14944577093484489478595501 5604216410056683554473313)
                  ·
                    refine ⟨4203162307542512665854985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604216410056683554473313 4203162307542512665854985)
                    ·
                      refine ⟨3152371730656884499391239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203162307542512665854985 3152371730656884499391239)
                      ·
                        rfl

theorem cell23_6139222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6139222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139222 prefixEnd_6139222 := by exact prefixLift 6139222
  have htrace : WordTrace (prefixWord ++ tailWord_6139222) baseStart_6139222 baseEnd_6139222 := by
    simpa [prefixWord, tailWord_6139222, baseEnd_6139222] using wordTrace_append hprefix tailTrace_6139222
  have hstable : (prefixWord ++ tailWord_6139222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139222).length < 2 ^ (prefixWord ++ tailWord_6139222).sum := by decide
  have hdescent : baseEnd_6139222 < baseStart_6139222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139278 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6139278 : Nat := 118140960795 + 6139278 * 2 ^ 59
def prefixEnd_6139278 : Nat := 4983230072969 + 3 ^ 40 * 6139278 * 2
def baseEnd_6139278 : Nat := 3152400485573536280290981

theorem tailTrace_6139278 : CollatzResearch.WordTrace tailWord_6139278 prefixEnd_6139278 3152400485573536280290981 := by
  unfold tailWord_6139278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989733031556473256468311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149278576168301190701164325 27989733031556473256468311)
  ·
    refine ⟨41984599547334709884702467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27989733031556473256468311 41984599547334709884702467)
    ·
      refine ⟨62976899321002064827053701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41984599547334709884702467 62976899321002064827053701)
      ·
        refine ⟨11808168622687887155072569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62976899321002064827053701 11808168622687887155072569)
        ·
          refine ⟨8856126467015915366304427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11808168622687887155072569 8856126467015915366304427)
          ·
            refine ⟨13284189700523873049456641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856126467015915366304427 13284189700523873049456641)
            ·
              refine ⟨9963142275392904787092481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13284189700523873049456641 9963142275392904787092481)
              ·
                refine ⟨7472356706544678590319361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9963142275392904787092481 7472356706544678590319361)
                ·
                  refine ⟨5604267529908508942739521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472356706544678590319361 5604267529908508942739521)
                  ·
                    refine ⟨4203200647431381707054641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604267529908508942739521 4203200647431381707054641)
                    ·
                      refine ⟨3152400485573536280290981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203200647431381707054641 3152400485573536280290981)
                      ·
                        rfl

theorem cell23_6139278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6139278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139278 prefixEnd_6139278 := by exact prefixLift 6139278
  have htrace : WordTrace (prefixWord ++ tailWord_6139278) baseStart_6139278 baseEnd_6139278 := by
    simpa [prefixWord, tailWord_6139278, baseEnd_6139278] using wordTrace_append hprefix tailTrace_6139278
  have hstable : (prefixWord ++ tailWord_6139278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139278).length < 2 ^ (prefixWord ++ tailWord_6139278).sum := by decide
  have hdescent : baseEnd_6139278 < baseStart_6139278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139284 : List Nat := [2, 4, 2, 1, 2, 2, 1, 4, 5]
def baseStart_6139284 : Nat := 118140960795 + 6139284 * 2 ^ 59
def prefixEnd_6139284 : Nat := 4983230072969 + 3 ^ 40 * 6139284 * 2
def baseEnd_6139284 : Nat := 350267062939718139646217

theorem tailTrace_6139284 : CollatzResearch.WordTrace tailWord_6139284 prefixEnd_6139284 350267062939718139646217 := by
  unfold tailWord_6139284
  simp only [CollatzResearch.WordTrace]
  refine ⟨111959041545215024538232453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149278722060286699384309937 111959041545215024538232453)
  ·
    refine ⟨20992320289727817100918585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111959041545215024538232453 20992320289727817100918585)
    ·
      refine ⟨15744240217295862825688939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20992320289727817100918585 15744240217295862825688939)
      ·
        refine ⟨23616360325943794238533409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744240217295862825688939 23616360325943794238533409)
        ·
          refine ⟨17712270244457845678900057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23616360325943794238533409 17712270244457845678900057)
          ·
            refine ⟨13284202683343384259175043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17712270244457845678900057 13284202683343384259175043)
            ·
              refine ⟨19926304025015076388762565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284202683343384259175043 19926304025015076388762565)
              ·
                refine ⟨3736182004690326822892981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19926304025015076388762565 3736182004690326822892981)
                ·
                  refine ⟨350267062939718139646217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736182004690326822892981 350267062939718139646217)
                  ·
                    rfl

theorem cell23_6139284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_6139284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139284 prefixEnd_6139284 := by exact prefixLift 6139284
  have htrace : WordTrace (prefixWord ++ tailWord_6139284) baseStart_6139284 baseEnd_6139284 := by
    simpa [prefixWord, tailWord_6139284, baseEnd_6139284] using wordTrace_append hprefix tailTrace_6139284
  have hstable : (prefixWord ++ tailWord_6139284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139284).length < 2 ^ (prefixWord ++ tailWord_6139284).sum := by decide
  have hdescent : baseEnd_6139284 < baseStart_6139284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139290 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6139290 : Nat := 118140960795 + 6139290 * 2 ^ 59
def prefixEnd_6139290 : Nat := 4983230072969 + 3 ^ 40 * 6139290 * 2
def baseEnd_6139290 : Nat := 3152406647341390233340925

theorem tailTrace_6139290 : CollatzResearch.WordTrace tailWord_6139290 prefixEnd_6139290 3152406647341390233340925 := by
  unfold tailWord_6139290
  simp only [CollatzResearch.WordTrace]
  refine ⟨55979575482102078025295831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149278867952272208067455549 55979575482102078025295831)
  ·
    refine ⟨83969363223153117037943747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55979575482102078025295831 83969363223153117037943747)
    ·
      refine ⟨125954044834729675556915621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83969363223153117037943747 125954044834729675556915621)
      ·
        refine ⟨23616383406511814166921679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125954044834729675556915621 23616383406511814166921679)
        ·
          refine ⟨35424575109767721250382519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23616383406511814166921679 35424575109767721250382519)
          ·
            refine ⟨53136862664651581875573779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35424575109767721250382519 53136862664651581875573779)
            ·
              refine ⟨79705293996977372813360669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53136862664651581875573779 79705293996977372813360669)
              ·
                refine ⟨29889485248866514805010251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79705293996977372813360669 29889485248866514805010251)
                ·
                  refine ⟨44834227873299772207515377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29889485248866514805010251 44834227873299772207515377)
                  ·
                    refine ⟨33625670904974829155636533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44834227873299772207515377 33625670904974829155636533)
                    ·
                      refine ⟨3152406647341390233340925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33625670904974829155636533 3152406647341390233340925)
                      ·
                        rfl

theorem cell23_6139290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6139290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139290 prefixEnd_6139290 := by exact prefixLift 6139290
  have htrace : WordTrace (prefixWord ++ tailWord_6139290) baseStart_6139290 baseEnd_6139290 := by
    simpa [prefixWord, tailWord_6139290, baseEnd_6139290] using wordTrace_append hprefix tailTrace_6139290
  have hstable : (prefixWord ++ tailWord_6139290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139290).length < 2 ^ (prefixWord ++ tailWord_6139290).sum := by decide
  have hdescent : baseEnd_6139290 < baseStart_6139290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139300 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_6139300 : Nat := 118140960795 + 6139300 * 2 ^ 59
def prefixEnd_6139300 : Nat := 4983230072969 + 3 ^ 40 * 6139300 * 2
def baseEnd_6139300 : Nat := 3152411782147935194215879

theorem tailTrace_6139300 : CollatzResearch.WordTrace tailWord_6139300 prefixEnd_6139300 3152411782147935194215879 := by
  unfold tailWord_6139300
  simp only [CollatzResearch.WordTrace]
  refine ⟨111959333329186041904523677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149279111105581389206031569 111959333329186041904523677)
  ·
    refine ⟨41984749998444765714196379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111959333329186041904523677 41984749998444765714196379)
    ·
      refine ⟨62977124997667148571294569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41984749998444765714196379 62977124997667148571294569)
      ·
        refine ⟨47232843748250361428470927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62977124997667148571294569 47232843748250361428470927)
        ·
          refine ⟨70849265622375542142706391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47232843748250361428470927 70849265622375542142706391)
          ·
            refine ⟨106273898433563313214059587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70849265622375542142706391 106273898433563313214059587)
            ·
              refine ⟨159410847650344969821089381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106273898433563313214059587 159410847650344969821089381)
              ·
                refine ⟨29889533934439681841454259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159410847650344969821089381 29889533934439681841454259)
                ·
                  refine ⟨44834300901659522762181389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29889533934439681841454259 44834300901659522762181389)
                  ·
                    refine ⟨16812862838122321035818021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44834300901659522762181389 16812862838122321035818021)
                    ·
                      refine ⟨3152411782147935194215879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16812862838122321035818021 3152411782147935194215879)
                      ·
                        rfl

theorem cell23_6139300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_6139300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139300 prefixEnd_6139300 := by exact prefixLift 6139300
  have htrace : WordTrace (prefixWord ++ tailWord_6139300) baseStart_6139300 baseEnd_6139300 := by
    simpa [prefixWord, tailWord_6139300, baseEnd_6139300] using wordTrace_append hprefix tailTrace_6139300
  have hstable : (prefixWord ++ tailWord_6139300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139300).length < 2 ^ (prefixWord ++ tailWord_6139300).sum := by decide
  have hdescent : baseEnd_6139300 < baseStart_6139300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139317 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6139317 : Nat := 118140960795 + 6139317 * 2 ^ 59
def prefixEnd_6139317 : Nat := 4983230072969 + 3 ^ 40 * 6139317 * 2
def baseEnd_6139317 : Nat := 3152420511319061627703301

theorem tailTrace_6139317 : CollatzResearch.WordTrace tailWord_6139317 prefixEnd_6139317 3152420511319061627703301 := by
  unfold tailWord_6139317
  simp only [CollatzResearch.WordTrace]
  refine ⟨223919286699310495712416205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149279524466206997141610803 223919286699310495712416205)
  ·
    refine ⟨83969732512241435892156077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223919286699310495712416205 83969732512241435892156077)
    ·
      refine ⟨31488649692090538459558529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83969732512241435892156077 31488649692090538459558529)
      ·
        refine ⟨23616487269067903844668897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31488649692090538459558529 23616487269067903844668897)
        ·
          refine ⟨17712365451800927883501673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23616487269067903844668897 17712365451800927883501673)
          ·
            refine ⟨13284274088850695912626255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17712365451800927883501673 13284274088850695912626255)
            ·
              refine ⟨19926411133276043868939383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284274088850695912626255 19926411133276043868939383)
              ·
                refine ⟨29889616699914065803409075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19926411133276043868939383 29889616699914065803409075)
                ·
                  refine ⟨44834425049871098705113613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29889616699914065803409075 44834425049871098705113613)
                  ·
                    refine ⟨16812909393701662014417605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44834425049871098705113613 16812909393701662014417605)
                    ·
                      refine ⟨3152420511319061627703301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16812909393701662014417605 3152420511319061627703301)
                      ·
                        rfl

theorem cell23_6139317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6139317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139317 prefixEnd_6139317 := by exact prefixLift 6139317
  have htrace : WordTrace (prefixWord ++ tailWord_6139317) baseStart_6139317 baseEnd_6139317 := by
    simpa [prefixWord, tailWord_6139317, baseEnd_6139317] using wordTrace_append hprefix tailTrace_6139317
  have hstable : (prefixWord ++ tailWord_6139317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139317).length < 2 ^ (prefixWord ++ tailWord_6139317).sum := by decide
  have hdescent : baseEnd_6139317 < baseStart_6139317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139378 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_6139378 : Nat := 118140960795 + 6139378 * 2 ^ 59
def prefixEnd_6139378 : Nat := 4983230072969 + 3 ^ 40 * 6139378 * 2
def baseEnd_6139378 : Nat := 1050817277879661963013507

theorem tailTrace_6139378 : CollatzResearch.WordTrace tailWord_6139378 prefixEnd_6139378 1050817277879661963013507 := by
  unfold tailWord_6139378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55980377888022375782596697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149281007701393002086924525 55980377888022375782596697)
  ·
    refine ⟨41985283416016781836947523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55980377888022375782596697 41985283416016781836947523)
    ·
      refine ⟨62977925124025172755421285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41985283416016781836947523 62977925124025172755421285)
      ·
        refine ⟨11808360960754719891641491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62977925124025172755421285 11808360960754719891641491)
        ·
          refine ⟨17712541441132079837462237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808360960754719891641491 17712541441132079837462237)
          ·
            refine ⟨6642203040424529939048339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17712541441132079837462237 6642203040424529939048339)
            ·
              refine ⟨9963304560636794908572509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642203040424529939048339 9963304560636794908572509)
              ·
                refine ⟨3736239210238798090714691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9963304560636794908572509 3736239210238798090714691)
                ·
                  refine ⟨5604358815358197136072037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736239210238798090714691 5604358815358197136072037)
                  ·
                    refine ⟨1050817277879661963013507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604358815358197136072037 1050817277879661963013507)
                    ·
                      rfl

theorem cell23_6139378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_6139378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139378 prefixEnd_6139378 := by exact prefixLift 6139378
  have htrace : WordTrace (prefixWord ++ tailWord_6139378) baseStart_6139378 baseEnd_6139378 := by
    simpa [prefixWord, tailWord_6139378, baseEnd_6139378] using wordTrace_append hprefix tailTrace_6139378
  have hstable : (prefixWord ++ tailWord_6139378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139378).length < 2 ^ (prefixWord ++ tailWord_6139378).sum := by decide
  have hdescent : baseEnd_6139378 < baseStart_6139378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139424 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6139424 : Nat := 118140960795 + 6139424 * 2 ^ 59
def prefixEnd_6139424 : Nat := 4983230072969 + 3 ^ 40 * 6139424 * 2
def baseEnd_6139424 : Nat := 3152475453749092709065309

theorem tailTrace_6139424 : CollatzResearch.WordTrace tailWord_6139424 prefixEnd_6139424 3152475453749092709065309 := by
  unfold tailWord_6139424
  simp only [CollatzResearch.WordTrace]
  refine ⟨111961594654961426493280663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149282126206615235324374217 111961594654961426493280663)
  ·
    refine ⟨167942391982442139739920995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111961594654961426493280663 167942391982442139739920995)
    ·
      refine ⟨251913587973663209609881493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167942391982442139739920995 251913587973663209609881493)
      ·
        refine ⟨11808449436265462950463195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251913587973663209609881493 11808449436265462950463195)
        ·
          refine ⟨17712674154398194425694793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808449436265462950463195 17712674154398194425694793)
          ·
            refine ⟨13284505615798645819271095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17712674154398194425694793 13284505615798645819271095)
            ·
              refine ⟨19926758423697968728906643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284505615798645819271095 19926758423697968728906643)
              ·
                refine ⟨29890137635546953093359965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19926758423697968728906643 29890137635546953093359965)
                ·
                  refine ⟨11208801613330107410009987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29890137635546953093359965 11208801613330107410009987)
                  ·
                    refine ⟨16813202419995161115014981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11208801613330107410009987 16813202419995161115014981)
                    ·
                      refine ⟨3152475453749092709065309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16813202419995161115014981 3152475453749092709065309)
                      ·
                        rfl

theorem cell23_6139424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6139424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139424 prefixEnd_6139424 := by exact prefixLift 6139424
  have htrace : WordTrace (prefixWord ++ tailWord_6139424) baseStart_6139424 baseEnd_6139424 := by
    simpa [prefixWord, tailWord_6139424, baseEnd_6139424] using wordTrace_append hprefix tailTrace_6139424
  have hstable : (prefixWord ++ tailWord_6139424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139424).length < 2 ^ (prefixWord ++ tailWord_6139424).sum := by decide
  have hdescent : baseEnd_6139424 < baseStart_6139424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139452 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_6139452 : Nat := 118140960795 + 6139452 * 2 ^ 59
def prefixEnd_6139452 : Nat := 4983230072969 + 3 ^ 40 * 6139452 * 2
def baseEnd_6139452 : Nat := 3152489831207418599515181

theorem tailTrace_6139452 : CollatzResearch.WordTrace tailWord_6139452 prefixEnd_6139452 3152489831207418599515181 := by
  unfold tailWord_6139452
  simp only [CollatzResearch.WordTrace]
  refine ⟨111962105276910706884290305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149282807035880942512387073 111962105276910706884290305)
  ·
    refine ⟨83971578957683030163217729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111962105276910706884290305 83971578957683030163217729)
    ·
      refine ⟨62978684218262272622413297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83971578957683030163217729 62978684218262272622413297)
      ·
        refine ⟨47234013163696704466809973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62978684218262272622413297 47234013163696704466809973)
        ·
          refine ⟨4428188734096566043763435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47234013163696704466809973 4428188734096566043763435)
          ·
            refine ⟨6642283101144849065645153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428188734096566043763435 6642283101144849065645153)
            ·
              refine ⟨4981712325858636799233865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642283101144849065645153 4981712325858636799233865)
              ·
                refine ⟨3736284244393977599425399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981712325858636799233865 3736284244393977599425399)
                ·
                  refine ⟨5604426366590966399138099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736284244393977599425399 5604426366590966399138099)
                  ·
                    refine ⟨8406639549886449598707149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604426366590966399138099 8406639549886449598707149)
                    ·
                      refine ⟨3152489831207418599515181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406639549886449598707149 3152489831207418599515181)
                      ·
                        rfl

theorem cell23_6139452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_6139452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139452 prefixEnd_6139452 := by exact prefixLift 6139452
  have htrace : WordTrace (prefixWord ++ tailWord_6139452) baseStart_6139452 baseEnd_6139452 := by
    simpa [prefixWord, tailWord_6139452, baseEnd_6139452] using wordTrace_append hprefix tailTrace_6139452
  have hstable : (prefixWord ++ tailWord_6139452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139452).length < 2 ^ (prefixWord ++ tailWord_6139452).sum := by decide
  have hdescent : baseEnd_6139452 < baseStart_6139452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139474 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_6139474 : Nat := 118140960795 + 6139474 * 2 ^ 59
def prefixEnd_6139474 : Nat := 4983230072969 + 3 ^ 40 * 6139474 * 2
def baseEnd_6139474 : Nat := 3152501127781817513440079

theorem tailTrace_6139474 : CollatzResearch.WordTrace tailWord_6139474 prefixEnd_6139474 3152501127781817513440079 := by
  unfold tailWord_6139474
  simp only [CollatzResearch.WordTrace]
  refine ⟨55981253239935427881470369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149283341973161141017254317 55981253239935427881470369)
  ·
    refine ⟨41985939929951570911102777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55981253239935427881470369 41985939929951570911102777)
    ·
      refine ⟨31489454947463678183327083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41985939929951570911102777 31489454947463678183327083)
      ·
        refine ⟨47234182421195517274990625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31489454947463678183327083 47234182421195517274990625)
        ·
          refine ⟨35425636815896637956242969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47234182421195517274990625 35425636815896637956242969)
          ·
            refine ⟨26569227611922478467182227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35425636815896637956242969 26569227611922478467182227)
            ·
              refine ⟨39853841417883717700773341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26569227611922478467182227 39853841417883717700773341)
              ·
                refine ⟨14945190531706394137790003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39853841417883717700773341 14945190531706394137790003)
                ·
                  refine ⟨22417785797559591206685005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14945190531706394137790003 22417785797559591206685005)
                  ·
                    refine ⟨8406669674084846702506877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22417785797559591206685005 8406669674084846702506877)
                    ·
                      refine ⟨3152501127781817513440079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406669674084846702506877 3152501127781817513440079)
                      ·
                        rfl

theorem cell23_6139474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_6139474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139474 prefixEnd_6139474 := by exact prefixLift 6139474
  have htrace : WordTrace (prefixWord ++ tailWord_6139474) baseStart_6139474 baseEnd_6139474 := by
    simpa [prefixWord, tailWord_6139474, baseEnd_6139474] using wordTrace_append hprefix tailTrace_6139474
  have hstable : (prefixWord ++ tailWord_6139474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139474).length < 2 ^ (prefixWord ++ tailWord_6139474).sum := by decide
  have hdescent : baseEnd_6139474 < baseStart_6139474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139551 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6139551 : Nat := 118140960795 + 6139551 * 2 ^ 59
def prefixEnd_6139551 : Nat := 4983230072969 + 3 ^ 40 * 6139551 * 2
def baseEnd_6139551 : Nat := 3152540665792213712177225

theorem tailTrace_6139551 : CollatzResearch.WordTrace tailWord_6139551 prefixEnd_6139551 3152540665792213712177225 := by
  unfold tailWord_6139551
  simp only [CollatzResearch.WordTrace]
  refine ⟨223927821380462753676434507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149285214253641835784289671 223927821380462753676434507)
  ·
    refine ⟨335891732070694130514651761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223927821380462753676434507 335891732070694130514651761)
    ·
      refine ⟨251918799053020597885988821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335891732070694130514651761 251918799053020597885988821)
      ·
        refine ⟨5904346852805170262952863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 251918799053020597885988821 5904346852805170262952863)
        ·
          refine ⟨8856520279207755394429295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904346852805170262952863 8856520279207755394429295)
          ·
            refine ⟨13284780418811633091643943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856520279207755394429295 13284780418811633091643943)
            ·
              refine ⟨19927170628217449637465915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284780418811633091643943 19927170628217449637465915)
              ·
                refine ⟨29890755942326174456198873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19927170628217449637465915 29890755942326174456198873)
                ·
                  refine ⟨22418066956744630842149155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29890755942326174456198873 22418066956744630842149155)
                  ·
                    refine ⟨33627100435116946263223733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22418066956744630842149155 33627100435116946263223733)
                    ·
                      refine ⟨3152540665792213712177225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33627100435116946263223733 3152540665792213712177225)
                      ·
                        rfl

theorem cell23_6139551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6139551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139551 prefixEnd_6139551 := by exact prefixLift 6139551
  have htrace : WordTrace (prefixWord ++ tailWord_6139551) baseStart_6139551 baseEnd_6139551 := by
    simpa [prefixWord, tailWord_6139551, baseEnd_6139551] using wordTrace_append hprefix tailTrace_6139551
  have hstable : (prefixWord ++ tailWord_6139551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139551).length < 2 ^ (prefixWord ++ tailWord_6139551).sum := by decide
  have hdescent : baseEnd_6139551 < baseStart_6139551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139571 : List Nat := [1, 1, 1, 2, 3, 3, 5, 2, 5]
def baseStart_6139571 : Nat := 118140960795 + 6139571 * 2 ^ 59
def prefixEnd_6139571 : Nat := 4983230072969 + 3 ^ 40 * 6139571 * 2
def baseEnd_6139571 : Nat := 350283437267255959325237

theorem tailTrace_6139571 : CollatzResearch.WordTrace tailWord_6139571 prefixEnd_6139571 350283437267255959325237 := by
  unfold tailWord_6139571
  simp only [CollatzResearch.WordTrace]
  refine ⟨223928550840390297092162567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149285700560260198061441711 223928550840390297092162567)
  ·
    refine ⟨335892826260585445638243851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223928550840390297092162567 335892826260585445638243851)
    ·
      refine ⟨503839239390878168457365777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335892826260585445638243851 503839239390878168457365777)
      ·
        refine ⟨377879429543158626343024333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503839239390878168457365777 377879429543158626343024333)
        ·
          refine ⟨141704786078684484878634125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377879429543158626343024333 141704786078684484878634125)
          ·
            refine ⟨53139294779506681829487797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141704786078684484878634125 53139294779506681829487797)
            ·
              refine ⟨4981808885578751421514481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53139294779506681829487797 4981808885578751421514481)
              ·
                refine ⟨3736356664184063566135861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981808885578751421514481 3736356664184063566135861)
                ·
                  refine ⟨350283437267255959325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736356664184063566135861 350283437267255959325237)
                  ·
                    rfl

theorem cell23_6139571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 5].length) (baseStart_6139571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139571 prefixEnd_6139571 := by exact prefixLift 6139571
  have htrace : WordTrace (prefixWord ++ tailWord_6139571) baseStart_6139571 baseEnd_6139571 := by
    simpa [prefixWord, tailWord_6139571, baseEnd_6139571] using wordTrace_append hprefix tailTrace_6139571
  have hstable : (prefixWord ++ tailWord_6139571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139571).length < 2 ^ (prefixWord ++ tailWord_6139571).sum := by decide
  have hdescent : baseEnd_6139571 < baseStart_6139571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139577 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6139577 : Nat := 118140960795 + 6139577 * 2 ^ 59
def prefixEnd_6139577 : Nat := 4983230072969 + 3 ^ 40 * 6139577 * 2
def baseEnd_6139577 : Nat := 3152554016289230610452105

theorem tailTrace_6139577 : CollatzResearch.WordTrace tailWord_6139577 prefixEnd_6139577 3152554016289230610452105 := by
  unfold tailWord_6139577
  simp only [CollatzResearch.WordTrace]
  refine ⟨223928769678368560116880985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149285846452245706744587323 223928769678368560116880985)
  ·
    refine ⟨167946577258776420087660739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223928769678368560116880985 167946577258776420087660739)
    ·
      refine ⟨251919865888164630131491109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167946577258776420087660739 251919865888164630131491109)
      ·
        refine ⟨47234974854030868149654583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251919865888164630131491109 47234974854030868149654583)
        ·
          refine ⟨70852462281046302224481875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47234974854030868149654583 70852462281046302224481875)
          ·
            refine ⟨106278693421569453336722813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70852462281046302224481875 106278693421569453336722813)
            ·
              refine ⟨39854510033088545001271055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106278693421569453336722813 39854510033088545001271055)
              ·
                refine ⟨59781765049632817501906583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39854510033088545001271055 59781765049632817501906583)
                ·
                  refine ⟨89672647574449226252859875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59781765049632817501906583 89672647574449226252859875)
                  ·
                    refine ⟨134508971361673839379289813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89672647574449226252859875 134508971361673839379289813)
                    ·
                      refine ⟨3152554016289230610452105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134508971361673839379289813 3152554016289230610452105)
                      ·
                        rfl

theorem cell23_6139577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6139577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139577 prefixEnd_6139577 := by exact prefixLift 6139577
  have htrace : WordTrace (prefixWord ++ tailWord_6139577) baseStart_6139577 baseEnd_6139577 := by
    simpa [prefixWord, tailWord_6139577, baseEnd_6139577] using wordTrace_append hprefix tailTrace_6139577
  have hstable : (prefixWord ++ tailWord_6139577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139577).length < 2 ^ (prefixWord ++ tailWord_6139577).sum := by decide
  have hdescent : baseEnd_6139577 < baseStart_6139577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139582 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_6139582 : Nat := 118140960795 + 6139582 * 2 ^ 59
def prefixEnd_6139582 : Nat := 4983230072969 + 3 ^ 40 * 6139582 * 2
def baseEnd_6139582 : Nat := 3152556583692503090889583

theorem tailTrace_6139582 : CollatzResearch.WordTrace tailWord_6139582 prefixEnd_6139582 3152556583692503090889583 := by
  unfold tailWord_6139582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991119005418805746351625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149285968028900297313875333 27991119005418805746351625)
  ·
    refine ⟨20993339254064104309763719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27991119005418805746351625 20993339254064104309763719)
    ·
      refine ⟨31490008881096156464645579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20993339254064104309763719 31490008881096156464645579)
      ·
        refine ⟨47235013321644234696968369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31490008881096156464645579 47235013321644234696968369)
        ·
          refine ⟨35426259991233176022726277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47235013321644234696968369 35426259991233176022726277)
          ·
            refine ⟨6642423748356220504261177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35426259991233176022726277 6642423748356220504261177)
            ·
              refine ⟨4981817811267165378195883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642423748356220504261177 4981817811267165378195883)
              ·
                refine ⟨7472726716900748067293825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981817811267165378195883 7472726716900748067293825)
                ·
                  refine ⟨5604545037675561050470369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472726716900748067293825 5604545037675561050470369)
                  ·
                    refine ⟨4203408778256670787852777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604545037675561050470369 4203408778256670787852777)
                    ·
                      refine ⟨3152556583692503090889583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203408778256670787852777 3152556583692503090889583)
                      ·
                        rfl

theorem cell23_6139582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_6139582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139582 prefixEnd_6139582 := by exact prefixLift 6139582
  have htrace : WordTrace (prefixWord ++ tailWord_6139582) baseStart_6139582 baseEnd_6139582 := by
    simpa [prefixWord, tailWord_6139582, baseEnd_6139582] using wordTrace_append hprefix tailTrace_6139582
  have hstable : (prefixWord ++ tailWord_6139582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139582).length < 2 ^ (prefixWord ++ tailWord_6139582).sum := by decide
  have hdescent : baseEnd_6139582 < baseStart_6139582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139586 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6139586 : Nat := 118140960795 + 6139586 * 2 ^ 59
def prefixEnd_6139586 : Nat := 4983230072969 + 3 ^ 40 * 6139586 * 2
def baseEnd_6139586 : Nat := 3152558637615121075239565

theorem tailTrace_6139586 : CollatzResearch.WordTrace tailWord_6139586 prefixEnd_6139586 3152558637615121075239565 := by
  unfold tailWord_6139586
  simp only [CollatzResearch.WordTrace]
  refine ⟨55982274483833988663489653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149286065290223969769305741 55982274483833988663489653)
  ·
    refine ⟨5248338232859436437202155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55982274483833988663489653 5248338232859436437202155)
    ·
      refine ⟨7872507349289154655803233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248338232859436437202155 7872507349289154655803233)
      ·
        refine ⟨5904380511966865991852425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7872507349289154655803233 5904380511966865991852425)
        ·
          refine ⟨4428285383975149493889319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904380511966865991852425 4428285383975149493889319)
          ·
            refine ⟨6642428075962724240833979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428285383975149493889319 6642428075962724240833979)
            ·
              refine ⟨9963642113944086361250969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642428075962724240833979 9963642113944086361250969)
              ·
                refine ⟨7472731585458064770938227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9963642113944086361250969 7472731585458064770938227)
                ·
                  refine ⟨11209097378187097156407341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472731585458064770938227 11209097378187097156407341)
                  ·
                    refine ⟨4203411516820161433652753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11209097378187097156407341 4203411516820161433652753)
                    ·
                      refine ⟨3152558637615121075239565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203411516820161433652753 3152558637615121075239565)
                      ·
                        rfl

theorem cell23_6139586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6139586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139586 prefixEnd_6139586 := by exact prefixLift 6139586
  have htrace : WordTrace (prefixWord ++ tailWord_6139586) baseStart_6139586 baseEnd_6139586 := by
    simpa [prefixWord, tailWord_6139586, baseEnd_6139586] using wordTrace_append hprefix tailTrace_6139586
  have hstable : (prefixWord ++ tailWord_6139586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139586).length < 2 ^ (prefixWord ++ tailWord_6139586).sum := by decide
  have hdescent : baseEnd_6139586 < baseStart_6139586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139621 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6139621 : Nat := 118140960795 + 6139621 * 2 ^ 59
def prefixEnd_6139621 : Nat := 4983230072969 + 3 ^ 40 * 6139621 * 2
def baseEnd_6139621 : Nat := 3152576609438028438301903

theorem tailTrace_6139621 : CollatzResearch.WordTrace tailWord_6139621 prefixEnd_6139621 3152576609438028438301903 := by
  unfold tailWord_6139621
  simp only [CollatzResearch.WordTrace]
  refine ⟨223930374490209155631482717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149286916326806103754321811 223930374490209155631482717)
  ·
    refine ⟨83973890433828433361806019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223930374490209155631482717 83973890433828433361806019)
    ·
      refine ⟨125960835650742650042709029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83973890433828433361806019 125960835650742650042709029)
      ·
        refine ⟨23617656684514246883007943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125960835650742650042709029 23617656684514246883007943)
        ·
          refine ⟨35426485026771370324511915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617656684514246883007943 35426485026771370324511915)
          ·
            refine ⟨53139727540157055486767873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35426485026771370324511915 53139727540157055486767873)
            ·
              refine ⟨39854795655117791615075905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53139727540157055486767873 39854795655117791615075905)
              ·
                refine ⟨29891096741338343711306929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39854795655117791615075905 29891096741338343711306929)
                ·
                  refine ⟨22418322556003757783480197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29891096741338343711306929 22418322556003757783480197)
                  ·
                    refine ⟨4203435479250704584402537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22418322556003757783480197 4203435479250704584402537)
                    ·
                      refine ⟨3152576609438028438301903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203435479250704584402537 3152576609438028438301903)
                      ·
                        rfl

theorem cell23_6139621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6139621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139621 prefixEnd_6139621 := by exact prefixLift 6139621
  have htrace : WordTrace (prefixWord ++ tailWord_6139621) baseStart_6139621 baseEnd_6139621 := by
    simpa [prefixWord, tailWord_6139621, baseEnd_6139621] using wordTrace_append hprefix tailTrace_6139621
  have hstable : (prefixWord ++ tailWord_6139621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139621).length < 2 ^ (prefixWord ++ tailWord_6139621).sum := by decide
  have hdescent : baseEnd_6139621 < baseStart_6139621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139627 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 8]
def baseStart_6139627 : Nat := 118140960795 + 6139627 * 2 ^ 59
def prefixEnd_6139627 : Nat := 4983230072969 + 3 ^ 40 * 6139627 * 2
def baseEnd_6139627 : Nat := 350286632257995046091875

theorem tailTrace_6139627 : CollatzResearch.WordTrace tailWord_6139627 prefixEnd_6139627 350286632257995046091875 := by
  unfold tailWord_6139627
  simp only [CollatzResearch.WordTrace]
  refine ⟨223930593328187418656201135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149287062218791612437467423 223930593328187418656201135)
  ·
    refine ⟨335895889992281127984301703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223930593328187418656201135 335895889992281127984301703)
    ·
      refine ⟨503843834988421691976452555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335895889992281127984301703 503843834988421691976452555)
      ·
        refine ⟨755765752482632537964678833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503843834988421691976452555 755765752482632537964678833)
        ·
          refine ⟨566824314361974403473509125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755765752482632537964678833 566824314361974403473509125)
          ·
            refine ⟨106279558942870200651282961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 566824314361974403473509125 106279558942870200651282961)
            ·
              refine ⟨79709669207152650488462221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106279558942870200651282961 79709669207152650488462221)
              ·
                refine ⟨29891125952682243933173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79709669207152650488462221 29891125952682243933173333)
                ·
                  refine ⟨350286632257995046091875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29891125952682243933173333 350286632257995046091875)
                  ·
                    rfl

theorem cell23_6139627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_6139627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139627 prefixEnd_6139627 := by exact prefixLift 6139627
  have htrace : WordTrace (prefixWord ++ tailWord_6139627) baseStart_6139627 baseEnd_6139627 := by
    simpa [prefixWord, tailWord_6139627, baseEnd_6139627] using wordTrace_append hprefix tailTrace_6139627
  have hstable : (prefixWord ++ tailWord_6139627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139627).length < 2 ^ (prefixWord ++ tailWord_6139627).sum := by decide
  have hdescent : baseEnd_6139627 < baseStart_6139627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139638 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6139638 : Nat := 118140960795 + 6139638 * 2 ^ 59
def prefixEnd_6139638 : Nat := 4983230072969 + 3 ^ 40 * 6139638 * 2
def baseEnd_6139638 : Nat := 3152585338609154871789325

theorem tailTrace_6139638 : CollatzResearch.WordTrace tailWord_6139638 prefixEnd_6139638 3152585338609154871789325 := by
  unfold tailWord_6139638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995687158196722970928223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149287329687431711689901045 13995687158196722970928223)
  ·
    refine ⟨20993530737295084456392335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13995687158196722970928223 20993530737295084456392335)
    ·
      refine ⟨31490296105942626684588503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20993530737295084456392335 31490296105942626684588503)
      ·
        refine ⟨47235444158913940026882755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31490296105942626684588503 47235444158913940026882755)
        ·
          refine ⟨70853166238370910040324133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47235444158913940026882755 70853166238370910040324133)
          ·
            refine ⟨13284968669694545632560775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70853166238370910040324133 13284968669694545632560775)
            ·
              refine ⟨19927453004541818448841163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284968669694545632560775 19927453004541818448841163)
              ·
                refine ⟨29891179506812727673261745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19927453004541818448841163 29891179506812727673261745)
                ·
                  refine ⟨22418384630109545754946309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29891179506812727673261745 22418384630109545754946309)
                  ·
                    refine ⟨4203447118145539829052433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22418384630109545754946309 4203447118145539829052433)
                    ·
                      refine ⟨3152585338609154871789325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203447118145539829052433 3152585338609154871789325)
                      ·
                        rfl

theorem cell23_6139638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6139638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139638 prefixEnd_6139638 := by exact prefixLift 6139638
  have htrace : WordTrace (prefixWord ++ tailWord_6139638) baseStart_6139638 baseEnd_6139638 := by
    simpa [prefixWord, tailWord_6139638, baseEnd_6139638] using wordTrace_append hprefix tailTrace_6139638
  have hstable : (prefixWord ++ tailWord_6139638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139638).length < 2 ^ (prefixWord ++ tailWord_6139638).sum := by decide
  have hdescent : baseEnd_6139638 < baseStart_6139638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139644 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 6]
def baseStart_6139644 : Nat := 118140960795 + 6139644 * 2 ^ 59
def prefixEnd_6139644 : Nat := 4983230072969 + 3 ^ 40 * 6139644 * 2
def baseEnd_6139644 : Nat := 350287602165897983146033

theorem tailTrace_6139644 : CollatzResearch.WordTrace tailWord_6139644 prefixEnd_6139644 350287602165897983146033 := by
  unfold tailWord_6139644
  simp only [CollatzResearch.WordTrace]
  refine ⟨111965606684562915279784993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149287475579417220373046657 111965606684562915279784993)
  ·
    refine ⟨83974205013422186459838745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111965606684562915279784993 83974205013422186459838745)
    ·
      refine ⟨62980653760066639844879059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83974205013422186459838745 62980653760066639844879059)
      ·
        refine ⟨94470980640099959767318589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62980653760066639844879059 94470980640099959767318589)
        ·
          refine ⟨35426617740037484912744471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94470980640099959767318589 35426617740037484912744471)
          ·
            refine ⟨53139926610056227369116707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35426617740037484912744471 53139926610056227369116707)
            ·
              refine ⟨79709889915084341053675061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53139926610056227369116707 79709889915084341053675061)
              ·
                refine ⟨7472802179539156973782037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79709889915084341053675061 7472802179539156973782037)
                ·
                  refine ⟨350287602165897983146033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7472802179539156973782037 350287602165897983146033)
                  ·
                    rfl

theorem cell23_6139644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_6139644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139644 prefixEnd_6139644 := by exact prefixLift 6139644
  have htrace : WordTrace (prefixWord ++ tailWord_6139644) baseStart_6139644 baseEnd_6139644 := by
    simpa [prefixWord, tailWord_6139644, baseEnd_6139644] using wordTrace_append hprefix tailTrace_6139644
  have hstable : (prefixWord ++ tailWord_6139644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139644).length < 2 ^ (prefixWord ++ tailWord_6139644).sum := by decide
  have hdescent : baseEnd_6139644 < baseStart_6139644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139655 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6139655 : Nat := 118140960795 + 6139655 * 2 ^ 59
def prefixEnd_6139655 : Nat := 4983230072969 + 3 ^ 40 * 6139655 * 2
def baseEnd_6139655 : Nat := 3152594067780281305276747

theorem tailTrace_6139655 : CollatzResearch.WordTrace tailWord_6139655 prefixEnd_6139655 3152594067780281305276747 := by
  unfold tailWord_6139655
  simp only [CollatzResearch.WordTrace]
  refine ⟨223931614572085979438220419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149287743048057319625480279 223931614572085979438220419)
  ·
    refine ⟨335897421858128969157330629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223931614572085979438220419 335897421858128969157330629)
    ·
      refine ⟨62980766598399181716999493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335897421858128969157330629 62980766598399181716999493)
      ·
        refine ⟨11808893737199846571937405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62980766598399181716999493 11808893737199846571937405)
        ·
          refine ⟨4428335151449942464476527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11808893737199846571937405 4428335151449942464476527)
          ·
            refine ⟨6642502727174913696714791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428335151449942464476527 6642502727174913696714791)
            ·
              refine ⟨9963754090762370545072187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642502727174913696714791 9963754090762370545072187)
              ·
                refine ⟨14945631136143555817608281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963754090762370545072187 14945631136143555817608281)
                ·
                  refine ⟨11209223352107666863206211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14945631136143555817608281 11209223352107666863206211)
                  ·
                    refine ⟨16813835028161500294809317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11209223352107666863206211 16813835028161500294809317)
                    ·
                      refine ⟨3152594067780281305276747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16813835028161500294809317 3152594067780281305276747)
                      ·
                        rfl

theorem cell23_6139655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6139655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139655 prefixEnd_6139655 := by exact prefixLift 6139655
  have htrace : WordTrace (prefixWord ++ tailWord_6139655) baseStart_6139655 baseEnd_6139655 := by
    simpa [prefixWord, tailWord_6139655, baseEnd_6139655] using wordTrace_append hprefix tailTrace_6139655
  have hstable : (prefixWord ++ tailWord_6139655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139655).length < 2 ^ (prefixWord ++ tailWord_6139655).sum := by decide
  have hdescent : baseEnd_6139655 < baseStart_6139655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139658 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_6139658 : Nat := 118140960795 + 6139658 * 2 ^ 59
def prefixEnd_6139658 : Nat := 4983230072969 + 3 ^ 40 * 6139658 * 2
def baseEnd_6139658 : Nat := 3152595608222244793539233

theorem tailTrace_6139658 : CollatzResearch.WordTrace tailWord_6139658 prefixEnd_6139658 3152595608222244793539233 := by
  unfold tailWord_6139658
  simp only [CollatzResearch.WordTrace]
  refine ⟨55982930997768777737644907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149287815994050073967053085 55982930997768777737644907)
  ·
    refine ⟨83974396496653166606467361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55982930997768777737644907 83974396496653166606467361)
    ·
      refine ⟨62980797372489874954850521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83974396496653166606467361 62980797372489874954850521)
      ·
        refine ⟨47235598029367406216137891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62980797372489874954850521 47235598029367406216137891)
        ·
          refine ⟨70853397044051109324206837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47235598029367406216137891 70853397044051109324206837)
          ·
            refine ⟨6642505972879791499144391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70853397044051109324206837 6642505972879791499144391)
            ·
              refine ⟨9963758959319687248716587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642505972879791499144391 9963758959319687248716587)
              ·
                refine ⟨14945638438979530873074881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963758959319687248716587 14945638438979530873074881)
                ·
                  refine ⟨11209228829234648154806161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14945638438979530873074881 11209228829234648154806161)
                  ·
                    refine ⟨8406921621925986116104621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11209228829234648154806161 8406921621925986116104621)
                    ·
                      refine ⟨3152595608222244793539233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406921621925986116104621 3152595608222244793539233)
                      ·
                        rfl

theorem cell23_6139658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_6139658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139658 prefixEnd_6139658 := by exact prefixLift 6139658
  have htrace : WordTrace (prefixWord ++ tailWord_6139658) baseStart_6139658 baseEnd_6139658 := by
    simpa [prefixWord, tailWord_6139658, baseEnd_6139658] using wordTrace_append hprefix tailTrace_6139658
  have hstable : (prefixWord ++ tailWord_6139658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139658).length < 2 ^ (prefixWord ++ tailWord_6139658).sum := by decide
  have hdescent : baseEnd_6139658 < baseStart_6139658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139688 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6139688 : Nat := 118140960795 + 6139688 * 2 ^ 59
def prefixEnd_6139688 : Nat := 4983230072969 + 3 ^ 40 * 6139688 * 2
def baseEnd_6139688 : Nat := 3152611012641879676164095

theorem tailTrace_6139688 : CollatzResearch.WordTrace tailWord_6139688 prefixEnd_6139688 3152611012641879676164095 := by
  unfold tailWord_6139688
  simp only [CollatzResearch.WordTrace]
  refine ⟨111966409090483213037085859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149288545453977617382781145 111966409090483213037085859)
  ·
    refine ⟨167949613635724819555628789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111966409090483213037085859 167949613635724819555628789)
    ·
      refine ⟨15745276278349201833340199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167949613635724819555628789 15745276278349201833340199)
      ·
        refine ⟨23617914417523802750010299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745276278349201833340199 23617914417523802750010299)
        ·
          refine ⟨35426871626285704125015449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617914417523802750010299 35426871626285704125015449)
          ·
            refine ⟨26570153719714278093761587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35426871626285704125015449 26570153719714278093761587)
            ·
              refine ⟨39855230579571417140642381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26570153719714278093761587 39855230579571417140642381)
              ·
                refine ⟨14945711467339281427740893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39855230579571417140642381 14945711467339281427740893)
                ·
                  refine ⟨5604641800252230535402835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14945711467339281427740893 5604641800252230535402835)
                  ·
                    refine ⟨8406962700378345803104253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604641800252230535402835 8406962700378345803104253)
                    ·
                      refine ⟨3152611012641879676164095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8406962700378345803104253 3152611012641879676164095)
                      ·
                        rfl

theorem cell23_6139688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6139688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139688 prefixEnd_6139688 := by exact prefixLift 6139688
  have htrace : WordTrace (prefixWord ++ tailWord_6139688) baseStart_6139688 baseEnd_6139688 := by
    simpa [prefixWord, tailWord_6139688, baseEnd_6139688] using wordTrace_append hprefix tailTrace_6139688
  have hstable : (prefixWord ++ tailWord_6139688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139688).length < 2 ^ (prefixWord ++ tailWord_6139688).sum := by decide
  have hdescent : baseEnd_6139688 < baseStart_6139688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139761 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_6139761 : Nat := 118140960795 + 6139761 * 2 ^ 59
def prefixEnd_6139761 : Nat := 4983230072969 + 3 ^ 40 * 6139761 * 2
def baseEnd_6139761 : Nat := 3152648496729657890551259

theorem tailTrace_6139761 : CollatzResearch.WordTrace tailWord_6139761 prefixEnd_6139761 3152648496729657890551259 := by
  unfold tailWord_6139761
  simp only [CollatzResearch.WordTrace]
  refine ⟨223935480709701959541579137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149290320473134639694386091 223935480709701959541579137)
  ·
    refine ⟨167951610532276469656184353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223935480709701959541579137 167951610532276469656184353)
    ·
      refine ⟨125963707899207352242138265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167951610532276469656184353 125963707899207352242138265)
      ·
        refine ⟨94472780924405514181603699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125963707899207352242138265 94472780924405514181603699)
        ·
          refine ⟨141709171386608271272405549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94472780924405514181603699 141709171386608271272405549)
          ·
            refine ⟨53140939269978101727152081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141709171386608271272405549 53140939269978101727152081)
            ·
              refine ⟨39855704452483576295364061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53140939269978101727152081 39855704452483576295364061)
              ·
                refine ⟨14945889169681341110761523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39855704452483576295364061 14945889169681341110761523)
                ·
                  refine ⟨22418833754522011666142285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14945889169681341110761523 22418833754522011666142285)
                  ·
                    refine ⟨8407062657945754374803357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22418833754522011666142285 8407062657945754374803357)
                    ·
                      refine ⟨3152648496729657890551259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407062657945754374803357 3152648496729657890551259)
                      ·
                        rfl

theorem cell23_6139761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_6139761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139761 prefixEnd_6139761 := by exact prefixLift 6139761
  have htrace : WordTrace (prefixWord ++ tailWord_6139761) baseStart_6139761 baseEnd_6139761 := by
    simpa [prefixWord, tailWord_6139761, baseEnd_6139761] using wordTrace_append hprefix tailTrace_6139761
  have hstable : (prefixWord ++ tailWord_6139761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139761).length < 2 ^ (prefixWord ++ tailWord_6139761).sum := by decide
  have hdescent : baseEnd_6139761 < baseStart_6139761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139796 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_6139796 : Nat := 118140960795 + 6139796 * 2 ^ 59
def prefixEnd_6139796 : Nat := 4983230072969 + 3 ^ 40 * 6139796 * 2
def baseEnd_6139796 : Nat := 3152666468552565253613599

theorem tailTrace_6139796 : CollatzResearch.WordTrace tailWord_6139796 prefixEnd_6139796 3152666468552565253613599 := by
  unfold tailWord_6139796
  simp only [CollatzResearch.WordTrace]
  refine ⟨111968378632287580259551621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149291171509716773679402161 111968378632287580259551621)
  ·
    refine ⟨20994070993553921298665929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111968378632287580259551621 20994070993553921298665929)
    ·
      refine ⟨15745553245165440973999447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20994070993553921298665929 15745553245165440973999447)
      ·
        refine ⟨23618329867748161460999171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745553245165440973999447 23618329867748161460999171)
        ·
          refine ⟨35427494801622242191498757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23618329867748161460999171 35427494801622242191498757)
          ·
            refine ⟨6642655275304170410906017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35427494801622242191498757 6642655275304170410906017)
            ·
              refine ⟨4981991456478127808179513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642655275304170410906017 4981991456478127808179513)
              ·
                refine ⟨3736493592358595856134635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981991456478127808179513 3736493592358595856134635)
                ·
                  refine ⟨5604740388537893784201953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736493592358595856134635 5604740388537893784201953)
                  ·
                    refine ⟨4203555291403420338151465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604740388537893784201953 4203555291403420338151465)
                    ·
                      refine ⟨3152666468552565253613599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203555291403420338151465 3152666468552565253613599)
                      ·
                        rfl

theorem cell23_6139796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_6139796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139796 prefixEnd_6139796 := by exact prefixLift 6139796
  have htrace : WordTrace (prefixWord ++ tailWord_6139796) baseStart_6139796 baseEnd_6139796 := by
    simpa [prefixWord, tailWord_6139796, baseEnd_6139796] using wordTrace_append hprefix tailTrace_6139796
  have hstable : (prefixWord ++ tailWord_6139796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139796).length < 2 ^ (prefixWord ++ tailWord_6139796).sum := by decide
  have hdescent : baseEnd_6139796 < baseStart_6139796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139851 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3]
def baseStart_6139851 : Nat := 118140960795 + 6139851 * 2 ^ 59
def prefixEnd_6139851 : Nat := 4983230072969 + 3 ^ 40 * 6139851 * 2
def baseEnd_6139851 : Nat := 3152694709988562538425845

theorem tailTrace_6139851 : CollatzResearch.WordTrace tailWord_6139851 prefixEnd_6139851 3152694709988562538425845 := by
  unfold tailWord_6139851
  simp only [CollatzResearch.WordTrace]
  refine ⟨223938763279375904912355407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149292508852917269941570271 223938763279375904912355407)
  ·
    refine ⟨335908144919063857368533111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223938763279375904912355407 335908144919063857368533111)
    ·
      refine ⟨503862217378595786052799667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335908144919063857368533111 503862217378595786052799667)
      ·
        refine ⟨755793326067893679079199501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503862217378595786052799667 755793326067893679079199501)
        ·
          refine ⟨283422497275460129654699813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755793326067893679079199501 283422497275460129654699813)
          ·
            refine ⟨53141718239148774310256215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283422497275460129654699813 53141718239148774310256215)
            ·
              refine ⟨79712577358723161465384323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53141718239148774310256215 79712577358723161465384323)
              ·
                refine ⟨119568866038084742198076485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79712577358723161465384323 119568866038084742198076485)
                ·
                  refine ⟨22419162382140889162139341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119568866038084742198076485 22419162382140889162139341)
                  ·
                    refine ⟨8407185893302833435802253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22419162382140889162139341 8407185893302833435802253)
                    ·
                      refine ⟨3152694709988562538425845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407185893302833435802253 3152694709988562538425845)
                      ·
                        rfl

theorem cell23_6139851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 3].length) (baseStart_6139851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139851 prefixEnd_6139851 := by exact prefixLift 6139851
  have htrace : WordTrace (prefixWord ++ tailWord_6139851) baseStart_6139851 baseEnd_6139851 := by
    simpa [prefixWord, tailWord_6139851, baseEnd_6139851] using wordTrace_append hprefix tailTrace_6139851
  have hstable : (prefixWord ++ tailWord_6139851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139851).length < 2 ^ (prefixWord ++ tailWord_6139851).sum := by decide
  have hdescent : baseEnd_6139851 < baseStart_6139851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
