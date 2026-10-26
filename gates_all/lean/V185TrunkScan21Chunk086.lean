import V185TrunkScan21Chunk085

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1044149 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1044149 : Nat := 118140960795 + 1044149 * 2 ^ 59
def prefixEnd_1044149 : Nat := 4983230072969 + 3 ^ 40 * 1044149 * 2
def baseEnd_1044149 : Nat := 238289027516240220415801

theorem tailTrace_1044149 : CollatzResearch.WordTrace tailWord_1044149 prefixEnd_1044149 238289027516240220415801 := by
  unfold tailWord_1044149
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083242694233974297015501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25388828462822649531343667 38083242694233974297015501)
  ·
    refine ⟨14281216010337740361380813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38083242694233974297015501 14281216010337740361380813)
    ·
      refine ⟨5355456003876652635517805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14281216010337740361380813 5355456003876652635517805)
      ·
        refine ⟨2008296001453744738319177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5355456003876652635517805 2008296001453744738319177)
        ·
          refine ⟨1506222001090308553739383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008296001453744738319177 1506222001090308553739383)
          ·
            refine ⟨2259333001635462830609075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506222001090308553739383 2259333001635462830609075)
            ·
              refine ⟨3388999502453194245913613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259333001635462830609075 3388999502453194245913613)
              ·
                refine ⟨1270874813419947842217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3388999502453194245913613 1270874813419947842217605)
                ·
                  refine ⟨238289027516240220415801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270874813419947842217605 238289027516240220415801)
                  ·
                    rfl

theorem cell21_1044149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1044149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044149 prefixEnd_1044149 := by exact prefixLift 1044149
  have htrace : WordTrace (prefixWord ++ tailWord_1044149) baseStart_1044149 baseEnd_1044149 := by
    simpa [prefixWord, tailWord_1044149, baseEnd_1044149] using wordTrace_append hprefix tailTrace_1044149
  have hstable : (prefixWord ++ tailWord_1044149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044149).length < 2 ^ (prefixWord ++ tailWord_1044149).sum := by decide
  have hdescent : baseEnd_1044149 < baseStart_1044149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044160 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1044160 : Nat := 118140960795 + 1044160 * 2 ^ 59
def prefixEnd_1044160 : Nat := 4983230072969 + 3 ^ 40 * 1044160 * 2
def baseEnd_1044160 : Nat := 238291537866106645732445

theorem tailTrace_1044160 : CollatzResearch.WordTrace tailWord_1044160 prefixEnd_1044160 238291537866106645732445 := by
  unfold tailWord_1044160
  simp only [CollatzResearch.WordTrace]
  refine ⟨19041821948597061587832967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25389095931462748783777289 19041821948597061587832967)
  ·
    refine ⟨28562732922895592381749451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19041821948597061587832967 28562732922895592381749451)
    ·
      refine ⟨42844099384343388572624177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28562732922895592381749451 42844099384343388572624177)
      ·
        refine ⟨32133074538257541429468133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42844099384343388572624177 32133074538257541429468133)
        ·
          refine ⟨6024951475923289018025275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32133074538257541429468133 6024951475923289018025275)
          ·
            refine ⟨9037427213884933527037913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6024951475923289018025275 9037427213884933527037913)
            ·
              refine ⟨6778070410413700145278435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9037427213884933527037913 6778070410413700145278435)
              ·
                refine ⟨10167105615620550217917653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6778070410413700145278435 10167105615620550217917653)
                ·
                  refine ⟨238291537866106645732445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10167105615620550217917653 238291537866106645732445)
                  ·
                    rfl

theorem cell21_1044160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1044160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044160 prefixEnd_1044160 := by exact prefixLift 1044160
  have htrace : WordTrace (prefixWord ++ tailWord_1044160) baseStart_1044160 baseEnd_1044160 := by
    simpa [prefixWord, tailWord_1044160, baseEnd_1044160] using wordTrace_append hprefix tailTrace_1044160
  have hstable : (prefixWord ++ tailWord_1044160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044160).length < 2 ^ (prefixWord ++ tailWord_1044160).sum := by decide
  have hdescent : baseEnd_1044160 < baseStart_1044160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044242 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1044242 : Nat := 118140960795 + 1044242 * 2 ^ 59
def prefixEnd_1044242 : Nat := 4983230072969 + 3 ^ 40 * 1044242 * 2
def baseEnd_1044242 : Nat := 238310251383292725365611

theorem tailTrace_1044242 : CollatzResearch.WordTrace tailWord_1044242 prefixEnd_1044242 238310251383292725365611 := by
  unfold tailWord_1044242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521658670724262795037745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25391089788598034120100653 9521658670724262795037745)
  ·
    refine ⟨7141244003043197096278309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9521658670724262795037745 7141244003043197096278309)
    ·
      refine ⟨1338983250570599455552183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7141244003043197096278309 1338983250570599455552183)
      ·
        refine ⟨2008474875855899183328275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338983250570599455552183 2008474875855899183328275)
        ·
          refine ⟨3012712313783848774992413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008474875855899183328275 3012712313783848774992413)
          ·
            refine ⟨1129767117668943290622155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3012712313783848774992413 1129767117668943290622155)
            ·
              refine ⟨1694650676503414935933233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129767117668943290622155 1694650676503414935933233)
              ·
                refine ⟨1270988007377561201949925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694650676503414935933233 1270988007377561201949925)
                ·
                  refine ⟨238310251383292725365611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270988007377561201949925 238310251383292725365611)
                  ·
                    rfl

theorem cell21_1044242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1044242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044242 prefixEnd_1044242 := by exact prefixLift 1044242
  have htrace : WordTrace (prefixWord ++ tailWord_1044242) baseStart_1044242 baseEnd_1044242 := by
    simpa [prefixWord, tailWord_1044242, baseEnd_1044242] using wordTrace_append hprefix tailTrace_1044242
  have hstable : (prefixWord ++ tailWord_1044242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044242).length < 2 ^ (prefixWord ++ tailWord_1044242).sum := by decide
  have hdescent : baseEnd_1044242 < baseStart_1044242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044287 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 3]
def baseStart_1044287 : Nat := 118140960795 + 1044287 * 2 ^ 59
def prefixEnd_1044287 : Nat := 4983230072969 + 3 ^ 40 * 1044287 * 2
def baseEnd_1044287 : Nat := 238320520996382647115519

theorem tailTrace_1044287 : CollatzResearch.WordTrace tailWord_1044287 prefixEnd_1044287 238320520996382647115519 := by
  unfold tailWord_1044287
  simp only [CollatzResearch.WordTrace]
  refine ⟨38088275967734023865539115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25392183978489349243692743 38088275967734023865539115)
  ·
    refine ⟨57132413951601035798308673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38088275967734023865539115 57132413951601035798308673)
    ·
      refine ⟨42849310463700776848731505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57132413951601035798308673 42849310463700776848731505)
      ·
        refine ⟨32136982847775582636548629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42849310463700776848731505 32136982847775582636548629)
        ·
          refine ⟨1506421070989480436088217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32136982847775582636548629 1506421070989480436088217)
          ·
            refine ⟨1129815803242110327066163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506421070989480436088217 1129815803242110327066163)
            ·
              refine ⟨1694723704863165490599245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129815803242110327066163 1694723704863165490599245)
              ·
                refine ⟨635521389323687058974717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1694723704863165490599245 635521389323687058974717)
                ·
                  refine ⟨238320520996382647115519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635521389323687058974717 238320520996382647115519)
                  ·
                    rfl

theorem cell21_1044287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].length) (baseStart_1044287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044287 prefixEnd_1044287 := by exact prefixLift 1044287
  have htrace : WordTrace (prefixWord ++ tailWord_1044287) baseStart_1044287 baseEnd_1044287 := by
    simpa [prefixWord, tailWord_1044287, baseEnd_1044287] using wordTrace_append hprefix tailTrace_1044287
  have hstable : (prefixWord ++ tailWord_1044287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044287).length < 2 ^ (prefixWord ++ tailWord_1044287).sum := by decide
  have hdescent : baseEnd_1044287 < baseStart_1044287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044388 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1044388 : Nat := 118140960795 + 1044388 * 2 ^ 59
def prefixEnd_1044388 : Nat := 4983230072969 + 3 ^ 40 * 1044388 * 2
def baseEnd_1044388 : Nat := 238343570572428915931979

theorem tailTrace_1044388 : CollatzResearch.WordTrace tailWord_1044388 prefixEnd_1044388 238343570572428915931979 := by
  unfold tailWord_1044388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045979870184059057482909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25394639826912078743310545 19045979870184059057482909)
  ·
    refine ⟨7142242451319022146556091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19045979870184059057482909 7142242451319022146556091)
    ·
      refine ⟨10713363676978533219834137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7142242451319022146556091 10713363676978533219834137)
      ·
        refine ⟨8035022757733899914875603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10713363676978533219834137 8035022757733899914875603)
        ·
          refine ⟨12052534136600849872313405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8035022757733899914875603 12052534136600849872313405)
          ·
            refine ⟨4519700301225318702117527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12052534136600849872313405 4519700301225318702117527)
            ·
              refine ⟨6779550451837978053176291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4519700301225318702117527 6779550451837978053176291)
              ·
                refine ⟨10169325677756967079764437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6779550451837978053176291 10169325677756967079764437)
                ·
                  refine ⟨238343570572428915931979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10169325677756967079764437 238343570572428915931979)
                  ·
                    rfl

theorem cell21_1044388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1044388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044388 prefixEnd_1044388 := by exact prefixLift 1044388
  have htrace : WordTrace (prefixWord ++ tailWord_1044388) baseStart_1044388 baseEnd_1044388 := by
    simpa [prefixWord, tailWord_1044388, baseEnd_1044388] using wordTrace_append hprefix tailTrace_1044388
  have hstable : (prefixWord ++ tailWord_1044388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044388).length < 2 ^ (prefixWord ++ tailWord_1044388).sum := by decide
  have hdescent : baseEnd_1044388 < baseStart_1044388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044391 : List Nat := [1, 1, 6, 1, 2, 2, 3, 5]
def baseStart_1044391 : Nat := 118140960795 + 1044391 * 2 ^ 59
def prefixEnd_1044391 : Nat := 4983230072969 + 3 ^ 40 * 1044391 * 2
def baseEnd_1044391 : Nat := 79448085071100525793991

theorem tailTrace_1044391 : CollatzResearch.WordTrace tailWord_1044391 prefixEnd_1044391 79448085071100525793991 := by
  unfold tailWord_1044391
  simp only [CollatzResearch.WordTrace]
  refine ⟨38092069159357249627325027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25394712772904833084883351 38092069159357249627325027)
  ·
    refine ⟨57138103739035874440987541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38092069159357249627325027 57138103739035874440987541)
    ·
      refine ⟨2678348612767306614421291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57138103739035874440987541 2678348612767306614421291)
      ·
        refine ⟨4017522919150959921631937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678348612767306614421291 4017522919150959921631937)
        ·
          refine ⟨3013142189363219941223953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4017522919150959921631937 3013142189363219941223953)
          ·
            refine ⟨2259856642022414955917965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013142189363219941223953 2259856642022414955917965)
            ·
              refine ⟨847446240758405608469237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2259856642022414955917965 847446240758405608469237)
              ·
                refine ⟨79448085071100525793991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 847446240758405608469237 79448085071100525793991)
                ·
                  rfl

theorem cell21_1044391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 5].length) (baseStart_1044391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044391 prefixEnd_1044391 := by exact prefixLift 1044391
  have htrace : WordTrace (prefixWord ++ tailWord_1044391) baseStart_1044391 baseEnd_1044391 := by
    simpa [prefixWord, tailWord_1044391, baseEnd_1044391] using wordTrace_append hprefix tailTrace_1044391
  have hstable : (prefixWord ++ tailWord_1044391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044391).length < 2 ^ (prefixWord ++ tailWord_1044391).sum := by decide
  have hdescent : baseEnd_1044391 < baseStart_1044391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044523 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_1044523 : Nat := 118140960795 + 1044523 * 2 ^ 59
def prefixEnd_1044523 : Nat := 4983230072969 + 3 ^ 40 * 1044523 * 2
def baseEnd_1044523 : Nat := 238374379411698681181703

theorem tailTrace_1044523 : CollatzResearch.WordTrace tailWord_1044523 prefixEnd_1044523 238374379411698681181703 := by
  unfold tailWord_1044523
  simp only [CollatzResearch.WordTrace]
  refine ⟨38096883594879036171130223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25397922396586024114086815 38096883594879036171130223)
  ·
    refine ⟨57145325392318554256695335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38096883594879036171130223 57145325392318554256695335)
    ·
      refine ⟨85717988088477831385043003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57145325392318554256695335 85717988088477831385043003)
      ·
        refine ⟨128576982132716747077564505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85717988088477831385043003 128576982132716747077564505)
        ·
          refine ⟨96432736599537560308173379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128576982132716747077564505 96432736599537560308173379)
          ·
            refine ⟨144649104899306340462260069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96432736599537560308173379 144649104899306340462260069)
            ·
              refine ⟨27121707168619938836673763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144649104899306340462260069 27121707168619938836673763)
              ·
                refine ⟨40682560752929908255010645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27121707168619938836673763 40682560752929908255010645)
                ·
                  refine ⟨238374379411698681181703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40682560752929908255010645 238374379411698681181703)
                  ·
                    rfl

theorem cell21_1044523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_1044523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044523 prefixEnd_1044523 := by exact prefixLift 1044523
  have htrace : WordTrace (prefixWord ++ tailWord_1044523) baseStart_1044523 baseEnd_1044523 := by
    simpa [prefixWord, tailWord_1044523, baseEnd_1044523] using wordTrace_append hprefix tailTrace_1044523
  have hstable : (prefixWord ++ tailWord_1044523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044523).length < 2 ^ (prefixWord ++ tailWord_1044523).sum := by decide
  have hdescent : baseEnd_1044523 < baseStart_1044523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044540 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_1044540 : Nat := 118140960795 + 1044540 * 2 ^ 59
def prefixEnd_1044540 : Nat := 4983230072969 + 3 ^ 40 * 1044540 * 2
def baseEnd_1044540 : Nat := 238378259043310429398335

theorem tailTrace_1044540 : CollatzResearch.WordTrace tailWord_1044540 prefixEnd_1044540 238378259043310429398335 := by
  unfold tailWord_1044540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048751817908724037249537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25398335757211632049666049 19048751817908724037249537)
  ·
    refine ⟨14286563863431543027937153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19048751817908724037249537 14286563863431543027937153)
    ·
      refine ⟨10714922897573657270952865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14286563863431543027937153 10714922897573657270952865)
      ·
        refine ⟨8036192173180242953214649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10714922897573657270952865 8036192173180242953214649)
        ·
          refine ⟨6027144129885182214910987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8036192173180242953214649 6027144129885182214910987)
          ·
            refine ⟨9040716194827773322366481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027144129885182214910987 9040716194827773322366481)
            ·
              refine ⟨6780537146120829991774861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9040716194827773322366481 6780537146120829991774861)
              ·
                refine ⟨2542701429795311246915573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6780537146120829991774861 2542701429795311246915573)
                ·
                  refine ⟨238378259043310429398335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2542701429795311246915573 238378259043310429398335)
                  ·
                    rfl

theorem cell21_1044540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_1044540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044540 prefixEnd_1044540 := by exact prefixLift 1044540
  have htrace : WordTrace (prefixWord ++ tailWord_1044540) baseStart_1044540 baseEnd_1044540 := by
    simpa [prefixWord, tailWord_1044540, baseEnd_1044540] using wordTrace_append hprefix tailTrace_1044540
  have hstable : (prefixWord ++ tailWord_1044540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044540).length < 2 ^ (prefixWord ++ tailWord_1044540).sum := by decide
  have hdescent : baseEnd_1044540 < baseStart_1044540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044554 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1044554 : Nat := 118140960795 + 1044554 * 2 ^ 59
def prefixEnd_1044554 : Nat := 4983230072969 + 3 ^ 40 * 1044554 * 2
def baseEnd_1044554 : Nat := 238381454034049516164973

theorem tailTrace_1044554 : CollatzResearch.WordTrace tailWord_1044554 prefixEnd_1044554 238381454034049516164973 := by
  unfold tailWord_1044554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524503564441682116377179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25398676171844485643672477 9524503564441682116377179)
  ·
    refine ⟨14286755346662523174565769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524503564441682116377179 14286755346662523174565769)
    ·
      refine ⟨10715066509996892380924327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14286755346662523174565769 10715066509996892380924327)
      ·
        refine ⟨16072599764995338571386491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10715066509996892380924327 16072599764995338571386491)
        ·
          refine ⟨24108899647493007857079737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072599764995338571386491 24108899647493007857079737)
          ·
            refine ⟨18081674735619755892809803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24108899647493007857079737 18081674735619755892809803)
            ·
              refine ⟨27122512103429633839214705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18081674735619755892809803 27122512103429633839214705)
              ·
                refine ⟨20341884077572225379411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27122512103429633839214705 20341884077572225379411029)
                ·
                  refine ⟨238381454034049516164973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20341884077572225379411029 238381454034049516164973)
                  ·
                    rfl

theorem cell21_1044554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1044554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044554 prefixEnd_1044554 := by exact prefixLift 1044554
  have htrace : WordTrace (prefixWord ++ tailWord_1044554) baseStart_1044554 baseEnd_1044554 := by
    simpa [prefixWord, tailWord_1044554, baseEnd_1044554] using wordTrace_append hprefix tailTrace_1044554
  have hstable : (prefixWord ++ tailWord_1044554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044554).length < 2 ^ (prefixWord ++ tailWord_1044554).sum := by decide
  have hdescent : baseEnd_1044554 < baseStart_1044554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044557 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1044557 : Nat := 118140960795 + 1044557 * 2 ^ 59
def prefixEnd_1044557 : Nat := 4983230072969 + 3 ^ 40 * 1044557 * 2
def baseEnd_1044557 : Nat := 238382138674922177614967

theorem tailTrace_1044557 : CollatzResearch.WordTrace tailWord_1044557 prefixEnd_1044557 238382138674922177614967 := by
  unfold tailWord_1044557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38098123676755859977867925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25398749117837239985245283 38098123676755859977867925)
  ·
    refine ⟨1785849547347930936462559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38098123676755859977867925 1785849547347930936462559)
    ·
      refine ⟨2678774321021896404693839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785849547347930936462559 2678774321021896404693839)
      ·
        refine ⟨4018161481532844607040759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678774321021896404693839 4018161481532844607040759)
        ·
          refine ⟨6027242222299266910561139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018161481532844607040759 6027242222299266910561139)
          ·
            refine ⟨9040863333448900365841709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027242222299266910561139 9040863333448900365841709)
            ·
              refine ⟨3390323750043337637190641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9040863333448900365841709 3390323750043337637190641)
              ·
                refine ⟨2542742812532503227892981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390323750043337637190641 2542742812532503227892981)
                ·
                  refine ⟨238382138674922177614967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2542742812532503227892981 238382138674922177614967)
                  ·
                    rfl

theorem cell21_1044557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1044557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044557 prefixEnd_1044557 := by exact prefixLift 1044557
  have htrace : WordTrace (prefixWord ++ tailWord_1044557) baseStart_1044557 baseEnd_1044557 := by
    simpa [prefixWord, tailWord_1044557, baseEnd_1044557] using wordTrace_append hprefix tailTrace_1044557
  have hstable : (prefixWord ++ tailWord_1044557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044557).length < 2 ^ (prefixWord ++ tailWord_1044557).sum := by decide
  have hdescent : baseEnd_1044557 < baseStart_1044557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044588 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_1044588 : Nat := 118140960795 + 1044588 * 2 ^ 59
def prefixEnd_1044588 : Nat := 4983230072969 + 3 ^ 40 * 1044588 * 2
def baseEnd_1044588 : Nat := 238389213297273012598237

theorem tailTrace_1044588 : CollatzResearch.WordTrace tailWord_1044588 prefixEnd_1044588 238389213297273012598237 := by
  unfold tailWord_1044588
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049627169821776136123209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25399502893095701514830945 19049627169821776136123209)
  ·
    refine ⟨14287220377366332102092407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19049627169821776136123209 14287220377366332102092407)
    ·
      refine ⟨21430830566049498153138611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287220377366332102092407 21430830566049498153138611)
      ·
        refine ⟨32146245849074247229707917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21430830566049498153138611 32146245849074247229707917)
        ·
          refine ⟨12054842193402842711140469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32146245849074247229707917 12054842193402842711140469)
          ·
            refine ⟨1130141455631516504169419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12054842193402842711140469 1130141455631516504169419)
            ·
              refine ⟨1695212183447274756254129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130141455631516504169419 1695212183447274756254129)
              ·
                refine ⟨1271409137585456067190597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695212183447274756254129 1271409137585456067190597)
                ·
                  refine ⟨238389213297273012598237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271409137585456067190597 238389213297273012598237)
                  ·
                    rfl

theorem cell21_1044588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_1044588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044588 prefixEnd_1044588 := by exact prefixLift 1044588
  have htrace : WordTrace (prefixWord ++ tailWord_1044588) baseStart_1044588 baseEnd_1044588 := by
    simpa [prefixWord, tailWord_1044588, baseEnd_1044588] using wordTrace_append hprefix tailTrace_1044588
  have hstable : (prefixWord ++ tailWord_1044588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044588).length < 2 ^ (prefixWord ++ tailWord_1044588).sum := by decide
  have hdescent : baseEnd_1044588 < baseStart_1044588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044743 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 3]
def baseStart_1044743 : Nat := 118140960795 + 1044743 * 2 ^ 59
def prefixEnd_1044743 : Nat := 4983230072969 + 3 ^ 40 * 1044743 * 2
def baseEnd_1044743 : Nat := 238424586409027187514587

theorem tailTrace_1044743 : CollatzResearch.WordTrace tailWord_1044743 prefixEnd_1044743 238424586409027187514587 := by
  unfold tailWord_1044743
  simp only [CollatzResearch.WordTrace]
  refine ⟨38104907654082013744138883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403271769388009162759255 38104907654082013744138883)
  ·
    refine ⟨57157361481123020616208325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38104907654082013744138883 57157361481123020616208325)
    ·
      refine ⟨10717005277710566365539061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57157361481123020616208325 10717005277710566365539061)
      ·
        refine ⟨1004719244785365596769287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10717005277710566365539061 1004719244785365596769287)
        ·
          refine ⟨1507078867178048395153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004719244785365596769287 1507078867178048395153931)
          ·
            refine ⟨2260618300767072592730897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507078867178048395153931 2260618300767072592730897)
            ·
              refine ⟨1695463725575304444548173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260618300767072592730897 1695463725575304444548173)
              ·
                refine ⟨635798897090739166705565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1695463725575304444548173 635798897090739166705565)
                ·
                  refine ⟨238424586409027187514587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635798897090739166705565 238424586409027187514587)
                  ·
                    rfl

theorem cell21_1044743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 3].length) (baseStart_1044743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044743 prefixEnd_1044743 := by exact prefixLift 1044743
  have htrace : WordTrace (prefixWord ++ tailWord_1044743) baseStart_1044743 baseEnd_1044743 := by
    simpa [prefixWord, tailWord_1044743, baseEnd_1044743] using wordTrace_append hprefix tailTrace_1044743
  have hstable : (prefixWord ++ tailWord_1044743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044743).length < 2 ^ (prefixWord ++ tailWord_1044743).sum := by decide
  have hdescent : baseEnd_1044743 < baseStart_1044743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044768 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1044768 : Nat := 118140960795 + 1044768 * 2 ^ 59
def prefixEnd_1044768 : Nat := 4983230072969 + 3 ^ 40 * 1044768 * 2
def baseEnd_1044768 : Nat := 238430291749632699597869

theorem tailTrace_1044768 : CollatzResearch.WordTrace tailWord_1044768 prefixEnd_1044768 238430291749632699597869 := by
  unfold tailWord_1044768
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052909739495721506899479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25403879652660962009199305 19052909739495721506899479)
  ·
    refine ⟨28579364609243582260349219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19052909739495721506899479 28579364609243582260349219)
    ·
      refine ⟨42869046913865373390523829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28579364609243582260349219 42869046913865373390523829)
      ·
        refine ⟨4018973148174878755361609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42869046913865373390523829 4018973148174878755361609)
        ·
          refine ⟨3014229861131159066521207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018973148174878755361609 3014229861131159066521207)
          ·
            refine ⟨4521344791696738599781811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014229861131159066521207 4521344791696738599781811)
            ·
              refine ⟨6782017187545107899672717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4521344791696738599781811 6782017187545107899672717)
              ·
                refine ⟨2543256445329415462377269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6782017187545107899672717 2543256445329415462377269)
                ·
                  refine ⟨238430291749632699597869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2543256445329415462377269 238430291749632699597869)
                  ·
                    rfl

theorem cell21_1044768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1044768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044768 prefixEnd_1044768 := by exact prefixLift 1044768
  have htrace : WordTrace (prefixWord ++ tailWord_1044768) baseStart_1044768 baseEnd_1044768 := by
    simpa [prefixWord, tailWord_1044768, baseEnd_1044768] using wordTrace_append hprefix tailTrace_1044768
  have hstable : (prefixWord ++ tailWord_1044768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044768).length < 2 ^ (prefixWord ++ tailWord_1044768).sum := by decide
  have hdescent : baseEnd_1044768 < baseStart_1044768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044875 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_1044875 : Nat := 118140960795 + 1044875 * 2 ^ 59
def prefixEnd_1044875 : Nat := 4983230072969 + 3 ^ 40 * 1044875 * 2
def baseEnd_1044875 : Nat := 238454710607424291314317

theorem tailTrace_1044875 : CollatzResearch.WordTrace tailWord_1044875 prefixEnd_1044875 238454710607424291314317 := by
  unfold tailWord_1044875
  simp only [CollatzResearch.WordTrace]
  refine ⟨38109722089603800287944079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25406481393069200191962719 38109722089603800287944079)
  ·
    refine ⟨57164583134405700431916119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38109722089603800287944079 57164583134405700431916119)
    ·
      refine ⟨85746874701608550647874179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57164583134405700431916119 85746874701608550647874179)
      ·
        refine ⟨128620312052412825971811269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85746874701608550647874179 128620312052412825971811269)
        ·
          refine ⟨24116308509827404869714613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128620312052412825971811269 24116308509827404869714613)
          ·
            refine ⟨2260903922796319206535745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24116308509827404869714613 2260903922796319206535745)
            ·
              refine ⟨1695677942097239404901809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260903922796319206535745 1695677942097239404901809)
              ·
                refine ⟨1271758456572929553676357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695677942097239404901809 1271758456572929553676357)
                ·
                  refine ⟨238454710607424291314317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271758456572929553676357 238454710607424291314317)
                  ·
                    rfl

theorem cell21_1044875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_1044875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044875 prefixEnd_1044875 := by exact prefixLift 1044875
  have htrace : WordTrace (prefixWord ++ tailWord_1044875) baseStart_1044875 baseEnd_1044875 := by
    simpa [prefixWord, tailWord_1044875, baseEnd_1044875] using wordTrace_append hprefix tailTrace_1044875
  have hstable : (prefixWord ++ tailWord_1044875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044875).length < 2 ^ (prefixWord ++ tailWord_1044875).sum := by decide
  have hdescent : baseEnd_1044875 < baseStart_1044875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044878 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_1044878 : Nat := 118140960795 + 1044878 * 2 ^ 59
def prefixEnd_1044878 : Nat := 4983230072969 + 3 ^ 40 * 1044878 * 2
def baseEnd_1044878 : Nat := 238455395248296952764311

theorem tailTrace_1044878 : CollatzResearch.WordTrace tailWord_1044878 prefixEnd_1044878 238455395248296952764311 := by
  unfold tailWord_1044878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763728938574116475037911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25406554339061954533535525 4763728938574116475037911)
  ·
    refine ⟨7145593407861174712556867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4763728938574116475037911 7145593407861174712556867)
    ·
      refine ⟨10718390111791762068835301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7145593407861174712556867 10718390111791762068835301)
      ·
        refine ⟨2009698145960955387906619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10718390111791762068835301 2009698145960955387906619)
        ·
          refine ⟨3014547218941433081859929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009698145960955387906619 3014547218941433081859929)
          ·
            refine ⟨2260910414206074811394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014547218941433081859929 2260910414206074811394947)
            ·
              refine ⟨3391365621309112217092421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260910414206074811394947 3391365621309112217092421)
              ·
                refine ⟨635881053995458540704829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3391365621309112217092421 635881053995458540704829)
                ·
                  refine ⟨238455395248296952764311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635881053995458540704829 238455395248296952764311)
                  ·
                    rfl

theorem cell21_1044878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_1044878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1044878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1044878 prefixEnd_1044878 := by exact prefixLift 1044878
  have htrace : WordTrace (prefixWord ++ tailWord_1044878) baseStart_1044878 baseEnd_1044878 := by
    simpa [prefixWord, tailWord_1044878, baseEnd_1044878] using wordTrace_append hprefix tailTrace_1044878
  have hstable : (prefixWord ++ tailWord_1044878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044878).length < 2 ^ (prefixWord ++ tailWord_1044878).sum := by decide
  have hdescent : baseEnd_1044878 < baseStart_1044878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045055 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_1045055 : Nat := 118140960795 + 1045055 * 2 ^ 59
def prefixEnd_1045055 : Nat := 4983230072969 + 3 ^ 40 * 1045055 * 2
def baseEnd_1045055 : Nat := 238495789059783978313949

theorem tailTrace_1045055 : CollatzResearch.WordTrace tailWord_1045055 prefixEnd_1045055 238495789059783978313949 := by
  unfold tailWord_1045055
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116287228951691029496619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25410858152634460686331079 38116287228951691029496619)
  ·
    refine ⟨57174430843427536544244929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38116287228951691029496619 57174430843427536544244929)
    ·
      refine ⟨42880823132570652408183697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57174430843427536544244929 42880823132570652408183697)
      ·
        refine ⟨32160617349427989306137773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42880823132570652408183697 32160617349427989306137773)
        ·
          refine ⟨12060231506035495989801665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32160617349427989306137773 12060231506035495989801665)
          ·
            refine ⟨9045173629526621992351249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12060231506035495989801665 9045173629526621992351249)
            ·
              refine ⟨6783880222144966494263437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9045173629526621992351249 6783880222144966494263437)
              ·
                refine ⟨2543955083304362435348789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6783880222144966494263437 2543955083304362435348789)
                ·
                  refine ⟨238495789059783978313949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2543955083304362435348789 238495789059783978313949)
                  ·
                    rfl

theorem cell21_1045055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_1045055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045055 prefixEnd_1045055 := by exact prefixLift 1045055
  have htrace : WordTrace (prefixWord ++ tailWord_1045055) baseStart_1045055 baseEnd_1045055 := by
    simpa [prefixWord, tailWord_1045055, baseEnd_1045055] using wordTrace_append hprefix tailTrace_1045055
  have hstable : (prefixWord ++ tailWord_1045055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045055).length < 2 ^ (prefixWord ++ tailWord_1045055).sum := by decide
  have hdescent : baseEnd_1045055 < baseStart_1045055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045089 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 3]
def baseStart_1045089 : Nat := 118140960795 + 1045089 * 2 ^ 59
def prefixEnd_1045089 : Nat := 4983230072969 + 3 ^ 40 * 1045089 * 2
def baseEnd_1045089 : Nat := 238503548323007474747213

theorem tailTrace_1045089 : CollatzResearch.WordTrace tailWord_1045089 prefixEnd_1045089 238503548323007474747213 := by
  unfold tailWord_1045089
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117527310828514836234321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411684873885676557489547 38117527310828514836234321)
  ·
    refine ⟨28588145483121386127175741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38117527310828514836234321 28588145483121386127175741)
    ·
      refine ⟨10720554556170519797690903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28588145483121386127175741 10720554556170519797690903)
      ·
        refine ⟨16080831834255779696536355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10720554556170519797690903 16080831834255779696536355)
        ·
          refine ⟨24121247751383669544804533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16080831834255779696536355 24121247751383669544804533)
          ·
            refine ⟨2261366976692219019825425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24121247751383669544804533 2261366976692219019825425)
            ·
              refine ⟨1696025232519164264869069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261366976692219019825425 1696025232519164264869069)
              ·
                refine ⟨636009462194686599325901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696025232519164264869069 636009462194686599325901)
                ·
                  refine ⟨238503548323007474747213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636009462194686599325901 238503548323007474747213)
                  ·
                    rfl

theorem cell21_1045089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_1045089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045089 prefixEnd_1045089 := by exact prefixLift 1045089
  have htrace : WordTrace (prefixWord ++ tailWord_1045089) baseStart_1045089 baseEnd_1045089 := by
    simpa [prefixWord, tailWord_1045089, baseEnd_1045089] using wordTrace_append hprefix tailTrace_1045089
  have hstable : (prefixWord ++ tailWord_1045089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045089).length < 2 ^ (prefixWord ++ tailWord_1045089).sum := by decide
  have hdescent : baseEnd_1045089 < baseStart_1045089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045145 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_1045145 : Nat := 118140960795 + 1045145 * 2 ^ 59
def prefixEnd_1045145 : Nat := 4983230072969 + 3 ^ 40 * 1045145 * 2
def baseEnd_1045145 : Nat := 238516328285963821813765

theorem tailTrace_1045145 : CollatzResearch.WordTrace tailWord_1045145 prefixEnd_1045145 238516328285963821813765 := by
  unfold tailWord_1045145
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119569798625636400272889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25413046532417090933515259 38119569798625636400272889)
  ·
    refine ⟨28589677348969227300204667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38119569798625636400272889 28589677348969227300204667)
    ·
      refine ⟨42884516023453840950307001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28589677348969227300204667 42884516023453840950307001)
      ·
        refine ⟨32163387017590380712730251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42884516023453840950307001 32163387017590380712730251)
        ·
          refine ⟨48245080526385571069095377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32163387017590380712730251 48245080526385571069095377)
          ·
            refine ⟨36183810394789178301821533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48245080526385571069095377 36183810394789178301821533)
            ·
              refine ⟨13568928898045941863183075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36183810394789178301821533 13568928898045941863183075)
              ·
                refine ⟨20353393347068912794774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13568928898045941863183075 20353393347068912794774613)
                ·
                  refine ⟨238516328285963821813765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20353393347068912794774613 238516328285963821813765)
                  ·
                    rfl

theorem cell21_1045145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_1045145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045145 prefixEnd_1045145 := by exact prefixLift 1045145
  have htrace : WordTrace (prefixWord ++ tailWord_1045145) baseStart_1045145 baseEnd_1045145 := by
    simpa [prefixWord, tailWord_1045145, baseEnd_1045145] using wordTrace_append hprefix tailTrace_1045145
  have hstable : (prefixWord ++ tailWord_1045145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045145).length < 2 ^ (prefixWord ++ tailWord_1045145).sum := by decide
  have hdescent : baseEnd_1045145 < baseStart_1045145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045165 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1045165 : Nat := 118140960795 + 1045165 * 2 ^ 59
def prefixEnd_1045165 : Nat := 4983230072969 + 3 ^ 40 * 1045165 * 2
def baseEnd_1045165 : Nat := 238520892558448231480391

theorem tailTrace_1045165 : CollatzResearch.WordTrace tailWord_1045165 prefixEnd_1045165 238520892558448231480391 := by
  unfold tailWord_1045165
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120299258553179816000949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25413532839035453210667299 38120299258553179816000949)
  ·
    refine ⟨3573778055489360607750089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38120299258553179816000949 3573778055489360607750089)
    ·
      refine ⟨2680333541617020455812567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573778055489360607750089 2680333541617020455812567)
      ·
        refine ⟨4020500312425530683718851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680333541617020455812567 4020500312425530683718851)
        ·
          refine ⟨6030750468638296025578277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020500312425530683718851 6030750468638296025578277)
          ·
            refine ⟨1130765712869680504795927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6030750468638296025578277 1130765712869680504795927)
            ·
              refine ⟨1696148569304520757193891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130765712869680504795927 1696148569304520757193891)
              ·
                refine ⟨2544222853956781135790837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696148569304520757193891 2544222853956781135790837)
                ·
                  refine ⟨238520892558448231480391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544222853956781135790837 238520892558448231480391)
                  ·
                    rfl

theorem cell21_1045165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1045165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045165 prefixEnd_1045165 := by exact prefixLift 1045165
  have htrace : WordTrace (prefixWord ++ tailWord_1045165) baseStart_1045165 baseEnd_1045165 := by
    simpa [prefixWord, tailWord_1045165, baseEnd_1045165] using wordTrace_append hprefix tailTrace_1045165
  have hstable : (prefixWord ++ tailWord_1045165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045165).length < 2 ^ (prefixWord ++ tailWord_1045165).sum := by decide
  have hdescent : baseEnd_1045165 < baseStart_1045165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045348 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1045348 : Nat := 118140960795 + 1045348 * 2 ^ 59
def prefixEnd_1045348 : Nat := 4983230072969 + 3 ^ 40 * 1045348 * 2
def baseEnd_1045348 : Nat := 238562655651680579930017

theorem tailTrace_1045348 : CollatzResearch.WordTrace tailWord_1045348 prefixEnd_1045348 238562655651680579930017 := by
  unfold tailWord_1045348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19063486908445101034956349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25417982544593468046608465 19063486908445101034956349)
  ·
    refine ⟨7148807590666912888108631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19063486908445101034956349 7148807590666912888108631)
    ·
      refine ⟨10723211386000369332162947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7148807590666912888108631 10723211386000369332162947)
      ·
        refine ⟨16084817079000553998244421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723211386000369332162947 16084817079000553998244421)
        ·
          refine ⟨3015903202312603874670829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16084817079000553998244421 3015903202312603874670829)
          ·
            refine ⟨1130963700867226453001561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3015903202312603874670829 1130963700867226453001561)
            ·
              refine ⟨848222775650419839751171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130963700867226453001561 848222775650419839751171)
              ·
                refine ⟨1272334163475629759626757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848222775650419839751171 1272334163475629759626757)
                ·
                  refine ⟨238562655651680579930017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272334163475629759626757 238562655651680579930017)
                  ·
                    rfl

theorem cell21_1045348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1045348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045348 prefixEnd_1045348 := by exact prefixLift 1045348
  have htrace : WordTrace (prefixWord ++ tailWord_1045348) baseStart_1045348 baseEnd_1045348 := by
    simpa [prefixWord, tailWord_1045348, baseEnd_1045348] using wordTrace_append hprefix tailTrace_1045348
  have hstable : (prefixWord ++ tailWord_1045348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045348).length < 2 ^ (prefixWord ++ tailWord_1045348).sum := by decide
  have hdescent : baseEnd_1045348 < baseStart_1045348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045373 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1045373 : Nat := 118140960795 + 1045373 * 2 ^ 59
def prefixEnd_1045373 : Nat := 4983230072969 + 3 ^ 40 * 1045373 * 2
def baseEnd_1045373 : Nat := 238568360992286092013299

theorem tailTrace_1045373 : CollatzResearch.WordTrace tailWord_1045373 prefixEnd_1045373 238568360992286092013299 := by
  unfold tailWord_1045373
  simp only [CollatzResearch.WordTrace]
  refine ⟨38127885641799631339572773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25418590427866420893048515 38127885641799631339572773)
  ·
    refine ⟨7148978557837430876169895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38127885641799631339572773 7148978557837430876169895)
    ·
      refine ⟨10723467836756146314254843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7148978557837430876169895 10723467836756146314254843)
      ·
        refine ⟨16085201755134219471382265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723467836756146314254843 16085201755134219471382265)
        ·
          refine ⟨12063901316350664603536699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16085201755134219471382265 12063901316350664603536699)
          ·
            refine ⟨18095851974525996905305049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12063901316350664603536699 18095851974525996905305049)
            ·
              refine ⟨13571888980894497678978787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18095851974525996905305049 13571888980894497678978787)
              ·
                refine ⟨20357833471341746518468181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13571888980894497678978787 20357833471341746518468181)
                ·
                  refine ⟨238568360992286092013299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20357833471341746518468181 238568360992286092013299)
                  ·
                    rfl

theorem cell21_1045373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1045373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045373 prefixEnd_1045373 := by exact prefixLift 1045373
  have htrace : WordTrace (prefixWord ++ tailWord_1045373) baseStart_1045373 baseEnd_1045373 := by
    simpa [prefixWord, tailWord_1045373, baseEnd_1045373] using wordTrace_append hprefix tailTrace_1045373
  have hstable : (prefixWord ++ tailWord_1045373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045373).length < 2 ^ (prefixWord ++ tailWord_1045373).sum := by decide
  have hdescent : baseEnd_1045373 < baseStart_1045373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045452 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_1045452 : Nat := 118140960795 + 1045452 * 2 ^ 59
def prefixEnd_1045452 : Nat := 4983230072969 + 3 ^ 40 * 1045452 * 2
def baseEnd_1045452 : Nat := 238586389868599510196471

theorem tailTrace_1045452 : CollatzResearch.WordTrace tailWord_1045452 prefixEnd_1045452 238586389868599510196471 := by
  unfold tailWord_1045452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065383504256713915849305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25420511339008951887799073 19065383504256713915849305)
  ·
    refine ⟨14299037628192535436886979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19065383504256713915849305 14299037628192535436886979)
    ·
      refine ⟨21448556442288803155330469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14299037628192535436886979 21448556442288803155330469)
      ·
        refine ⟨4021604332929150591624463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21448556442288803155330469 4021604332929150591624463)
        ·
          refine ⟨6032406499393725887436695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021604332929150591624463 6032406499393725887436695)
          ·
            refine ⟨9048609749090588831155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032406499393725887436695 9048609749090588831155043)
            ·
              refine ⟨13572914623635883246732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048609749090588831155043 13572914623635883246732565)
              ·
                refine ⟨636230372982932027190589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13572914623635883246732565 636230372982932027190589)
                ·
                  refine ⟨238586389868599510196471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636230372982932027190589 238586389868599510196471)
                  ·
                    rfl

theorem cell21_1045452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_1045452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045452 prefixEnd_1045452 := by exact prefixLift 1045452
  have htrace : WordTrace (prefixWord ++ tailWord_1045452) baseStart_1045452 baseEnd_1045452 := by
    simpa [prefixWord, tailWord_1045452, baseEnd_1045452] using wordTrace_append hprefix tailTrace_1045452
  have hstable : (prefixWord ++ tailWord_1045452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045452).length < 2 ^ (prefixWord ++ tailWord_1045452).sum := by decide
  have hdescent : baseEnd_1045452 < baseStart_1045452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045486 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_1045486 : Nat := 118140960795 + 1045486 * 2 ^ 59
def prefixEnd_1045486 : Nat := 4983230072969 + 3 ^ 40 * 1045486 * 2
def baseEnd_1045486 : Nat := 238594149131823006629735

theorem tailTrace_1045486 : CollatzResearch.WordTrace tailWord_1045486 prefixEnd_1045486 238594149131823006629735 := by
  unfold tailWord_1045486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766500886298781454804539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25421338060260167758957541 4766500886298781454804539)
  ·
    refine ⟨7149751329448172182206809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766500886298781454804539 7149751329448172182206809)
    ·
      refine ⟨5362313497086129136655107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7149751329448172182206809 5362313497086129136655107)
      ·
        refine ⟨8043470245629193704982661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362313497086129136655107 8043470245629193704982661)
        ·
          refine ⟨1508150671055473819684249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8043470245629193704982661 1508150671055473819684249)
          ·
            refine ⟨1131113003291605364763187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508150671055473819684249 1131113003291605364763187)
            ·
              refine ⟨1696669504937408047144781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131113003291605364763187 1696669504937408047144781)
              ·
                refine ⟨636251064351528017679293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696669504937408047144781 636251064351528017679293)
                ·
                  refine ⟨238594149131823006629735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636251064351528017679293 238594149131823006629735)
                  ·
                    rfl

theorem cell21_1045486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_1045486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045486 prefixEnd_1045486 := by exact prefixLift 1045486
  have htrace : WordTrace (prefixWord ++ tailWord_1045486) baseStart_1045486 baseEnd_1045486 := by
    simpa [prefixWord, tailWord_1045486, baseEnd_1045486] using wordTrace_append hprefix tailTrace_1045486
  have hstable : (prefixWord ++ tailWord_1045486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045486).length < 2 ^ (prefixWord ++ tailWord_1045486).sum := by decide
  have hdescent : baseEnd_1045486 < baseStart_1045486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045615 : List Nat := [1, 1, 2, 1, 3, 3, 10]
def baseStart_1045615 : Nat := 118140960795 + 1045615 * 2 ^ 59
def prefixEnd_1045615 : Nat := 4983230072969 + 3 ^ 40 * 1045615 * 2
def baseEnd_1045615 : Nat := 26513732076594160997719

theorem tailTrace_1045615 : CollatzResearch.WordTrace tailWord_1045615 prefixEnd_1045615 26513732076594160997719 := by
  unfold tailWord_1045615
  simp only [CollatzResearch.WordTrace]
  refine ⟨38136712106922906669882299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25424474737948604446588199 38136712106922906669882299)
  ·
    refine ⟨57205068160384360004823449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38136712106922906669882299 57205068160384360004823449)
    ·
      refine ⟨42903801120288270003617587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57205068160384360004823449 42903801120288270003617587)
      ·
        refine ⟨64355701680432405005426381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42903801120288270003617587 64355701680432405005426381)
        ·
          refine ⟨24133388130162151877034893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64355701680432405005426381 24133388130162151877034893)
          ·
            refine ⟨9050020548810806953888085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24133388130162151877034893 9050020548810806953888085)
            ·
              refine ⟨26513732076594160997719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9050020548810806953888085 26513732076594160997719)
              ·
                rfl

theorem cell21_1045615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_1045615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045615 prefixEnd_1045615 := by exact prefixLift 1045615
  have htrace : WordTrace (prefixWord ++ tailWord_1045615) baseStart_1045615 baseEnd_1045615 := by
    simpa [prefixWord, tailWord_1045615, baseEnd_1045615] using wordTrace_append hprefix tailTrace_1045615
  have hstable : (prefixWord ++ tailWord_1045615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045615).length < 2 ^ (prefixWord ++ tailWord_1045615).sum := by decide
  have hdescent : baseEnd_1045615 < baseStart_1045615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045621 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1045621 : Nat := 118140960795 + 1045621 * 2 ^ 59
def prefixEnd_1045621 : Nat := 4983230072969 + 3 ^ 40 * 1045621 * 2
def baseEnd_1045621 : Nat := 238624957971092771879459

theorem tailTrace_1045621 : CollatzResearch.WordTrace tailWord_1045621 prefixEnd_1045621 238624957971092771879459 := by
  unfold tailWord_1045621
  simp only [CollatzResearch.WordTrace]
  refine ⟨38136930944901169694600717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25424620629934113129733811 38136930944901169694600717)
  ·
    refine ⟨14301349104337938635475269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38136930944901169694600717 14301349104337938635475269)
    ·
      refine ⟨2681502957063363494151613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14301349104337938635475269 2681502957063363494151613)
      ·
        refine ⟨1005563608898761310306855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681502957063363494151613 1005563608898761310306855)
        ·
          refine ⟨1508345413348141965460283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005563608898761310306855 1508345413348141965460283)
          ·
            refine ⟨2262518120022212948190425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508345413348141965460283 2262518120022212948190425)
            ·
              refine ⟨1696888590016659711142819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262518120022212948190425 1696888590016659711142819)
              ·
                refine ⟨2545332885024989566714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696888590016659711142819 2545332885024989566714229)
                ·
                  refine ⟨238624957971092771879459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2545332885024989566714229 238624957971092771879459)
                  ·
                    rfl

theorem cell21_1045621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1045621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045621 prefixEnd_1045621 := by exact prefixLift 1045621
  have htrace : WordTrace (prefixWord ++ tailWord_1045621) baseStart_1045621 baseEnd_1045621 := by
    simpa [prefixWord, tailWord_1045621, baseEnd_1045621] using wordTrace_append hprefix tailTrace_1045621
  have hstable : (prefixWord ++ tailWord_1045621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045621).length < 2 ^ (prefixWord ++ tailWord_1045621).sum := by decide
  have hdescent : baseEnd_1045621 < baseStart_1045621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045666 : List Nat := [3, 3, 1, 3, 3, 1, 7]
def baseStart_1045666 : Nat := 118140960795 + 1045666 * 2 ^ 59
def prefixEnd_1045666 : Nat := 4983230072969 + 3 ^ 40 * 1045666 * 2
def baseEnd_1045666 : Nat := 26515025287131410403263

theorem tailTrace_1045666 : CollatzResearch.WordTrace tailWord_1045666 prefixEnd_1045666 26515025287131410403263 := by
  unfold tailWord_1045666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534643057434535594997213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25425714819825428253325901 9534643057434535594997213)
  ·
    refine ⟨3575491146537950848123955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9534643057434535594997213 3575491146537950848123955)
    ·
      refine ⟨5363236719806926272185933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575491146537950848123955 5363236719806926272185933)
      ·
        refine ⟨2011213769927597352069725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5363236719806926272185933 2011213769927597352069725)
        ·
          refine ⟨754205163722849007026147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2011213769927597352069725 754205163722849007026147)
          ·
            refine ⟨1131307745584273510539221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754205163722849007026147 1131307745584273510539221)
            ·
              refine ⟨26515025287131410403263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1131307745584273510539221 26515025287131410403263)
              ·
                rfl

theorem cell21_1045666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 7].length) (baseStart_1045666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045666 prefixEnd_1045666 := by exact prefixLift 1045666
  have htrace : WordTrace (prefixWord ++ tailWord_1045666) baseStart_1045666 baseEnd_1045666 := by
    simpa [prefixWord, tailWord_1045666, baseEnd_1045666] using wordTrace_append hprefix tailTrace_1045666
  have hstable : (prefixWord ++ tailWord_1045666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045666).length < 2 ^ (prefixWord ++ tailWord_1045666).sum := by decide
  have hdescent : baseEnd_1045666 < baseStart_1045666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045686 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1045686 : Nat := 118140960795 + 1045686 * 2 ^ 59
def prefixEnd_1045686 : Nat := 4983230072969 + 3 ^ 40 * 1045686 * 2
def baseEnd_1045686 : Nat := 238639791856667103295993

theorem tailTrace_1045686 : CollatzResearch.WordTrace tailWord_1045686 prefixEnd_1045686 238639791856667103295993 := by
  unfold tailWord_1045686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383706355604105362232307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25426201126443790530477941 2383706355604105362232307)
  ·
    refine ⟨3575559533406158043348461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383706355604105362232307 3575559533406158043348461)
    ·
      refine ⟨1340834825027309266255673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3575559533406158043348461 1340834825027309266255673)
      ·
        refine ⟨1005626118770481949691755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340834825027309266255673 1005626118770481949691755)
        ·
          refine ⟨1508439178155722924537633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005626118770481949691755 1508439178155722924537633)
          ·
            refine ⟨1131329383616792193403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508439178155722924537633 1131329383616792193403225)
            ·
              refine ⟨848497037712594145052419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131329383616792193403225 848497037712594145052419)
              ·
                refine ⟨1272745556568891217578629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848497037712594145052419 1272745556568891217578629)
                ·
                  refine ⟨238639791856667103295993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272745556568891217578629 238639791856667103295993)
                  ·
                    rfl

theorem cell21_1045686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1045686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045686 prefixEnd_1045686 := by exact prefixLift 1045686
  have htrace : WordTrace (prefixWord ++ tailWord_1045686) baseStart_1045686 baseEnd_1045686 := by
    simpa [prefixWord, tailWord_1045686, baseEnd_1045686] using wordTrace_append hprefix tailTrace_1045686
  have hstable : (prefixWord ++ tailWord_1045686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045686).length < 2 ^ (prefixWord ++ tailWord_1045686).sum := by decide
  have hdescent : baseEnd_1045686 < baseStart_1045686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045725 : List Nat := [1, 4, 3, 2, 3, 8]
def baseStart_1045725 : Nat := 118140960795 + 1045725 * 2 ^ 59
def prefixEnd_1045725 : Nat := 4983230072969 + 3 ^ 40 * 1045725 * 2
def baseEnd_1045725 : Nat := 8838840451407840820219

theorem tailTrace_1045725 : CollatzResearch.WordTrace tailWord_1045725 prefixEnd_1045725 8838840451407840820219 := by
  unfold tailWord_1045725
  simp only [CollatzResearch.WordTrace]
  refine ⟨38140724136524395456386629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25427149424349596970924419 38140724136524395456386629)
  ·
    refine ⟨7151385775598324148072493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38140724136524395456386629 7151385775598324148072493)
    ·
      refine ⟨2681769665849371555527185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7151385775598324148072493 2681769665849371555527185)
      ·
        refine ⟨2011327249387028666645389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2681769665849371555527185 2011327249387028666645389)
        ·
          refine ⟨754247718520135749992021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2011327249387028666645389 754247718520135749992021)
          ·
            refine ⟨8838840451407840820219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 754247718520135749992021 8838840451407840820219)
            ·
              rfl

theorem cell21_1045725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 8].length) (baseStart_1045725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045725 prefixEnd_1045725 := by exact prefixLift 1045725
  have htrace : WordTrace (prefixWord ++ tailWord_1045725) baseStart_1045725 baseEnd_1045725 := by
    simpa [prefixWord, tailWord_1045725, baseEnd_1045725] using wordTrace_append hprefix tailTrace_1045725
  have hstable : (prefixWord ++ tailWord_1045725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045725).length < 2 ^ (prefixWord ++ tailWord_1045725).sum := by decide
  have hdescent : baseEnd_1045725 < baseStart_1045725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045753 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_1045753 : Nat := 118140960795 + 1045753 * 2 ^ 59
def prefixEnd_1045753 : Nat := 4983230072969 + 3 ^ 40 * 1045753 * 2
def baseEnd_1045753 : Nat := 238655082169489875679189

theorem tailTrace_1045753 : CollatzResearch.WordTrace tailWord_1045753 prefixEnd_1045753 238655082169489875679189 := by
  unfold tailWord_1045753
  simp only [CollatzResearch.WordTrace]
  refine ⟨38141745380422956238405913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25427830253615304158937275 38141745380422956238405913)
  ·
    refine ⟨28606309035317217178804435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38141745380422956238405913 28606309035317217178804435)
    ·
      refine ⟨42909463552975825768206653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606309035317217178804435 42909463552975825768206653)
      ·
        refine ⟨16091048832365934663077495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42909463552975825768206653 16091048832365934663077495)
        ·
          refine ⟨24136573248548901994616243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091048832365934663077495 24136573248548901994616243)
          ·
            refine ⟨36204859872823352991924365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24136573248548901994616243 36204859872823352991924365)
            ·
              refine ⟨13576822452308757371971637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36204859872823352991924365 13576822452308757371971637)
              ·
                refine ⟨1272827104903946003622341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13576822452308757371971637 1272827104903946003622341)
                ·
                  refine ⟨238655082169489875679189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272827104903946003622341 238655082169489875679189)
                  ·
                    rfl

theorem cell21_1045753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_1045753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045753 prefixEnd_1045753 := by exact prefixLift 1045753
  have htrace : WordTrace (prefixWord ++ tailWord_1045753) baseStart_1045753 baseEnd_1045753 := by
    simpa [prefixWord, tailWord_1045753, baseEnd_1045753] using wordTrace_append hprefix tailTrace_1045753
  have hstable : (prefixWord ++ tailWord_1045753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045753).length < 2 ^ (prefixWord ++ tailWord_1045753).sum := by decide
  have hdescent : baseEnd_1045753 < baseStart_1045753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045860 : List Nat := [2, 3, 1, 1, 3, 3, 2, 6]
def baseStart_1045860 : Nat := 118140960795 + 1045860 * 2 ^ 59
def prefixEnd_1045860 : Nat := 4983230072969 + 3 ^ 40 * 1045860 * 2
def baseEnd_1045860 : Nat := 79559833675760489131879

theorem tailTrace_1045860 : CollatzResearch.WordTrace tailWord_1045860 prefixEnd_1045860 79559833675760489131879 := by
  unfold tailWord_1045860
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072823995517656756275517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25430431994023542341700689 19072823995517656756275517)
  ·
    refine ⟨7152308998319121283603319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19072823995517656756275517 7152308998319121283603319)
    ·
      refine ⟨10728463497478681925404979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152308998319121283603319 10728463497478681925404979)
      ·
        refine ⟨16092695246218022888107469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728463497478681925404979 16092695246218022888107469)
        ·
          refine ⟨6034760717331758583040301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16092695246218022888107469 6034760717331758583040301)
          ·
            refine ⟨2263035268999409468640113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6034760717331758583040301 2263035268999409468640113)
            ·
              refine ⟨1697276451749557101480085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263035268999409468640113 1697276451749557101480085)
              ·
                refine ⟨79559833675760489131879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1697276451749557101480085 79559833675760489131879)
                ·
                  rfl

theorem cell21_1045860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_1045860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045860 prefixEnd_1045860 := by exact prefixLift 1045860
  have htrace : WordTrace (prefixWord ++ tailWord_1045860) baseStart_1045860 baseEnd_1045860 := by
    simpa [prefixWord, tailWord_1045860, baseEnd_1045860] using wordTrace_append hprefix tailTrace_1045860
  have hstable : (prefixWord ++ tailWord_1045860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045860).length < 2 ^ (prefixWord ++ tailWord_1045860).sum := by decide
  have hdescent : baseEnd_1045860 < baseStart_1045860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045874 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1045874 : Nat := 118140960795 + 1045874 * 2 ^ 59
def prefixEnd_1045874 : Nat := 4983230072969 + 3 ^ 40 * 1045874 * 2
def baseEnd_1045874 : Nat := 238682696018020554162275

theorem tailTrace_1045874 : CollatzResearch.WordTrace tailWord_1045874 prefixEnd_1045874 238682696018020554162275 := by
  unfold tailWord_1045874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536539653246148475890169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25430772408656395935707117 9536539653246148475890169)
  ·
    refine ⟨7152404739934611356917627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9536539653246148475890169 7152404739934611356917627)
    ·
      refine ⟨10728607109901917035376441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152404739934611356917627 10728607109901917035376441)
      ·
        refine ⟨8046455332426437776532331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728607109901917035376441 8046455332426437776532331)
        ·
          refine ⟨12069682998639656664798497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046455332426437776532331 12069682998639656664798497)
          ·
            refine ⟨9052262248979742498598873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069682998639656664798497 9052262248979742498598873)
            ·
              refine ⟨6789196686734806873949155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9052262248979742498598873 6789196686734806873949155)
              ·
                refine ⟨10183795030102210310923733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6789196686734806873949155 10183795030102210310923733)
                ·
                  refine ⟨238682696018020554162275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10183795030102210310923733 238682696018020554162275)
                  ·
                    rfl

theorem cell21_1045874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1045874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045874 prefixEnd_1045874 := by exact prefixLift 1045874
  have htrace : WordTrace (prefixWord ++ tailWord_1045874) baseStart_1045874 baseEnd_1045874 := by
    simpa [prefixWord, tailWord_1045874, baseEnd_1045874] using wordTrace_append hprefix tailTrace_1045874
  have hstable : (prefixWord ++ tailWord_1045874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045874).length < 2 ^ (prefixWord ++ tailWord_1045874).sum := by decide
  have hdescent : baseEnd_1045874 < baseStart_1045874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045888 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1045888 : Nat := 118140960795 + 1045888 * 2 ^ 59
def prefixEnd_1045888 : Nat := 4983230072969 + 3 ^ 40 * 1045888 * 2
def baseEnd_1045888 : Nat := 238685891008759640928913

theorem tailTrace_1045888 : CollatzResearch.WordTrace tailWord_1045888 prefixEnd_1045888 238685891008759640928913 := by
  unfold tailWord_1045888
  simp only [CollatzResearch.WordTrace]
  refine ⟨19073334617466937147285159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25431112823289249529713545 19073334617466937147285159)
  ·
    refine ⟨28610001926200405720927739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19073334617466937147285159 28610001926200405720927739)
    ·
      refine ⟨42915002889300608581391609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28610001926200405720927739 42915002889300608581391609)
      ·
        refine ⟨32186252166975456436043707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42915002889300608581391609 32186252166975456436043707)
        ·
          refine ⟨48279378250463184654065561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32186252166975456436043707 48279378250463184654065561)
          ·
            refine ⟨36209533687847388490549171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48279378250463184654065561 36209533687847388490549171)
            ·
              refine ⟨54314300531771082735823757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36209533687847388490549171 54314300531771082735823757)
              ·
                refine ⟨20367862699414156025933909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54314300531771082735823757 20367862699414156025933909)
                ·
                  refine ⟨238685891008759640928913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20367862699414156025933909 238685891008759640928913)
                  ·
                    rfl

theorem cell21_1045888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1045888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045888 prefixEnd_1045888 := by exact prefixLift 1045888
  have htrace : WordTrace (prefixWord ++ tailWord_1045888) baseStart_1045888 baseEnd_1045888 := by
    simpa [prefixWord, tailWord_1045888, baseEnd_1045888] using wordTrace_append hprefix tailTrace_1045888
  have hstable : (prefixWord ++ tailWord_1045888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045888).length < 2 ^ (prefixWord ++ tailWord_1045888).sum := by decide
  have hdescent : baseEnd_1045888 < baseStart_1045888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045922 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1045922 : Nat := 118140960795 + 1045922 * 2 ^ 59
def prefixEnd_1045922 : Nat := 4983230072969 + 3 ^ 40 * 1045922 * 2
def baseEnd_1045922 : Nat := 238693650271983137362177

theorem tailTrace_1045922 : CollatzResearch.WordTrace tailWord_1045922 prefixEnd_1045922 238693650271983137362177 := by
  unfold tailWord_1045922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536977329202674525327005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25431939544540465400872013 9536977329202674525327005)
  ·
    refine ⟨3576366498451002946997627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9536977329202674525327005 3576366498451002946997627)
    ·
      refine ⟨5364549747676504420496441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576366498451002946997627 5364549747676504420496441)
      ·
        refine ⟨4023412310757378315372331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364549747676504420496441 4023412310757378315372331)
        ·
          refine ⟨6035118466136067473058497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023412310757378315372331 6035118466136067473058497)
          ·
            refine ⟨4526338849602050604793873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035118466136067473058497 4526338849602050604793873)
            ·
              refine ⟨3394754137201537953595405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526338849602050604793873 3394754137201537953595405)
              ·
                refine ⟨1273032801450576732598277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3394754137201537953595405 1273032801450576732598277)
                ·
                  refine ⟨238693650271983137362177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273032801450576732598277 238693650271983137362177)
                  ·
                    rfl

theorem cell21_1045922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1045922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045922 prefixEnd_1045922 := by exact prefixLift 1045922
  have htrace : WordTrace (prefixWord ++ tailWord_1045922) baseStart_1045922 baseEnd_1045922 := by
    simpa [prefixWord, tailWord_1045922, baseEnd_1045922] using wordTrace_append hprefix tailTrace_1045922
  have hstable : (prefixWord ++ tailWord_1045922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045922).length < 2 ^ (prefixWord ++ tailWord_1045922).sum := by decide
  have hdescent : baseEnd_1045922 < baseStart_1045922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045950 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1045950 : Nat := 118140960795 + 1045950 * 2 ^ 59
def prefixEnd_1045950 : Nat := 4983230072969 + 3 ^ 40 * 1045950 * 2
def baseEnd_1045950 : Nat := 238700040253461310895453

theorem tailTrace_1045950 : CollatzResearch.WordTrace tailWord_1045950 prefixEnd_1045950 238700040253461310895453 := by
  unfold tailWord_1045950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768616320088657360415913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25432620373806172588884869 4768616320088657360415913)
  ·
    refine ⟨3576462240066493020311935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4768616320088657360415913 3576462240066493020311935)
    ·
      refine ⟨5364693360099739530467903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576462240066493020311935 5364693360099739530467903)
      ·
        refine ⟨8047040040149609295701855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364693360099739530467903 8047040040149609295701855)
        ·
          refine ⟨12070560060224413943552783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047040040149609295701855 12070560060224413943552783)
          ·
            refine ⟨18105840090336620915329175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070560060224413943552783 18105840090336620915329175)
            ·
              refine ⟨27158760135504931372993763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18105840090336620915329175 27158760135504931372993763)
              ·
                refine ⟨40738140203257397059490645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27158760135504931372993763 40738140203257397059490645)
                ·
                  refine ⟨238700040253461310895453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40738140203257397059490645 238700040253461310895453)
                  ·
                    rfl

theorem cell21_1045950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1045950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045950 prefixEnd_1045950 := by exact prefixLift 1045950
  have htrace : WordTrace (prefixWord ++ tailWord_1045950) baseStart_1045950 baseEnd_1045950 := by
    simpa [prefixWord, tailWord_1045950, baseEnd_1045950] using wordTrace_append hprefix tailTrace_1045950
  have hstable : (prefixWord ++ tailWord_1045950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045950).length < 2 ^ (prefixWord ++ tailWord_1045950).sum := by decide
  have hdescent : baseEnd_1045950 < baseStart_1045950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045967 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 3]
def baseStart_1045967 : Nat := 118140960795 + 1045967 * 2 ^ 59
def prefixEnd_1045967 : Nat := 4983230072969 + 3 ^ 40 * 1045967 * 2
def baseEnd_1045967 : Nat := 238703919885073059112085

theorem tailTrace_1045967 : CollatzResearch.WordTrace tailWord_1045967 prefixEnd_1045967 238703919885073059112085 := by
  unfold tailWord_1045967
  simp only [CollatzResearch.WordTrace]
  refine ⟨38149550601647670786696155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25433033734431780524464103 38149550601647670786696155)
  ·
    refine ⟨57224325902471506180044233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38149550601647670786696155 57224325902471506180044233)
    ·
      refine ⟨42918244426853629635033175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57224325902471506180044233 42918244426853629635033175)
      ·
        refine ⟨64377366640280444452549763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42918244426853629635033175 64377366640280444452549763)
        ·
          refine ⟨96566049960420666678824645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64377366640280444452549763 96566049960420666678824645)
          ·
            refine ⟨18106134367578875002279621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96566049960420666678824645 18106134367578875002279621)
            ·
              refine ⟨3394900193921039062927429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18106134367578875002279621 3394900193921039062927429)
              ·
                refine ⟨636543786360194824298893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3394900193921039062927429 636543786360194824298893)
                ·
                  refine ⟨238703919885073059112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636543786360194824298893 238703919885073059112085)
                  ·
                    rfl

theorem cell21_1045967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 3].length) (baseStart_1045967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1045967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1045967 prefixEnd_1045967 := by exact prefixLift 1045967
  have htrace : WordTrace (prefixWord ++ tailWord_1045967) baseStart_1045967 baseEnd_1045967 := by
    simpa [prefixWord, tailWord_1045967, baseEnd_1045967] using wordTrace_append hprefix tailTrace_1045967
  have hstable : (prefixWord ++ tailWord_1045967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045967).length < 2 ^ (prefixWord ++ tailWord_1045967).sum := by decide
  have hdescent : baseEnd_1045967 < baseStart_1045967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046018 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1046018 : Nat := 118140960795 + 1046018 * 2 ^ 59
def prefixEnd_1046018 : Nat := 4983230072969 + 3 ^ 40 * 1046018 * 2
def baseEnd_1046018 : Nat := 238715558779908303761981

theorem tailTrace_1046018 : CollatzResearch.WordTrace tailWord_1046018 prefixEnd_1046018 238715558779908303761981 := by
  unfold tailWord_1046018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537852681115726624200677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25434273816308604331201805 9537852681115726624200677)
  ·
    refine ⟨1788347377709198742037627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9537852681115726624200677 1788347377709198742037627)
    ·
      refine ⟨2682521066563798113056441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788347377709198742037627 2682521066563798113056441)
      ·
        refine ⟨2011890799922848584792331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2682521066563798113056441 2011890799922848584792331)
        ·
          refine ⟨3017836199884272877188497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011890799922848584792331 3017836199884272877188497)
          ·
            refine ⟨2263377149913204657891373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017836199884272877188497 2263377149913204657891373)
            ·
              refine ⟨848766431217451746709265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2263377149913204657891373 848766431217451746709265)
              ·
                refine ⟨636574823413088810031949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848766431217451746709265 636574823413088810031949)
                ·
                  refine ⟨238715558779908303761981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636574823413088810031949 238715558779908303761981)
                  ·
                    rfl

theorem cell21_1046018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1046018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046018 prefixEnd_1046018 := by exact prefixLift 1046018
  have htrace : WordTrace (prefixWord ++ tailWord_1046018) baseStart_1046018 baseEnd_1046018 := by
    simpa [prefixWord, tailWord_1046018, baseEnd_1046018] using wordTrace_append hprefix tailTrace_1046018
  have hstable : (prefixWord ++ tailWord_1046018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046018).length < 2 ^ (prefixWord ++ tailWord_1046018).sum := by decide
  have hdescent : baseEnd_1046018 < baseStart_1046018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046119 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 3]
def baseStart_1046119 : Nat := 118140960795 + 1046119 * 2 ^ 59
def prefixEnd_1046119 : Nat := 4983230072969 + 3 ^ 40 * 1046119 * 2
def baseEnd_1046119 : Nat := 238738608355954572578441

theorem tailTrace_1046119 : CollatzResearch.WordTrace tailWord_1046119 prefixEnd_1046119 238738608355954572578441 := by
  unfold tailWord_1046119
  simp only [CollatzResearch.WordTrace]
  refine ⟨38155094497097000746229411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25436729664731333830819607 38155094497097000746229411)
  ·
    refine ⟨57232641745645501119344117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38155094497097000746229411 57232641745645501119344117)
    ·
      refine ⟨5365560163654265729938511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57232641745645501119344117 5365560163654265729938511)
      ·
        refine ⟨8048340245481398594907767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365560163654265729938511 8048340245481398594907767)
        ·
          refine ⟨12072510368222097892361651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048340245481398594907767 12072510368222097892361651)
          ·
            refine ⟨18108765552333146838542477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072510368222097892361651 18108765552333146838542477)
            ·
              refine ⟨6790787082124930064453429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18108765552333146838542477 6790787082124930064453429)
              ·
                refine ⟨636636288949212193542509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6790787082124930064453429 636636288949212193542509)
                ·
                  refine ⟨238738608355954572578441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636636288949212193542509 238738608355954572578441)
                  ·
                    rfl

theorem cell21_1046119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 3].length) (baseStart_1046119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046119 prefixEnd_1046119 := by exact prefixLift 1046119
  have htrace : WordTrace (prefixWord ++ tailWord_1046119) baseStart_1046119 baseEnd_1046119 := by
    simpa [prefixWord, tailWord_1046119, baseEnd_1046119] using wordTrace_append hprefix tailTrace_1046119
  have hstable : (prefixWord ++ tailWord_1046119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046119).length < 2 ^ (prefixWord ++ tailWord_1046119).sum := by decide
  have hdescent : baseEnd_1046119 < baseStart_1046119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046161 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1046161 : Nat := 118140960795 + 1046161 * 2 ^ 59
def prefixEnd_1046161 : Nat := 4983230072969 + 3 ^ 40 * 1046161 * 2
def baseEnd_1046161 : Nat := 238748193328171832878355

theorem tailTrace_1046161 : CollatzResearch.WordTrace tailWord_1046161 prefixEnd_1046161 238748193328171832878355 := by
  unfold tailWord_1046161
  simp only [CollatzResearch.WordTrace]
  refine ⟨38156626362944841919258337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25437750908629894612838891 38156626362944841919258337)
  ·
    refine ⟨28617469772208631439443753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38156626362944841919258337 28617469772208631439443753)
    ·
      refine ⟨21463102329156473579582815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28617469772208631439443753 21463102329156473579582815)
      ·
        refine ⟨32194653493734710369374223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463102329156473579582815 32194653493734710369374223)
        ·
          refine ⟨48291980240602065554061335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32194653493734710369374223 48291980240602065554061335)
          ·
            refine ⟨72437970360903098331092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48291980240602065554061335 72437970360903098331092003)
            ·
              refine ⟨108656955541354647496638005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72437970360903098331092003 108656955541354647496638005)
              ·
                refine ⟨10186589582001998202809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108656955541354647496638005 10186589582001998202809813)
                ·
                  refine ⟨238748193328171832878355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10186589582001998202809813 238748193328171832878355)
                  ·
                    rfl

theorem cell21_1046161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1046161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046161 prefixEnd_1046161 := by exact prefixLift 1046161
  have htrace : WordTrace (prefixWord ++ tailWord_1046161) baseStart_1046161 baseEnd_1046161 := by
    simpa [prefixWord, tailWord_1046161, baseEnd_1046161] using wordTrace_append hprefix tailTrace_1046161
  have hstable : (prefixWord ++ tailWord_1046161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046161).length < 2 ^ (prefixWord ++ tailWord_1046161).sum := by decide
  have hdescent : baseEnd_1046161 < baseStart_1046161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046192 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_1046192 : Nat := 118140960795 + 1046192 * 2 ^ 59
def prefixEnd_1046192 : Nat := 4983230072969 + 3 ^ 40 * 1046192 * 2
def baseEnd_1046192 : Nat := 238755267950522667861625

theorem tailTrace_1046192 : CollatzResearch.WordTrace tailWord_1046192 prefixEnd_1046192 238755267950522667861625 := by
  unfold tailWord_1046192
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078878512916267106818415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25438504683888356142424553 19078878512916267106818415)
  ·
    refine ⟨28618317769374400660227623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19078878512916267106818415 28618317769374400660227623)
    ·
      refine ⟨42927476654061600990341435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28618317769374400660227623 42927476654061600990341435)
      ·
        refine ⟨64391214981092401485512153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42927476654061600990341435 64391214981092401485512153)
        ·
          refine ⟨48293411235819301114134115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64391214981092401485512153 48293411235819301114134115)
          ·
            refine ⟨72440116853728951671201173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48293411235819301114134115 72440116853728951671201173)
            ·
              refine ⟨3395630477518544609587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72440116853728951671201173 3395630477518544609587555)
              ·
                refine ⟨5093445716277816914381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395630477518544609587555 5093445716277816914381333)
                ·
                  refine ⟨238755267950522667861625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5093445716277816914381333 238755267950522667861625)
                  ·
                    rfl

theorem cell21_1046192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_1046192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046192 prefixEnd_1046192 := by exact prefixLift 1046192
  have htrace : WordTrace (prefixWord ++ tailWord_1046192) baseStart_1046192 baseEnd_1046192 := by
    simpa [prefixWord, tailWord_1046192, baseEnd_1046192] using wordTrace_append hprefix tailTrace_1046192
  have hstable : (prefixWord ++ tailWord_1046192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046192).length < 2 ^ (prefixWord ++ tailWord_1046192).sum := by decide
  have hdescent : baseEnd_1046192 < baseStart_1046192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046254 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1046254 : Nat := 118140960795 + 1046254 * 2 ^ 59
def prefixEnd_1046254 : Nat := 4983230072969 + 3 ^ 40 * 1046254 * 2
def baseEnd_1046254 : Nat := 238769417195224337828165

theorem tailTrace_1046254 : CollatzResearch.WordTrace tailWord_1046254 prefixEnd_1046254 238769417195224337828165 := by
  unfold tailWord_1046254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770002293950989850299227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25440012234405279201595877 4770002293950989850299227)
  ·
    refine ⟨7155003440926484775448841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770002293950989850299227 7155003440926484775448841)
    ·
      refine ⟨5366252580694863581586631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7155003440926484775448841 5366252580694863581586631)
      ·
        refine ⟨8049378871042295372379947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366252580694863581586631 8049378871042295372379947)
        ·
          refine ⟨12074068306563443058569921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049378871042295372379947 12074068306563443058569921)
          ·
            refine ⟨9055551229922582293927441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12074068306563443058569921 9055551229922582293927441)
            ·
              refine ⟨6791663422441936720445581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9055551229922582293927441 6791663422441936720445581)
              ·
                refine ⟨2546873783415726270167093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791663422441936720445581 2546873783415726270167093)
                ·
                  refine ⟨238769417195224337828165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546873783415726270167093 238769417195224337828165)
                  ·
                    rfl

theorem cell21_1046254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1046254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046254 prefixEnd_1046254 := by exact prefixLift 1046254
  have htrace : WordTrace (prefixWord ++ tailWord_1046254) baseStart_1046254 baseEnd_1046254 := by
    simpa [prefixWord, tailWord_1046254, baseEnd_1046254] using wordTrace_append hprefix tailTrace_1046254
  have hstable : (prefixWord ++ tailWord_1046254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046254).length < 2 ^ (prefixWord ++ tailWord_1046254).sum := by decide
  have hdescent : baseEnd_1046254 < baseStart_1046254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046330 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1046330 : Nat := 118140960795 + 1046330 * 2 ^ 59
def prefixEnd_1046330 : Nat := 4983230072969 + 3 ^ 40 * 1046330 * 2
def baseEnd_1046330 : Nat := 238786761430665094561343

theorem tailTrace_1046330 : CollatzResearch.WordTrace tailWord_1046330 prefixEnd_1046330 238786761430665094561343 := by
  unfold tailWord_1046330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540697574833145945540111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25441860199555055854773629 9540697574833145945540111)
  ·
    refine ⟨14311046362249718918310167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9540697574833145945540111 14311046362249718918310167)
    ·
      refine ⟨21466569543374578377465251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14311046362249718918310167 21466569543374578377465251)
      ·
        refine ⟨32199854315061867566197877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21466569543374578377465251 32199854315061867566197877)
        ·
          refine ⟨3018736342037050084331051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32199854315061867566197877 3018736342037050084331051)
          ·
            refine ⟨4528104513055575126496577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018736342037050084331051 4528104513055575126496577)
            ·
              refine ⟨3396078384791681344872433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528104513055575126496577 3396078384791681344872433)
              ·
                refine ⟨2547058788593761008654325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396078384791681344872433 2547058788593761008654325)
                ·
                  refine ⟨238786761430665094561343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547058788593761008654325 238786761430665094561343)
                  ·
                    rfl

theorem cell21_1046330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1046330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046330 prefixEnd_1046330 := by exact prefixLift 1046330
  have htrace : WordTrace (prefixWord ++ tailWord_1046330) baseStart_1046330 baseEnd_1046330 := by
    simpa [prefixWord, tailWord_1046330, baseEnd_1046330] using wordTrace_append hprefix tailTrace_1046330
  have hstable : (prefixWord ++ tailWord_1046330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046330).length < 2 ^ (prefixWord ++ tailWord_1046330).sum := by decide
  have hdescent : baseEnd_1046330 < baseStart_1046330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046333 : List Nat := [1, 4, 1, 4, 1, 3, 2, 5]
def baseStart_1046333 : Nat := 118140960795 + 1046333 * 2 ^ 59
def prefixEnd_1046333 : Nat := 4983230072969 + 3 ^ 40 * 1046333 * 2
def baseEnd_1046333 : Nat := 79595815357179252003779

theorem tailTrace_1046333 : CollatzResearch.WordTrace tailWord_1046333 prefixEnd_1046333 79595815357179252003779 := by
  unfold tailWord_1046333
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162899718321715294519653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25441933145547810196346435 38162899718321715294519653)
  ·
    refine ⟨7155543697185321617722435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38162899718321715294519653 7155543697185321617722435)
    ·
      refine ⟨10733315545777982426583653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155543697185321617722435 10733315545777982426583653)
      ·
        refine ⟨2012496664833371704984435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10733315545777982426583653 2012496664833371704984435)
        ·
          refine ⟨3018744997250057557476653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012496664833371704984435 3018744997250057557476653)
          ·
            refine ⟨1132029373968771584053745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3018744997250057557476653 1132029373968771584053745)
            ·
              refine ⟨849022030476578688040309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132029373968771584053745 849022030476578688040309)
              ·
                refine ⟨79595815357179252003779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849022030476578688040309 79595815357179252003779)
                ·
                  rfl

theorem cell21_1046333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 5].length) (baseStart_1046333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046333 prefixEnd_1046333 := by exact prefixLift 1046333
  have htrace : WordTrace (prefixWord ++ tailWord_1046333) baseStart_1046333 baseEnd_1046333 := by
    simpa [prefixWord, tailWord_1046333, baseEnd_1046333] using wordTrace_append hprefix tailTrace_1046333
  have hstable : (prefixWord ++ tailWord_1046333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046333).length < 2 ^ (prefixWord ++ tailWord_1046333).sum := by decide
  have hdescent : baseEnd_1046333 < baseStart_1046333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046344 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1046344 : Nat := 118140960795 + 1046344 * 2 ^ 59
def prefixEnd_1046344 : Nat := 4983230072969 + 3 ^ 40 * 1046344 * 2
def baseEnd_1046344 : Nat := 238789956421404181327981

theorem tailTrace_1046344 : CollatzResearch.WordTrace tailWord_1046344 prefixEnd_1046344 238789956421404181327981 := by
  unfold tailWord_1046344
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081650460640932086585043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25442200614187909448780057 19081650460640932086585043)
  ·
    refine ⟨28622475690961398129877565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19081650460640932086585043 28622475690961398129877565)
    ·
      refine ⟨10733428384110524298704087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28622475690961398129877565 10733428384110524298704087)
      ·
        refine ⟨16100142576165786448056131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733428384110524298704087 16100142576165786448056131)
        ·
          refine ⟨24150213864248679672084197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16100142576165786448056131 24150213864248679672084197)
          ·
            refine ⟨4528165099546627438515787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24150213864248679672084197 4528165099546627438515787)
            ·
              refine ⟨6792247649319941157773681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528165099546627438515787 6792247649319941157773681)
              ·
                refine ⟨5094185736989955868330261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6792247649319941157773681 5094185736989955868330261)
                ·
                  refine ⟨238789956421404181327981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5094185736989955868330261 238789956421404181327981)
                  ·
                    rfl

theorem cell21_1046344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1046344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046344 prefixEnd_1046344 := by exact prefixLift 1046344
  have htrace : WordTrace (prefixWord ++ tailWord_1046344) baseStart_1046344 baseEnd_1046344 := by
    simpa [prefixWord, tailWord_1046344, baseEnd_1046344] using wordTrace_append hprefix tailTrace_1046344
  have hstable : (prefixWord ++ tailWord_1046344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046344).length < 2 ^ (prefixWord ++ tailWord_1046344).sum := by decide
  have hdescent : baseEnd_1046344 < baseStart_1046344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046364 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_1046364 : Nat := 118140960795 + 1046364 * 2 ^ 59
def prefixEnd_1046364 : Nat := 4983230072969 + 3 ^ 40 * 1046364 * 2
def baseEnd_1046364 : Nat := 238794520693888590994607

theorem tailTrace_1046364 : CollatzResearch.WordTrace tailWord_1046364 prefixEnd_1046364 238794520693888590994607 := by
  unfold tailWord_1046364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19082015190604703794449073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25442686920806271725932097 19082015190604703794449073)
  ·
    refine ⟨14311511392953527845836805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19082015190604703794449073 14311511392953527845836805)
    ·
      refine ⟨2683408386178786471094401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14311511392953527845836805 2683408386178786471094401)
      ·
        refine ⟨2012556289634089853320801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683408386178786471094401 2012556289634089853320801)
        ·
          refine ⟨1509417217225567389990601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2012556289634089853320801 1509417217225567389990601)
          ·
            refine ⟨1132062912919175542492951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509417217225567389990601 1132062912919175542492951)
            ·
              refine ⟨1698094369378763313739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132062912919175542492951 1698094369378763313739427)
              ·
                refine ⟨2547141554068144970609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698094369378763313739427 2547141554068144970609141)
                ·
                  refine ⟨238794520693888590994607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547141554068144970609141 238794520693888590994607)
                  ·
                    rfl

theorem cell21_1046364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_1046364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046364 prefixEnd_1046364 := by exact prefixLift 1046364
  have htrace : WordTrace (prefixWord ++ tailWord_1046364) baseStart_1046364 baseEnd_1046364 := by
    simpa [prefixWord, tailWord_1046364, baseEnd_1046364] using wordTrace_append hprefix tailTrace_1046364
  have hstable : (prefixWord ++ tailWord_1046364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046364).length < 2 ^ (prefixWord ++ tailWord_1046364).sum := by decide
  have hdescent : baseEnd_1046364 < baseStart_1046364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046375 : List Nat := [1, 1, 5, 1, 2, 1, 4, 6]
def baseStart_1046375 : Nat := 118140960795 + 1046375 * 2 ^ 59
def prefixEnd_1046375 : Nat := 4983230072969 + 3 ^ 40 * 1046375 * 2
def baseEnd_1046375 : Nat := 79599010347918338770417

theorem tailTrace_1046375 : CollatzResearch.WordTrace tailWord_1046375 prefixEnd_1046375 79599010347918338770417 := by
  unfold tailWord_1046375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38164431584169556467548579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25442954389446370978365719 38164431584169556467548579)
  ·
    refine ⟨57246647376254334701322869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38164431584169556467548579 57246647376254334701322869)
    ·
      refine ⟨5366873191523843878249019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57246647376254334701322869 5366873191523843878249019)
      ·
        refine ⟨8050309787285765817373529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366873191523843878249019 8050309787285765817373529)
        ·
          refine ⟨6037732340464324363030147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050309787285765817373529 6037732340464324363030147)
          ·
            refine ⟨9056598510696486544545221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037732340464324363030147 9056598510696486544545221)
            ·
              refine ⟨1698112220755591227102229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9056598510696486544545221 1698112220755591227102229)
              ·
                refine ⟨79599010347918338770417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1698112220755591227102229 79599010347918338770417)
                ·
                  rfl

theorem cell21_1046375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_1046375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046375 prefixEnd_1046375 := by exact prefixLift 1046375
  have htrace : WordTrace (prefixWord ++ tailWord_1046375) baseStart_1046375 baseEnd_1046375 := by
    simpa [prefixWord, tailWord_1046375, baseEnd_1046375] using wordTrace_append hprefix tailTrace_1046375
  have hstable : (prefixWord ++ tailWord_1046375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046375).length < 2 ^ (prefixWord ++ tailWord_1046375).sum := by decide
  have hdescent : baseEnd_1046375 < baseStart_1046375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046423 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 3]
def baseStart_1046423 : Nat := 118140960795 + 1046423 * 2 ^ 59
def prefixEnd_1046423 : Nat := 4983230072969 + 3 ^ 40 * 1046423 * 2
def baseEnd_1046423 : Nat := 238807985297717599511153

theorem tailTrace_1046423 : CollatzResearch.WordTrace tailWord_1046423 prefixEnd_1046423 238807985297717599511153 := by
  unfold tailWord_1046423
  simp only [CollatzResearch.WordTrace]
  refine ⟨38166182287995660665295923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25444121525330440443530615 38166182287995660665295923)
  ·
    refine ⟨57249273431993490997943885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38166182287995660665295923 57249273431993490997943885)
    ·
      refine ⟨21468477536997559124228957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57249273431993490997943885 21468477536997559124228957)
      ·
        refine ⟨8050679076374084671585859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21468477536997559124228957 8050679076374084671585859)
        ·
          refine ⟨12076018614561127007378789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8050679076374084671585859 12076018614561127007378789)
          ·
            refine ⟨2264253490230211313883523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12076018614561127007378789 2264253490230211313883523)
            ·
              refine ⟨3396380235345316970825285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264253490230211313883523 3396380235345316970825285)
              ·
                refine ⟨636821294127246932029741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3396380235345316970825285 636821294127246932029741)
                ·
                  refine ⟨238807985297717599511153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636821294127246932029741 238807985297717599511153)
                  ·
                    rfl

theorem cell21_1046423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 3].length) (baseStart_1046423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046423 prefixEnd_1046423 := by exact prefixLift 1046423
  have htrace : WordTrace (prefixWord ++ tailWord_1046423) baseStart_1046423 baseEnd_1046423 := by
    simpa [prefixWord, tailWord_1046423, baseEnd_1046423] using wordTrace_append hprefix tailTrace_1046423
  have hstable : (prefixWord ++ tailWord_1046423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046423).length < 2 ^ (prefixWord ++ tailWord_1046423).sum := by decide
  have hdescent : baseEnd_1046423 < baseStart_1046423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046440 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_1046440 : Nat := 118140960795 + 1046440 * 2 ^ 59
def prefixEnd_1046440 : Nat := 4983230072969 + 3 ^ 40 * 1046440 * 2
def baseEnd_1046440 : Nat := 238811864929329347727785

theorem tailTrace_1046440 : CollatzResearch.WordTrace tailWord_1046440 prefixEnd_1046440 238811864929329347727785 := by
  unfold tailWord_1046440
  simp only [CollatzResearch.WordTrace]
  refine ⟨19083401164467036284332387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25444534885956048379109849 19083401164467036284332387)
  ·
    refine ⟨28625101746700554426498581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19083401164467036284332387 28625101746700554426498581)
    ·
      refine ⟨1341801644376588488742121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28625101746700554426498581 1341801644376588488742121)
      ·
        refine ⟨1006351233282441366556591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1341801644376588488742121 1006351233282441366556591)
        ·
          refine ⟨1509526849923662049834887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006351233282441366556591 1509526849923662049834887)
          ·
            refine ⟨2264290274885493074752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509526849923662049834887 2264290274885493074752331)
            ·
              refine ⟨3396435412328239612128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264290274885493074752331 3396435412328239612128497)
              ·
                refine ⟨2547326559246179709096373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396435412328239612128497 2547326559246179709096373)
                ·
                  refine ⟨238811864929329347727785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547326559246179709096373 238811864929329347727785)
                  ·
                    rfl

theorem cell21_1046440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_1046440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046440 prefixEnd_1046440 := by exact prefixLift 1046440
  have htrace : WordTrace (prefixWord ++ tailWord_1046440) baseStart_1046440 baseEnd_1046440 := by
    simpa [prefixWord, tailWord_1046440, baseEnd_1046440] using wordTrace_append hprefix tailTrace_1046440
  have hstable : (prefixWord ++ tailWord_1046440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046440).length < 2 ^ (prefixWord ++ tailWord_1046440).sum := by decide
  have hdescent : baseEnd_1046440 < baseStart_1046440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046451 : List Nat := [1, 1, 1, 2, 3, 1, 7, 5]
def baseStart_1046451 : Nat := 118140960795 + 1046451 * 2 ^ 59
def prefixEnd_1046451 : Nat := 4983230072969 + 3 ^ 40 * 1046451 * 2
def baseEnd_1046451 : Nat := 79604791759731924348143

theorem tailTrace_1046451 : CollatzResearch.WordTrace tailWord_1046451 prefixEnd_1046451 79604791759731924348143 := by
  unfold tailWord_1046451
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167203531894221447315207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25444802354596147631543471 38167203531894221447315207)
  ·
    refine ⟨57250805297841332170972811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38167203531894221447315207 57250805297841332170972811)
    ·
      refine ⟨85876207946761998256459217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57250805297841332170972811 85876207946761998256459217)
      ·
        refine ⟨64407155960071498692344413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85876207946761998256459217 64407155960071498692344413)
        ·
          refine ⟨24152683485026812009629155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64407155960071498692344413 24152683485026812009629155)
          ·
            refine ⟨36229025227540218014443733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24152683485026812009629155 36229025227540218014443733)
            ·
              refine ⟨849117778770473859713525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36229025227540218014443733 849117778770473859713525)
              ·
                refine ⟨79604791759731924348143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849117778770473859713525 79604791759731924348143)
                ·
                  rfl

theorem cell21_1046451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].length) (baseStart_1046451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046451 prefixEnd_1046451 := by exact prefixLift 1046451
  have htrace : WordTrace (prefixWord ++ tailWord_1046451) baseStart_1046451 baseEnd_1046451 := by
    simpa [prefixWord, tailWord_1046451, baseEnd_1046451] using wordTrace_append hprefix tailTrace_1046451
  have hstable : (prefixWord ++ tailWord_1046451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046451).length < 2 ^ (prefixWord ++ tailWord_1046451).sum := by decide
  have hdescent : baseEnd_1046451 < baseStart_1046451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046496 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_1046496 : Nat := 118140960795 + 1046496 * 2 ^ 59
def prefixEnd_1046496 : Nat := 4983230072969 + 3 ^ 40 * 1046496 * 2
def baseEnd_1046496 : Nat := 238824644892285694794337

theorem tailTrace_1046496 : CollatzResearch.WordTrace tailWord_1046496 prefixEnd_1046496 238824644892285694794337 := by
  unfold tailWord_1046496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19084422408365597066351671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25445896544487462755135561 19084422408365597066351671)
  ·
    refine ⟨28626633612548395599527507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19084422408365597066351671 28626633612548395599527507)
    ·
      refine ⟨42939950418822593399291261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28626633612548395599527507 42939950418822593399291261)
      ·
        refine ⟨16102481407058472524734223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42939950418822593399291261 16102481407058472524734223)
        ·
          refine ⟨24153722110587708787101335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102481407058472524734223 24153722110587708787101335)
          ·
            refine ⟨36230583165881563180652003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153722110587708787101335 36230583165881563180652003)
            ·
              refine ⟨54345874748822344770978005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36230583165881563180652003 54345874748822344770978005)
              ·
                refine ⟨1273731439425523705569797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 54345874748822344770978005 1273731439425523705569797)
                ·
                  refine ⟨238824644892285694794337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273731439425523705569797 238824644892285694794337)
                  ·
                    rfl

theorem cell21_1046496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_1046496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046496 prefixEnd_1046496 := by exact prefixLift 1046496
  have htrace : WordTrace (prefixWord ++ tailWord_1046496) baseStart_1046496 baseEnd_1046496 := by
    simpa [prefixWord, tailWord_1046496, baseEnd_1046496] using wordTrace_append hprefix tailTrace_1046496
  have hstable : (prefixWord ++ tailWord_1046496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046496).length < 2 ^ (prefixWord ++ tailWord_1046496).sum := by decide
  have hdescent : baseEnd_1046496 < baseStart_1046496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046555 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_1046555 : Nat := 118140960795 + 1046555 * 2 ^ 59
def prefixEnd_1046555 : Nat := 4983230072969 + 3 ^ 40 * 1046555 * 2
def baseEnd_1046555 : Nat := 238838109496114703310883

theorem tailTrace_1046555 : CollatzResearch.WordTrace tailWord_1046555 prefixEnd_1046555 238838109496114703310883 := by
  unfold tailWord_1046555
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170996723517447209101119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25447331149011631472734079 38170996723517447209101119)
  ·
    refine ⟨57256495085276170813651679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38170996723517447209101119 57256495085276170813651679)
    ·
      refine ⟨85884742627914256220477519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57256495085276170813651679 85884742627914256220477519)
      ·
        refine ⟨128827113941871384330716279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85884742627914256220477519 128827113941871384330716279)
        ·
          refine ⟨193240670912807076496074419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128827113941871384330716279 193240670912807076496074419)
          ·
            refine ⟨289861006369210614744111629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193240670912807076496074419 289861006369210614744111629)
            ·
              refine ⟨108697877388453980529041861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289861006369210614744111629 108697877388453980529041861)
              ·
                refine ⟨20380852010335121349195349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108697877388453980529041861 20380852010335121349195349)
                ·
                  refine ⟨238838109496114703310883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20380852010335121349195349 238838109496114703310883)
                  ·
                    rfl

theorem cell21_1046555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_1046555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046555 prefixEnd_1046555 := by exact prefixLift 1046555
  have htrace : WordTrace (prefixWord ++ tailWord_1046555) baseStart_1046555 baseEnd_1046555 := by
    simpa [prefixWord, tailWord_1046555, baseEnd_1046555] using wordTrace_append hprefix tailTrace_1046555
  have hstable : (prefixWord ++ tailWord_1046555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046555).length < 2 ^ (prefixWord ++ tailWord_1046555).sum := by decide
  have hdescent : baseEnd_1046555 < baseStart_1046555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046589 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1046589 : Nat := 118140960795 + 1046589 * 2 ^ 59
def prefixEnd_1046589 : Nat := 4983230072969 + 3 ^ 40 * 1046589 * 2
def baseEnd_1046589 : Nat := 238845868759338199744147

theorem tailTrace_1046589 : CollatzResearch.WordTrace tailWord_1046589 prefixEnd_1046589 238845868759338199744147 := by
  unfold tailWord_1046589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172236805394271015838821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25448157870262847343892547 38172236805394271015838821)
  ·
    refine ⟨7157294401011425815469779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38172236805394271015838821 7157294401011425815469779)
    ·
      refine ⟨10735941601517138723204669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157294401011425815469779 10735941601517138723204669)
      ·
        refine ⟨4025978100568927021201751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10735941601517138723204669 4025978100568927021201751)
        ·
          refine ⟨6038967150853390531802627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025978100568927021201751 6038967150853390531802627)
          ·
            refine ⟨9058450726280085797703941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6038967150853390531802627 9058450726280085797703941)
            ·
              refine ⟨1698459511177516087069489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9058450726280085797703941 1698459511177516087069489)
              ·
                refine ⟨1273844633383137065302117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698459511177516087069489 1273844633383137065302117)
                ·
                  refine ⟨238845868759338199744147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273844633383137065302117 238845868759338199744147)
                  ·
                    rfl

theorem cell21_1046589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1046589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046589 prefixEnd_1046589 := by exact prefixLift 1046589
  have htrace : WordTrace (prefixWord ++ tailWord_1046589) baseStart_1046589 baseEnd_1046589 := by
    simpa [prefixWord, tailWord_1046589, baseEnd_1046589] using wordTrace_append hprefix tailTrace_1046589
  have hstable : (prefixWord ++ tailWord_1046589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046589).length < 2 ^ (prefixWord ++ tailWord_1046589).sum := by decide
  have hdescent : baseEnd_1046589 < baseStart_1046589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046592 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_1046592 : Nat := 118140960795 + 1046592 * 2 ^ 59
def prefixEnd_1046592 : Nat := 4983230072969 + 3 ^ 40 * 1046592 * 2
def baseEnd_1046592 : Nat := 238846553400210861194141

theorem tailTrace_1046592 : CollatzResearch.WordTrace tailWord_1046592 prefixEnd_1046592 238846553400210861194141 := by
  unfold tailWord_1046592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086173112191701264099015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25448230816255601685465353 19086173112191701264099015)
  ·
    refine ⟨28629259668287551896148523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19086173112191701264099015 28629259668287551896148523)
    ·
      refine ⟨42943889502431327844222785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28629259668287551896148523 42943889502431327844222785)
      ·
        refine ⟨32207917126823495883167089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42943889502431327844222785 32207917126823495883167089)
        ·
          refine ⟨24155937845117621912375317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32207917126823495883167089 24155937845117621912375317)
          ·
            refine ⟨1132309586489888527142593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24155937845117621912375317 1132309586489888527142593)
            ·
              refine ⟨849232189867416395356945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132309586489888527142593 849232189867416395356945)
              ·
                refine ⟨636924142400562296517709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849232189867416395356945 636924142400562296517709)
                ·
                  refine ⟨238846553400210861194141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636924142400562296517709 238846553400210861194141)
                  ·
                    rfl

theorem cell21_1046592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_1046592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046592 prefixEnd_1046592 := by exact prefixLift 1046592
  have htrace : WordTrace (prefixWord ++ tailWord_1046592) baseStart_1046592 baseEnd_1046592 := by
    simpa [prefixWord, tailWord_1046592, baseEnd_1046592] using wordTrace_append hprefix tailTrace_1046592
  have hstable : (prefixWord ++ tailWord_1046592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046592).length < 2 ^ (prefixWord ++ tailWord_1046592).sum := by decide
  have hdescent : baseEnd_1046592 < baseStart_1046592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046617 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_1046617 : Nat := 118140960795 + 1046617 * 2 ^ 59
def prefixEnd_1046617 : Nat := 4983230072969 + 3 ^ 40 * 1046617 * 2
def baseEnd_1046617 : Nat := 238852258740816373277423

theorem tailTrace_1046617 : CollatzResearch.WordTrace tailWord_1046617 prefixEnd_1046617 238852258740816373277423 := by
  unfold tailWord_1046617
  simp only [CollatzResearch.WordTrace]
  refine ⟨38173258049292831797858105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25448838699528554531905403 38173258049292831797858105)
  ·
    refine ⟨28629943536969623848393579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38173258049292831797858105 28629943536969623848393579)
    ·
      refine ⟨42944915305454435772590369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28629943536969623848393579 42944915305454435772590369)
      ·
        refine ⟨32208686479090826829442777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42944915305454435772590369 32208686479090826829442777)
        ·
          refine ⟨24156514859318120122082083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32208686479090826829442777 24156514859318120122082083)
          ·
            refine ⟨36234772288977180183123125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24156514859318120122082083 36234772288977180183123125)
            ·
              refine ⟨3397009902091610642167793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36234772288977180183123125 3397009902091610642167793)
              ·
                refine ⟨2547757426568707981625845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3397009902091610642167793 2547757426568707981625845)
                ·
                  refine ⟨238852258740816373277423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2547757426568707981625845 238852258740816373277423)
                  ·
                    rfl

theorem cell21_1046617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_1046617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046617 prefixEnd_1046617 := by exact prefixLift 1046617
  have htrace : WordTrace (prefixWord ++ tailWord_1046617) baseStart_1046617 baseEnd_1046617 := by
    simpa [prefixWord, tailWord_1046617, baseEnd_1046617] using wordTrace_append hprefix tailTrace_1046617
  have hstable : (prefixWord ++ tailWord_1046617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046617).length < 2 ^ (prefixWord ++ tailWord_1046617).sum := by decide
  have hdescent : baseEnd_1046617 < baseStart_1046617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046620 : List Nat := [2, 2, 4, 1, 1, 3, 3, 5]
def baseStart_1046620 : Nat := 118140960795 + 1046620 * 2 ^ 59
def prefixEnd_1046620 : Nat := 4983230072969 + 3 ^ 40 * 1046620 * 2
def baseEnd_1046620 : Nat := 79617647793896344909139

theorem tailTrace_1046620 : CollatzResearch.WordTrace tailWord_1046620 prefixEnd_1046620 79617647793896344909139 := by
  unfold tailWord_1046620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086683734140981655108657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25448911645521308873478209 19086683734140981655108657)
  ·
    refine ⟨14315012800605736241331493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19086683734140981655108657 14315012800605736241331493)
    ·
      refine ⟨2684064900113575545249655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14315012800605736241331493 2684064900113575545249655)
      ·
        refine ⟨4026097350170363317874483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684064900113575545249655 4026097350170363317874483)
        ·
          refine ⟨6039146025255544976811725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026097350170363317874483 6039146025255544976811725)
          ·
            refine ⟨2264679759470829366304397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6039146025255544976811725 2264679759470829366304397)
            ·
              refine ⟨849254909801561012364149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264679759470829366304397 849254909801561012364149)
              ·
                refine ⟨79617647793896344909139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849254909801561012364149 79617647793896344909139)
                ·
                  rfl

theorem cell21_1046620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_1046620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046620 prefixEnd_1046620 := by exact prefixLift 1046620
  have htrace : WordTrace (prefixWord ++ tailWord_1046620) baseStart_1046620 baseEnd_1046620 := by
    simpa [prefixWord, tailWord_1046620, baseEnd_1046620] using wordTrace_append hprefix tailTrace_1046620
  have hstable : (prefixWord ++ tailWord_1046620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046620).length < 2 ^ (prefixWord ++ tailWord_1046620).sum := by decide
  have hdescent : baseEnd_1046620 < baseStart_1046620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046665 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 4]
def baseStart_1046665 : Nat := 118140960795 + 1046665 * 2 ^ 59
def prefixEnd_1046665 : Nat := 4983230072969 + 3 ^ 40 * 1046665 * 2
def baseEnd_1046665 : Nat := 238863212994778956477325

theorem tailTrace_1046665 : CollatzResearch.WordTrace tailWord_1046665 prefixEnd_1046665 238863212994778956477325 := by
  unfold tailWord_1046665
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175008753118935995605449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25450005835412623997070299 38175008753118935995605449)
  ·
    refine ⟨28631256564839201996704087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38175008753118935995605449 28631256564839201996704087)
    ·
      refine ⟨42946884847258802995056131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28631256564839201996704087 42946884847258802995056131)
      ·
        refine ⟨64420327270888204492584197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42946884847258802995056131 64420327270888204492584197)
        ·
          refine ⟨12078811363291538342359537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64420327270888204492584197 12078811363291538342359537)
          ·
            refine ⟨9059108522468653756769653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12078811363291538342359537 9059108522468653756769653)
            ·
              refine ⟨849291423981436289697155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9059108522468653756769653 849291423981436289697155)
              ·
                refine ⟨1273937135972154434545733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849291423981436289697155 1273937135972154434545733)
                ·
                  refine ⟨238863212994778956477325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273937135972154434545733 238863212994778956477325)
                  ·
                    rfl

theorem cell21_1046665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_1046665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046665 prefixEnd_1046665 := by exact prefixLift 1046665
  have htrace : WordTrace (prefixWord ++ tailWord_1046665) baseStart_1046665 baseEnd_1046665 := by
    simpa [prefixWord, tailWord_1046665, baseEnd_1046665] using wordTrace_append hprefix tailTrace_1046665
  have hstable : (prefixWord ++ tailWord_1046665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046665).length < 2 ^ (prefixWord ++ tailWord_1046665).sum := by decide
  have hdescent : baseEnd_1046665 < baseStart_1046665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046679 : List Nat := [1, 1, 3, 3, 4, 1, 1, 7]
def baseStart_1046679 : Nat := 118140960795 + 1046679 * 2 ^ 59
def prefixEnd_1046679 : Nat := 4983230072969 + 3 ^ 40 * 1046679 * 2
def baseEnd_1046679 : Nat := 79622135995172681081321

theorem tailTrace_1046679 : CollatzResearch.WordTrace tailWord_1046679 prefixEnd_1046679 79622135995172681081321 := by
  unfold tailWord_1046679
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175519375068216386615091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25450346250045477591076727 38175519375068216386615091)
  ·
    refine ⟨57263279062602324579922637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38175519375068216386615091 57263279062602324579922637)
    ·
      refine ⟨21473729648475871717470989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57263279062602324579922637 21473729648475871717470989)
      ·
        refine ⟨8052648618178451894051621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21473729648475871717470989 8052648618178451894051621)
        ·
          refine ⟨1509871615908459730134679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8052648618178451894051621 1509871615908459730134679)
          ·
            refine ⟨2264807423862689595202019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509871615908459730134679 2264807423862689595202019)
            ·
              refine ⟨3397211135794034392803029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264807423862689595202019 3397211135794034392803029)
              ·
                refine ⟨79622135995172681081321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3397211135794034392803029 79622135995172681081321)
                ·
                  rfl

theorem cell21_1046679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_1046679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046679 prefixEnd_1046679 := by exact prefixLift 1046679
  have htrace : WordTrace (prefixWord ++ tailWord_1046679) baseStart_1046679 baseEnd_1046679 := by
    simpa [prefixWord, tailWord_1046679, baseEnd_1046679] using wordTrace_append hprefix tailTrace_1046679
  have hstable : (prefixWord ++ tailWord_1046679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046679).length < 2 ^ (prefixWord ++ tailWord_1046679).sum := by decide
  have hdescent : baseEnd_1046679 < baseStart_1046679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046702 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_1046702 : Nat := 118140960795 + 1046702 * 2 ^ 59
def prefixEnd_1046702 : Nat := 4983230072969 + 3 ^ 40 * 1046702 * 2
def baseEnd_1046702 : Nat := 238871656898875114360583

theorem tailTrace_1046702 : CollatzResearch.WordTrace tailWord_1046702 prefixEnd_1046702 238871656898875114360583 := by
  unfold tailWord_1046702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772044781748111414337795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25450905502656594209801573 4772044781748111414337795)
  ·
    refine ⟨7158067172622167121506693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4772044781748111414337795 7158067172622167121506693)
    ·
      refine ⟨1342137594866656335282505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7158067172622167121506693 1342137594866656335282505)
      ·
        refine ⟨1006603196149992251461879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1342137594866656335282505 1006603196149992251461879)
        ·
          refine ⟨1509904794224988377192819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006603196149992251461879 1509904794224988377192819)
          ·
            refine ⟨2264857191337482565789229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509904794224988377192819 2264857191337482565789229)
            ·
              refine ⟨849321446751555962170961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264857191337482565789229 849321446751555962170961)
              ·
                refine ⟨636991085063666971628221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849321446751555962170961 636991085063666971628221)
                ·
                  refine ⟨238871656898875114360583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636991085063666971628221 238871656898875114360583)
                  ·
                    rfl

theorem cell21_1046702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_1046702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046702 prefixEnd_1046702 := by exact prefixLift 1046702
  have htrace : WordTrace (prefixWord ++ tailWord_1046702) baseStart_1046702 baseEnd_1046702 := by
    simpa [prefixWord, tailWord_1046702, baseEnd_1046702] using wordTrace_append hprefix tailTrace_1046702
  have hstable : (prefixWord ++ tailWord_1046702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046702).length < 2 ^ (prefixWord ++ tailWord_1046702).sum := by decide
  have hdescent : baseEnd_1046702 < baseStart_1046702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046755 : List Nat := [1, 1, 1, 8, 1, 9]
def baseStart_1046755 : Nat := 118140960795 + 1046755 * 2 ^ 59
def prefixEnd_1046755 : Nat := 4983230072969 + 3 ^ 40 * 1046755 * 2
def baseEnd_1046755 : Nat := 8847546378554029628783

theorem tailTrace_1046755 : CollatzResearch.WordTrace tailWord_1046755 prefixEnd_1046755 8847546378554029628783 := by
  unfold tailWord_1046755
  simp only [CollatzResearch.WordTrace]
  refine ⟨38178291322792881366381719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25452194215195254244254479 38178291322792881366381719)
  ·
    refine ⟨57267436984189322049572579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38178291322792881366381719 57267436984189322049572579)
    ·
      refine ⟨85901155476283983074358869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57267436984189322049572579 85901155476283983074358869)
      ·
        refine ⟨1006654165737702926652643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 85901155476283983074358869 1006654165737702926652643)
        ·
          refine ⟨1509981248606554389978965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006654165737702926652643 1509981248606554389978965)
          ·
            refine ⟨8847546378554029628783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1509981248606554389978965 8847546378554029628783)
            ·
              rfl

theorem cell21_1046755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 9].length) (baseStart_1046755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046755 prefixEnd_1046755 := by exact prefixLift 1046755
  have htrace : WordTrace (prefixWord ++ tailWord_1046755) baseStart_1046755 baseEnd_1046755 := by
    simpa [prefixWord, tailWord_1046755, baseEnd_1046755] using wordTrace_append hprefix tailTrace_1046755
  have hstable : (prefixWord ++ tailWord_1046755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046755).length < 2 ^ (prefixWord ++ tailWord_1046755).sum := by decide
  have hdescent : baseEnd_1046755 < baseStart_1046755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046786 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1046786 : Nat := 118140960795 + 1046786 * 2 ^ 59
def prefixEnd_1046786 : Nat := 4983230072969 + 3 ^ 40 * 1046786 * 2
def baseEnd_1046786 : Nat := 238890826843309634960411

theorem tailTrace_1046786 : CollatzResearch.WordTrace tailWord_1046786 prefixEnd_1046786 238890826843309634960411 := by
  unfold tailWord_1046786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9544855496420143415190053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25452947990453715773840141 9544855496420143415190053)
  ·
    refine ⟨1789660405578776890348135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9544855496420143415190053 1789660405578776890348135)
    ·
      refine ⟨2684490608368165335522203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789660405578776890348135 2684490608368165335522203)
      ·
        refine ⟨4026735912552248003283305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684490608368165335522203 4026735912552248003283305)
        ·
          refine ⟨3020051934414186002462479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4026735912552248003283305 3020051934414186002462479)
          ·
            refine ⟨4530077901621279003693719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020051934414186002462479 4530077901621279003693719)
            ·
              refine ⟨6795116852431918505540579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530077901621279003693719 6795116852431918505540579)
              ·
                refine ⟨10192675278647877758310869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795116852431918505540579 10192675278647877758310869)
                ·
                  refine ⟨238890826843309634960411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10192675278647877758310869 238890826843309634960411)
                  ·
                    rfl

theorem cell21_1046786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1046786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046786 prefixEnd_1046786 := by exact prefixLift 1046786
  have htrace : WordTrace (prefixWord ++ tailWord_1046786) baseStart_1046786 baseEnd_1046786 := by
    simpa [prefixWord, tailWord_1046786, baseEnd_1046786] using wordTrace_append hprefix tailTrace_1046786
  have hstable : (prefixWord ++ tailWord_1046786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046786).length < 2 ^ (prefixWord ++ tailWord_1046786).sum := by decide
  have hdescent : baseEnd_1046786 < baseStart_1046786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046834 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1046834 : Nat := 118140960795 + 1046834 * 2 ^ 59
def prefixEnd_1046834 : Nat := 4983230072969 + 3 ^ 40 * 1046834 * 2
def baseEnd_1046834 : Nat := 238901781097272218160313

theorem tailTrace_1046834 : CollatzResearch.WordTrace tailWord_1046834 prefixEnd_1046834 238901781097272218160313 := by
  unfold tailWord_1046834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545293172376669464626889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25454115126337785239005037 9545293172376669464626889)
  ·
    refine ⟨7158969879282502098470167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9545293172376669464626889 7158969879282502098470167)
    ·
      refine ⟨10738454818923753147705251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158969879282502098470167 10738454818923753147705251)
      ·
        refine ⟨16107682228385629721557877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738454818923753147705251 16107682228385629721557877)
        ·
          refine ⟨1510095208911152786396051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16107682228385629721557877 1510095208911152786396051)
          ·
            refine ⟨2265142813366729179594077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510095208911152786396051 2265142813366729179594077)
            ·
              refine ⟨849428555012523442347779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2265142813366729179594077 849428555012523442347779)
              ·
                refine ⟨1274142832518785163521669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849428555012523442347779 1274142832518785163521669)
                ·
                  refine ⟨238901781097272218160313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274142832518785163521669 238901781097272218160313)
                  ·
                    rfl

theorem cell21_1046834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1046834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046834 prefixEnd_1046834 := by exact prefixLift 1046834
  have htrace : WordTrace (prefixWord ++ tailWord_1046834) baseStart_1046834 baseEnd_1046834 := by
    simpa [prefixWord, tailWord_1046834, baseEnd_1046834] using wordTrace_append hprefix tailTrace_1046834
  have hstable : (prefixWord ++ tailWord_1046834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046834).length < 2 ^ (prefixWord ++ tailWord_1046834).sum := by decide
  have hdescent : baseEnd_1046834 < baseStart_1046834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1046862 : Nat := 118140960795 + 1046862 * 2 ^ 59
def prefixEnd_1046862 : Nat := 4983230072969 + 3 ^ 40 * 1046862 * 2
def baseEnd_1046862 : Nat := 238908171078750391693589

theorem tailTrace_1046862 : CollatzResearch.WordTrace tailWord_1046862 prefixEnd_1046862 238908171078750391693589 := by
  unfold tailWord_1046862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772774241675654830065855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25454795955603492427017893 4772774241675654830065855)
  ·
    refine ⟨7159161362513482245098783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4772774241675654830065855 7159161362513482245098783)
    ·
      refine ⟨10738742043770223367648175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7159161362513482245098783 10738742043770223367648175)
      ·
        refine ⟨16108113065655335051472263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738742043770223367648175 16108113065655335051472263)
        ·
          refine ⟨24162169598483002577208395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16108113065655335051472263 24162169598483002577208395)
          ·
            refine ⟨36243254397724503865812593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24162169598483002577208395 36243254397724503865812593)
            ·
              refine ⟨27182440798293377899359445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36243254397724503865812593 27182440798293377899359445)
              ·
                refine ⟨637088456210001044516237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27182440798293377899359445 637088456210001044516237)
                ·
                  refine ⟨238908171078750391693589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637088456210001044516237 238908171078750391693589)
                  ·
                    rfl

theorem cell21_1046862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1046862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046862 prefixEnd_1046862 := by exact prefixLift 1046862
  have htrace : WordTrace (prefixWord ++ tailWord_1046862) baseStart_1046862 baseEnd_1046862 := by
    simpa [prefixWord, tailWord_1046862, baseEnd_1046862] using wordTrace_append hprefix tailTrace_1046862
  have hstable : (prefixWord ++ tailWord_1046862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046862).length < 2 ^ (prefixWord ++ tailWord_1046862).sum := by decide
  have hdescent : baseEnd_1046862 < baseStart_1046862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046935 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_1046935 : Nat := 118140960795 + 1046935 * 2 ^ 59
def prefixEnd_1046935 : Nat := 4983230072969 + 3 ^ 40 * 1046935 * 2
def baseEnd_1046935 : Nat := 238924830673318486976773

theorem tailTrace_1046935 : CollatzResearch.WordTrace tailWord_1046935 prefixEnd_1046935 238924830673318486976773 := by
  unfold tailWord_1046935
  simp only [CollatzResearch.WordTrace]
  refine ⟨38184856462140772107934259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25456570974760514738622839 38184856462140772107934259)
  ·
    refine ⟨57277284693211158161901389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38184856462140772107934259 57277284693211158161901389)
    ·
      refine ⟨21478981759954184310713021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57277284693211158161901389 21478981759954184310713021)
      ·
        refine ⟨8054618159982819116517383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21478981759954184310713021 8054618159982819116517383)
        ·
          refine ⟨12081927239974228674776075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054618159982819116517383 12081927239974228674776075)
          ·
            refine ⟨18122890859961343012164113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081927239974228674776075 18122890859961343012164113)
            ·
              refine ⟨13592168144971007259123085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18122890859961343012164113 13592168144971007259123085)
              ·
                refine ⟨5097063054364127722171157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13592168144971007259123085 5097063054364127722171157)
                ·
                  refine ⟨238924830673318486976773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5097063054364127722171157 238924830673318486976773)
                  ·
                    rfl

theorem cell21_1046935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_1046935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046935 prefixEnd_1046935 := by exact prefixLift 1046935
  have htrace : WordTrace (prefixWord ++ tailWord_1046935) baseStart_1046935 baseEnd_1046935 := by
    simpa [prefixWord, tailWord_1046935, baseEnd_1046935] using wordTrace_append hprefix tailTrace_1046935
  have hstable : (prefixWord ++ tailWord_1046935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046935).length < 2 ^ (prefixWord ++ tailWord_1046935).sum := by decide
  have hdescent : baseEnd_1046935 < baseStart_1046935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046997 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1046997 : Nat := 118140960795 + 1046997 * 2 ^ 59
def prefixEnd_1046997 : Nat := 4983230072969 + 3 ^ 40 * 1046997 * 2
def baseEnd_1046997 : Nat := 238938979918020156943313

theorem tailTrace_1046997 : CollatzResearch.WordTrace tailWord_1046997 prefixEnd_1046997 238938979918020156943313 := by
  unfold tailWord_1046997
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187117787916156696691245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458078525277437797794163 38187117787916156696691245)
  ·
    refine ⟨14320169170468558761259217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38187117787916156696691245 14320169170468558761259217)
    ·
      refine ⟨10740126877851419070944413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14320169170468558761259217 10740126877851419070944413)
      ·
        refine ⟨4027547579194282151604155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10740126877851419070944413 4027547579194282151604155)
        ·
          refine ⟨6041321368791423227406233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027547579194282151604155 6041321368791423227406233)
          ·
            refine ⟨4530991026593567420554675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041321368791423227406233 4530991026593567420554675)
            ·
              refine ⟨6796486539890351130832013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530991026593567420554675 6796486539890351130832013)
              ·
                refine ⟨2548682452458881674062005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6796486539890351130832013 2548682452458881674062005)
                ·
                  refine ⟨238938979918020156943313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2548682452458881674062005 238938979918020156943313)
                  ·
                    rfl

theorem cell21_1046997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1046997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1046997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1046997 prefixEnd_1046997 := by exact prefixLift 1046997
  have htrace : WordTrace (prefixWord ++ tailWord_1046997) baseStart_1046997 baseEnd_1046997 := by
    simpa [prefixWord, tailWord_1046997, baseEnd_1046997] using wordTrace_append hprefix tailTrace_1046997
  have hstable : (prefixWord ++ tailWord_1046997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046997).length < 2 ^ (prefixWord ++ tailWord_1046997).sum := by decide
  have hdescent : baseEnd_1046997 < baseStart_1046997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047118 : List Nat := [4, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1047118 : Nat := 118140960795 + 1047118 * 2 ^ 59
def prefixEnd_1047118 : Nat := 4983230072969 + 3 ^ 40 * 1047118 * 2
def baseEnd_1047118 : Nat := 79655531255516945142133

theorem tailTrace_1047118 : CollatzResearch.WordTrace tailWord_1047118 prefixEnd_1047118 79655531255516945142133 := by
  unfold tailWord_1047118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773941377559724295230751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25461020680318529574564005 4773941377559724295230751)
  ·
    refine ⟨7160912066339586442846127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773941377559724295230751 7160912066339586442846127)
    ·
      refine ⟨10741368099509379664269191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160912066339586442846127 10741368099509379664269191)
      ·
        refine ⟨16112052149264069496403787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741368099509379664269191 16112052149264069496403787)
        ·
          refine ⟨24168078223896104244605681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16112052149264069496403787 24168078223896104244605681)
          ·
            refine ⟨18126058667922078183454261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24168078223896104244605681 18126058667922078183454261)
            ·
              refine ⟨1699318000117694829698837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18126058667922078183454261 1699318000117694829698837)
              ·
                refine ⟨79655531255516945142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1699318000117694829698837 79655531255516945142133)
                ·
                  rfl

theorem cell21_1047118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1047118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047118 prefixEnd_1047118 := by exact prefixLift 1047118
  have htrace : WordTrace (prefixWord ++ tailWord_1047118) baseStart_1047118 baseEnd_1047118 := by
    simpa [prefixWord, tailWord_1047118, baseEnd_1047118] using wordTrace_append hprefix tailTrace_1047118
  have hstable : (prefixWord ++ tailWord_1047118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047118).length < 2 ^ (prefixWord ++ tailWord_1047118).sum := by decide
  have hdescent : baseEnd_1047118 < baseStart_1047118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047163 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_1047163 : Nat := 118140960795 + 1047163 * 2 ^ 59
def prefixEnd_1047163 : Nat := 4983230072969 + 3 ^ 40 * 1047163 * 2
def baseEnd_1047163 : Nat := 238976863379640757176307

theorem tailTrace_1047163 : CollatzResearch.WordTrace tailWord_1047163 prefixEnd_1047163 238976863379640757176307 := by
  unfold tailWord_1047163
  simp only [CollatzResearch.WordTrace]
  refine ⟨38193172305314767047234143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25462114870209844698156095 38193172305314767047234143)
  ·
    refine ⟨57289758457972150570851215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38193172305314767047234143 57289758457972150570851215)
    ·
      refine ⟨85934637686958225856276823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57289758457972150570851215 85934637686958225856276823)
      ·
        refine ⟨128901956530437338784415235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85934637686958225856276823 128901956530437338784415235)
        ·
          refine ⟨193352934795656008176622853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128901956530437338784415235 193352934795656008176622853)
          ·
            refine ⟨36253675274185501533116785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193352934795656008176622853 36253675274185501533116785)
            ·
              refine ⟨27190256455639126149837589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36253675274185501533116785 27190256455639126149837589)
              ·
                refine ⟨1274543271358084038273637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27190256455639126149837589 1274543271358084038273637)
                ·
                  refine ⟨238976863379640757176307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274543271358084038273637 238976863379640757176307)
                  ·
                    rfl

theorem cell21_1047163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_1047163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047163 prefixEnd_1047163 := by exact prefixLift 1047163
  have htrace : WordTrace (prefixWord ++ tailWord_1047163) baseStart_1047163 baseEnd_1047163 := by
    simpa [prefixWord, tailWord_1047163, baseEnd_1047163] using wordTrace_append hprefix tailTrace_1047163
  have hstable : (prefixWord ++ tailWord_1047163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047163).length < 2 ^ (prefixWord ++ tailWord_1047163).sum := by decide
  have hdescent : baseEnd_1047163 < baseStart_1047163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047177 : List Nat := [1, 2, 1, 1, 4, 1, 1, 10]
def baseStart_1047177 : Nat := 118140960795 + 1047177 * 2 ^ 59
def prefixEnd_1047177 : Nat := 4983230072969 + 3 ^ 40 * 1047177 * 2
def baseEnd_1047177 : Nat := 79660019456793281314315

theorem tailTrace_1047177 : CollatzResearch.WordTrace tailWord_1047177 prefixEnd_1047177 79660019456793281314315 := by
  unfold tailWord_1047177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38193682927264047438243785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25462455284842698292162523 38193682927264047438243785)
  ·
    refine ⟨28645262195448035578682839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38193682927264047438243785 28645262195448035578682839)
    ·
      refine ⟨42967893293172053368024259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28645262195448035578682839 42967893293172053368024259)
      ·
        refine ⟨64451839939758080052036389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42967893293172053368024259 64451839939758080052036389)
        ·
          refine ⟨12084719988704640009756823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64451839939758080052036389 12084719988704640009756823)
          ·
            refine ⟨18127079983056960014635235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12084719988704640009756823 18127079983056960014635235)
            ·
              refine ⟨27190619974585440021952853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18127079983056960014635235 27190619974585440021952853)
              ·
                refine ⟨79660019456793281314315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27190619974585440021952853 79660019456793281314315)
                ·
                  rfl

theorem cell21_1047177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_1047177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047177 prefixEnd_1047177 := by exact prefixLift 1047177
  have htrace : WordTrace (prefixWord ++ tailWord_1047177) baseStart_1047177 baseEnd_1047177 := by
    simpa [prefixWord, tailWord_1047177, baseEnd_1047177] using wordTrace_append hprefix tailTrace_1047177
  have hstable : (prefixWord ++ tailWord_1047177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047177).length < 2 ^ (prefixWord ++ tailWord_1047177).sum := by decide
  have hdescent : baseEnd_1047177 < baseStart_1047177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047200 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_1047200 : Nat := 118140960795 + 1047200 * 2 ^ 59
def prefixEnd_1047200 : Nat := 4983230072969 + 3 ^ 40 * 1047200 * 2
def baseEnd_1047200 : Nat := 238985307283736915059565

theorem tailTrace_1047200 : CollatzResearch.WordTrace tailWord_1047200 prefixEnd_1047200 238985307283736915059565 := by
  unfold tailWord_1047200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097260903090361183165527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25463014537453814910887369 19097260903090361183165527)
  ·
    refine ⟨28645891354635541774748291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19097260903090361183165527 28645891354635541774748291)
    ·
      refine ⟨42968837031953312662122437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28645891354635541774748291 42968837031953312662122437)
      ·
        refine ⟨8056656943491246124147957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42968837031953312662122437 8056656943491246124147957)
        ·
          refine ⟨755311588452304324138871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8056656943491246124147957 755311588452304324138871)
          ·
            refine ⟨1132967382678456486208307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755311588452304324138871 1132967382678456486208307)
            ·
              refine ⟨1699451074017684729312461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132967382678456486208307 1699451074017684729312461)
              ·
                refine ⟨637294152756631773492173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699451074017684729312461 637294152756631773492173)
                ·
                  refine ⟨238985307283736915059565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637294152756631773492173 238985307283736915059565)
                  ·
                    rfl

theorem cell21_1047200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_1047200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047200 prefixEnd_1047200 := by exact prefixLift 1047200
  have htrace : WordTrace (prefixWord ++ tailWord_1047200) baseStart_1047200 baseEnd_1047200 := by
    simpa [prefixWord, tailWord_1047200, baseEnd_1047200] using wordTrace_append hprefix tailTrace_1047200
  have hstable : (prefixWord ++ tailWord_1047200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047200).length < 2 ^ (prefixWord ++ tailWord_1047200).sum := by decide
  have hdescent : baseEnd_1047200 < baseStart_1047200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047329 : List Nat := [1, 2, 3, 2, 1, 2, 10]
def baseStart_1047329 : Nat := 118140960795 + 1047329 * 2 ^ 59
def prefixEnd_1047329 : Nat := 4983230072969 + 3 ^ 40 * 1047329 * 2
def baseEnd_1047329 : Nat := 26557194093473484156589

theorem tailTrace_1047329 : CollatzResearch.WordTrace tailWord_1047329 prefixEnd_1047329 26557194093473484156589 := by
  unfold tailWord_1047329
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199226822713377397777041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25466151215142251598518027 38199226822713377397777041)
  ·
    refine ⟨28649420117035033048332781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38199226822713377397777041 28649420117035033048332781)
    ·
      refine ⟨10743532543888137393124793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28649420117035033048332781 10743532543888137393124793)
      ·
        refine ⟨8057649407916103044843595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10743532543888137393124793 8057649407916103044843595)
        ·
          refine ⟨12086474111874154567265393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057649407916103044843595 12086474111874154567265393)
          ·
            refine ⟨9064855583905615925449045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086474111874154567265393 9064855583905615925449045)
            ·
              refine ⟨26557194093473484156589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9064855583905615925449045 26557194093473484156589)
              ·
                rfl

theorem cell21_1047329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 10].length) (baseStart_1047329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047329 prefixEnd_1047329 := by exact prefixLift 1047329
  have htrace : WordTrace (prefixWord ++ tailWord_1047329) baseStart_1047329 baseEnd_1047329 := by
    simpa [prefixWord, tailWord_1047329, baseEnd_1047329] using wordTrace_append hprefix tailTrace_1047329
  have hstable : (prefixWord ++ tailWord_1047329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047329).length < 2 ^ (prefixWord ++ tailWord_1047329).sum := by decide
  have hdescent : baseEnd_1047329 < baseStart_1047329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047332 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1047332 : Nat := 118140960795 + 1047332 * 2 ^ 59
def prefixEnd_1047332 : Nat := 4983230072969 + 3 ^ 40 * 1047332 * 2
def baseEnd_1047332 : Nat := 239015431482134018859295

theorem tailTrace_1047332 : CollatzResearch.WordTrace tailWord_1047332 prefixEnd_1047332 239015431482134018859295 := by
  unfold tailWord_1047332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19099668120851254455068125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25466224161135005940090833 19099668120851254455068125)
  ·
    refine ⟨7162375545319220420650547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19099668120851254455068125 7162375545319220420650547)
    ·
      refine ⟨10743563317978830630975821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162375545319220420650547 10743563317978830630975821)
      ·
        refine ⟨4028836244242061486615933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10743563317978830630975821 4028836244242061486615933)
        ·
          refine ⟨1510813591590773057480975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4028836244242061486615933 1510813591590773057480975)
          ·
            refine ⟨2266220387386159586221463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510813591590773057480975 2266220387386159586221463)
            ·
              refine ⟨3399330581079239379332195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266220387386159586221463 3399330581079239379332195)
              ·
                refine ⟨5098995871618859068998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399330581079239379332195 5098995871618859068998293)
                ·
                  refine ⟨239015431482134018859295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5098995871618859068998293 239015431482134018859295)
                  ·
                    rfl

theorem cell21_1047332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1047332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047332 prefixEnd_1047332 := by exact prefixLift 1047332
  have htrace : WordTrace (prefixWord ++ tailWord_1047332) baseStart_1047332 baseEnd_1047332 := by
    simpa [prefixWord, tailWord_1047332, baseEnd_1047332] using wordTrace_append hprefix tailTrace_1047332
  have hstable : (prefixWord ++ tailWord_1047332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047332).length < 2 ^ (prefixWord ++ tailWord_1047332).sum := by decide
  have hdescent : baseEnd_1047332 < baseStart_1047332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047349 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1047349 : Nat := 118140960795 + 1047349 * 2 ^ 59
def prefixEnd_1047349 : Nat := 4983230072969 + 3 ^ 40 * 1047349 * 2
def baseEnd_1047349 : Nat := 239019311113745767075927

theorem tailTrace_1047349 : CollatzResearch.WordTrace tailWord_1047349 prefixEnd_1047349 239019311113745767075927 := by
  unfold tailWord_1047349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38199956282640920813505101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25466637521760613875670067 38199956282640920813505101)
  ·
    refine ⟨14324983605990345305064413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38199956282640920813505101 14324983605990345305064413)
    ·
      refine ⟨5371868852246379489399155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14324983605990345305064413 5371868852246379489399155)
      ·
        refine ⟨8057803278369569234098733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371868852246379489399155 8057803278369569234098733)
        ·
          refine ⟨3021676229388588462787025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8057803278369569234098733 3021676229388588462787025)
          ·
            refine ⟨2266257172041441347090269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021676229388588462787025 2266257172041441347090269)
            ·
              refine ⟨849846439515540505158851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2266257172041441347090269 849846439515540505158851)
              ·
                refine ⟨1274769659273310757738277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849846439515540505158851 1274769659273310757738277)
                ·
                  refine ⟨239019311113745767075927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274769659273310757738277 239019311113745767075927)
                  ·
                    rfl

theorem cell21_1047349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1047349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047349 prefixEnd_1047349 := by exact prefixLift 1047349
  have htrace : WordTrace (prefixWord ++ tailWord_1047349) baseStart_1047349 baseEnd_1047349 := by
    simpa [prefixWord, tailWord_1047349, baseEnd_1047349] using wordTrace_append hprefix tailTrace_1047349
  have hstable : (prefixWord ++ tailWord_1047349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047349).length < 2 ^ (prefixWord ++ tailWord_1047349).sum := by decide
  have hdescent : baseEnd_1047349 < baseStart_1047349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047391 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_1047391 : Nat := 118140960795 + 1047391 * 2 ^ 59
def prefixEnd_1047391 : Nat := 4983230072969 + 3 ^ 40 * 1047391 * 2
def baseEnd_1047391 : Nat := 239028896085963027375841

theorem tailTrace_1047391 : CollatzResearch.WordTrace tailWord_1047391 prefixEnd_1047391 239028896085963027375841 := by
  unfold tailWord_1047391
  simp only [CollatzResearch.WordTrace]
  refine ⟨38201488148488761986534027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25467658765659174657689351 38201488148488761986534027)
  ·
    refine ⟨57302232222733142979801041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38201488148488761986534027 57302232222733142979801041)
    ·
      refine ⟨42976674167049857234850781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57302232222733142979801041 42976674167049857234850781)
      ·
        refine ⟨16116252812643696463069043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42976674167049857234850781 16116252812643696463069043)
        ·
          refine ⟨24174379218965544694603565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116252812643696463069043 24174379218965544694603565)
          ·
            refine ⟨9065392207112079260476337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24174379218965544694603565 9065392207112079260476337)
            ·
              refine ⟨6799044155334059445357253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065392207112079260476337 6799044155334059445357253)
              ·
                refine ⟨1274820779125136146004485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6799044155334059445357253 1274820779125136146004485)
                ·
                  refine ⟨239028896085963027375841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274820779125136146004485 239028896085963027375841)
                  ·
                    rfl

theorem cell21_1047391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_1047391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047391 prefixEnd_1047391 := by exact prefixLift 1047391
  have htrace : WordTrace (prefixWord ++ tailWord_1047391) baseStart_1047391 baseEnd_1047391 := by
    simpa [prefixWord, tailWord_1047391, baseEnd_1047391] using wordTrace_append hprefix tailTrace_1047391
  have hstable : (prefixWord ++ tailWord_1047391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047391).length < 2 ^ (prefixWord ++ tailWord_1047391).sum := by decide
  have hdescent : baseEnd_1047391 < baseStart_1047391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047408 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_1047408 : Nat := 118140960795 + 1047408 * 2 ^ 59
def prefixEnd_1047408 : Nat := 4983230072969 + 3 ^ 40 * 1047408 * 2
def baseEnd_1047408 : Nat := 239032775717574775592473

theorem tailTrace_1047408 : CollatzResearch.WordTrace tailWord_1047408 prefixEnd_1047408 239032775717574775592473 := by
  unfold tailWord_1047408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19101054094713586944951439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25468072126284782593268585 19101054094713586944951439)
  ·
    refine ⟨28651581142070380417427159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19101054094713586944951439 28651581142070380417427159)
    ·
      refine ⟨42977371713105570626140739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28651581142070380417427159 42977371713105570626140739)
      ·
        refine ⟨64466057569658355939211109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42977371713105570626140739 64466057569658355939211109)
        ·
          refine ⟨12087385794310941738602083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64466057569658355939211109 12087385794310941738602083)
          ·
            refine ⟨18131078691466412607903125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12087385794310941738602083 18131078691466412607903125)
            ·
              refine ⟨849894313662488090995459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18131078691466412607903125 849894313662488090995459)
              ·
                refine ⟨1274841470493732136493189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849894313662488090995459 1274841470493732136493189)
                ·
                  refine ⟨239032775717574775592473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1274841470493732136493189 239032775717574775592473)
                  ·
                    rfl

theorem cell21_1047408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_1047408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047408 prefixEnd_1047408 := by exact prefixLift 1047408
  have htrace : WordTrace (prefixWord ++ tailWord_1047408) baseStart_1047408 baseEnd_1047408 := by
    simpa [prefixWord, tailWord_1047408, baseEnd_1047408] using wordTrace_append hprefix tailTrace_1047408
  have hstable : (prefixWord ++ tailWord_1047408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047408).length < 2 ^ (prefixWord ++ tailWord_1047408).sum := by decide
  have hdescent : baseEnd_1047408 < baseStart_1047408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047512 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_1047512 : Nat := 118140960795 + 1047512 * 2 ^ 59
def prefixEnd_1047512 : Nat := 4983230072969 + 3 ^ 40 * 1047512 * 2
def baseEnd_1047512 : Nat := 239056509934493705858927

theorem tailTrace_1047512 : CollatzResearch.WordTrace tailWord_1047512 prefixEnd_1047512 239056509934493705858927 := by
  unfold tailWord_1047512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102950690525199825844395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25470600920700266434459193 19102950690525199825844395)
  ·
    refine ⟨28654426035787799738766593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19102950690525199825844395 28654426035787799738766593)
    ·
      refine ⟨21490819526840849804074945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28654426035787799738766593 21490819526840849804074945)
      ·
        refine ⟨16118114645130637353056209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21490819526840849804074945 16118114645130637353056209)
        ·
          refine ⟨12088585983847978014792157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118114645130637353056209 12088585983847978014792157)
          ·
            refine ⟨4533219743942991755547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12088585983847978014792157 4533219743942991755547059)
            ·
              refine ⟨6799829615914487633320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533219743942991755547059 6799829615914487633320589)
              ·
                refine ⟨2549936105967932862495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6799829615914487633320589 2549936105967932862495221)
                ·
                  refine ⟨239056509934493705858927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2549936105967932862495221 239056509934493705858927)
                  ·
                    rfl

theorem cell21_1047512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_1047512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047512 prefixEnd_1047512 := by exact prefixLift 1047512
  have htrace : WordTrace (prefixWord ++ tailWord_1047512) baseStart_1047512 baseEnd_1047512 := by
    simpa [prefixWord, tailWord_1047512, baseEnd_1047512] using wordTrace_append hprefix tailTrace_1047512
  have hstable : (prefixWord ++ tailWord_1047512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047512).length < 2 ^ (prefixWord ++ tailWord_1047512).sum := by decide
  have hdescent : baseEnd_1047512 < baseStart_1047512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047605 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 3]
def baseStart_1047605 : Nat := 118140960795 + 1047605 * 2 ^ 59
def prefixEnd_1047605 : Nat := 4983230072969 + 3 ^ 40 * 1047605 * 2
def baseEnd_1047605 : Nat := 239077733801546210808737

theorem tailTrace_1047605 : CollatzResearch.WordTrace tailWord_1047605 prefixEnd_1047605 239077733801546210808737 := by
  unfold tailWord_1047605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209293369713476534824269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25472862246475651023216179 38209293369713476534824269)
  ·
    refine ⟨14328485013642553700559101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38209293369713476534824269 14328485013642553700559101)
    ·
      refine ⟨5373181880115957637709663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14328485013642553700559101 5373181880115957637709663)
      ·
        refine ⟨8059772820173936456564495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373181880115957637709663 8059772820173936456564495)
        ·
          refine ⟨12089659230260904684846743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8059772820173936456564495 12089659230260904684846743)
          ·
            refine ⟨18134488845391357027270115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089659230260904684846743 18134488845391357027270115)
            ·
              refine ⟨27201733268087035540905173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18134488845391357027270115 27201733268087035540905173)
              ·
                refine ⟨637540623470789895489965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27201733268087035540905173 637540623470789895489965)
                ·
                  refine ⟨239077733801546210808737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637540623470789895489965 239077733801546210808737)
                  ·
                    rfl

theorem cell21_1047605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_1047605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047605 prefixEnd_1047605 := by exact prefixLift 1047605
  have htrace : WordTrace (prefixWord ++ tailWord_1047605) baseStart_1047605 baseEnd_1047605 := by
    simpa [prefixWord, tailWord_1047605, baseEnd_1047605] using wordTrace_append hprefix tailTrace_1047605
  have hstable : (prefixWord ++ tailWord_1047605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047605).length < 2 ^ (prefixWord ++ tailWord_1047605).sum := by decide
  have hdescent : baseEnd_1047605 < baseStart_1047605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047619 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_1047619 : Nat := 118140960795 + 1047619 * 2 ^ 59
def prefixEnd_1047619 : Nat := 4983230072969 + 3 ^ 40 * 1047619 * 2
def baseEnd_1047619 : Nat := 239080928792285297575375

theorem tailTrace_1047619 : CollatzResearch.WordTrace tailWord_1047619 prefixEnd_1047619 239080928792285297575375 := by
  unfold tailWord_1047619
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209803991662756925833911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25473202661108504617222607 38209803991662756925833911)
  ·
    refine ⟨57314705987494135388750867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38209803991662756925833911 57314705987494135388750867)
    ·
      refine ⟨85972058981241203083126301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57314705987494135388750867 85972058981241203083126301)
      ·
        refine ⟨32239522117965451156172363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85972058981241203083126301 32239522117965451156172363)
        ·
          refine ⟨48359283176948176734258545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32239522117965451156172363 48359283176948176734258545)
          ·
            refine ⟨36269462382711132550693909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48359283176948176734258545 36269462382711132550693909)
            ·
              refine ⟨1700131049189584338313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36269462382711132550693909 1700131049189584338313777)
              ·
                refine ⟨1275098286892188253735333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700131049189584338313777 1275098286892188253735333)
                ·
                  refine ⟨239080928792285297575375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275098286892188253735333 239080928792285297575375)
                  ·
                    rfl

theorem cell21_1047619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_1047619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047619 prefixEnd_1047619 := by exact prefixLift 1047619
  have htrace : WordTrace (prefixWord ++ tailWord_1047619) baseStart_1047619 baseEnd_1047619 := by
    simpa [prefixWord, tailWord_1047619, baseEnd_1047619] using wordTrace_append hprefix tailTrace_1047619
  have hstable : (prefixWord ++ tailWord_1047619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047619).length < 2 ^ (prefixWord ++ tailWord_1047619).sum := by decide
  have hdescent : baseEnd_1047619 < baseStart_1047619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047633 : List Nat := [1, 2, 2, 1, 3, 1, 5, 6]
def baseStart_1047633 : Nat := 118140960795 + 1047633 * 2 ^ 59
def prefixEnd_1047633 : Nat := 4983230072969 + 3 ^ 40 * 1047633 * 2
def baseEnd_1047633 : Nat := 79694707927674794780671

theorem tailTrace_1047633 : CollatzResearch.WordTrace tailWord_1047633 prefixEnd_1047633 79694707927674794780671 := by
  unfold tailWord_1047633
  simp only [CollatzResearch.WordTrace]
  refine ⟨38210314613612037316843553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25473543075741358211229035 38210314613612037316843553)
  ·
    refine ⟨28657735960209027987632665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38210314613612037316843553 28657735960209027987632665)
    ·
      refine ⟨21493301970156770990724499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28657735960209027987632665 21493301970156770990724499)
      ·
        refine ⟨32239952955235156486086749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493301970156770990724499 32239952955235156486086749)
        ·
          refine ⟨12089982358213183682282531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32239952955235156486086749 12089982358213183682282531)
          ·
            refine ⟨18134973537319775523423797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089982358213183682282531 18134973537319775523423797)
            ·
              refine ⟨1700153769123728955320981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18134973537319775523423797 1700153769123728955320981)
              ·
                refine ⟨79694707927674794780671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1700153769123728955320981 79694707927674794780671)
                ·
                  rfl

theorem cell21_1047633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_1047633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047633 prefixEnd_1047633 := by exact prefixLift 1047633
  have htrace : WordTrace (prefixWord ++ tailWord_1047633) baseStart_1047633 baseEnd_1047633 := by
    simpa [prefixWord, tailWord_1047633, baseEnd_1047633] using wordTrace_append hprefix tailTrace_1047633
  have hstable : (prefixWord ++ tailWord_1047633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047633).length < 2 ^ (prefixWord ++ tailWord_1047633).sum := by decide
  have hdescent : baseEnd_1047633 < baseStart_1047633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047681 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_1047681 : Nat := 118140960795 + 1047681 * 2 ^ 59
def prefixEnd_1047681 : Nat := 4983230072969 + 3 ^ 40 * 1047681 * 2
def baseEnd_1047681 : Nat := 239095078036986967541915

theorem tailTrace_1047681 : CollatzResearch.WordTrace tailWord_1047681 prefixEnd_1047681 239095078036986967541915 := by
  unfold tailWord_1047681
  simp only [CollatzResearch.WordTrace]
  refine ⟨38212065317438141514590897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25474710211625427676393931 38212065317438141514590897)
  ·
    refine ⟨28659048988078606135943173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38212065317438141514590897 28659048988078606135943173)
    ·
      refine ⟨5373571685264738650489345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28659048988078606135943173 5373571685264738650489345)
      ·
        refine ⟨4030178763948553987867009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373571685264738650489345 4030178763948553987867009)
        ·
          refine ⟨3022634072961415490900257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030178763948553987867009 3022634072961415490900257)
          ·
            refine ⟨2266975554721061618175193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3022634072961415490900257 2266975554721061618175193)
            ·
              refine ⟨1700231666040796213631395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266975554721061618175193 1700231666040796213631395)
              ·
                refine ⟨2550347499061194320447093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700231666040796213631395 2550347499061194320447093)
                ·
                  refine ⟨239095078036986967541915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2550347499061194320447093 239095078036986967541915)
                  ·
                    rfl

theorem cell21_1047681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_1047681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047681 prefixEnd_1047681 := by exact prefixLift 1047681
  have htrace : WordTrace (prefixWord ++ tailWord_1047681) baseStart_1047681 baseEnd_1047681 := by
    simpa [prefixWord, tailWord_1047681, baseEnd_1047681] using wordTrace_append hprefix tailTrace_1047681
  have hstable : (prefixWord ++ tailWord_1047681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047681).length < 2 ^ (prefixWord ++ tailWord_1047681).sum := by decide
  have hdescent : baseEnd_1047681 < baseStart_1047681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047709 : List Nat := [1, 4, 2, 1, 1, 2, 3, 7]
def baseStart_1047709 : Nat := 118140960795 + 1047709 * 2 ^ 59
def prefixEnd_1047709 : Nat := 4983230072969 + 3 ^ 40 * 1047709 * 2
def baseEnd_1047709 : Nat := 79700489339488380358397

theorem tailTrace_1047709 : CollatzResearch.WordTrace tailWord_1047709 prefixEnd_1047709 79700489339488380358397 := by
  unfold tailWord_1047709
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213086561336702296610181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25475391040891134864406787 38213086561336702296610181)
  ·
    refine ⟨7164953730250631680614409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38213086561336702296610181 7164953730250631680614409)
    ·
      refine ⟨5373715297687973760460807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7164953730250631680614409 5373715297687973760460807)
      ·
        refine ⟨8060572946531960640691211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373715297687973760460807 8060572946531960640691211)
        ·
          refine ⟨12090859419797940961036817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060572946531960640691211 12090859419797940961036817)
          ·
            refine ⟨9068144564848455720777613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090859419797940961036817 9068144564848455720777613)
            ·
              refine ⟨3400554211818170895291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9068144564848455720777613 3400554211818170895291605)
              ·
                refine ⟨79700489339488380358397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3400554211818170895291605 79700489339488380358397)
                ·
                  rfl

theorem cell21_1047709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_1047709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047709 prefixEnd_1047709 := by exact prefixLift 1047709
  have htrace : WordTrace (prefixWord ++ tailWord_1047709) baseStart_1047709 baseEnd_1047709 := by
    simpa [prefixWord, tailWord_1047709, baseEnd_1047709] using wordTrace_append hprefix tailTrace_1047709
  have hstable : (prefixWord ++ tailWord_1047709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047709).length < 2 ^ (prefixWord ++ tailWord_1047709).sum := by decide
  have hdescent : baseEnd_1047709 < baseStart_1047709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047746 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1047746 : Nat := 118140960795 + 1047746 * 2 ^ 59
def prefixEnd_1047746 : Nat := 4983230072969 + 3 ^ 40 * 1047746 * 2
def baseEnd_1047746 : Nat := 239109911922561298958449

theorem tailTrace_1047746 : CollatzResearch.WordTrace tailWord_1047746 prefixEnd_1047746 239109911922561298958449 := by
  unfold tailWord_1047746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553609015550664403926773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25476290708135105077138061 9553609015550664403926773)
  ·
    refine ⟨895650845207874787868135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9553609015550664403926773 895650845207874787868135)
    ·
      refine ⟨1343476267811812181802203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895650845207874787868135 1343476267811812181802203)
      ·
        refine ⟨2015214401717718272703305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343476267811812181802203 2015214401717718272703305)
        ·
          refine ⟨1511410801288288704527479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015214401717718272703305 1511410801288288704527479)
          ·
            refine ⟨2267116201932433056791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511410801288288704527479 2267116201932433056791219)
            ·
              refine ⟨3400674302898649585186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267116201932433056791219 3400674302898649585186829)
              ·
                refine ⟨1275252863586993594445061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3400674302898649585186829 1275252863586993594445061)
                ·
                  refine ⟨239109911922561298958449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1275252863586993594445061 239109911922561298958449)
                  ·
                    rfl

theorem cell21_1047746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1047746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047746 prefixEnd_1047746 := by exact prefixLift 1047746
  have htrace : WordTrace (prefixWord ++ tailWord_1047746) baseStart_1047746 baseEnd_1047746 := by
    simpa [prefixWord, tailWord_1047746, baseEnd_1047746] using wordTrace_append hprefix tailTrace_1047746
  have hstable : (prefixWord ++ tailWord_1047746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047746).length < 2 ^ (prefixWord ++ tailWord_1047746).sum := by decide
  have hdescent : baseEnd_1047746 < baseStart_1047746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047791 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 3]
def baseStart_1047791 : Nat := 118140960795 + 1047791 * 2 ^ 59
def prefixEnd_1047791 : Nat := 4983230072969 + 3 ^ 40 * 1047791 * 2
def baseEnd_1047791 : Nat := 239120181535651220708357

theorem tailTrace_1047791 : CollatzResearch.WordTrace tailWord_1047791 prefixEnd_1047791 239120181535651220708357 := by
  unfold tailWord_1047791
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216077347039630301095227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25477384898026420200730151 38216077347039630301095227)
  ·
    refine ⟨57324116020559445451642841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38216077347039630301095227 57324116020559445451642841)
    ·
      refine ⟨42993087015419584088732131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57324116020559445451642841 42993087015419584088732131)
      ·
        refine ⟨64489630523129376133098197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42993087015419584088732131 64489630523129376133098197)
        ·
          refine ⟨1511475715385844753119489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64489630523129376133098197 1511475715385844753119489)
          ·
            refine ⟨1133606786539383564839617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511475715385844753119489 1133606786539383564839617)
            ·
              refine ⟨850205089904537673629713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133606786539383564839617 850205089904537673629713)
              ·
                refine ⟨637653817428403255222285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850205089904537673629713 637653817428403255222285)
                ·
                  refine ⟨239120181535651220708357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637653817428403255222285 239120181535651220708357)
                  ·
                    rfl

theorem cell21_1047791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 3].length) (baseStart_1047791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047791 prefixEnd_1047791 := by exact prefixLift 1047791
  have htrace : WordTrace (prefixWord ++ tailWord_1047791) baseStart_1047791 baseEnd_1047791 := by
    simpa [prefixWord, tailWord_1047791, baseEnd_1047791] using wordTrace_append hprefix tailTrace_1047791
  have hstable : (prefixWord ++ tailWord_1047791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047791).length < 2 ^ (prefixWord ++ tailWord_1047791).sum := by decide
  have hdescent : baseEnd_1047791 < baseStart_1047791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047850 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_1047850 : Nat := 118140960795 + 1047850 * 2 ^ 59
def prefixEnd_1047850 : Nat := 4983230072969 + 3 ^ 40 * 1047850 * 2
def baseEnd_1047850 : Nat := 239133646139480229224903

theorem tailTrace_1047850 : CollatzResearch.WordTrace tailWord_1047850 prefixEnd_1047850 239133646139480229224903 := by
  unfold tailWord_1047850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554557313456470844373251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25478819502550588918328669 9554557313456470844373251)
  ·
    refine ⟨14331835970184706266559877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554557313456470844373251 14331835970184706266559877)
    ·
      refine ⟨2687219244409632424979977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14331835970184706266559877 2687219244409632424979977)
      ·
        refine ⟨2015414433307224318734983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2687219244409632424979977 2015414433307224318734983)
        ·
          refine ⟨3023121649960836478102475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015414433307224318734983 3023121649960836478102475)
          ·
            refine ⟨4534682474941254717153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023121649960836478102475 4534682474941254717153713)
            ·
              refine ⟨3401011856205941037865285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4534682474941254717153713 3401011856205941037865285)
              ·
                refine ⟨637689723038613944599741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3401011856205941037865285 637689723038613944599741)
                ·
                  refine ⟨239133646139480229224903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637689723038613944599741 239133646139480229224903)
                  ·
                    rfl

theorem cell21_1047850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_1047850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047850 prefixEnd_1047850 := by exact prefixLift 1047850
  have htrace : WordTrace (prefixWord ++ tailWord_1047850) baseStart_1047850 baseEnd_1047850 := by
    simpa [prefixWord, tailWord_1047850, baseEnd_1047850] using wordTrace_append hprefix tailTrace_1047850
  have hstable : (prefixWord ++ tailWord_1047850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047850).length < 2 ^ (prefixWord ++ tailWord_1047850).sum := by decide
  have hdescent : baseEnd_1047850 < baseStart_1047850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047901 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1047901 : Nat := 118140960795 + 1047901 * 2 ^ 59
def prefixEnd_1047901 : Nat := 4983230072969 + 3 ^ 40 * 1047901 * 2
def baseEnd_1047901 : Nat := 239145285034315473874799

theorem tailTrace_1047901 : CollatzResearch.WordTrace tailWord_1047901 prefixEnd_1047901 239145285034315473874799 := by
  unfold tailWord_1047901
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220089376641119087599557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25480059584427412725066371 38220089376641119087599557)
  ·
    refine ⟨7166266758120209828924917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38220089376641119087599557 7166266758120209828924917)
    ·
      refine ⟨671837508573769671461711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7166266758120209828924917 671837508573769671461711)
      ·
        refine ⟨1007756262860654507192567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671837508573769671461711 1007756262860654507192567)
        ·
          refine ⟨1511634394290981760788851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007756262860654507192567 1511634394290981760788851)
          ·
            refine ⟨2267451591436472641183277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511634394290981760788851 2267451591436472641183277)
            ·
              refine ⟨850294346788677240443729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267451591436472641183277 850294346788677240443729)
              ·
                refine ⟨637720760091507930332797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850294346788677240443729 637720760091507930332797)
                ·
                  refine ⟨239145285034315473874799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637720760091507930332797 239145285034315473874799)
                  ·
                    rfl

theorem cell21_1047901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1047901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047901 prefixEnd_1047901 := by exact prefixLift 1047901
  have htrace : WordTrace (prefixWord ++ tailWord_1047901) baseStart_1047901 baseEnd_1047901 := by
    simpa [prefixWord, tailWord_1047901, baseEnd_1047901] using wordTrace_append hprefix tailTrace_1047901
  have hstable : (prefixWord ++ tailWord_1047901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047901).length < 2 ^ (prefixWord ++ tailWord_1047901).sum := by decide
  have hdescent : baseEnd_1047901 < baseStart_1047901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047954 : List Nat := [3, 2, 3, 3, 1, 9]
def baseStart_1047954 : Nat := 118140960795 + 1047954 * 2 ^ 59
def prefixEnd_1047954 : Nat := 4983230072969 + 3 ^ 40 * 1047954 * 2
def baseEnd_1047954 : Nat := 8857680753940709610791

theorem tailTrace_1047954 : CollatzResearch.WordTrace tailWord_1047954 prefixEnd_1047954 8857680753940709610791 := by
  unfold tailWord_1047954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555505611362277284819729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25481348296966072759519277 9555505611362277284819729)
  ·
    refine ⟨7166629208521707963614797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9555505611362277284819729 7166629208521707963614797)
    ·
      refine ⟨2687485953195640486355549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7166629208521707963614797 2687485953195640486355549)
      ·
        refine ⟨1007807232448365182383331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2687485953195640486355549 1007807232448365182383331)
        ·
          refine ⟨1511710848672547773574997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007807232448365182383331 1511710848672547773574997)
          ·
            refine ⟨8857680753940709610791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1511710848672547773574997 8857680753940709610791)
            ·
              rfl

theorem cell21_1047954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 9].length) (baseStart_1047954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047954 prefixEnd_1047954 := by exact prefixLift 1047954
  have htrace : WordTrace (prefixWord ++ tailWord_1047954) baseStart_1047954 baseEnd_1047954 := by
    simpa [prefixWord, tailWord_1047954, baseEnd_1047954] using wordTrace_append hprefix tailTrace_1047954
  have hstable : (prefixWord ++ tailWord_1047954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047954).length < 2 ^ (prefixWord ++ tailWord_1047954).sum := by decide
  have hdescent : baseEnd_1047954 < baseStart_1047954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047960 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_1047960 : Nat := 118140960795 + 1047960 * 2 ^ 59
def prefixEnd_1047960 : Nat := 4983230072969 + 3 ^ 40 * 1047960 * 2
def baseEnd_1047960 : Nat := 239158749638144482391345

theorem tailTrace_1047960 : CollatzResearch.WordTrace tailWord_1047960 prefixEnd_1047960 239158749638144482391345 := by
  unfold tailWord_1047960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111120641713686081998667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25481494188951581442664889 19111120641713686081998667)
  ·
    refine ⟨28666680962570529122998001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19111120641713686081998667 28666680962570529122998001)
    ·
      refine ⟨21500010721927896842248501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28666680962570529122998001 21500010721927896842248501)
      ·
        refine ⟨2015626005180740328960797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21500010721927896842248501 2015626005180740328960797)
        ·
          refine ⟨755859751942777623360299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2015626005180740328960797 755859751942777623360299)
          ·
            refine ⟨1133789627914166435040449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755859751942777623360299 1133789627914166435040449)
            ·
              refine ⟨850342220935624826280337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133789627914166435040449 850342220935624826280337)
              ·
                refine ⟨637756665701718619710253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850342220935624826280337 637756665701718619710253)
                ·
                  refine ⟨239158749638144482391345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637756665701718619710253 239158749638144482391345)
                  ·
                    rfl

theorem cell21_1047960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_1047960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1047960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1047960 prefixEnd_1047960 := by exact prefixLift 1047960
  have htrace : WordTrace (prefixWord ++ tailWord_1047960) baseStart_1047960 baseEnd_1047960 := by
    simpa [prefixWord, tailWord_1047960, baseEnd_1047960] using wordTrace_append hprefix tailTrace_1047960
  have hstable : (prefixWord ++ tailWord_1047960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047960).length < 2 ^ (prefixWord ++ tailWord_1047960).sum := by decide
  have hdescent : baseEnd_1047960 < baseStart_1047960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048061 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1048061 : Nat := 118140960795 + 1048061 * 2 ^ 59
def prefixEnd_1048061 : Nat := 4983230072969 + 3 ^ 40 * 1048061 * 2
def baseEnd_1048061 : Nat := 239181799214190751207805

theorem tailTrace_1048061 : CollatzResearch.WordTrace tailWord_1048061 prefixEnd_1048061 239181799214190751207805 := by
  unfold tailWord_1048061
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225925056061466413424037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483950037374310942282691 38225925056061466413424037)
  ·
    refine ⟨7167360948011524952517007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38225925056061466413424037 7167360948011524952517007)
    ·
      refine ⟨10751041422017287428775511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167360948011524952517007 10751041422017287428775511)
      ·
        refine ⟨16126562133025931143163267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751041422017287428775511 16126562133025931143163267)
        ·
          refine ⟨24189843199538896714744901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126562133025931143163267 24189843199538896714744901)
          ·
            refine ⟨4535595599913543134014669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24189843199538896714744901 4535595599913543134014669)
            ·
              refine ⟨1700848349967578675255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4535595599913543134014669 1700848349967578675255501)
              ·
                refine ⟨637818131237842003220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1700848349967578675255501 637818131237842003220813)
                ·
                  refine ⟨239181799214190751207805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637818131237842003220813 239181799214190751207805)
                  ·
                    rfl

theorem cell21_1048061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1048061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048061 prefixEnd_1048061 := by exact prefixLift 1048061
  have htrace : WordTrace (prefixWord ++ tailWord_1048061) baseStart_1048061 baseEnd_1048061 := by
    simpa [prefixWord, tailWord_1048061, baseEnd_1048061] using wordTrace_append hprefix tailTrace_1048061
  have hstable : (prefixWord ++ tailWord_1048061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048061).length < 2 ^ (prefixWord ++ tailWord_1048061).sum := by decide
  have hdescent : baseEnd_1048061 < baseStart_1048061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048072 : List Nat := [2, 1, 3, 2, 1, 1, 11]
def baseStart_1048072 : Nat := 118140960795 + 1048072 * 2 ^ 59
def prefixEnd_1048072 : Nat := 4983230072969 + 3 ^ 40 * 1048072 * 2
def baseEnd_1048072 : Nat := 26576034396006352947161

theorem tailTrace_1048072 : CollatzResearch.WordTrace tailWord_1048072 prefixEnd_1048072 26576034396006352947161 := by
  unfold tailWord_1048072
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113163129510807646037235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25484217506014410194716313 19113163129510807646037235)
  ·
    refine ⟨28669744694266211469055853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19113163129510807646037235 28669744694266211469055853)
    ·
      refine ⟨10751154260349829300895945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28669744694266211469055853 10751154260349829300895945)
      ·
        refine ⟨8063365695262371975671959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751154260349829300895945 8063365695262371975671959)
        ·
          refine ⟨12095048542893557963507939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063365695262371975671959 12095048542893557963507939)
          ·
            refine ⟨18142572814340336945261909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095048542893557963507939 18142572814340336945261909)
            ·
              refine ⟨26576034396006352947161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18142572814340336945261909 26576034396006352947161)
              ·
                rfl

theorem cell21_1048072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 11].length) (baseStart_1048072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048072 prefixEnd_1048072 := by exact prefixLift 1048072
  have htrace : WordTrace (prefixWord ++ tailWord_1048072) baseStart_1048072 baseEnd_1048072 := by
    simpa [prefixWord, tailWord_1048072, baseEnd_1048072] using wordTrace_append hprefix tailTrace_1048072
  have hstable : (prefixWord ++ tailWord_1048072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048072).length < 2 ^ (prefixWord ++ tailWord_1048072).sum := by decide
  have hdescent : baseEnd_1048072 < baseStart_1048072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048078 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_1048078 : Nat := 118140960795 + 1048078 * 2 ^ 59
def prefixEnd_1048078 : Nat := 4983230072969 + 3 ^ 40 * 1048078 * 2
def baseEnd_1048078 : Nat := 239185678845802499424437

theorem tailTrace_1048078 : CollatzResearch.WordTrace tailWord_1048078 prefixEnd_1048078 239185678845802499424437 := by
  unfold tailWord_1048078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778318137124984789599111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25484363397999918877861925 4778318137124984789599111)
  ·
    refine ⟨7167477205687477184398667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778318137124984789599111 7167477205687477184398667)
    ·
      refine ⟨10751215808531215776598001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167477205687477184398667 10751215808531215776598001)
      ·
        refine ⟨8063411856398411832448501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751215808531215776598001 8063411856398411832448501)
        ·
          refine ⟨755944861537351109292047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8063411856398411832448501 755944861537351109292047)
          ·
            refine ⟨1133917292306026663938071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755944861537351109292047 1133917292306026663938071)
            ·
              refine ⟨1700875938459039995907107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133917292306026663938071 1700875938459039995907107)
              ·
                refine ⟨2551313907688559993860661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700875938459039995907107 2551313907688559993860661)
                ·
                  refine ⟨239185678845802499424437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2551313907688559993860661 239185678845802499424437)
                  ·
                    rfl

theorem cell21_1048078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_1048078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048078 prefixEnd_1048078 := by exact prefixLift 1048078
  have htrace : WordTrace (prefixWord ++ tailWord_1048078) baseStart_1048078 baseEnd_1048078 := by
    simpa [prefixWord, tailWord_1048078, baseEnd_1048078] using wordTrace_append hprefix tailTrace_1048078
  have hstable : (prefixWord ++ tailWord_1048078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048078).length < 2 ^ (prefixWord ++ tailWord_1048078).sum := by decide
  have hdescent : baseEnd_1048078 < baseStart_1048078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048326 : List Nat := [6, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1048326 : Nat := 118140960795 + 1048326 * 2 ^ 59
def prefixEnd_1048326 : Nat := 4983230072969 + 3 ^ 40 * 1048326 * 2
def baseEnd_1048326 : Nat := 79747425274869726430199

theorem tailTrace_1048326 : CollatzResearch.WordTrace tailWord_1048326 prefixEnd_1048326 79747425274869726430199 := by
  unfold tailWord_1048326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194862200003169270994401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25490393600067611114547221 1194862200003169270994401)
  ·
    refine ⟨896146650002376953245801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1194862200003169270994401 896146650002376953245801)
    ·
      refine ⟨672109987501782714934351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 896146650002376953245801 672109987501782714934351)
      ·
        refine ⟨1008164981252674072401527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672109987501782714934351 1008164981252674072401527)
        ·
          refine ⟨1512247471879011108602291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008164981252674072401527 1512247471879011108602291)
          ·
            refine ⟨2268371207818516662903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512247471879011108602291 2268371207818516662903437)
            ·
              refine ⟨850639202931943748588789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2268371207818516662903437 850639202931943748588789)
              ·
                refine ⟨79747425274869726430199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 850639202931943748588789 79747425274869726430199)
                ·
                  rfl

theorem cell21_1048326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1048326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048326 prefixEnd_1048326 := by exact prefixLift 1048326
  have htrace : WordTrace (prefixWord ++ tailWord_1048326) baseStart_1048326 baseEnd_1048326 := by
    simpa [prefixWord, tailWord_1048326, baseEnd_1048326] using wordTrace_append hprefix tailTrace_1048326
  have hstable : (prefixWord ++ tailWord_1048326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048326).length < 2 ^ (prefixWord ++ tailWord_1048326).sum := by decide
  have hdescent : baseEnd_1048326 < baseStart_1048326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048340 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1048340 : Nat := 118140960795 + 1048340 * 2 ^ 59
def prefixEnd_1048340 : Nat := 4983230072969 + 3 ^ 40 * 1048340 * 2
def baseEnd_1048340 : Nat := 239245470815348266057235

theorem tailTrace_1048340 : CollatzResearch.WordTrace tailWord_1048340 prefixEnd_1048340 239245470815348266057235 := by
  unfold tailWord_1048340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118050511025348531415237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25490734014700464708553649 19118050511025348531415237)
  ·
    refine ⟨3584634470817252849640357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19118050511025348531415237 3584634470817252849640357)
    ·
      refine ⟨672118963278234909307567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3584634470817252849640357 672118963278234909307567)
      ·
        refine ⟨1008178444917352363961351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672118963278234909307567 1008178444917352363961351)
        ·
          refine ⟨1512267667376028545942027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008178444917352363961351 1512267667376028545942027)
          ·
            refine ⟨2268401501064042818913041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512267667376028545942027 2268401501064042818913041)
            ·
              refine ⟨1701301125798032114184781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268401501064042818913041 1701301125798032114184781)
              ·
                refine ⟨637987922174262042819293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701301125798032114184781 637987922174262042819293)
                ·
                  refine ⟨239245470815348266057235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 637987922174262042819293 239245470815348266057235)
                  ·
                    rfl

theorem cell21_1048340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1048340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048340 prefixEnd_1048340 := by exact prefixLift 1048340
  have htrace : WordTrace (prefixWord ++ tailWord_1048340) baseStart_1048340 baseEnd_1048340 := by
    simpa [prefixWord, tailWord_1048340, baseEnd_1048340] using wordTrace_append hprefix tailTrace_1048340
  have hstable : (prefixWord ++ tailWord_1048340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048340).length < 2 ^ (prefixWord ++ tailWord_1048340).sum := by decide
  have hdescent : baseEnd_1048340 < baseStart_1048340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048452 : List Nat := [2, 3, 2, 1, 1, 1, 4, 7]
def baseStart_1048452 : Nat := 118140960795 + 1048452 * 2 ^ 59
def prefixEnd_1048452 : Nat := 4983230072969 + 3 ^ 40 * 1048452 * 2
def baseEnd_1048452 : Nat := 79757010247086986730113

theorem tailTrace_1048452 : CollatzResearch.WordTrace tailWord_1048452 prefixEnd_1048452 79757010247086986730113 := by
  unfold tailWord_1048452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120092998822470095453805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25493457331763293460605073 19120092998822470095453805)
  ·
    refine ⟨7170034874558426285795177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19120092998822470095453805 7170034874558426285795177)
    ·
      refine ⟨5377526155918819714346383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7170034874558426285795177 5377526155918819714346383)
      ·
        refine ⟨8066289233878229571519575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377526155918819714346383 8066289233878229571519575)
        ·
          refine ⟨12099433850817344357279363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066289233878229571519575 12099433850817344357279363)
          ·
            refine ⟨18149150776226016535919045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099433850817344357279363 18149150776226016535919045)
            ·
              refine ⟨3402965770542378100484821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18149150776226016535919045 3402965770542378100484821)
              ·
                refine ⟨79757010247086986730113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3402965770542378100484821 79757010247086986730113)
                ·
                  rfl

theorem cell21_1048452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_1048452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048452 prefixEnd_1048452 := by exact prefixLift 1048452
  have htrace : WordTrace (prefixWord ++ tailWord_1048452) baseStart_1048452 baseEnd_1048452 := by
    simpa [prefixWord, tailWord_1048452, baseEnd_1048452] using wordTrace_append hprefix tailTrace_1048452
  have hstable : (prefixWord ++ tailWord_1048452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048452).length < 2 ^ (prefixWord ++ tailWord_1048452).sum := by decide
  have hdescent : baseEnd_1048452 < baseStart_1048452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048472 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_1048472 : Nat := 118140960795 + 1048472 * 2 ^ 59
def prefixEnd_1048472 : Nat := 4983230072969 + 3 ^ 40 * 1048472 * 2
def baseEnd_1048472 : Nat := 239275595013745369856965

theorem tailTrace_1048472 : CollatzResearch.WordTrace tailWord_1048472 prefixEnd_1048472 239275595013745369856965 := by
  unfold tailWord_1048472
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120457728786241803317835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25493943638381655737757113 19120457728786241803317835)
  ·
    refine ⟨28680686593179362704976753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19120457728786241803317835 28680686593179362704976753)
    ·
      refine ⟨21510514944884522028732565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28680686593179362704976753 21510514944884522028732565)
      ·
        refine ⟨1008305388041461970096839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21510514944884522028732565 1008305388041461970096839)
        ·
          refine ⟨1512458082062192955145259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008305388041461970096839 1512458082062192955145259)
          ·
            refine ⟨2268687123093289432717889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512458082062192955145259 2268687123093289432717889)
            ·
              refine ⟨1701515342319967074538417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268687123093289432717889 1701515342319967074538417)
              ·
                refine ⟨1276136506739975305903813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701515342319967074538417 1276136506739975305903813)
                ·
                  refine ⟨239275595013745369856965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276136506739975305903813 239275595013745369856965)
                  ·
                    rfl

theorem cell21_1048472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_1048472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048472 prefixEnd_1048472 := by exact prefixLift 1048472
  have htrace : WordTrace (prefixWord ++ tailWord_1048472) baseStart_1048472 baseEnd_1048472 := by
    simpa [prefixWord, tailWord_1048472, baseEnd_1048472] using wordTrace_append hprefix tailTrace_1048472
  have hstable : (prefixWord ++ tailWord_1048472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048472).length < 2 ^ (prefixWord ++ tailWord_1048472).sum := by decide
  have hdescent : baseEnd_1048472 < baseStart_1048472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048573 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1048573 : Nat := 118140960795 + 1048573 * 2 ^ 59
def prefixEnd_1048573 : Nat := 4983230072969 + 3 ^ 40 * 1048573 * 2
def baseEnd_1048573 : Nat := 239298644589791638673425

theorem tailTrace_1048573 : CollatzResearch.WordTrace tailWord_1048573 prefixEnd_1048573 239298644589791638673425 := by
  unfold tailWord_1048573
  simp only [CollatzResearch.WordTrace]
  refine ⟨38244599230206577856062373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25496399486804385237374915 38244599230206577856062373)
  ·
    refine ⟨7170862355663733348011695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38244599230206577856062373 7170862355663733348011695)
    ·
      refine ⟨10756293533495600022017543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170862355663733348011695 10756293533495600022017543)
      ·
        refine ⟨16134440300243400033026315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10756293533495600022017543 16134440300243400033026315)
        ·
          refine ⟨24201660450365100049539473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16134440300243400033026315 24201660450365100049539473)
          ·
            refine ⟨18151245337773825037154605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24201660450365100049539473 18151245337773825037154605)
            ·
              refine ⟨6806717001665184388932977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18151245337773825037154605 6806717001665184388932977)
              ·
                refine ⟨5105037751248888291699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806717001665184388932977 5105037751248888291699733)
                ·
                  refine ⟨239298644589791638673425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5105037751248888291699733 239298644589791638673425)
                  ·
                    rfl

theorem cell21_1048573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1048573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048573 prefixEnd_1048573 := by exact prefixLift 1048573
  have htrace : WordTrace (prefixWord ++ tailWord_1048573) baseStart_1048573 baseEnd_1048573 := by
    simpa [prefixWord, tailWord_1048573, baseEnd_1048573] using wordTrace_append hprefix tailTrace_1048573
  have hstable : (prefixWord ++ tailWord_1048573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048573).length < 2 ^ (prefixWord ++ tailWord_1048573).sum := by decide
  have hdescent : baseEnd_1048573 < baseStart_1048573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048590 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1048590 : Nat := 118140960795 + 1048590 * 2 ^ 59
def prefixEnd_1048590 : Nat := 4983230072969 + 3 ^ 40 * 1048590 * 2
def baseEnd_1048590 : Nat := 239302524221403386890057

theorem tailTrace_1048590 : CollatzResearch.WordTrace tailWord_1048590 prefixEnd_1048590 239302524221403386890057 := by
  unfold tailWord_1048590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780652408893123719928903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25496812847429993172954149 4780652408893123719928903)
  ·
    refine ⟨7170978613339685579893355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4780652408893123719928903 7170978613339685579893355)
    ·
      refine ⟨10756467920009528369840033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170978613339685579893355 10756467920009528369840033)
      ·
        refine ⟨8067350940007146277380025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10756467920009528369840033 8067350940007146277380025)
        ·
          refine ⟨6050513205005359708035019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067350940007146277380025 6050513205005359708035019)
          ·
            refine ⟨9075769807508039562052529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050513205005359708035019 9075769807508039562052529)
            ·
              refine ⟨6806827355631029671539397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075769807508039562052529 6806827355631029671539397)
              ·
                refine ⟨1276280129180818063413637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6806827355631029671539397 1276280129180818063413637)
                ·
                  refine ⟨239302524221403386890057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276280129180818063413637 239302524221403386890057)
                  ·
                    rfl

theorem cell21_1048590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1048590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048590 prefixEnd_1048590 := by exact prefixLift 1048590
  have htrace : WordTrace (prefixWord ++ tailWord_1048590) baseStart_1048590 baseEnd_1048590 := by
    simpa [prefixWord, tailWord_1048590, baseEnd_1048590] using wordTrace_append hprefix tailTrace_1048590
  have hstable : (prefixWord ++ tailWord_1048590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048590).length < 2 ^ (prefixWord ++ tailWord_1048590).sum := by decide
  have hdescent : baseEnd_1048590 < baseStart_1048590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048604 : List Nat := [2, 2, 3, 1, 3, 1, 1, 8]
def baseStart_1048604 : Nat := 118140960795 + 1048604 * 2 ^ 59
def prefixEnd_1048604 : Nat := 4983230072969 + 3 ^ 40 * 1048604 * 2
def baseEnd_1048604 : Nat := 79768573070714157885565

theorem tailTrace_1048604 : CollatzResearch.WordTrace tailWord_1048604 prefixEnd_1048604 79768573070714157885565 := by
  unfold tailWord_1048604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19122864946547135075220433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25497153262062846766960577 19122864946547135075220433)
  ·
    refine ⟨14342148709910351306415325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19122864946547135075220433 14342148709910351306415325)
    ·
      refine ⟨5378305766216381739905747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14342148709910351306415325 5378305766216381739905747)
      ·
        refine ⟨8067458649324572609858621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378305766216381739905747 8067458649324572609858621)
        ·
          refine ⟨3025296993496714728696983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8067458649324572609858621 3025296993496714728696983)
          ·
            refine ⟨4537945490245072093045475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025296993496714728696983 4537945490245072093045475)
            ·
              refine ⟨6806918235367608139568213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537945490245072093045475 6806918235367608139568213)
              ·
                refine ⟨79768573070714157885565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6806918235367608139568213 79768573070714157885565)
                ·
                  rfl

theorem cell21_1048604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_1048604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048604 prefixEnd_1048604 := by exact prefixLift 1048604
  have htrace : WordTrace (prefixWord ++ tailWord_1048604) baseStart_1048604 baseEnd_1048604 := by
    simpa [prefixWord, tailWord_1048604, baseEnd_1048604] using wordTrace_append hprefix tailTrace_1048604
  have hstable : (prefixWord ++ tailWord_1048604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048604).length < 2 ^ (prefixWord ++ tailWord_1048604).sum := by decide
  have hdescent : baseEnd_1048604 < baseStart_1048604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048815 : List Nat := [1, 1, 2, 1, 6, 10]
def baseStart_1048815 : Nat := 118140960795 + 1048815 * 2 ^ 59
def prefixEnd_1048815 : Nat := 4983230072969 + 3 ^ 40 * 1048815 * 2
def baseEnd_1048815 : Nat := 8864958232846407245911

theorem tailTrace_1048815 : CollatzResearch.WordTrace tailWord_1048815 prefixEnd_1048815 8864958232846407245911 := by
  unfold tailWord_1048815
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253425695329853186371899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25502283796886568790914599 38253425695329853186371899)
  ·
    refine ⟨57380138542994779779557849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38253425695329853186371899 57380138542994779779557849)
    ·
      refine ⟨43035103907246084834668387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57380138542994779779557849 43035103907246084834668387)
      ·
        refine ⟨64552655860869127252002581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43035103907246084834668387 64552655860869127252002581)
        ·
          refine ⟨3025905743478240339937621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64552655860869127252002581 3025905743478240339937621)
          ·
            refine ⟨8864958232846407245911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3025905743478240339937621 8864958232846407245911)
            ·
              rfl

theorem cell21_1048815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 10].length) (baseStart_1048815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048815 prefixEnd_1048815 := by exact prefixLift 1048815
  have htrace : WordTrace (prefixWord ++ tailWord_1048815) baseStart_1048815 baseEnd_1048815 := by
    simpa [prefixWord, tailWord_1048815, baseEnd_1048815] using wordTrace_append hprefix tailTrace_1048815
  have hstable : (prefixWord ++ tailWord_1048815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048815).length < 2 ^ (prefixWord ++ tailWord_1048815).sum := by decide
  have hdescent : baseEnd_1048815 < baseStart_1048815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048818 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1048818 : Nat := 118140960795 + 1048818 * 2 ^ 59
def prefixEnd_1048818 : Nat := 4983230072969 + 3 ^ 40 * 1048818 * 2
def baseEnd_1048818 : Nat := 239354556927725657089591

theorem tailTrace_1048818 : CollatzResearch.WordTrace tailWord_1048818 prefixEnd_1048818 239354556927725657089591 := by
  unfold tailWord_1048818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563383778579746174682777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25502356742879323132487405 9563383778579746174682777)
  ·
    refine ⟨7172537833934809631012083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9563383778579746174682777 7172537833934809631012083)
    ·
      refine ⟨10758806750902214446518125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7172537833934809631012083 10758806750902214446518125)
      ·
        refine ⟨4034552531588330417444297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10758806750902214446518125 4034552531588330417444297)
        ·
          refine ⟨3025914398691247813083223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4034552531588330417444297 3025914398691247813083223)
          ·
            refine ⟨4538871598036871719624835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025914398691247813083223 4538871598036871719624835)
            ·
              refine ⟨6808307397055307579437253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538871598036871719624835 6808307397055307579437253)
              ·
                refine ⟨1276557636947870171144485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6808307397055307579437253 1276557636947870171144485)
                ·
                  refine ⟨239354556927725657089591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1276557636947870171144485 239354556927725657089591)
                  ·
                    rfl

theorem cell21_1048818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1048818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048818 prefixEnd_1048818 := by exact prefixLift 1048818
  have htrace : WordTrace (prefixWord ++ tailWord_1048818) baseStart_1048818 baseEnd_1048818 := by
    simpa [prefixWord, tailWord_1048818, baseEnd_1048818] using wordTrace_append hprefix tailTrace_1048818
  have hstable : (prefixWord ++ tailWord_1048818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048818).length < 2 ^ (prefixWord ++ tailWord_1048818).sum := by decide
  have hdescent : baseEnd_1048818 < baseStart_1048818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048967 : List Nat := [1, 1, 4, 2, 2, 1, 1, 9]
def baseStart_1048967 : Nat := 118140960795 + 1048967 * 2 ^ 59
def prefixEnd_1048967 : Nat := 4983230072969 + 3 ^ 40 * 1048967 * 2
def baseEnd_1048967 : Nat := 79796186919244836368651

theorem tailTrace_1048967 : CollatzResearch.WordTrace tailWord_1048967 prefixEnd_1048967 79796186919244836368651 := by
  unfold tailWord_1048967
  simp only [CollatzResearch.WordTrace]
  refine ⟨38258969590779183145905155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25505979727186122097270103 38258969590779183145905155)
  ·
    refine ⟨57388454386168774718857733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38258969590779183145905155 57388454386168774718857733)
    ·
      refine ⟨10760335197406645259785825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57388454386168774718857733 10760335197406645259785825)
      ·
        refine ⟨8070251398054983944839369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760335197406645259785825 8070251398054983944839369)
        ·
          refine ⟨6052688548541237958629527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8070251398054983944839369 6052688548541237958629527)
          ·
            refine ⟨9079032822811856937944291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052688548541237958629527 9079032822811856937944291)
            ·
              refine ⟨13618549234217785406916437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9079032822811856937944291 13618549234217785406916437)
              ·
                refine ⟨79796186919244836368651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13618549234217785406916437 79796186919244836368651)
                ·
                  rfl

theorem cell21_1048967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_1048967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048967 prefixEnd_1048967 := by exact prefixLift 1048967
  have htrace : WordTrace (prefixWord ++ tailWord_1048967) baseStart_1048967 baseEnd_1048967 := by
    simpa [prefixWord, tailWord_1048967, baseEnd_1048967] using wordTrace_append hprefix tailTrace_1048967
  have hstable : (prefixWord ++ tailWord_1048967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048967).length < 2 ^ (prefixWord ++ tailWord_1048967).sum := by decide
  have hdescent : baseEnd_1048967 < baseStart_1048967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048990 : List Nat := [4, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1048990 : Nat := 118140960795 + 1048990 * 2 ^ 59
def prefixEnd_1048990 : Nat := 4983230072969 + 3 ^ 40 * 1048990 * 2
def baseEnd_1048990 : Nat := 239393809671091580222573

theorem tailTrace_1048990 : CollatzResearch.WordTrace tailWord_1048990 prefixEnd_1048990 239393809671091580222573 := by
  unfold tailWord_1048990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782476058711982259249053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25506538979797238715994949 4782476058711982259249053)
  ·
    refine ⟨1793428522016993347218395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4782476058711982259249053 1793428522016993347218395)
    ·
      refine ⟨2690142783025490020827593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793428522016993347218395 2690142783025490020827593)
      ·
        refine ⟨2017607087269117515620695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2690142783025490020827593 2017607087269117515620695)
        ·
          refine ⟨3026410630903676273431043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017607087269117515620695 3026410630903676273431043)
          ·
            refine ⟨4539615946355514410146565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026410630903676273431043 4539615946355514410146565)
            ·
              refine ⟨851177989941658951902481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4539615946355514410146565 851177989941658951902481)
              ·
                refine ⟨638383492456244213926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851177989941658951902481 638383492456244213926861)
                ·
                  refine ⟨239393809671091580222573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638383492456244213926861 239393809671091580222573)
                  ·
                    rfl

theorem cell21_1048990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1048990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1048990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1048990 prefixEnd_1048990 := by exact prefixLift 1048990
  have htrace : WordTrace (prefixWord ++ tailWord_1048990) baseStart_1048990 baseEnd_1048990 := by
    simpa [prefixWord, tailWord_1048990, baseEnd_1048990] using wordTrace_append hprefix tailTrace_1048990
  have hstable : (prefixWord ++ tailWord_1048990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048990).length < 2 ^ (prefixWord ++ tailWord_1048990).sum := by decide
  have hdescent : baseEnd_1048990 < baseStart_1048990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049032 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_1049032 : Nat := 118140960795 + 1049032 * 2 ^ 59
def prefixEnd_1049032 : Nat := 4983230072969 + 3 ^ 40 * 1049032 * 2
def baseEnd_1049032 : Nat := 239403394643308840522487

theorem tailTrace_1049032 : CollatzResearch.WordTrace tailWord_1049032 prefixEnd_1049032 239403394643308840522487 := by
  unfold tailWord_1049032
  simp only [CollatzResearch.WordTrace]
  refine ⟨19130670167771849623510675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25507560223695799498014233 19130670167771849623510675)
  ·
    refine ⟨28696005251657774435266013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19130670167771849623510675 28696005251657774435266013)
    ·
      refine ⟨10761001969371665413224755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28696005251657774435266013 10761001969371665413224755)
      ·
        refine ⟨16141502954057498119837133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10761001969371665413224755 16141502954057498119837133)
        ·
          refine ⟨6053063607771561794938925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16141502954057498119837133 6053063607771561794938925)
          ·
            refine ⟨2269898852914335673102097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6053063607771561794938925 2269898852914335673102097)
            ·
              refine ⟨1702424139685751754826573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269898852914335673102097 1702424139685751754826573)
              ·
                refine ⟨638409052382156908059965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702424139685751754826573 638409052382156908059965)
                ·
                  refine ⟨239403394643308840522487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638409052382156908059965 239403394643308840522487)
                  ·
                    rfl

theorem cell21_1049032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_1049032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049032 prefixEnd_1049032 := by exact prefixLift 1049032
  have htrace : WordTrace (prefixWord ++ tailWord_1049032) baseStart_1049032 baseEnd_1049032 := by
    simpa [prefixWord, tailWord_1049032, baseEnd_1049032] using wordTrace_append hprefix tailTrace_1049032
  have hstable : (prefixWord ++ tailWord_1049032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049032).length < 2 ^ (prefixWord ++ tailWord_1049032).sum := by decide
  have hdescent : baseEnd_1049032 < baseStart_1049032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049046 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1049046 : Nat := 118140960795 + 1049046 * 2 ^ 59
def prefixEnd_1049046 : Nat := 4983230072969 + 3 ^ 40 * 1049046 * 2
def baseEnd_1049046 : Nat := 239406589634047927289125

theorem tailTrace_1049046 : CollatzResearch.WordTrace tailWord_1049046 prefixEnd_1049046 239406589634047927289125 := by
  unfold tailWord_1049046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391365684843311227376937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25507900638328653092020661 2391365684843311227376937)
  ·
    refine ⟨1793524263632483420532703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2391365684843311227376937 1793524263632483420532703)
    ·
      refine ⟨2690286395448725130799055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793524263632483420532703 2690286395448725130799055)
      ·
        refine ⟨4035429593173087696198583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690286395448725130799055 4035429593173087696198583)
        ·
          refine ⟨6053144389759631544297875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035429593173087696198583 6053144389759631544297875)
          ·
            refine ⟨9079716584639447316446813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053144389759631544297875 9079716584639447316446813)
            ·
              refine ⟨3404893719239792743667555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9079716584639447316446813 3404893719239792743667555)
              ·
                refine ⟨5107340578859689115501333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404893719239792743667555 5107340578859689115501333)
                ·
                  refine ⟨239406589634047927289125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5107340578859689115501333 239406589634047927289125)
                  ·
                    rfl

theorem cell21_1049046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1049046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049046 prefixEnd_1049046 := by exact prefixLift 1049046
  have htrace : WordTrace (prefixWord ++ tailWord_1049046) baseStart_1049046 baseEnd_1049046 := by
    simpa [prefixWord, tailWord_1049046, baseEnd_1049046] using wordTrace_append hprefix tailTrace_1049046
  have hstable : (prefixWord ++ tailWord_1049046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049046).length < 2 ^ (prefixWord ++ tailWord_1049046).sum := by decide
  have hdescent : baseEnd_1049046 < baseStart_1049046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049077 : List Nat := [1, 3, 5, 1, 2, 1, 1, 7]
def baseStart_1049077 : Nat := 118140960795 + 1049077 * 2 ^ 59
def prefixEnd_1049077 : Nat := 4983230072969 + 3 ^ 40 * 1049077 * 2
def baseEnd_1049077 : Nat := 79804554752132920757465

theorem tailTrace_1049077 : CollatzResearch.WordTrace tailWord_1049077 prefixEnd_1049077 79804554752132920757465 := by
  unfold tailWord_1049077
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262981620380671932409485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25508654413587114621606323 38262981620380671932409485)
  ·
    refine ⟨14348618107642751974653557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38262981620380671932409485 14348618107642751974653557)
    ·
      refine ⟨1345182947591507997623771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14348618107642751974653557 1345182947591507997623771)
      ·
        refine ⟨2017774421387261996435657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345182947591507997623771 2017774421387261996435657)
        ·
          refine ⟨1513330816040446497326743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017774421387261996435657 1513330816040446497326743)
          ·
            refine ⟨2269996224060669745990115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513330816040446497326743 2269996224060669745990115)
            ·
              refine ⟨3404994336091004618985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269996224060669745990115 3404994336091004618985173)
              ·
                refine ⟨79804554752132920757465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3404994336091004618985173 79804554752132920757465)
                ·
                  rfl

theorem cell21_1049077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_1049077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049077 prefixEnd_1049077 := by exact prefixLift 1049077
  have htrace : WordTrace (prefixWord ++ tailWord_1049077) baseStart_1049077 baseEnd_1049077 := by
    simpa [prefixWord, tailWord_1049077, baseEnd_1049077] using wordTrace_append hprefix tailTrace_1049077
  have hstable : (prefixWord ++ tailWord_1049077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049077).length < 2 ^ (prefixWord ++ tailWord_1049077).sum := by decide
  have hdescent : baseEnd_1049077 < baseStart_1049077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049094 : List Nat := [6, 2, 1, 1, 1, 1, 9]
def baseStart_1049094 : Nat := 118140960795 + 1049094 * 2 ^ 59
def prefixEnd_1049094 : Nat := 4983230072969 + 3 ^ 40 * 1049094 * 2
def baseEnd_1049094 : Nat := 26601949320890056721003

theorem tailTrace_1049094 : CollatzResearch.WordTrace tailWord_1049094 prefixEnd_1049094 26601949320890056721003 := by
  unfold tailWord_1049094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195737551916221369868073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25509067774212722557185557 1195737551916221369868073)
  ·
    refine ⟨896803163937166027401055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195737551916221369868073 896803163937166027401055)
    ·
      refine ⟨1345204745905749041101583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896803163937166027401055 1345204745905749041101583)
      ·
        refine ⟨2017807118858623561652375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345204745905749041101583 2017807118858623561652375)
        ·
          refine ⟨3026710678287935342478563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017807118858623561652375 3026710678287935342478563)
          ·
            refine ⟨4540066017431903013717845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026710678287935342478563 4540066017431903013717845)
            ·
              refine ⟨26601949320890056721003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4540066017431903013717845 26601949320890056721003)
              ·
                rfl

theorem cell21_1049094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 9].length) (baseStart_1049094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049094 prefixEnd_1049094 := by exact prefixLift 1049094
  have htrace : WordTrace (prefixWord ++ tailWord_1049094) baseStart_1049094 baseEnd_1049094 := by
    simpa [prefixWord, tailWord_1049094, baseEnd_1049094] using wordTrace_append hprefix tailTrace_1049094
  have hstable : (prefixWord ++ tailWord_1049094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049094).length < 2 ^ (prefixWord ++ tailWord_1049094).sum := by decide
  have hdescent : baseEnd_1049094 < baseStart_1049094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049108 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1049108 : Nat := 118140960795 + 1049108 * 2 ^ 59
def prefixEnd_1049108 : Nat := 4983230072969 + 3 ^ 40 * 1049108 * 2
def baseEnd_1049108 : Nat := 239420738878749597255665

theorem tailTrace_1049108 : CollatzResearch.WordTrace tailWord_1049108 prefixEnd_1049108 239420738878749597255665 := by
  unfold tailWord_1049108
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132056141634182113393989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25509408188845576151191985 19132056141634182113393989)
  ·
    refine ⟨3587260526556409146261373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19132056141634182113393989 3587260526556409146261373)
    ·
      refine ⟨1345222697458653429848015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3587260526556409146261373 1345222697458653429848015)
      ·
        refine ⟨2017834046187980144772023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345222697458653429848015 2017834046187980144772023)
        ·
          refine ⟨3026751069281970217158035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017834046187980144772023 3026751069281970217158035)
          ·
            refine ⟨4540126603922955325737053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026751069281970217158035 4540126603922955325737053)
            ·
              refine ⟨1702547476471108247151395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4540126603922955325737053 1702547476471108247151395)
              ·
                refine ⟨2553821214706662370727093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702547476471108247151395 2553821214706662370727093)
                ·
                  refine ⟨239420738878749597255665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553821214706662370727093 239420738878749597255665)
                  ·
                    rfl

theorem cell21_1049108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1049108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049108 prefixEnd_1049108 := by exact prefixLift 1049108
  have htrace : WordTrace (prefixWord ++ tailWord_1049108) baseStart_1049108 baseEnd_1049108 := by
    simpa [prefixWord, tailWord_1049108, baseEnd_1049108] using wordTrace_append hprefix tailTrace_1049108
  have hstable : (prefixWord ++ tailWord_1049108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049108).length < 2 ^ (prefixWord ++ tailWord_1049108).sum := by decide
  have hdescent : baseEnd_1049108 < baseStart_1049108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049218 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1049218 : Nat := 118140960795 + 1049218 * 2 ^ 59
def prefixEnd_1049218 : Nat := 4983230072969 + 3 ^ 40 * 1049218 * 2
def baseEnd_1049218 : Nat := 239445842377413850422107

theorem tailTrace_1049218 : CollatzResearch.WordTrace tailWord_1049218 prefixEnd_1049218 239445842377413850422107 := by
  unfold tailWord_1049218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567031078217463253323077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25512082875246568675528205 9567031078217463253323077)
  ·
    refine ⟨1793818327165774359998077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9567031078217463253323077 1793818327165774359998077)
    ·
      refine ⟨672681872687165384999279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1793818327165774359998077 672681872687165384999279)
      ·
        refine ⟨1009022809030748077498919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672681872687165384999279 1009022809030748077498919)
        ·
          refine ⟨1513534213546122116248379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009022809030748077498919 1513534213546122116248379)
          ·
            refine ⟨2270301320319183174372569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513534213546122116248379 2270301320319183174372569)
            ·
              refine ⟨1702725990239387380779427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270301320319183174372569 1702725990239387380779427)
              ·
                refine ⟨2554088985359081071169141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702725990239387380779427 2554088985359081071169141)
                ·
                  refine ⟨239445842377413850422107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554088985359081071169141 239445842377413850422107)
                  ·
                    rfl

theorem cell21_1049218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1049218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049218 prefixEnd_1049218 := by exact prefixLift 1049218
  have htrace : WordTrace (prefixWord ++ tailWord_1049218) baseStart_1049218 baseEnd_1049218 := by
    simpa [prefixWord, tailWord_1049218, baseEnd_1049218] using wordTrace_append hprefix tailTrace_1049218
  have hstable : (prefixWord ++ tailWord_1049218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049218).length < 2 ^ (prefixWord ++ tailWord_1049218).sum := by decide
  have hdescent : baseEnd_1049218 < baseStart_1049218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049361 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1049361 : Nat := 118140960795 + 1049361 * 2 ^ 59
def prefixEnd_1049361 : Nat := 4983230072969 + 3 ^ 40 * 1049361 * 2
def baseEnd_1049361 : Nat := 239478476925677379538481

theorem tailTrace_1049361 : CollatzResearch.WordTrace tailWord_1049361 prefixEnd_1049361 239478476925677379538481 := by
  unfold tailWord_1049361
  simp only [CollatzResearch.WordTrace]
  refine ⟨38273339951351788435747937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25515559967567858957165291 38273339951351788435747937)
  ·
    refine ⟨28705004963513841326810953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38273339951351788435747937 28705004963513841326810953)
    ·
      refine ⟨21528753722635380995108215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28705004963513841326810953 21528753722635380995108215)
      ·
        refine ⟨32293130583953071492662323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21528753722635380995108215 32293130583953071492662323)
        ·
          refine ⟨48439695875929607238993485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32293130583953071492662323 48439695875929607238993485)
          ·
            refine ⟨18164885953473602714622557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48439695875929607238993485 18164885953473602714622557)
            ·
              refine ⟨6811832232552601017983459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18164885953473602714622557 6811832232552601017983459)
              ·
                refine ⟨10217748348828901526975189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6811832232552601017983459 10217748348828901526975189)
                ·
                  refine ⟨239478476925677379538481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10217748348828901526975189 239478476925677379538481)
                  ·
                    rfl

theorem cell21_1049361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1049361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049361 prefixEnd_1049361 := by exact prefixLift 1049361
  have htrace : WordTrace (prefixWord ++ tailWord_1049361) baseStart_1049361 baseEnd_1049361 := by
    simpa [prefixWord, tailWord_1049361, baseEnd_1049361] using wordTrace_append hprefix tailTrace_1049361
  have hstable : (prefixWord ++ tailWord_1049361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049361).length < 2 ^ (prefixWord ++ tailWord_1049361).sum := by decide
  have hdescent : baseEnd_1049361 < baseStart_1049361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049395 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 3]
def baseStart_1049395 : Nat := 118140960795 + 1049395 * 2 ^ 59
def prefixEnd_1049395 : Nat := 4983230072969 + 3 ^ 40 * 1049395 * 2
def baseEnd_1049395 : Nat := 239486236188900875971745

theorem tailTrace_1049395 : CollatzResearch.WordTrace tailWord_1049395 prefixEnd_1049395 239486236188900875971745 := by
  unfold tailWord_1049395
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274580033228612242485639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25516386688819074828323759 38274580033228612242485639)
  ·
    refine ⟨57411870049842918363728459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38274580033228612242485639 57411870049842918363728459)
    ·
      refine ⟨86117805074764377545592689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57411870049842918363728459 86117805074764377545592689)
      ·
        refine ⟨64588353806073283159194517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86117805074764377545592689 64588353806073283159194517)
        ·
          refine ⟨3027579084659685148087243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64588353806073283159194517 3027579084659685148087243)
          ·
            refine ⟨4541368626989527722130865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3027579084659685148087243 4541368626989527722130865)
            ·
              refine ⟨3406026470242145791598149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541368626989527722130865 3406026470242145791598149)
              ·
                refine ⟨638629963170402335924653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3406026470242145791598149 638629963170402335924653)
                ·
                  refine ⟨239486236188900875971745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638629963170402335924653 239486236188900875971745)
                  ·
                    rfl

theorem cell21_1049395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 3].length) (baseStart_1049395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049395 prefixEnd_1049395 := by exact prefixLift 1049395
  have htrace : WordTrace (prefixWord ++ tailWord_1049395) baseStart_1049395 baseEnd_1049395 := by
    simpa [prefixWord, tailWord_1049395, baseEnd_1049395] using wordTrace_append hprefix tailTrace_1049395
  have hstable : (prefixWord ++ tailWord_1049395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049395).length < 2 ^ (prefixWord ++ tailWord_1049395).sum := by decide
  have hdescent : baseEnd_1049395 < baseStart_1049395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049505 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 3]
def baseStart_1049505 : Nat := 118140960795 + 1049505 * 2 ^ 59
def prefixEnd_1049505 : Nat := 4983230072969 + 3 ^ 40 * 1049505 * 2
def baseEnd_1049505 : Nat := 239511339687565129138187

theorem tailTrace_1049505 : CollatzResearch.WordTrace tailWord_1049505 prefixEnd_1049505 239511339687565129138187 := by
  unfold tailWord_1049505
  simp only [CollatzResearch.WordTrace]
  refine ⟨38278592062830101028989969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25519061375220067352659979 38278592062830101028989969)
  ·
    refine ⟨28708944047122575771742477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38278592062830101028989969 28708944047122575771742477)
    ·
      refine ⟨10765854017670965914403429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28708944047122575771742477 10765854017670965914403429)
      ·
        refine ⟨2018597628313306108950643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10765854017670965914403429 2018597628313306108950643)
        ·
          refine ⟨3027896442469959163425965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018597628313306108950643 3027896442469959163425965)
          ·
            refine ⟨1135461165926234686284737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3027896442469959163425965 1135461165926234686284737)
            ·
              refine ⟨851595874444676014713553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135461165926234686284737 851595874444676014713553)
              ·
                refine ⟨638696905833507011035165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851595874444676014713553 638696905833507011035165)
                ·
                  refine ⟨239511339687565129138187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638696905833507011035165 239511339687565129138187)
                  ·
                    rfl

theorem cell21_1049505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_1049505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049505 prefixEnd_1049505 := by exact prefixLift 1049505
  have htrace : WordTrace (prefixWord ++ tailWord_1049505) baseStart_1049505 baseEnd_1049505 := by
    simpa [prefixWord, tailWord_1049505, baseEnd_1049505] using wordTrace_append hprefix tailTrace_1049505
  have hstable : (prefixWord ++ tailWord_1049505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049505).length < 2 ^ (prefixWord ++ tailWord_1049505).sum := by decide
  have hdescent : baseEnd_1049505 < baseStart_1049505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049513 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 5]
def baseStart_1049513 : Nat := 118140960795 + 1049513 * 2 ^ 59
def prefixEnd_1049513 : Nat := 4983230072969 + 3 ^ 40 * 1049513 * 2
def baseEnd_1049513 : Nat := 239513165396558893004837

theorem tailTrace_1049513 : CollatzResearch.WordTrace tailWord_1049513 prefixEnd_1049513 239513165396558893004837 := by
  unfold tailWord_1049513
  simp only [CollatzResearch.WordTrace]
  refine ⟨38278883846801118395281193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25519255897867412263520795 38278883846801118395281193)
  ·
    refine ⟨28709162885100838796460895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38278883846801118395281193 28709162885100838796460895)
    ·
      refine ⟨43063744327651258194691343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28709162885100838796460895 43063744327651258194691343)
      ·
        refine ⟨64595616491476887292037015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43063744327651258194691343 64595616491476887292037015)
        ·
          refine ⟨96893424737215330938055523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64595616491476887292037015 96893424737215330938055523)
          ·
            refine ⟨145340137105822996407083285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96893424737215330938055523 145340137105822996407083285)
            ·
              refine ⟨6812818926835452956582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145340137105822996407083285 6812818926835452956582029)
              ·
                refine ⟨2554807097563294858718261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6812818926835452956582029 2554807097563294858718261)
                ·
                  refine ⟨239513165396558893004837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2554807097563294858718261 239513165396558893004837)
                  ·
                    rfl

theorem cell21_1049513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_1049513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049513 prefixEnd_1049513 := by exact prefixLift 1049513
  have htrace : WordTrace (prefixWord ++ tailWord_1049513) baseStart_1049513 baseEnd_1049513 := by
    simpa [prefixWord, tailWord_1049513, baseEnd_1049513] using wordTrace_append hprefix tailTrace_1049513
  have hstable : (prefixWord ++ tailWord_1049513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049513).length < 2 ^ (prefixWord ++ tailWord_1049513).sum := by decide
  have hdescent : baseEnd_1049513 < baseStart_1049513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049547 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 3]
def baseStart_1049547 : Nat := 118140960795 + 1049547 * 2 ^ 59
def prefixEnd_1049547 : Nat := 4983230072969 + 3 ^ 40 * 1049547 * 2
def baseEnd_1049547 : Nat := 239520924659782389438101

theorem tailTrace_1049547 : CollatzResearch.WordTrace tailWord_1049547 prefixEnd_1049547 239520924659782389438101 := by
  unfold tailWord_1049547
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280123928677942202018895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520082619118628134679263 38280123928677942202018895)
  ·
    refine ⟨57420185893016913303028343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38280123928677942202018895 57420185893016913303028343)
    ·
      refine ⟨86130278839525369954542515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57420185893016913303028343 86130278839525369954542515)
      ·
        refine ⟨129195418259288054931813773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86130278839525369954542515 129195418259288054931813773)
        ·
          refine ⟨48448281847233020599430165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129195418259288054931813773 48448281847233020599430165)
          ·
            refine ⟨2271013211589047840598289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48448281847233020599430165 2271013211589047840598289)
            ·
              refine ⟨1703259908691785880448717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271013211589047840598289 1703259908691785880448717)
              ·
                refine ⟨638722465759419705168269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1703259908691785880448717 638722465759419705168269)
                ·
                  refine ⟨239520924659782389438101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638722465759419705168269 239520924659782389438101)
                  ·
                    rfl

theorem cell21_1049547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].length) (baseStart_1049547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049547 prefixEnd_1049547 := by exact prefixLift 1049547
  have htrace : WordTrace (prefixWord ++ tailWord_1049547) baseStart_1049547 baseEnd_1049547 := by
    simpa [prefixWord, tailWord_1049547, baseEnd_1049547] using wordTrace_append hprefix tailTrace_1049547
  have hstable : (prefixWord ++ tailWord_1049547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049547).length < 2 ^ (prefixWord ++ tailWord_1049547).sum := by decide
  have hdescent : baseEnd_1049547 < baseStart_1049547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049561 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_1049561 : Nat := 118140960795 + 1049561 * 2 ^ 59
def prefixEnd_1049561 : Nat := 4983230072969 + 3 ^ 40 * 1049561 * 2
def baseEnd_1049561 : Nat := 239524119650521476204739

theorem tailTrace_1049561 : CollatzResearch.WordTrace tailWord_1049561 prefixEnd_1049561 239524119650521476204739 := by
  unfold tailWord_1049561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280634550627222593028537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520423033751481728685691 38280634550627222593028537)
  ·
    refine ⟨28710475912970416944771403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38280634550627222593028537 28710475912970416944771403)
    ·
      refine ⟨43065713869455625417157105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28710475912970416944771403 43065713869455625417157105)
      ·
        refine ⟨32299285402091719062867829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43065713869455625417157105 32299285402091719062867829)
        ·
          refine ⟨3028058006446098662143859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32299285402091719062867829 3028058006446098662143859)
          ·
            refine ⟨4542087009669147993215789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3028058006446098662143859 4542087009669147993215789)
            ·
              refine ⟨1703282628625930497455921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4542087009669147993215789 1703282628625930497455921)
              ·
                refine ⟨1277461971469447873091941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703282628625930497455921 1277461971469447873091941)
                ·
                  refine ⟨239524119650521476204739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277461971469447873091941 239524119650521476204739)
                  ·
                    rfl

theorem cell21_1049561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_1049561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049561 prefixEnd_1049561 := by exact prefixLift 1049561
  have htrace : WordTrace (prefixWord ++ tailWord_1049561) baseStart_1049561 baseEnd_1049561 := by
    simpa [prefixWord, tailWord_1049561, baseEnd_1049561] using wordTrace_append hprefix tailTrace_1049561
  have hstable : (prefixWord ++ tailWord_1049561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049561).length < 2 ^ (prefixWord ++ tailWord_1049561).sum := by decide
  have hdescent : baseEnd_1049561 < baseStart_1049561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049578 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_1049578 : Nat := 118140960795 + 1049578 * 2 ^ 59
def prefixEnd_1049578 : Nat := 4983230072969 + 3 ^ 40 * 1049578 * 2
def baseEnd_1049578 : Nat := 239527999282133224421371

theorem tailTrace_1049578 : CollatzResearch.WordTrace tailWord_1049578 prefixEnd_1049578 239527999282133224421371 := by
  unfold tailWord_1049578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570313647891408624099347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25520836394377089664264925 9570313647891408624099347)
  ·
    refine ⟨14355470471837112936149021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9570313647891408624099347 14355470471837112936149021)
    ·
      refine ⟨5383301426938917351055883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14355470471837112936149021 5383301426938917351055883)
      ·
        refine ⟨8074952140408376026583825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383301426938917351055883 8074952140408376026583825)
        ·
          refine ⟨6056214105306282019937869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8074952140408376026583825 6056214105306282019937869)
          ·
            refine ⟨2271080289489855757476701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6056214105306282019937869 2271080289489855757476701)
            ·
              refine ⟨851655108558695909053763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2271080289489855757476701 851655108558695909053763)
              ·
                refine ⟨1277482662838043863580645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851655108558695909053763 1277482662838043863580645)
                ·
                  refine ⟨239527999282133224421371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277482662838043863580645 239527999282133224421371)
                  ·
                    rfl

theorem cell21_1049578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_1049578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049578 prefixEnd_1049578 := by exact prefixLift 1049578
  have htrace : WordTrace (prefixWord ++ tailWord_1049578) baseStart_1049578 baseEnd_1049578 := by
    simpa [prefixWord, tailWord_1049578, baseEnd_1049578] using wordTrace_append hprefix tailTrace_1049578
  have hstable : (prefixWord ++ tailWord_1049578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049578).length < 2 ^ (prefixWord ++ tailWord_1049578).sum := by decide
  have hdescent : baseEnd_1049578 < baseStart_1049578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049598 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1049598 : Nat := 118140960795 + 1049598 * 2 ^ 59
def prefixEnd_1049598 : Nat := 4983230072969 + 3 ^ 40 * 1049598 * 2
def baseEnd_1049598 : Nat := 239532563554617634087997

theorem tailTrace_1049598 : CollatzResearch.WordTrace tailWord_1049598 prefixEnd_1049598 239532563554617634087997 := by
  unfold tailWord_1049598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785248006436647239015681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25521322700995451941416965 4785248006436647239015681)
  ·
    refine ⟨3588936004827485429261761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4785248006436647239015681 3588936004827485429261761)
    ·
      refine ⟨2691702003620614071946321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3588936004827485429261761 2691702003620614071946321)
      ·
        refine ⟨2018776502715460553959741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691702003620614071946321 2018776502715460553959741)
        ·
          refine ⟨757041188518297707734903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2018776502715460553959741 757041188518297707734903)
          ·
            refine ⟨1135561782777446561602355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757041188518297707734903 1135561782777446561602355)
            ·
              refine ⟨1703342674166169842403533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135561782777446561602355 1703342674166169842403533)
              ·
                refine ⟨638753502812313690901325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1703342674166169842403533 638753502812313690901325)
                ·
                  refine ⟨239532563554617634087997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638753502812313690901325 239532563554617634087997)
                  ·
                    rfl

theorem cell21_1049598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1049598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049598 prefixEnd_1049598 := by exact prefixLift 1049598
  have htrace : WordTrace (prefixWord ++ tailWord_1049598) baseStart_1049598 baseEnd_1049598 := by
    simpa [prefixWord, tailWord_1049598, baseEnd_1049598] using wordTrace_append hprefix tailTrace_1049598
  have hstable : (prefixWord ++ tailWord_1049598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049598).length < 2 ^ (prefixWord ++ tailWord_1049598).sum := by decide
  have hdescent : baseEnd_1049598 < baseStart_1049598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049623 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_1049623 : Nat := 118140960795 + 1049623 * 2 ^ 59
def prefixEnd_1049623 : Nat := 4983230072969 + 3 ^ 40 * 1049623 * 2
def baseEnd_1049623 : Nat := 239538268895223146171279

theorem tailTrace_1049623 : CollatzResearch.WordTrace tailWord_1049623 prefixEnd_1049623 239538268895223146171279 := by
  unfold tailWord_1049623
  simp only [CollatzResearch.WordTrace]
  refine ⟨38282895876402607181785523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25521930584268404787857015 38282895876402607181785523)
  ·
    refine ⟨57424343814603910772678285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38282895876402607181785523 57424343814603910772678285)
    ·
      refine ⟨21534128930476466539754357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57424343814603910772678285 21534128930476466539754357)
      ·
        refine ⟨2018824587232168738101971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21534128930476466539754357 2018824587232168738101971)
        ·
          refine ⟨3028236880848253107152957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018824587232168738101971 3028236880848253107152957)
          ·
            refine ⟨1135588830318094915182359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3028236880848253107152957 1135588830318094915182359)
            ·
              refine ⟨1703383245477142372773539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135588830318094915182359 1703383245477142372773539)
              ·
                refine ⟨2555074868215713559160309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703383245477142372773539 2555074868215713559160309)
                ·
                  refine ⟨239538268895223146171279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555074868215713559160309 239538268895223146171279)
                  ·
                    rfl

theorem cell21_1049623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_1049623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049623 prefixEnd_1049623 := by exact prefixLift 1049623
  have htrace : WordTrace (prefixWord ++ tailWord_1049623) baseStart_1049623 baseEnd_1049623 := by
    simpa [prefixWord, tailWord_1049623, baseEnd_1049623] using wordTrace_append hprefix tailTrace_1049623
  have hstable : (prefixWord ++ tailWord_1049623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049623).length < 2 ^ (prefixWord ++ tailWord_1049623).sum := by decide
  have hdescent : baseEnd_1049623 < baseStart_1049623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049696 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_1049696 : Nat := 118140960795 + 1049696 * 2 ^ 59
def prefixEnd_1049696 : Nat := 4983230072969 + 3 ^ 40 * 1049696 * 2
def baseEnd_1049696 : Nat := 239554928489791241454463

theorem tailTrace_1049696 : CollatzResearch.WordTrace tailWord_1049696 prefixEnd_1049696 239554928489791241454463 := by
  unfold tailWord_1049696
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142779202569070324596471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25523705603425427099461961 19142779202569070324596471)
  ·
    refine ⟨28714168803853605486894707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19142779202569070324596471 28714168803853605486894707)
    ·
      refine ⟨43071253205780408230342061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28714168803853605486894707 43071253205780408230342061)
      ·
        refine ⟨16151719952167653086378273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43071253205780408230342061 16151719952167653086378273)
        ·
          refine ⟨12113789964125739814783705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16151719952167653086378273 12113789964125739814783705)
          ·
            refine ⟨9085342473094304861087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12113789964125739814783705 9085342473094304861087779)
            ·
              refine ⟨13628013709641457291631669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085342473094304861087779 13628013709641457291631669)
              ·
                refine ⟨1277626285278886621090469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13628013709641457291631669 1277626285278886621090469)
                ·
                  refine ⟨239554928489791241454463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277626285278886621090469 239554928489791241454463)
                  ·
                    rfl

theorem cell21_1049696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_1049696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049696 prefixEnd_1049696 := by exact prefixLift 1049696
  have htrace : WordTrace (prefixWord ++ tailWord_1049696) baseStart_1049696 baseEnd_1049696 := by
    simpa [prefixWord, tailWord_1049696, baseEnd_1049696] using wordTrace_append hprefix tailTrace_1049696
  have hstable : (prefixWord ++ tailWord_1049696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049696).length < 2 ^ (prefixWord ++ tailWord_1049696).sum := by decide
  have hdescent : baseEnd_1049696 < baseStart_1049696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049792 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_1049792 : Nat := 118140960795 + 1049792 * 2 ^ 59
def prefixEnd_1049792 : Nat := 4983230072969 + 3 ^ 40 * 1049792 * 2
def baseEnd_1049792 : Nat := 239576836997716407854267

theorem tailTrace_1049792 : CollatzResearch.WordTrace tailWord_1049792 prefixEnd_1049792 239576836997716407854267 := by
  unfold tailWord_1049792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19144529906395174522343815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25526039875193566029791753 19144529906395174522343815)
  ·
    refine ⟨28716794859592761783515723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19144529906395174522343815 28716794859592761783515723)
    ·
      refine ⟨43075192289389142675273585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28716794859592761783515723 43075192289389142675273585)
      ·
        refine ⟨32306394217041857006455189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43075192289389142675273585 32306394217041857006455189)
        ·
          refine ⟨1514362228923837047177587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32306394217041857006455189 1514362228923837047177587)
          ·
            refine ⟨2271543343385755570766381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514362228923837047177587 2271543343385755570766381)
            ·
              refine ⟨851828753769658339037393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2271543343385755570766381 851828753769658339037393)
              ·
                refine ⟨638871565327243754278045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851828753769658339037393 638871565327243754278045)
                ·
                  refine ⟨239576836997716407854267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638871565327243754278045 239576836997716407854267)
                  ·
                    rfl

theorem cell21_1049792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_1049792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049792 prefixEnd_1049792 := by exact prefixLift 1049792
  have htrace : WordTrace (prefixWord ++ tailWord_1049792) baseStart_1049792 baseEnd_1049792 := by
    simpa [prefixWord, tailWord_1049792, baseEnd_1049792] using wordTrace_append hprefix tailTrace_1049792
  have hstable : (prefixWord ++ tailWord_1049792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049792).length < 2 ^ (prefixWord ++ tailWord_1049792).sum := by decide
  have hdescent : baseEnd_1049792 < baseStart_1049792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049798 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1049798 : Nat := 118140960795 + 1049798 * 2 ^ 59
def prefixEnd_1049798 : Nat := 4983230072969 + 3 ^ 40 * 1049798 * 2
def baseEnd_1049798 : Nat := 239578206279461730754255

theorem tailTrace_1049798 : CollatzResearch.WordTrace tailWord_1049798 prefixEnd_1049798 239578206279461730754255 := by
  unfold tailWord_1049798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196539957836519127168939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25526185767179074712937365 1196539957836519127168939)
  ·
    refine ⟨1794809936754778690753409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1196539957836519127168939 1794809936754778690753409)
    ·
      refine ⟨1346107452566084018065057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1794809936754778690753409 1346107452566084018065057)
      ·
        refine ⟨1009580589424563013548793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1346107452566084018065057 1009580589424563013548793)
        ·
          refine ⟨757185442068422260161595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009580589424563013548793 757185442068422260161595)
          ·
            refine ⟨1135778163102633390242393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757185442068422260161595 1135778163102633390242393)
            ·
              refine ⟨851833622326975042681795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135778163102633390242393 851833622326975042681795)
              ·
                refine ⟨1277750433490462564022693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851833622326975042681795 1277750433490462564022693)
                ·
                  refine ⟨239578206279461730754255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1277750433490462564022693 239578206279461730754255)
                  ·
                    rfl

theorem cell21_1049798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1049798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049798 prefixEnd_1049798 := by exact prefixLift 1049798
  have htrace : WordTrace (prefixWord ++ tailWord_1049798) baseStart_1049798 baseEnd_1049798 := by
    simpa [prefixWord, tailWord_1049798, baseEnd_1049798] using wordTrace_append hprefix tailTrace_1049798
  have hstable : (prefixWord ++ tailWord_1049798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049798).length < 2 ^ (prefixWord ++ tailWord_1049798).sum := by decide
  have hdescent : baseEnd_1049798 < baseStart_1049798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049879 : List Nat := [1, 1, 3, 4, 1, 1, 5, 5]
def baseStart_1049879 : Nat := 118140960795 + 1049879 * 2 ^ 59
def prefixEnd_1049879 : Nat := 4983230072969 + 3 ^ 40 * 1049879 * 2
def baseEnd_1049879 : Nat := 79865563861007863301363

theorem tailTrace_1049879 : CollatzResearch.WordTrace tailWord_1049879 prefixEnd_1049879 79865563861007863301363 := by
  unfold tailWord_1049879
  simp only [CollatzResearch.WordTrace]
  refine ⟨38292232963475162903104691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25528155308983441935403127 38292232963475162903104691)
  ·
    refine ⟨57438349445212744354657037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38292232963475162903104691 57438349445212744354657037)
    ·
      refine ⟨21539381041954779132996389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57438349445212744354657037 21539381041954779132996389)
      ·
        refine ⟨4038633945366521087436823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21539381041954779132996389 4038633945366521087436823)
        ·
          refine ⟨6057950918049781631155235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4038633945366521087436823 6057950918049781631155235)
          ·
            refine ⟨9086926377074672446732853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6057950918049781631155235 9086926377074672446732853)
            ·
              refine ⟨851899347850750541881205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9086926377074672446732853 851899347850750541881205)
              ·
                refine ⟨79865563861007863301363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851899347850750541881205 79865563861007863301363)
                ·
                  rfl

theorem cell21_1049879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 5].length) (baseStart_1049879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049879 prefixEnd_1049879 := by exact prefixLift 1049879
  have htrace : WordTrace (prefixWord ++ tailWord_1049879) baseStart_1049879 baseEnd_1049879 := by
    simpa [prefixWord, tailWord_1049879, baseEnd_1049879] using wordTrace_append hprefix tailTrace_1049879
  have hstable : (prefixWord ++ tailWord_1049879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049879).length < 2 ^ (prefixWord ++ tailWord_1049879).sum := by decide
  have hdescent : baseEnd_1049879 < baseStart_1049879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049969 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 5]
def baseStart_1049969 : Nat := 118140960795 + 1049969 * 2 ^ 59
def prefixEnd_1049969 : Nat := 4983230072969 + 3 ^ 40 * 1049969 * 2
def baseEnd_1049969 : Nat := 239617230809203433403905

theorem tailTrace_1049969 : CollatzResearch.WordTrace tailWord_1049969 prefixEnd_1049969 239617230809203433403905 := by
  unfold tailWord_1049969
  simp only [CollatzResearch.WordTrace]
  refine ⟨38295515533149108273880961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25530343688766072182587307 38295515533149108273880961)
  ·
    refine ⟨28721636649861831205410721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38295515533149108273880961 28721636649861831205410721)
    ·
      refine ⟨21541227487396373404058041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28721636649861831205410721 21541227487396373404058041)
      ·
        refine ⟨16155920615547280053043531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21541227487396373404058041 16155920615547280053043531)
        ·
          refine ⟨24233880923320920079565297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16155920615547280053043531 24233880923320920079565297)
          ·
            refine ⟨18175410692490690059673973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24233880923320920079565297 18175410692490690059673973)
            ·
              refine ⟨1703944752421002193094435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18175410692490690059673973 1703944752421002193094435)
              ·
                refine ⟨2555917128631503289641653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703944752421002193094435 2555917128631503289641653)
                ·
                  refine ⟨239617230809203433403905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2555917128631503289641653 239617230809203433403905)
                  ·
                    rfl

theorem cell21_1049969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_1049969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1049969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1049969 prefixEnd_1049969 := by exact prefixLift 1049969
  have htrace : WordTrace (prefixWord ++ tailWord_1049969) baseStart_1049969 baseEnd_1049969 := by
    simpa [prefixWord, tailWord_1049969, baseEnd_1049969] using wordTrace_append hprefix tailTrace_1049969
  have hstable : (prefixWord ++ tailWord_1049969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049969).length < 2 ^ (prefixWord ++ tailWord_1049969).sum := by decide
  have hdescent : baseEnd_1049969 < baseStart_1049969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050045 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1050045 : Nat := 118140960795 + 1050045 * 2 ^ 59
def prefixEnd_1050045 : Nat := 4983230072969 + 3 ^ 40 * 1050045 * 2
def baseEnd_1050045 : Nat := 239634575044644190137083

theorem tailTrace_1050045 : CollatzResearch.WordTrace tailWord_1050045 prefixEnd_1050045 239634575044644190137083 := by
  unfold tailWord_1050045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38298287480873773253647589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25532191653915848835765059 38298287480873773253647589)
  ·
    refine ⟨7180928902663832485058923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38298287480873773253647589 7180928902663832485058923)
    ·
      refine ⟨10771393353995748727588385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7180928902663832485058923 10771393353995748727588385)
      ·
        refine ⟨8078545015496811545691289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10771393353995748727588385 8078545015496811545691289)
        ·
          refine ⟨6058908761622608659268467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8078545015496811545691289 6058908761622608659268467)
          ·
            refine ⟨9088363142433912988902701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6058908761622608659268467 9088363142433912988902701)
            ·
              refine ⟨3408136178412717370838513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9088363142433912988902701 3408136178412717370838513)
              ·
                refine ⟨2556102133809538028128885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408136178412717370838513 2556102133809538028128885)
                ·
                  refine ⟨239634575044644190137083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556102133809538028128885 239634575044644190137083)
                  ·
                    rfl

theorem cell21_1050045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1050045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050045 prefixEnd_1050045 := by exact prefixLift 1050045
  have htrace : WordTrace (prefixWord ++ tailWord_1050045) baseStart_1050045 baseEnd_1050045 := by
    simpa [prefixWord, tailWord_1050045, baseEnd_1050045] using wordTrace_append hprefix tailTrace_1050045
  have hstable : (prefixWord ++ tailWord_1050045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050045).length < 2 ^ (prefixWord ++ tailWord_1050045).sum := by decide
  have hdescent : baseEnd_1050045 < baseStart_1050045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050062 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_1050062 : Nat := 118140960795 + 1050062 * 2 ^ 59
def prefixEnd_1050062 : Nat := 4983230072969 + 3 ^ 40 * 1050062 * 2
def baseEnd_1050062 : Nat := 239638454676255938353715

theorem tailTrace_1050062 : CollatzResearch.WordTrace tailWord_1050062 prefixEnd_1050062 239638454676255938353715 := by
  unfold tailWord_1050062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4787363440226523144627055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25532605014541456771344293 4787363440226523144627055)
  ·
    refine ⟨7181045160339784716940583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4787363440226523144627055 7181045160339784716940583)
    ·
      refine ⟨10771567740509677075410875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7181045160339784716940583 10771567740509677075410875)
      ·
        refine ⟨16157351610764515613116313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10771567740509677075410875 16157351610764515613116313)
        ·
          refine ⟨12118013708073386709837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16157351610764515613116313 12118013708073386709837235)
          ·
            refine ⟨18177020562110080064755853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12118013708073386709837235 18177020562110080064755853)
            ·
              refine ⟨6816382710791280024283445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18177020562110080064755853 6816382710791280024283445)
              ·
                refine ⟨639035879136682502276573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6816382710791280024283445 639035879136682502276573)
                ·
                  refine ⟨239638454676255938353715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639035879136682502276573 239638454676255938353715)
                  ·
                    rfl

theorem cell21_1050062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_1050062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050062 prefixEnd_1050062 := by exact prefixLift 1050062
  have htrace : WordTrace (prefixWord ++ tailWord_1050062) baseStart_1050062 baseEnd_1050062 := by
    simpa [prefixWord, tailWord_1050062, baseEnd_1050062] using wordTrace_append hprefix tailTrace_1050062
  have hstable : (prefixWord ++ tailWord_1050062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050062).length < 2 ^ (prefixWord ++ tailWord_1050062).sum := by decide
  have hdescent : baseEnd_1050062 < baseStart_1050062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050189 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1050189 : Nat := 118140960795 + 1050189 * 2 ^ 59
def prefixEnd_1050189 : Nat := 4983230072969 + 3 ^ 40 * 1050189 * 2
def baseEnd_1050189 : Nat := 239667437806531939736789

theorem tailTrace_1050189 : CollatzResearch.WordTrace tailWord_1050189 prefixEnd_1050189 239667437806531939736789 := by
  unfold tailWord_1050189
  simp only [CollatzResearch.WordTrace]
  refine ⟨38303539592352085846889621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25535693061568057231259747 38303539592352085846889621)
  ·
    refine ⟨1795478418391504024072951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38303539592352085846889621 1795478418391504024072951)
    ·
      refine ⟨2693217627587256036109427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795478418391504024072951 2693217627587256036109427)
      ·
        refine ⟨4039826441380884054164141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693217627587256036109427 4039826441380884054164141)
        ·
          refine ⟨1514934915517831520311553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4039826441380884054164141 1514934915517831520311553)
          ·
            refine ⟨1136201186638373640233665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514934915517831520311553 1136201186638373640233665)
            ·
              refine ⟨852150889978780230175249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136201186638373640233665 852150889978780230175249)
              ·
                refine ⟨639113167484085172631437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852150889978780230175249 639113167484085172631437)
                ·
                  refine ⟨239667437806531939736789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639113167484085172631437 239667437806531939736789)
                  ·
                    rfl

theorem cell21_1050189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1050189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050189 prefixEnd_1050189 := by exact prefixLift 1050189
  have htrace : WordTrace (prefixWord ++ tailWord_1050189) baseStart_1050189 baseEnd_1050189 := by
    simpa [prefixWord, tailWord_1050189, baseEnd_1050189] using wordTrace_append hprefix tailTrace_1050189
  have hstable : (prefixWord ++ tailWord_1050189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050189).length < 2 ^ (prefixWord ++ tailWord_1050189).sum := by decide
  have hdescent : baseEnd_1050189 < baseStart_1050189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050225 : List Nat := [1, 2, 2, 2, 1, 1, 1, 11]
def baseStart_1050225 : Nat := 118140960795 + 1050225 * 2 ^ 59
def prefixEnd_1050225 : Nat := 4983230072969 + 3 ^ 40 * 1050225 * 2
def baseEnd_1050225 : Nat := 79891884499001292378905

theorem tailTrace_1050225 : CollatzResearch.WordTrace tailWord_1050225 prefixEnd_1050225 79891884499001292378905 := by
  unfold tailWord_1050225
  simp only [CollatzResearch.WordTrace]
  refine ⟨38304852620221663995200129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25536568413481109330133419 38304852620221663995200129)
  ·
    refine ⟨28728639465166247996400097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38304852620221663995200129 28728639465166247996400097)
    ·
      refine ⟨21546479598874685997300073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28728639465166247996400097 21546479598874685997300073)
      ·
        refine ⟨16159859699156014497975055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21546479598874685997300073 16159859699156014497975055)
        ·
          refine ⟨24239789548734021746962583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16159859699156014497975055 24239789548734021746962583)
          ·
            refine ⟨36359684323101032620443875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24239789548734021746962583 36359684323101032620443875)
            ·
              refine ⟨54539526484651548930665813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36359684323101032620443875 54539526484651548930665813)
              ·
                refine ⟨79891884499001292378905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 54539526484651548930665813 79891884499001292378905)
                ·
                  rfl

theorem cell21_1050225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_1050225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050225 prefixEnd_1050225 := by exact prefixLift 1050225
  have htrace : WordTrace (prefixWord ++ tailWord_1050225) baseStart_1050225 baseEnd_1050225 := by
    simpa [prefixWord, tailWord_1050225, baseEnd_1050225] using wordTrace_append hprefix tailTrace_1050225
  have hstable : (prefixWord ++ tailWord_1050225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050225).length < 2 ^ (prefixWord ++ tailWord_1050225).sum := by decide
  have hdescent : baseEnd_1050225 < baseStart_1050225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050273 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1050273 : Nat := 118140960795 + 1050273 * 2 ^ 59
def prefixEnd_1050273 : Nat := 4983230072969 + 3 ^ 40 * 1050273 * 2
def baseEnd_1050273 : Nat := 239686607750966460336617

theorem tailTrace_1050273 : CollatzResearch.WordTrace tailWord_1050273 prefixEnd_1050273 239686607750966460336617 := by
  unfold tailWord_1050273
  simp only [CollatzResearch.WordTrace]
  refine ⟨38306603324047768192947473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25537735549365178795298315 38306603324047768192947473)
  ·
    refine ⟨28729952493035826144710605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38306603324047768192947473 28729952493035826144710605)
    ·
      refine ⟨10773732184888434804266477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28729952493035826144710605 10773732184888434804266477)
      ·
        refine ⟨4040149569333163051599929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10773732184888434804266477 4040149569333163051599929)
        ·
          refine ⟨3030112176999872288699947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4040149569333163051599929 3030112176999872288699947)
          ·
            refine ⟨4545168265499808433049921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030112176999872288699947 4545168265499808433049921)
            ·
              refine ⟨3408876199124856324787441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545168265499808433049921 3408876199124856324787441)
              ·
                refine ⟨2556657149343642243590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408876199124856324787441 2556657149343642243590581)
                ·
                  refine ⟨239686607750966460336617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2556657149343642243590581 239686607750966460336617)
                  ·
                    rfl

theorem cell21_1050273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1050273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050273 prefixEnd_1050273 := by exact prefixLift 1050273
  have htrace : WordTrace (prefixWord ++ tailWord_1050273) baseStart_1050273 baseEnd_1050273 := by
    simpa [prefixWord, tailWord_1050273, baseEnd_1050273] using wordTrace_append hprefix tailTrace_1050273
  have hstable : (prefixWord ++ tailWord_1050273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050273).length < 2 ^ (prefixWord ++ tailWord_1050273).sum := by decide
  have hdescent : baseEnd_1050273 < baseStart_1050273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050290 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_1050290 : Nat := 118140960795 + 1050290 * 2 ^ 59
def prefixEnd_1050290 : Nat := 4983230072969 + 3 ^ 40 * 1050290 * 2
def baseEnd_1050290 : Nat := 239690487382578208553249

theorem tailTrace_1050290 : CollatzResearch.WordTrace tailWord_1050290 prefixEnd_1050290 239690487382578208553249 := by
  unfold tailWord_1050290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9576805841246545024079081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25538148909990786730877549 9576805841246545024079081)
  ·
    refine ⟨7182604380934908768059311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9576805841246545024079081 7182604380934908768059311)
    ·
      refine ⟨10773906571402363152088967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182604380934908768059311 10773906571402363152088967)
      ·
        refine ⟨16160859857103544728133451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10773906571402363152088967 16160859857103544728133451)
        ·
          refine ⟨24241289785655317092200177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16160859857103544728133451 24241289785655317092200177)
          ·
            refine ⟨18180967339241487819150133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24241289785655317092200177 18180967339241487819150133)
            ·
              refine ⟨1704465688053889483045325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18180967339241487819150133 1704465688053889483045325)
              ·
                refine ⟨639174633020208556141997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1704465688053889483045325 639174633020208556141997)
                ·
                  refine ⟨239690487382578208553249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639174633020208556141997 239690487382578208553249)
                  ·
                    rfl

theorem cell21_1050290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_1050290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050290 prefixEnd_1050290 := by exact prefixLift 1050290
  have htrace : WordTrace (prefixWord ++ tailWord_1050290) baseStart_1050290 baseEnd_1050290 := by
    simpa [prefixWord, tailWord_1050290, baseEnd_1050290] using wordTrace_append hprefix tailTrace_1050290
  have hstable : (prefixWord ++ tailWord_1050290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050290).length < 2 ^ (prefixWord ++ tailWord_1050290).sum := by decide
  have hdescent : baseEnd_1050290 < baseStart_1050290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050318 : List Nat := [4, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1050318 : Nat := 118140960795 + 1050318 * 2 ^ 59
def prefixEnd_1050318 : Nat := 4983230072969 + 3 ^ 40 * 1050318 * 2
def baseEnd_1050318 : Nat := 79898959121352127362175

theorem tailTrace_1050318 : CollatzResearch.WordTrace tailWord_1050318 prefixEnd_1050318 79898959121352127362175 := by
  unfold tailWord_1050318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788530576110592609791951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25538829739256493918890405 4788530576110592609791951)
  ·
    refine ⟨7182795864165888914687927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788530576110592609791951 7182795864165888914687927)
    ·
      refine ⟨10774193796248833372031891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182795864165888914687927 10774193796248833372031891)
      ·
        refine ⟨16161290694373250058047837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10774193796248833372031891 16161290694373250058047837)
        ·
          refine ⟨6060484010389968771767939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16161290694373250058047837 6060484010389968771767939)
          ·
            refine ⟨9090726015584953157651909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6060484010389968771767939 9090726015584953157651909)
            ·
              refine ⟨1704511127922178717059733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9090726015584953157651909 1704511127922178717059733)
              ·
                refine ⟨79898959121352127362175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1704511127922178717059733 79898959121352127362175)
                ·
                  rfl

theorem cell21_1050318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1050318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050318 prefixEnd_1050318 := by exact prefixLift 1050318
  have htrace : WordTrace (prefixWord ++ tailWord_1050318) baseStart_1050318 baseEnd_1050318 := by
    simpa [prefixWord, tailWord_1050318, baseEnd_1050318] using wordTrace_append hprefix tailTrace_1050318
  have hstable : (prefixWord ++ tailWord_1050318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050318).length < 2 ^ (prefixWord ++ tailWord_1050318).sum := by decide
  have hdescent : baseEnd_1050318 < baseStart_1050318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050321 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 4]
def baseStart_1050321 : Nat := 118140960795 + 1050321 * 2 ^ 59
def prefixEnd_1050321 : Nat := 4983230072969 + 3 ^ 40 * 1050321 * 2
def baseEnd_1050321 : Nat := 239697562004929043536519

theorem tailTrace_1050321 : CollatzResearch.WordTrace tailWord_1050321 prefixEnd_1050321 239697562004929043536519 := by
  unfold tailWord_1050321
  simp only [CollatzResearch.WordTrace]
  refine ⟨38308354027873872390694817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25538902685249248260463211 38308354027873872390694817)
  ·
    refine ⟨28731265520905404293021113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38308354027873872390694817 28731265520905404293021113)
    ·
      refine ⟨21548449140679053219765835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28731265520905404293021113 21548449140679053219765835)
      ·
        refine ⟨32322673711018579829648753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21548449140679053219765835 32322673711018579829648753)
        ·
          refine ⟨24242005283263934872236565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32322673711018579829648753 24242005283263934872236565)
          ·
            refine ⟨1136343997652996947136089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24242005283263934872236565 1136343997652996947136089)
            ·
              refine ⟨852257998239747710352067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136343997652996947136089 852257998239747710352067)
              ·
                refine ⟨1278386997359621565528101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852257998239747710352067 1278386997359621565528101)
                ·
                  refine ⟨239697562004929043536519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278386997359621565528101 239697562004929043536519)
                  ·
                    rfl

theorem cell21_1050321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_1050321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050321 prefixEnd_1050321 := by exact prefixLift 1050321
  have htrace : WordTrace (prefixWord ++ tailWord_1050321) baseStart_1050321 baseEnd_1050321 := by
    simpa [prefixWord, tailWord_1050321, baseEnd_1050321] using wordTrace_append hprefix tailTrace_1050321
  have hstable : (prefixWord ++ tailWord_1050321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050321).length < 2 ^ (prefixWord ++ tailWord_1050321).sum := by decide
  have hdescent : baseEnd_1050321 < baseStart_1050321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050414 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1050414 : Nat := 118140960795 + 1050414 * 2 ^ 59
def prefixEnd_1050414 : Nat := 4983230072969 + 3 ^ 40 * 1050414 * 2
def baseEnd_1050414 : Nat := 239718785871981548486329

theorem tailTrace_1050414 : CollatzResearch.WordTrace tailWord_1050414 prefixEnd_1050414 239718785871981548486329 := by
  unfold tailWord_1050414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788968252067118659228787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25541164011024632849220197 4788968252067118659228787)
  ·
    refine ⟨7183452378100677988843181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788968252067118659228787 7183452378100677988843181)
    ·
      refine ⟨2693794641787754245816193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7183452378100677988843181 2693794641787754245816193)
      ·
        refine ⟨2020345981340815684362145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693794641787754245816193 2020345981340815684362145)
        ·
          refine ⟨1515259486005611763271609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020345981340815684362145 1515259486005611763271609)
          ·
            refine ⟨1136444614504208822453707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515259486005611763271609 1136444614504208822453707)
            ·
              refine ⟨1704666921756313233680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136444614504208822453707 1704666921756313233680561)
              ·
                refine ⟨1278500191317234925260421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704666921756313233680561 1278500191317234925260421)
                ·
                  refine ⟨239718785871981548486329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278500191317234925260421 239718785871981548486329)
                  ·
                    rfl

theorem cell21_1050414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1050414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050414 prefixEnd_1050414 := by exact prefixLift 1050414
  have htrace : WordTrace (prefixWord ++ tailWord_1050414) baseStart_1050414 baseEnd_1050414 := by
    simpa [prefixWord, tailWord_1050414, baseEnd_1050414] using wordTrace_append hprefix tailTrace_1050414
  have hstable : (prefixWord ++ tailWord_1050414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050414).length < 2 ^ (prefixWord ++ tailWord_1050414).sum := by decide
  have hdescent : baseEnd_1050414 < baseStart_1050414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050439 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_1050439 : Nat := 118140960795 + 1050439 * 2 ^ 59
def prefixEnd_1050439 : Nat := 4983230072969 + 3 ^ 40 * 1050439 * 2
def baseEnd_1050439 : Nat := 239724491212587060569611

theorem tailTrace_1050439 : CollatzResearch.WordTrace tailWord_1050439 prefixEnd_1050439 239724491212587060569611 := by
  unfold tailWord_1050439
  simp only [CollatzResearch.WordTrace]
  refine ⟨38312657841446378543490371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25541771894297585695660247 38312657841446378543490371)
  ·
    refine ⟨57468986762169567815235557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38312657841446378543490371 57468986762169567815235557)
    ·
      refine ⟨10775435017906793965356667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57468986762169567815235557 10775435017906793965356667)
      ·
        refine ⟨16163152526860190948035001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10775435017906793965356667 16163152526860190948035001)
        ·
          refine ⟨12122364395145143211026251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16163152526860190948035001 12122364395145143211026251)
          ·
            refine ⟨18183546592717714816539377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12122364395145143211026251 18183546592717714816539377)
            ·
              refine ⟨13637659944538286112404533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18183546592717714816539377 13637659944538286112404533)
              ·
                refine ⟨1278530619800464323037925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13637659944538286112404533 1278530619800464323037925)
                ·
                  refine ⟨239724491212587060569611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278530619800464323037925 239724491212587060569611)
                  ·
                    rfl

theorem cell21_1050439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_1050439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050439 prefixEnd_1050439 := by exact prefixLift 1050439
  have htrace : WordTrace (prefixWord ++ tailWord_1050439) baseStart_1050439 baseEnd_1050439 := by
    simpa [prefixWord, tailWord_1050439, baseEnd_1050439] using wordTrace_append hprefix tailTrace_1050439
  have hstable : (prefixWord ++ tailWord_1050439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050439).length < 2 ^ (prefixWord ++ tailWord_1050439).sum := by decide
  have hdescent : baseEnd_1050439 < baseStart_1050439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050529 : List Nat := [1, 2, 3, 4, 11]
def baseStart_1050529 : Nat := 118140960795 + 1050529 * 2 ^ 59
def prefixEnd_1050529 : Nat := 4983230072969 + 3 ^ 40 * 1050529 * 2
def baseEnd_1050529 : Nat := 2959815190602060544067

theorem tailTrace_1050529 : CollatzResearch.WordTrace tailWord_1050529 prefixEnd_1050529 2959815190602060544067 := by
  unfold tailWord_1050529
  simp only [CollatzResearch.WordTrace]
  refine ⟨38315940411120323914266641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25543960274080215942844427 38315940411120323914266641)
  ·
    refine ⟨28736955308340242935699981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38315940411120323914266641 28736955308340242935699981)
    ·
      refine ⟨10776358240627591100887493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28736955308340242935699981 10776358240627591100887493)
      ·
        refine ⟨2020567170117673331416405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10776358240627591100887493 2020567170117673331416405)
        ·
          refine ⟨2959815190602060544067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2020567170117673331416405 2959815190602060544067)
          ·
            rfl

theorem cell21_1050529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 11].length) (baseStart_1050529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050529 prefixEnd_1050529 := by exact prefixLift 1050529
  have htrace : WordTrace (prefixWord ++ tailWord_1050529) baseStart_1050529 baseEnd_1050529 := by
    simpa [prefixWord, tailWord_1050529, baseEnd_1050529] using wordTrace_append hprefix tailTrace_1050529
  have hstable : (prefixWord ++ tailWord_1050529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050529).length < 2 ^ (prefixWord ++ tailWord_1050529).sum := by decide
  have hdescent : baseEnd_1050529 < baseStart_1050529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050532 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_1050532 : Nat := 118140960795 + 1050532 * 2 ^ 59
def prefixEnd_1050532 : Nat := 4983230072969 + 3 ^ 40 * 1050532 * 2
def baseEnd_1050532 : Nat := 239745715079639565519421

theorem tailTrace_1050532 : CollatzResearch.WordTrace tailWord_1050532 prefixEnd_1050532 239745715079639565519421 := by
  unfold tailWord_1050532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158024915054727713312925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25544033220072970284417233 19158024915054727713312925)
  ·
    refine ⟨7184259343145522892492347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19158024915054727713312925 7184259343145522892492347)
    ·
      refine ⟨10776389014718284338738521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7184259343145522892492347 10776389014718284338738521)
      ·
        refine ⟨8082291761038713254053891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10776389014718284338738521 8082291761038713254053891)
        ·
          refine ⟨12123437641558069881080837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8082291761038713254053891 12123437641558069881080837)
          ·
            refine ⟨2273144557792138102702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12123437641558069881080837 2273144557792138102702657)
            ·
              refine ⟨1704858418344103577026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2273144557792138102702657 1704858418344103577026993)
              ·
                refine ⟨1278643813758077682770245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704858418344103577026993 1278643813758077682770245)
                ·
                  refine ⟨239745715079639565519421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278643813758077682770245 239745715079639565519421)
                  ·
                    rfl

theorem cell21_1050532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_1050532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050532 prefixEnd_1050532 := by exact prefixLift 1050532
  have htrace : WordTrace (prefixWord ++ tailWord_1050532) baseStart_1050532 baseEnd_1050532 := by
    simpa [prefixWord, tailWord_1050532, baseEnd_1050532] using wordTrace_append hprefix tailTrace_1050532
  have hstable : (prefixWord ++ tailWord_1050532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050532).length < 2 ^ (prefixWord ++ tailWord_1050532).sum := by decide
  have hdescent : baseEnd_1050532 < baseStart_1050532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050535 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 3]
def baseStart_1050535 : Nat := 118140960795 + 1050535 * 2 ^ 59
def prefixEnd_1050535 : Nat := 4983230072969 + 3 ^ 40 * 1050535 * 2
def baseEnd_1050535 : Nat := 239746399720512226969415

theorem tailTrace_1050535 : CollatzResearch.WordTrace tailWord_1050535 prefixEnd_1050535 239746399720512226969415 := by
  unfold tailWord_1050535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38316159249098586938985059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25544106166065724625990039 38316159249098586938985059)
  ·
    refine ⟨57474238873647880408477589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38316159249098586938985059 57474238873647880408477589)
    ·
      refine ⟨2694104947202244394147387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57474238873647880408477589 2694104947202244394147387)
      ·
        refine ⟨4041157420803366591221081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694104947202244394147387 4041157420803366591221081)
        ·
          refine ⟨3030868065602524943415811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041157420803366591221081 3030868065602524943415811)
          ·
            refine ⟨4546302098403787415123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3030868065602524943415811 4546302098403787415123717)
            ·
              refine ⟨852431643450710140335697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4546302098403787415123717 852431643450710140335697)
              ·
                refine ⟨639323732588032605251773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852431643450710140335697 639323732588032605251773)
                ·
                  refine ⟨239746399720512226969415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639323732588032605251773 239746399720512226969415)
                  ·
                    rfl

theorem cell21_1050535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].length) (baseStart_1050535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050535 prefixEnd_1050535 := by exact prefixLift 1050535
  have htrace : WordTrace (prefixWord ++ tailWord_1050535) baseStart_1050535 baseEnd_1050535 := by
    simpa [prefixWord, tailWord_1050535, baseEnd_1050535] using wordTrace_append hprefix tailTrace_1050535
  have hstable : (prefixWord ++ tailWord_1050535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050535).length < 2 ^ (prefixWord ++ tailWord_1050535).sum := by decide
  have hdescent : baseEnd_1050535 < baseStart_1050535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050560 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_1050560 : Nat := 118140960795 + 1050560 * 2 ^ 59
def prefixEnd_1050560 : Nat := 4983230072969 + 3 ^ 40 * 1050560 * 2
def baseEnd_1050560 : Nat := 239752105061117739052697

theorem tailTrace_1050560 : CollatzResearch.WordTrace tailWord_1050560 prefixEnd_1050560 239752105061117739052697 := by
  unfold tailWord_1050560
  simp only [CollatzResearch.WordTrace]
  refine ⟨19158535537004008104322567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25544714049338677472430089 19158535537004008104322567)
  ·
    refine ⟨28737803305506012156483851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19158535537004008104322567 28737803305506012156483851)
    ·
      refine ⟨43106704958259018234725777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28737803305506012156483851 43106704958259018234725777)
      ·
        refine ⟨32330028718694263676044333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43106704958259018234725777 32330028718694263676044333)
        ·
          refine ⟨12123760769510348878516625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32330028718694263676044333 12123760769510348878516625)
          ·
            refine ⟨9092820577132761658887469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12123760769510348878516625 9092820577132761658887469)
            ·
              refine ⟨3409807716424785622082801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9092820577132761658887469 3409807716424785622082801)
              ·
                refine ⟨2557355787318589216562101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409807716424785622082801 2557355787318589216562101)
                ·
                  refine ⟨239752105061117739052697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2557355787318589216562101 239752105061117739052697)
                  ·
                    rfl

theorem cell21_1050560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_1050560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050560 prefixEnd_1050560 := by exact prefixLift 1050560
  have htrace : WordTrace (prefixWord ++ tailWord_1050560) baseStart_1050560 baseEnd_1050560 := by
    simpa [prefixWord, tailWord_1050560, baseEnd_1050560] using wordTrace_append hprefix tailTrace_1050560
  have hstable : (prefixWord ++ tailWord_1050560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050560).length < 2 ^ (prefixWord ++ tailWord_1050560).sum := by decide
  have hdescent : baseEnd_1050560 < baseStart_1050560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050591 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_1050591 : Nat := 118140960795 + 1050591 * 2 ^ 59
def prefixEnd_1050591 : Nat := 4983230072969 + 3 ^ 40 * 1050591 * 2
def baseEnd_1050591 : Nat := 239759179683468574035967

theorem tailTrace_1050591 : CollatzResearch.WordTrace tailWord_1050591 prefixEnd_1050591 239759179683468574035967 := by
  unfold tailWord_1050591
  simp only [CollatzResearch.WordTrace]
  refine ⟨38318201736895708503023627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25545467824597139002015751 38318201736895708503023627)
  ·
    refine ⟨57477302605343562754535441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38318201736895708503023627 57477302605343562754535441)
    ·
      refine ⟨43107976954007672065901581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57477302605343562754535441 43107976954007672065901581)
      ·
        refine ⟨16165491357752877024713093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43107976954007672065901581 16165491357752877024713093)
        ·
          refine ⟨3031029629578664442133705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16165491357752877024713093 3031029629578664442133705)
          ·
            refine ⟨2273272222183998331600279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031029629578664442133705 2273272222183998331600279)
            ·
              refine ⟨3409908333275997497400419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273272222183998331600279 3409908333275997497400419)
              ·
                refine ⟨5114862499913996246100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3409908333275997497400419 5114862499913996246100629)
                ·
                  refine ⟨239759179683468574035967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5114862499913996246100629 239759179683468574035967)
                  ·
                    rfl

theorem cell21_1050591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_1050591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050591 prefixEnd_1050591 := by exact prefixLift 1050591
  have htrace : WordTrace (prefixWord ++ tailWord_1050591) baseStart_1050591 baseEnd_1050591 := by
    simpa [prefixWord, tailWord_1050591, baseEnd_1050591] using wordTrace_append hprefix tailTrace_1050591
  have hstable : (prefixWord ++ tailWord_1050591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050591).length < 2 ^ (prefixWord ++ tailWord_1050591).sum := by decide
  have hdescent : baseEnd_1050591 < baseStart_1050591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050628 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_1050628 : Nat := 118140960795 + 1050628 * 2 ^ 59
def prefixEnd_1050628 : Nat := 4983230072969 + 3 ^ 40 * 1050628 * 2
def baseEnd_1050628 : Nat := 239767623587564731919225

theorem tailTrace_1050628 : CollatzResearch.WordTrace tailWord_1050628 prefixEnd_1050628 239767623587564731919225 := by
  unfold tailWord_1050628
  simp only [CollatzResearch.WordTrace]
  refine ⟨19159775618880831911060269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25546367491841109214747025 19159775618880831911060269)
  ·
    refine ⟨7184915857080311966647601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19159775618880831911060269 7184915857080311966647601)
    ·
      refine ⟨5388686892810233974985701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7184915857080311966647601 5388686892810233974985701)
      ·
        refine ⟨1010378792401918870309819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5388686892810233974985701 1010378792401918870309819)
        ·
          refine ⟨1515568188602878305464729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010378792401918870309819 1515568188602878305464729)
          ·
            refine ⟨1136676141452158729098547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515568188602878305464729 1136676141452158729098547)
            ·
              refine ⟨1705014212178238093647821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136676141452158729098547 1705014212178238093647821)
              ·
                refine ⟨639380329566839285117933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705014212178238093647821 639380329566839285117933)
                ·
                  refine ⟨239767623587564731919225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639380329566839285117933 239767623587564731919225)
                  ·
                    rfl

theorem cell21_1050628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_1050628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050628 prefixEnd_1050628 := by exact prefixLift 1050628
  have htrace : WordTrace (prefixWord ++ tailWord_1050628) baseStart_1050628 baseEnd_1050628 := by
    simpa [prefixWord, tailWord_1050628, baseEnd_1050628] using wordTrace_append hprefix tailTrace_1050628
  have hstable : (prefixWord ++ tailWord_1050628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050628).length < 2 ^ (prefixWord ++ tailWord_1050628).sum := by decide
  have hdescent : baseEnd_1050628 < baseStart_1050628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050653 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1050653 : Nat := 118140960795 + 1050653 * 2 ^ 59
def prefixEnd_1050653 : Nat := 4983230072969 + 3 ^ 40 * 1050653 * 2
def baseEnd_1050653 : Nat := 239773328928170244002507

theorem tailTrace_1050653 : CollatzResearch.WordTrace tailWord_1050653 prefixEnd_1050653 239773328928170244002507 := by
  unfold tailWord_1050653
  simp only [CollatzResearch.WordTrace]
  refine ⟨38320463062671093091780613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25546975375114062061187075 38320463062671093091780613)
  ·
    refine ⟨7185086824250829954708865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38320463062671093091780613 7185086824250829954708865)
    ·
      refine ⟨5388815118188122466031649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7185086824250829954708865 5388815118188122466031649)
      ·
        refine ⟨4041611338641091849523737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5388815118188122466031649 4041611338641091849523737)
        ·
          refine ⟨3031208503980818887142803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4041611338641091849523737 3031208503980818887142803)
          ·
            refine ⟨4546812755971228330714205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031208503980818887142803 4546812755971228330714205)
            ·
              refine ⟨1705054783489210624017827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4546812755971228330714205 1705054783489210624017827)
              ·
                refine ⟨2557582175233815936026741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705054783489210624017827 2557582175233815936026741)
                ·
                  refine ⟨239773328928170244002507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2557582175233815936026741 239773328928170244002507)
                  ·
                    rfl

theorem cell21_1050653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1050653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050653 prefixEnd_1050653 := by exact prefixLift 1050653
  have htrace : WordTrace (prefixWord ++ tailWord_1050653) baseStart_1050653 baseEnd_1050653 := by
    simpa [prefixWord, tailWord_1050653, baseEnd_1050653] using wordTrace_append hprefix tailTrace_1050653
  have hstable : (prefixWord ++ tailWord_1050653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050653).length < 2 ^ (prefixWord ++ tailWord_1050653).sum := by decide
  have hdescent : baseEnd_1050653 < baseStart_1050653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050757 : List Nat := [1, 3, 1, 1, 5, 2, 8]
def baseStart_1050757 : Nat := 118140960795 + 1050757 * 2 ^ 59
def prefixEnd_1050757 : Nat := 4983230072969 + 3 ^ 40 * 1050757 * 2
def baseEnd_1050757 : Nat := 26644118127232130474329

theorem tailTrace_1050757 : CollatzResearch.WordTrace tailWord_1050757 prefixEnd_1050757 26644118127232130474329 := by
  unfold tailWord_1050757
  simp only [CollatzResearch.WordTrace]
  refine ⟨38324256254294318853566525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25549504169529545902377683 38324256254294318853566525)
  ·
    refine ⟨14371596095360369570087447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38324256254294318853566525 14371596095360369570087447)
    ·
      refine ⟨21557394143040554355131171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14371596095360369570087447 21557394143040554355131171)
      ·
        refine ⟨32336091214560831532696757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21557394143040554355131171 32336091214560831532696757)
        ·
          refine ⟨3031508551365077956190321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32336091214560831532696757 3031508551365077956190321)
          ·
            refine ⟨2273631413523808467142741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031508551365077956190321 2273631413523808467142741)
            ·
              refine ⟨26644118127232130474329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2273631413523808467142741 26644118127232130474329)
              ·
                rfl

theorem cell21_1050757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 8].length) (baseStart_1050757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050757 prefixEnd_1050757 := by exact prefixLift 1050757
  have htrace : WordTrace (prefixWord ++ tailWord_1050757) baseStart_1050757 baseEnd_1050757 := by
    simpa [prefixWord, tailWord_1050757, baseEnd_1050757] using wordTrace_append hprefix tailTrace_1050757
  have hstable : (prefixWord ++ tailWord_1050757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050757).length < 2 ^ (prefixWord ++ tailWord_1050757).sum := by decide
  have hdescent : baseEnd_1050757 < baseStart_1050757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050760 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_1050760 : Nat := 118140960795 + 1050760 * 2 ^ 59
def prefixEnd_1050760 : Nat := 4983230072969 + 3 ^ 40 * 1050760 * 2
def baseEnd_1050760 : Nat := 239797747785961835718955

theorem tailTrace_1050760 : CollatzResearch.WordTrace tailWord_1050760 prefixEnd_1050760 239797747785961835718955 := by
  unfold tailWord_1050760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19162182836641725182962867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25549577115522300243950489 19162182836641725182962867)
  ·
    refine ⟨28743274254962587774444301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19162182836641725182962867 28743274254962587774444301)
    ·
      refine ⟨10778727845610970415416613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28743274254962587774444301 10778727845610970415416613)
      ·
        refine ⟨2021011471052056952890615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10778727845610970415416613 2021011471052056952890615)
        ·
          refine ⟨3031517206578085429335923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021011471052056952890615 3031517206578085429335923)
          ·
            refine ⟨4547275809867128144003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031517206578085429335923 4547275809867128144003885)
            ·
              refine ⟨1705228428700173054001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4547275809867128144003885 1705228428700173054001457)
              ·
                refine ⟨1278921321525129790501093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705228428700173054001457 1278921321525129790501093)
                ·
                  refine ⟨239797747785961835718955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1278921321525129790501093 239797747785961835718955)
                  ·
                    rfl

theorem cell21_1050760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_1050760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050760 prefixEnd_1050760 := by exact prefixLift 1050760
  have htrace : WordTrace (prefixWord ++ tailWord_1050760) baseStart_1050760 baseEnd_1050760 := by
    simpa [prefixWord, tailWord_1050760, baseEnd_1050760] using wordTrace_append hprefix tailTrace_1050760
  have hstable : (prefixWord ++ tailWord_1050760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050760).length < 2 ^ (prefixWord ++ tailWord_1050760).sum := by decide
  have hdescent : baseEnd_1050760 < baseStart_1050760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050802 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1050802 : Nat := 118140960795 + 1050802 * 2 ^ 59
def prefixEnd_1050802 : Nat := 4983230072969 + 3 ^ 40 * 1050802 * 2
def baseEnd_1050802 : Nat := 239807332758179096018869

theorem tailTrace_1050802 : CollatzResearch.WordTrace tailWord_1050802 prefixEnd_1050802 239807332758179096018869 := by
  unfold tailWord_1050802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581474384782822884738665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25550598359420861025969773 9581474384782822884738665)
  ·
    refine ⟨7186105788587117163553999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9581474384782822884738665 7186105788587117163553999)
    ·
      refine ⟨10779158682880675745330999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186105788587117163553999 10779158682880675745330999)
      ·
        refine ⟨16168738024321013617996499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10779158682880675745330999 16168738024321013617996499)
        ·
          refine ⟨24253107036481520426994749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16168738024321013617996499 24253107036481520426994749)
          ·
            refine ⟨9094915138680570160123031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24253107036481520426994749 9094915138680570160123031)
            ·
              refine ⟨13642372708020855240184547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094915138680570160123031 13642372708020855240184547)
              ·
                refine ⟨20463559062031282860276821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13642372708020855240184547 20463559062031282860276821)
                ·
                  refine ⟨239807332758179096018869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20463559062031282860276821 239807332758179096018869)
                  ·
                    rfl

theorem cell21_1050802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1050802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050802 prefixEnd_1050802 := by exact prefixLift 1050802
  have htrace : WordTrace (prefixWord ++ tailWord_1050802) baseStart_1050802 baseEnd_1050802 := by
    simpa [prefixWord, tailWord_1050802, baseEnd_1050802] using wordTrace_append hprefix tailTrace_1050802
  have hstable : (prefixWord ++ tailWord_1050802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050802).length < 2 ^ (prefixWord ++ tailWord_1050802).sum := by decide
  have hdescent : baseEnd_1050802 < baseStart_1050802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050847 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_1050847 : Nat := 118140960795 + 1050847 * 2 ^ 59
def prefixEnd_1050847 : Nat := 4983230072969 + 3 ^ 40 * 1050847 * 2
def baseEnd_1050847 : Nat := 239817602371269017768777

theorem tailTrace_1050847 : CollatzResearch.WordTrace tailWord_1050847 prefixEnd_1050847 239817602371269017768777 := by
  unfold tailWord_1050847
  simp only [CollatzResearch.WordTrace]
  refine ⟨38327538823968264224342795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25551692549312176149561863 38327538823968264224342795)
  ·
    refine ⟨57491308235952396336514193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38327538823968264224342795 57491308235952396336514193)
    ·
      refine ⟨43118481176964297252385645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57491308235952396336514193 43118481176964297252385645)
      ·
        refine ⟨16169430441361611469644617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43118481176964297252385645 16169430441361611469644617)
        ·
          refine ⟨12127072831021208602233463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16169430441361611469644617 12127072831021208602233463)
          ·
            refine ⟨18190609246531812903350195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127072831021208602233463 18190609246531812903350195)
            ·
              refine ⟨27285913869797719355025293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18190609246531812903350195 27285913869797719355025293)
              ·
                refine ⟨10232217701174144758134485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27285913869797719355025293 10232217701174144758134485)
                ·
                  refine ⟨239817602371269017768777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10232217701174144758134485 239817602371269017768777)
                  ·
                    rfl

theorem cell21_1050847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_1050847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050847 prefixEnd_1050847 := by exact prefixLift 1050847
  have htrace : WordTrace (prefixWord ++ tailWord_1050847) baseStart_1050847 baseEnd_1050847 := by
    simpa [prefixWord, tailWord_1050847, baseEnd_1050847] using wordTrace_append hprefix tailTrace_1050847
  have hstable : (prefixWord ++ tailWord_1050847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050847).length < 2 ^ (prefixWord ++ tailWord_1050847).sum := by decide
  have hdescent : baseEnd_1050847 < baseStart_1050847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050881 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 3]
def baseStart_1050881 : Nat := 118140960795 + 1050881 * 2 ^ 59
def prefixEnd_1050881 : Nat := 4983230072969 + 3 ^ 40 * 1050881 * 2
def baseEnd_1050881 : Nat := 239825361634492514202041

theorem tailTrace_1050881 : CollatzResearch.WordTrace tailWord_1050881 prefixEnd_1050881 239825361634492514202041 := by
  unfold tailWord_1050881
  simp only [CollatzResearch.WordTrace]
  refine ⟨38328778905845088031080497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25552519270563392020720331 38328778905845088031080497)
  ·
    refine ⟨28746584179383816023310373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38328778905845088031080497 28746584179383816023310373)
    ·
      refine ⟨5389984533634465504370695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28746584179383816023310373 5389984533634465504370695)
      ·
        refine ⟨8084976800451698256556043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389984533634465504370695 8084976800451698256556043)
        ·
          refine ⟨12127465200677547384834065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8084976800451698256556043 12127465200677547384834065)
          ·
            refine ⟨9095598900508160538625549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12127465200677547384834065 9095598900508160538625549)
            ·
              refine ⟨3410849587690560201984581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9095598900508160538625549 3410849587690560201984581)
              ·
                refine ⟨639534297691980037872109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3410849587690560201984581 639534297691980037872109)
                ·
                  refine ⟨239825361634492514202041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639534297691980037872109 239825361634492514202041)
                  ·
                    rfl

theorem cell21_1050881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_1050881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050881 prefixEnd_1050881 := by exact prefixLift 1050881
  have htrace : WordTrace (prefixWord ++ tailWord_1050881) baseStart_1050881 baseEnd_1050881 := by
    simpa [prefixWord, tailWord_1050881, baseEnd_1050881] using wordTrace_append hprefix tailTrace_1050881
  have hstable : (prefixWord ++ tailWord_1050881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050881).length < 2 ^ (prefixWord ++ tailWord_1050881).sum := by decide
  have hdescent : baseEnd_1050881 < baseStart_1050881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050929 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 4]
def baseStart_1050929 : Nat := 118140960795 + 1050929 * 2 ^ 59
def prefixEnd_1050929 : Nat := 4983230072969 + 3 ^ 40 * 1050929 * 2
def baseEnd_1050929 : Nat := 239836315888455097401943

theorem tailTrace_1050929 : CollatzResearch.WordTrace tailWord_1050929 prefixEnd_1050929 239836315888455097401943 := by
  unfold tailWord_1050929
  simp only [CollatzResearch.WordTrace]
  refine ⟨38330529609671192228827841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25553686406447461485885227 38330529609671192228827841)
  ·
    refine ⟨28747897207253394171620881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38330529609671192228827841 28747897207253394171620881)
    ·
      refine ⟨21560922905440045628715661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28747897207253394171620881 21560922905440045628715661)
      ·
        refine ⟨8085346089540017110768373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21560922905440045628715661 8085346089540017110768373)
        ·
          refine ⟨758001195894376604134535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8085346089540017110768373 758001195894376604134535)
          ·
            refine ⟨1137001793841564906201803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758001195894376604134535 1137001793841564906201803)
            ·
              refine ⟨1705502690762347359302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137001793841564906201803 1705502690762347359302705)
              ·
                refine ⟨1279127018071760519477029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705502690762347359302705 1279127018071760519477029)
                ·
                  refine ⟨239836315888455097401943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279127018071760519477029 239836315888455097401943)
                  ·
                    rfl

theorem cell21_1050929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_1050929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050929 prefixEnd_1050929 := by exact prefixLift 1050929
  have htrace : WordTrace (prefixWord ++ tailWord_1050929) baseStart_1050929 baseEnd_1050929 := by
    simpa [prefixWord, tailWord_1050929, baseEnd_1050929] using wordTrace_append hprefix tailTrace_1050929
  have hstable : (prefixWord ++ tailWord_1050929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050929).length < 2 ^ (prefixWord ++ tailWord_1050929).sum := by decide
  have hdescent : baseEnd_1050929 < baseStart_1050929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050940 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_1050940 : Nat := 118140960795 + 1050940 * 2 ^ 59
def prefixEnd_1050940 : Nat := 4983230072969 + 3 ^ 40 * 1050940 * 2
def baseEnd_1050940 : Nat := 239838826238321522718587

theorem tailTrace_1050940 : CollatzResearch.WordTrace tailWord_1050940 prefixEnd_1050940 239838826238321522718587 := by
  unfold tailWord_1050940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165465406315670553739137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25553953875087560738318849 19165465406315670553739137)
  ·
    refine ⟨14374099054736752915304353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19165465406315670553739137 14374099054736752915304353)
    ·
      refine ⟨10780574291052564686478265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14374099054736752915304353 10780574291052564686478265)
      ·
        refine ⟨8085430718289423514858699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10780574291052564686478265 8085430718289423514858699)
        ·
          refine ⟨12128146077434135272288049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8085430718289423514858699 12128146077434135272288049)
          ·
            refine ⟨9096109558075601454216037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12128146077434135272288049 9096109558075601454216037)
            ·
              refine ⟨1705520542139175272665507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9096109558075601454216037 1705520542139175272665507)
              ·
                refine ⟨2558280813208762908998261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705520542139175272665507 2558280813208762908998261)
                ·
                  refine ⟨239838826238321522718587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558280813208762908998261 239838826238321522718587)
                  ·
                    rfl

theorem cell21_1050940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_1050940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050940 prefixEnd_1050940 := by exact prefixLift 1050940
  have htrace : WordTrace (prefixWord ++ tailWord_1050940) baseStart_1050940 baseEnd_1050940 := by
    simpa [prefixWord, tailWord_1050940, baseEnd_1050940] using wordTrace_append hprefix tailTrace_1050940
  have hstable : (prefixWord ++ tailWord_1050940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050940).length < 2 ^ (prefixWord ++ tailWord_1050940).sum := by decide
  have hdescent : baseEnd_1050940 < baseStart_1050940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050999 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_1050999 : Nat := 118140960795 + 1050999 * 2 ^ 59
def prefixEnd_1050999 : Nat := 4983230072969 + 3 ^ 40 * 1050999 * 2
def baseEnd_1050999 : Nat := 239852290842150531235133

theorem tailTrace_1050999 : CollatzResearch.WordTrace tailWord_1050999 prefixEnd_1050999 239852290842150531235133 := by
  unfold tailWord_1050999
  simp only [CollatzResearch.WordTrace]
  refine ⟨38333082719417594183876051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25555388479611729455917367 38333082719417594183876051)
  ·
    refine ⟨57499624079126391275814077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38333082719417594183876051 57499624079126391275814077)
    ·
      refine ⟨21562359029672396728430279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57499624079126391275814077 21562359029672396728430279)
      ·
        refine ⟨32343538544508595092645419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21562359029672396728430279 32343538544508595092645419)
        ·
          refine ⟨48515307816762892638968129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32343538544508595092645419 48515307816762892638968129)
          ·
            refine ⟨36386480862572169479226097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48515307816762892638968129 36386480862572169479226097)
            ·
              refine ⟨27289860646929127109419573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36386480862572169479226097 27289860646929127109419573)
              ·
                refine ⟨2558424435649605666508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27289860646929127109419573 2558424435649605666508085)
                ·
                  refine ⟨239852290842150531235133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558424435649605666508085 239852290842150531235133)
                  ·
                    rfl

theorem cell21_1050999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_1050999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1050999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1050999 prefixEnd_1050999 := by exact prefixLift 1050999
  have htrace : WordTrace (prefixWord ++ tailWord_1050999) baseStart_1050999 baseEnd_1050999 := by
    simpa [prefixWord, tailWord_1050999, baseEnd_1050999] using wordTrace_append hprefix tailTrace_1050999
  have hstable : (prefixWord ++ tailWord_1050999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050999).length < 2 ^ (prefixWord ++ tailWord_1050999).sum := by decide
  have hdescent : baseEnd_1050999 < baseStart_1050999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051047 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_1051047 : Nat := 118140960795 + 1051047 * 2 ^ 59
def prefixEnd_1051047 : Nat := 4983230072969 + 3 ^ 40 * 1051047 * 2
def baseEnd_1051047 : Nat := 239863245096113114435035

theorem tailTrace_1051047 : CollatzResearch.WordTrace tailWord_1051047 prefixEnd_1051047 239863245096113114435035 := by
  unfold tailWord_1051047
  simp only [CollatzResearch.WordTrace]
  refine ⟨38334833423243698381623395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25556555615495798921082263 38334833423243698381623395)
  ·
    refine ⟨57502250134865547572435093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38334833423243698381623395 57502250134865547572435093)
    ·
      refine ⟨2695417975071822542457895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57502250134865547572435093 2695417975071822542457895)
      ·
        refine ⟨4043126962607733813686843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695417975071822542457895 4043126962607733813686843)
        ·
          refine ⟨6064690443911600720530265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4043126962607733813686843 6064690443911600720530265)
          ·
            refine ⟨4548517832933700540397699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064690443911600720530265 4548517832933700540397699)
            ·
              refine ⟨6822776749400550810596549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548517832933700540397699 6822776749400550810596549)
              ·
                refine ⟨1279270640512603276986853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6822776749400550810596549 1279270640512603276986853)
                ·
                  refine ⟨239863245096113114435035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279270640512603276986853 239863245096113114435035)
                  ·
                    rfl

theorem cell21_1051047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_1051047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051047 prefixEnd_1051047 := by exact prefixLift 1051047
  have htrace : WordTrace (prefixWord ++ tailWord_1051047) baseStart_1051047 baseEnd_1051047 := by
    simpa [prefixWord, tailWord_1051047, baseEnd_1051047] using wordTrace_append hprefix tailTrace_1051047
  have hstable : (prefixWord ++ tailWord_1051047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051047).length < 2 ^ (prefixWord ++ tailWord_1051047).sum := by decide
  have hdescent : baseEnd_1051047 < baseStart_1051047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051109 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1051109 : Nat := 118140960795 + 1051109 * 2 ^ 59
def prefixEnd_1051109 : Nat := 4983230072969 + 3 ^ 40 * 1051109 * 2
def baseEnd_1051109 : Nat := 239877394340814784401575

theorem tailTrace_1051109 : CollatzResearch.WordTrace tailWord_1051109 prefixEnd_1051109 239877394340814784401575 := by
  unfold tailWord_1051109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38337094749019082970380381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25558063166012721980253587 38337094749019082970380381)
  ·
    refine ⟨14376410530882156113892643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38337094749019082970380381 14376410530882156113892643)
    ·
      refine ⟨21564615796323234170838965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14376410530882156113892643 21564615796323234170838965)
      ·
        refine ⟨2021682730905303203516153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21564615796323234170838965 2021682730905303203516153)
        ·
          refine ⟨1516262048178977402637115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021682730905303203516153 1516262048178977402637115)
          ·
            refine ⟨2274393072268466103955673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516262048178977402637115 2274393072268466103955673)
            ·
              refine ⟨1705794804201349577966755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274393072268466103955673 1705794804201349577966755)
              ·
                refine ⟨2558692206302024366950133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705794804201349577966755 2558692206302024366950133)
                ·
                  refine ⟨239877394340814784401575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2558692206302024366950133 239877394340814784401575)
                  ·
                    rfl

theorem cell21_1051109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1051109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051109 prefixEnd_1051109 := by exact prefixLift 1051109
  have htrace : WordTrace (prefixWord ++ tailWord_1051109) baseStart_1051109 baseEnd_1051109 := by
    simpa [prefixWord, tailWord_1051109, baseEnd_1051109] using wordTrace_append hprefix tailTrace_1051109
  have hstable : (prefixWord ++ tailWord_1051109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051109).length < 2 ^ (prefixWord ++ tailWord_1051109).sum := by decide
  have hdescent : baseEnd_1051109 < baseStart_1051109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051120 : List Nat := [2, 1, 1, 1, 3, 3, 2, 8]
def baseStart_1051120 : Nat := 118140960795 + 1051120 * 2 ^ 59
def prefixEnd_1051120 : Nat := 4983230072969 + 3 ^ 40 * 1051120 * 2
def baseEnd_1051120 : Nat := 79959968230227069906073

theorem tailTrace_1051120 : CollatzResearch.WordTrace tailWord_1051120 prefixEnd_1051120 79959968230227069906073 := by
  unfold tailWord_1051120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19168747975989615924515407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25558330634652821232687209 19168747975989615924515407)
  ·
    refine ⟨28753121963984423886773111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19168747975989615924515407 28753121963984423886773111)
    ·
      refine ⟨43129682945976635830159667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28753121963984423886773111 43129682945976635830159667)
      ·
        refine ⟨64694524418964953745239501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43129682945976635830159667 64694524418964953745239501)
        ·
          refine ⟨24260446657111857654464813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64694524418964953745239501 24260446657111857654464813)
          ·
            refine ⟨9097667496416946620424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24260446657111857654464813 9097667496416946620424305)
            ·
              refine ⟨6823250622312709965318229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9097667496416946620424305 6823250622312709965318229)
              ·
                refine ⟨79959968230227069906073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6823250622312709965318229 79959968230227069906073)
                ·
                  rfl

theorem cell21_1051120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_1051120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051120 prefixEnd_1051120 := by exact prefixLift 1051120
  have htrace : WordTrace (prefixWord ++ tailWord_1051120) baseStart_1051120 baseEnd_1051120 := by
    simpa [prefixWord, tailWord_1051120, baseEnd_1051120] using wordTrace_append hprefix tailTrace_1051120
  have hstable : (prefixWord ++ tailWord_1051120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051120).length < 2 ^ (prefixWord ++ tailWord_1051120).sum := by decide
  have hdescent : baseEnd_1051120 < baseStart_1051120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051123 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 4]
def baseStart_1051123 : Nat := 118140960795 + 1051123 * 2 ^ 59
def prefixEnd_1051123 : Nat := 4983230072969 + 3 ^ 40 * 1051123 * 2
def baseEnd_1051123 : Nat := 239880589331553871168213

theorem tailTrace_1051123 : CollatzResearch.WordTrace tailWord_1051123 prefixEnd_1051123 239880589331553871168213 := by
  unfold tailWord_1051123
  simp only [CollatzResearch.WordTrace]
  refine ⟨38337605370968363361390023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25558403580645575574260015 38337605370968363361390023)
  ·
    refine ⟨57506408056452545042085035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38337605370968363361390023 57506408056452545042085035)
    ·
      refine ⟨86259612084678817563127553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57506408056452545042085035 86259612084678817563127553)
      ·
        refine ⟨64694709063509113172345665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86259612084678817563127553 64694709063509113172345665)
        ·
          refine ⟨48521031797631834879259249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64694709063509113172345665 48521031797631834879259249)
          ·
            refine ⟨36390773848223876159444437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48521031797631834879259249 36390773848223876159444437)
            ·
              refine ⟨852908762067747097486979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36390773848223876159444437 852908762067747097486979)
              ·
                refine ⟨1279363143101620646230469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852908762067747097486979 1279363143101620646230469)
                ·
                  refine ⟨239880589331553871168213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279363143101620646230469 239880589331553871168213)
                  ·
                    rfl

theorem cell21_1051123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_1051123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051123 prefixEnd_1051123 := by exact prefixLift 1051123
  have htrace : WordTrace (prefixWord ++ tailWord_1051123) baseStart_1051123 baseEnd_1051123 := by
    simpa [prefixWord, tailWord_1051123, baseEnd_1051123] using wordTrace_append hprefix tailTrace_1051123
  have hstable : (prefixWord ++ tailWord_1051123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051123).length < 2 ^ (prefixWord ++ tailWord_1051123).sum := by decide
  have hdescent : baseEnd_1051123 < baseStart_1051123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051137 : List Nat := [1, 2, 4, 1, 3, 2, 1, 7]
def baseStart_1051137 : Nat := 118140960795 + 1051137 * 2 ^ 59
def prefixEnd_1051137 : Nat := 4983230072969 + 3 ^ 40 * 1051137 * 2
def baseEnd_1051137 : Nat := 79961261440764319311617

theorem tailTrace_1051137 : CollatzResearch.WordTrace tailWord_1051137 prefixEnd_1051137 79961261440764319311617 := by
  unfold tailWord_1051137
  simp only [CollatzResearch.WordTrace]
  refine ⟨38338115992917643752399665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25558743995278429168266443 38338115992917643752399665)
  ·
    refine ⟨28753586994688232814299749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38338115992917643752399665 28753586994688232814299749)
    ·
      refine ⟨5391297561504043652681203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28753586994688232814299749 5391297561504043652681203)
      ·
        refine ⟨8086946342256065479021805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391297561504043652681203 8086946342256065479021805)
        ·
          refine ⟨3032604878346024554633177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8086946342256065479021805 3032604878346024554633177)
          ·
            refine ⟨2274453658759518415974883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3032604878346024554633177 2274453658759518415974883)
            ·
              refine ⟨3411680488139277623962325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274453658759518415974883 3411680488139277623962325)
              ·
                refine ⟨79961261440764319311617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3411680488139277623962325 79961261440764319311617)
                ·
                  rfl

theorem cell21_1051137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_1051137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051137 prefixEnd_1051137 := by exact prefixLift 1051137
  have htrace : WordTrace (prefixWord ++ tailWord_1051137) baseStart_1051137 baseEnd_1051137 := by
    simpa [prefixWord, tailWord_1051137, baseEnd_1051137] using wordTrace_append hprefix tailTrace_1051137
  have hstable : (prefixWord ++ tailWord_1051137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051137).length < 2 ^ (prefixWord ++ tailWord_1051137).sum := by decide
  have hdescent : baseEnd_1051137 < baseStart_1051137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051143 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 3]
def baseStart_1051143 : Nat := 118140960795 + 1051143 * 2 ^ 59
def prefixEnd_1051143 : Nat := 4983230072969 + 3 ^ 40 * 1051143 * 2
def baseEnd_1051143 : Nat := 239885153604038280834839

theorem tailTrace_1051143 : CollatzResearch.WordTrace tailWord_1051143 prefixEnd_1051143 239885153604038280834839 := by
  unfold tailWord_1051143
  simp only [CollatzResearch.WordTrace]
  refine ⟨38338334830895906777118083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25558889887263937851412055 38338334830895906777118083)
  ·
    refine ⟨57507502246343860165677125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38338334830895906777118083 57507502246343860165677125)
    ·
      refine ⟨10782656671189473781064461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57507502246343860165677125 10782656671189473781064461)
      ·
        refine ⟨4043496251696052667899173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10782656671189473781064461 4043496251696052667899173)
        ·
          refine ⟨758155547193009875231095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4043496251696052667899173 758155547193009875231095)
          ·
            refine ⟨1137233320789514812846643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758155547193009875231095 1137233320789514812846643)
            ·
              refine ⟨1705849981184272219269965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137233320789514812846643 1705849981184272219269965)
              ·
                refine ⟨639693742944102082226237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705849981184272219269965 639693742944102082226237)
                ·
                  refine ⟨239885153604038280834839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639693742944102082226237 239885153604038280834839)
                  ·
                    rfl

theorem cell21_1051143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 3].length) (baseStart_1051143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051143 prefixEnd_1051143 := by exact prefixLift 1051143
  have htrace : WordTrace (prefixWord ++ tailWord_1051143) baseStart_1051143 baseEnd_1051143 := by
    simpa [prefixWord, tailWord_1051143, baseEnd_1051143] using wordTrace_append hprefix tailTrace_1051143
  have hstable : (prefixWord ++ tailWord_1051143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051143).length < 2 ^ (prefixWord ++ tailWord_1051143).sum := by decide
  have hdescent : baseEnd_1051143 < baseStart_1051143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051213 : List Nat := [1, 6, 1, 1, 2, 10]
def baseStart_1051213 : Nat := 118140960795 + 1051213 * 2 ^ 59
def prefixEnd_1051213 : Nat := 4983230072969 + 3 ^ 40 * 1051213 * 2
def baseEnd_1051213 : Nat := 8885226983619767209927

theorem tailTrace_1051213 : CollatzResearch.WordTrace tailWord_1051213 prefixEnd_1051213 8885226983619767209927 := by
  unfold tailWord_1051213
  simp only [CollatzResearch.WordTrace]
  refine ⟨38340887940642308732166293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560591960428205821444195 38340887940642308732166293)
  ·
    refine ⟨1797229122217608221820295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38340887940642308732166293 1797229122217608221820295)
    ·
      refine ⟨2695843683326412332730443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797229122217608221820295 2695843683326412332730443)
      ·
        refine ⟨4043765524989618499095665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695843683326412332730443 4043765524989618499095665)
        ·
          refine ⟨3032824143742213874321749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4043765524989618499095665 3032824143742213874321749)
          ·
            refine ⟨8885226983619767209927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3032824143742213874321749 8885226983619767209927)
            ·
              rfl

theorem cell21_1051213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 10].length) (baseStart_1051213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051213 prefixEnd_1051213 := by exact prefixLift 1051213
  have htrace : WordTrace (prefixWord ++ tailWord_1051213) baseStart_1051213 baseEnd_1051213 := by
    simpa [prefixWord, tailWord_1051213, baseEnd_1051213] using wordTrace_append hprefix tailTrace_1051213
  have hstable : (prefixWord ++ tailWord_1051213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051213).length < 2 ^ (prefixWord ++ tailWord_1051213).sum := by decide
  have hdescent : baseEnd_1051213 < baseStart_1051213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051241 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_1051241 : Nat := 118140960795 + 1051241 * 2 ^ 59
def prefixEnd_1051241 : Nat := 4983230072969 + 3 ^ 40 * 1051241 * 2
def baseEnd_1051241 : Nat := 239907518539211888201305

theorem tailTrace_1051241 : CollatzResearch.WordTrace tailWord_1051241 prefixEnd_1051241 239907518539211888201305 := by
  unfold tailWord_1051241
  simp only [CollatzResearch.WordTrace]
  refine ⟨38341909184540869514185577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25561272789693913009457051 38341909184540869514185577)
  ·
    refine ⟨28756431888405652135639183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38341909184540869514185577 28756431888405652135639183)
    ·
      refine ⟨43134647832608478203458775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28756431888405652135639183 43134647832608478203458775)
      ·
        refine ⟨64701971748912717305188163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43134647832608478203458775 64701971748912717305188163)
        ·
          refine ⟨97052957623369075957782245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64701971748912717305188163 97052957623369075957782245)
          ·
            refine ⟨18197429554381701742084171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97052957623369075957782245 18197429554381701742084171)
            ·
              refine ⟨27296144331572552613126257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18197429554381701742084171 27296144331572552613126257)
              ·
                refine ⟨20472108248679414459844693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27296144331572552613126257 20472108248679414459844693)
                ·
                  refine ⟨239907518539211888201305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20472108248679414459844693 239907518539211888201305)
                  ·
                    rfl

theorem cell21_1051241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_1051241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051241 prefixEnd_1051241 := by exact prefixLift 1051241
  have htrace : WordTrace (prefixWord ++ tailWord_1051241) baseStart_1051241 baseEnd_1051241 := by
    simpa [prefixWord, tailWord_1051241, baseEnd_1051241] using wordTrace_append hprefix tailTrace_1051241
  have hstable : (prefixWord ++ tailWord_1051241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051241).length < 2 ^ (prefixWord ++ tailWord_1051241).sum := by decide
  have hdescent : baseEnd_1051241 < baseStart_1051241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051292 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_1051292 : Nat := 118140960795 + 1051292 * 2 ^ 59
def prefixEnd_1051292 : Nat := 4983230072969 + 3 ^ 40 * 1051292 * 2
def baseEnd_1051292 : Nat := 239919157434047132851201

theorem tailTrace_1051292 : CollatzResearch.WordTrace tailWord_1051292 prefixEnd_1051292 239919157434047132851201 := by
  unfold tailWord_1051292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19171884653678052612146065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25562512871570736816194753 19171884653678052612146065)
  ·
    refine ⟨14378913490258539459109549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19171884653678052612146065 14378913490258539459109549)
    ·
      refine ⟨5392092558846952297166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14378913490258539459109549 5392092558846952297166081)
      ·
        refine ⟨4044069419135214222874561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5392092558846952297166081 4044069419135214222874561)
        ·
          refine ⟨3033052064351410667155921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4044069419135214222874561 3033052064351410667155921)
          ·
            refine ⟨2274789048263558000366941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3033052064351410667155921 2274789048263558000366941)
            ·
              refine ⟨853045893098834250137603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2274789048263558000366941 853045893098834250137603)
              ·
                refine ⟨1279568839648251375206405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853045893098834250137603 1279568839648251375206405)
                ·
                  refine ⟨239919157434047132851201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279568839648251375206405 239919157434047132851201)
                  ·
                    rfl

theorem cell21_1051292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_1051292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051292 prefixEnd_1051292 := by exact prefixLift 1051292
  have htrace : WordTrace (prefixWord ++ tailWord_1051292) baseStart_1051292 baseEnd_1051292 := by
    simpa [prefixWord, tailWord_1051292, baseEnd_1051292] using wordTrace_append hprefix tailTrace_1051292
  have hstable : (prefixWord ++ tailWord_1051292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051292).length < 2 ^ (prefixWord ++ tailWord_1051292).sum := by decide
  have hdescent : baseEnd_1051292 < baseStart_1051292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051351 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 4]
def baseStart_1051351 : Nat := 118140960795 + 1051351 * 2 ^ 59
def prefixEnd_1051351 : Nat := 4983230072969 + 3 ^ 40 * 1051351 * 2
def baseEnd_1051351 : Nat := 239932622037876141367747

theorem tailTrace_1051351 : CollatzResearch.WordTrace tailWord_1051351 prefixEnd_1051351 239932622037876141367747 := by
  unfold tailWord_1051351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38345921214142358300689907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25563947476094905533793271 38345921214142358300689907)
  ·
    refine ⟨57518881821213537451034861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38345921214142358300689907 57518881821213537451034861)
    ·
      refine ⟨21569580682955076544138073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57518881821213537451034861 21569580682955076544138073)
      ·
        refine ⟨16177185512216307408103555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21569580682955076544138073 16177185512216307408103555)
        ·
          refine ⟨24265778268324461112155333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16177185512216307408103555 24265778268324461112155333)
          ·
            refine ⟨4549833425310836458529125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24265778268324461112155333 4549833425310836458529125)
            ·
              refine ⟨853093767245781835974211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4549833425310836458529125 853093767245781835974211)
              ·
                refine ⟨1279640650868672753961317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853093767245781835974211 1279640650868672753961317)
                ·
                  refine ⟨239932622037876141367747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1279640650868672753961317 239932622037876141367747)
                  ·
                    rfl

theorem cell21_1051351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_1051351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051351 prefixEnd_1051351 := by exact prefixLift 1051351
  have htrace : WordTrace (prefixWord ++ tailWord_1051351) baseStart_1051351 baseEnd_1051351 := by
    simpa [prefixWord, tailWord_1051351, baseEnd_1051351] using wordTrace_append hprefix tailTrace_1051351
  have hstable : (prefixWord ++ tailWord_1051351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051351).length < 2 ^ (prefixWord ++ tailWord_1051351).sum := by decide
  have hdescent : baseEnd_1051351 < baseStart_1051351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051455 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_1051455 : Nat := 118140960795 + 1051455 * 2 ^ 59
def prefixEnd_1051455 : Nat := 4983230072969 + 3 ^ 40 * 1051455 * 2
def baseEnd_1051455 : Nat := 239956356254795071634201

theorem tailTrace_1051455 : CollatzResearch.WordTrace tailWord_1051455 prefixEnd_1051455 239956356254795071634201 := by
  unfold tailWord_1051455
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349714405765584062475819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25566476270510389374983879 38349714405765584062475819)
  ·
    refine ⟨57524571608648376093713729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38349714405765584062475819 57524571608648376093713729)
    ·
      refine ⟨43143428706486282070285297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57524571608648376093713729 43143428706486282070285297)
      ·
        refine ⟨32357571529864711552713973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43143428706486282070285297 32357571529864711552713973)
        ·
          refine ⟨3033522330924816708066935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32357571529864711552713973 3033522330924816708066935)
          ·
            refine ⟨4550283496387225062100403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033522330924816708066935 4550283496387225062100403)
            ·
              refine ⟨6825425244580837593150605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550283496387225062100403 6825425244580837593150605)
              ·
                refine ⟨2559534466717814097431477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6825425244580837593150605 2559534466717814097431477)
                ·
                  refine ⟨239956356254795071634201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2559534466717814097431477 239956356254795071634201)
                  ·
                    rfl

theorem cell21_1051455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_1051455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051455 prefixEnd_1051455 := by exact prefixLift 1051455
  have htrace : WordTrace (prefixWord ++ tailWord_1051455) baseStart_1051455 baseEnd_1051455 := by
    simpa [prefixWord, tailWord_1051455, baseEnd_1051455] using wordTrace_append hprefix tailTrace_1051455
  have hstable : (prefixWord ++ tailWord_1051455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051455).length < 2 ^ (prefixWord ++ tailWord_1051455).sum := by decide
  have hdescent : baseEnd_1051455 < baseStart_1051455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051576 : List Nat := [2, 1, 2, 1, 2, 4, 3, 6]
def baseStart_1051576 : Nat := 118140960795 + 1051576 * 2 ^ 59
def prefixEnd_1051576 : Nat := 4983230072969 + 3 ^ 40 * 1051576 * 2
def baseEnd_1051576 : Nat := 79994656701108583372429

theorem tailTrace_1051576 : CollatzResearch.WordTrace tailWord_1051576 prefixEnd_1051576 79994656701108583372429 := by
  unfold tailWord_1051576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177063819163610863815291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25569418425551481151753721 19177063819163610863815291)
  ·
    refine ⟨28765595728745416295722937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177063819163610863815291 28765595728745416295722937)
    ·
      refine ⟨21574196796559062221792203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28765595728745416295722937 21574196796559062221792203)
      ·
        refine ⟨32361295194838593332688305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21574196796559062221792203 32361295194838593332688305)
        ·
          refine ⟨24270971396128944999516229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32361295194838593332688305 24270971396128944999516229)
          ·
            refine ⟨4550807136774177187409293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24270971396128944999516229 4550807136774177187409293)
            ·
              refine ⟨1706552676290316445278485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550807136774177187409293 1706552676290316445278485)
              ·
                refine ⟨79994656701108583372429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1706552676290316445278485 79994656701108583372429)
                ·
                  rfl

theorem cell21_1051576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_1051576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051576 prefixEnd_1051576 := by exact prefixLift 1051576
  have htrace : WordTrace (prefixWord ++ tailWord_1051576) baseStart_1051576 baseEnd_1051576 := by
    simpa [prefixWord, tailWord_1051576, baseEnd_1051576] using wordTrace_append hprefix tailTrace_1051576
  have hstable : (prefixWord ++ tailWord_1051576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051576).length < 2 ^ (prefixWord ++ tailWord_1051576).sum := by decide
  have hdescent : baseEnd_1051576 < baseStart_1051576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051624 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_1051624 : Nat := 118140960795 + 1051624 * 2 ^ 59
def prefixEnd_1051624 : Nat := 4983230072969 + 3 ^ 40 * 1051624 * 2
def baseEnd_1051624 : Nat := 239994924357288333317189

theorem tailTrace_1051624 : CollatzResearch.WordTrace tailWord_1051624 prefixEnd_1051624 239994924357288333317189 := by
  unfold tailWord_1051624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177939171076662962688963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25570585561435550616918617 19177939171076662962688963)
  ·
    refine ⟨28766908756614994444033445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19177939171076662962688963 28766908756614994444033445)
    ·
      refine ⟨5393795391865311458256271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28766908756614994444033445 5393795391865311458256271)
      ·
        refine ⟨8090693087797967187384407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393795391865311458256271 8090693087797967187384407)
        ·
          refine ⟨12136039631696950781076611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090693087797967187384407 12136039631696950781076611)
          ·
            refine ⟨18204059447545426171614917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12136039631696950781076611 18204059447545426171614917)
            ·
              refine ⟨3413261146414767407177797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18204059447545426171614917 3413261146414767407177797)
              ·
                refine ⟨639986464952768888845837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3413261146414767407177797 639986464952768888845837)
                ·
                  refine ⟨239994924357288333317189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639986464952768888845837 239994924357288333317189)
                  ·
                    rfl

theorem cell21_1051624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_1051624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051624 prefixEnd_1051624 := by exact prefixLift 1051624
  have htrace : WordTrace (prefixWord ++ tailWord_1051624) baseStart_1051624 baseEnd_1051624 := by
    simpa [prefixWord, tailWord_1051624, baseEnd_1051624] using wordTrace_append hprefix tailTrace_1051624
  have hstable : (prefixWord ++ tailWord_1051624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051624).length < 2 ^ (prefixWord ++ tailWord_1051624).sum := by decide
  have hdescent : baseEnd_1051624 < baseStart_1051624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051683 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_1051683 : Nat := 118140960795 + 1051683 * 2 ^ 59
def prefixEnd_1051683 : Nat := 4983230072969 + 3 ^ 40 * 1051683 * 2
def baseEnd_1051683 : Nat := 240008388961117341833735

theorem tailTrace_1051683 : CollatzResearch.WordTrace tailWord_1051683 prefixEnd_1051683 240008388961117341833735 := by
  unfold tailWord_1051683
  simp only [CollatzResearch.WordTrace]
  refine ⟨38358030248939579001775703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25572020165959719334517135 38358030248939579001775703)
  ·
    refine ⟨57537045373409368502663555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38358030248939579001775703 57537045373409368502663555)
    ·
      refine ⟨86305568060114052753995333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57537045373409368502663555 86305568060114052753995333)
      ·
        refine ⟨16182294011271384891374125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86305568060114052753995333 16182294011271384891374125)
        ·
          refine ⟨6068360254226769334265297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16182294011271384891374125 6068360254226769334265297)
          ·
            refine ⟨4551270190670077000698973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6068360254226769334265297 4551270190670077000698973)
            ·
              refine ⟨1706726321501278875262115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4551270190670077000698973 1706726321501278875262115)
              ·
                refine ⟨2560089482251918312893173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1706726321501278875262115 2560089482251918312893173)
                ·
                  refine ⟨240008388961117341833735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2560089482251918312893173 240008388961117341833735)
                  ·
                    rfl

theorem cell21_1051683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_1051683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051683 prefixEnd_1051683 := by exact prefixLift 1051683
  have htrace : WordTrace (prefixWord ++ tailWord_1051683) baseStart_1051683 baseEnd_1051683 := by
    simpa [prefixWord, tailWord_1051683, baseEnd_1051683] using wordTrace_append hprefix tailTrace_1051683
  have hstable : (prefixWord ++ tailWord_1051683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051683).length < 2 ^ (prefixWord ++ tailWord_1051683).sum := by decide
  have hdescent : baseEnd_1051683 < baseStart_1051683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051773 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1051773 : Nat := 118140960795 + 1051773 * 2 ^ 59
def prefixEnd_1051773 : Nat := 4983230072969 + 3 ^ 40 * 1051773 * 2
def baseEnd_1051773 : Nat := 240028928187297185333551

theorem tailTrace_1051773 : CollatzResearch.WordTrace tailWord_1051773 prefixEnd_1051773 240028928187297185333551 := by
  unfold tailWord_1051773
  simp only [CollatzResearch.WordTrace]
  refine ⟨38361312818613524372551973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25574208545742349581701315 38361312818613524372551973)
  ·
    refine ⟨7192746153490035819853495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38361312818613524372551973 7192746153490035819853495)
    ·
      refine ⟨10789119230235053729780243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192746153490035819853495 10789119230235053729780243)
      ·
        refine ⟨16183678845352580594670365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10789119230235053729780243 16183678845352580594670365)
        ·
          refine ⟨6068879567007217723001387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16183678845352580594670365 6068879567007217723001387)
          ·
            refine ⟨9103319350510826584502081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068879567007217723001387 9103319350510826584502081)
            ·
              refine ⟨6827489512883119938376561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9103319350510826584502081 6827489512883119938376561)
              ·
                refine ⟨5120617134662339953782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6827489512883119938376561 5120617134662339953782421)
                ·
                  refine ⟨240028928187297185333551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5120617134662339953782421 240028928187297185333551)
                  ·
                    rfl

theorem cell21_1051773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1051773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051773 prefixEnd_1051773 := by exact prefixLift 1051773
  have htrace : WordTrace (prefixWord ++ tailWord_1051773) baseStart_1051773 baseEnd_1051773 := by
    simpa [prefixWord, tailWord_1051773, baseEnd_1051773] using wordTrace_append hprefix tailTrace_1051773
  have hstable : (prefixWord ++ tailWord_1051773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051773).length < 2 ^ (prefixWord ++ tailWord_1051773).sum := by decide
  have hdescent : baseEnd_1051773 < baseStart_1051773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051790 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_1051790 : Nat := 118140960795 + 1051790 * 2 ^ 59
def prefixEnd_1051790 : Nat := 4983230072969 + 3 ^ 40 * 1051790 * 2
def baseEnd_1051790 : Nat := 240032807818908933550183

theorem tailTrace_1051790 : CollatzResearch.WordTrace tailWord_1051790 prefixEnd_1051790 240032807818908933550183 := by
  unfold tailWord_1051790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795241607443992034490103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25574621906367957517280549 4795241607443992034490103)
  ·
    refine ⟨7192862411165988051735155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795241607443992034490103 7192862411165988051735155)
    ·
      refine ⟨10789293616748982077602733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192862411165988051735155 10789293616748982077602733)
      ·
        refine ⟨4045985106280868279101025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10789293616748982077602733 4045985106280868279101025)
        ·
          refine ⟨3034488829710651209325769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4045985106280868279101025 3034488829710651209325769)
          ·
            refine ⟨2275866622282988406994327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3034488829710651209325769 2275866622282988406994327)
            ·
              refine ⟨3413799933424482610491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275866622282988406994327 3413799933424482610491491)
              ·
                refine ⟨5120699900136723915737237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413799933424482610491491 5120699900136723915737237)
                ·
                  refine ⟨240032807818908933550183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5120699900136723915737237 240032807818908933550183)
                  ·
                    rfl

theorem cell21_1051790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_1051790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051790 prefixEnd_1051790 := by exact prefixLift 1051790
  have htrace : WordTrace (prefixWord ++ tailWord_1051790) baseStart_1051790 baseEnd_1051790 := by
    simpa [prefixWord, tailWord_1051790, baseEnd_1051790] using wordTrace_append hprefix tailTrace_1051790
  have hstable : (prefixWord ++ tailWord_1051790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051790).length < 2 ^ (prefixWord ++ tailWord_1051790).sum := by decide
  have hdescent : baseEnd_1051790 < baseStart_1051790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051821 : List Nat := [1, 5, 2, 1, 3, 1, 1, 7]
def baseStart_1051821 : Nat := 118140960795 + 1051821 * 2 ^ 59
def prefixEnd_1051821 : Nat := 4983230072969 + 3 ^ 40 * 1051821 * 2
def baseEnd_1051821 : Nat := 80013294147086589511151

theorem tailTrace_1051821 : CollatzResearch.WordTrace tailWord_1051821 prefixEnd_1051821 80013294147086589511151 := by
  unfold tailWord_1051821
  simp only [CollatzResearch.WordTrace]
  refine ⟨38363063522439628570299317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25575375681626419046866211 38363063522439628570299317)
  ·
    refine ⟨3596537205228715178465561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38363063522439628570299317 3596537205228715178465561)
    ·
      refine ⟨2697402903921536383849171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3596537205228715178465561 2697402903921536383849171)
      ·
        refine ⟨4046104355882304575773757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697402903921536383849171 4046104355882304575773757)
        ·
          refine ⟨1517289133455864215915159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4046104355882304575773757 1517289133455864215915159)
          ·
            refine ⟨2275933700183796323872739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517289133455864215915159 2275933700183796323872739)
            ·
              refine ⟨3413900550275694485809109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2275933700183796323872739 3413900550275694485809109)
              ·
                refine ⟨80013294147086589511151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3413900550275694485809109 80013294147086589511151)
                ·
                  rfl

theorem cell21_1051821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_1051821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051821 prefixEnd_1051821 := by exact prefixLift 1051821
  have htrace : WordTrace (prefixWord ++ tailWord_1051821) baseStart_1051821 baseEnd_1051821 := by
    simpa [prefixWord, tailWord_1051821, baseEnd_1051821] using wordTrace_append hprefix tailTrace_1051821
  have hstable : (prefixWord ++ tailWord_1051821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051821).length < 2 ^ (prefixWord ++ tailWord_1051821).sum := by decide
  have hdescent : baseEnd_1051821 < baseStart_1051821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051835 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 3]
def baseStart_1051835 : Nat := 118140960795 + 1051835 * 2 ^ 59
def prefixEnd_1051835 : Nat := 4983230072969 + 3 ^ 40 * 1051835 * 2
def baseEnd_1051835 : Nat := 240043077431998855300091

theorem tailTrace_1051835 : CollatzResearch.WordTrace tailWord_1051835 prefixEnd_1051835 240043077431998855300091 := by
  unfold tailWord_1051835
  simp only [CollatzResearch.WordTrace]
  refine ⟨38363574144388908961308959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25575716096259272640872639 38363574144388908961308959)
  ·
    refine ⟨57545361216583363441963439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38363574144388908961308959 57545361216583363441963439)
    ·
      refine ⟨86318041824875045162945159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57545361216583363441963439 86318041824875045162945159)
      ·
        refine ⟨129477062737312567744417739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86318041824875045162945159 129477062737312567744417739)
        ·
          refine ⟨194215594105968851616626609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129477062737312567744417739 194215594105968851616626609)
          ·
            refine ⟨145661695579476638712469957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194215594105968851616626609 145661695579476638712469957)
            ·
              refine ⟨27311567921151869758588117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145661695579476638712469957 27311567921151869758588117)
              ·
                refine ⟨640114873151996947466909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27311567921151869758588117 640114873151996947466909)
                ·
                  refine ⟨240043077431998855300091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640114873151996947466909 240043077431998855300091)
                  ·
                    rfl

theorem cell21_1051835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 3].length) (baseStart_1051835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051835 prefixEnd_1051835 := by exact prefixLift 1051835
  have htrace : WordTrace (prefixWord ++ tailWord_1051835) baseStart_1051835 baseEnd_1051835 := by
    simpa [prefixWord, tailWord_1051835, baseEnd_1051835] using wordTrace_append hprefix tailTrace_1051835
  have hstable : (prefixWord ++ tailWord_1051835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051835).length < 2 ^ (prefixWord ++ tailWord_1051835).sum := by decide
  have hdescent : baseEnd_1051835 < baseStart_1051835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051863 : List Nat := [1, 1, 3, 2, 1, 2, 3, 8]
def baseStart_1051863 : Nat := 118140960795 + 1051863 * 2 ^ 59
def prefixEnd_1051863 : Nat := 4983230072969 + 3 ^ 40 * 1051863 * 2
def baseEnd_1051863 : Nat := 80016489137825676277789

theorem tailTrace_1051863 : CollatzResearch.WordTrace tailWord_1051863 prefixEnd_1051863 80016489137825676277789 := by
  unfold tailWord_1051863
  simp only [CollatzResearch.WordTrace]
  refine ⟨38364595388287469743328243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25576396925524979828885495 38364595388287469743328243)
  ·
    refine ⟨57546893082431204614992365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38364595388287469743328243 57546893082431204614992365)
    ·
      refine ⟨21580084905911701730622137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57546893082431204614992365 21580084905911701730622137)
      ·
        refine ⟨16185063679433776297966603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21580084905911701730622137 16185063679433776297966603)
        ·
          refine ⟨24277595519150664446949905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16185063679433776297966603 24277595519150664446949905)
          ·
            refine ⟨18208196639362998335212429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24277595519150664446949905 18208196639362998335212429)
            ·
              refine ⟨6828073739761124375704661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18208196639362998335212429 6828073739761124375704661)
              ·
                refine ⟨80016489137825676277789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6828073739761124375704661 80016489137825676277789)
                ·
                  rfl

theorem cell21_1051863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_1051863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051863 prefixEnd_1051863 := by exact prefixLift 1051863
  have htrace : WordTrace (prefixWord ++ tailWord_1051863) baseStart_1051863 baseEnd_1051863 := by
    simpa [prefixWord, tailWord_1051863, baseEnd_1051863] using wordTrace_append hprefix tailTrace_1051863
  have hstable : (prefixWord ++ tailWord_1051863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051863).length < 2 ^ (prefixWord ++ tailWord_1051863).sum := by decide
  have hdescent : baseEnd_1051863 < baseStart_1051863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051956 : List Nat := [2, 5, 1, 1, 1, 1, 10]
def baseStart_1051956 : Nat := 118140960795 + 1051956 * 2 ^ 59
def prefixEnd_1051956 : Nat := 4983230072969 + 3 ^ 40 * 1051956 * 2
def baseEnd_1051956 : Nat := 26674521253392170420353

theorem tailTrace_1051956 : CollatzResearch.WordTrace tailWord_1051956 prefixEnd_1051956 26674521253392170420353 := by
  unfold tailWord_1051956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183993688475273313231861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25578658251300364417642481 19183993688475273313231861)
  ·
    refine ⟨1798499408294556873115487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19183993688475273313231861 1798499408294556873115487)
    ·
      refine ⟨2697749112441835309673231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1798499408294556873115487 2697749112441835309673231)
      ·
        refine ⟨4046623668662752964509847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697749112441835309673231 4046623668662752964509847)
        ·
          refine ⟨6069935502994129446764771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046623668662752964509847 6069935502994129446764771)
          ·
            refine ⟨9104903254491194170147157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069935502994129446764771 9104903254491194170147157)
            ·
              refine ⟨26674521253392170420353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9104903254491194170147157 26674521253392170420353)
              ·
                rfl

theorem cell21_1051956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 10].length) (baseStart_1051956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1051956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1051956 prefixEnd_1051956 := by exact prefixLift 1051956
  have htrace : WordTrace (prefixWord ++ tailWord_1051956) baseStart_1051956 baseEnd_1051956 := by
    simpa [prefixWord, tailWord_1051956, baseEnd_1051956] using wordTrace_append hprefix tailTrace_1051956
  have hstable : (prefixWord ++ tailWord_1051956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051956).length < 2 ^ (prefixWord ++ tailWord_1051956).sum := by decide
  have hdescent : baseEnd_1051956 < baseStart_1051956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052004 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1052004 : Nat := 118140960795 + 1052004 * 2 ^ 59
def prefixEnd_1052004 : Nat := 4983230072969 + 3 ^ 40 * 1052004 * 2
def baseEnd_1052004 : Nat := 240081645534492116983079

theorem tailTrace_1052004 : CollatzResearch.WordTrace tailWord_1052004 prefixEnd_1052004 240081645534492116983079 := by
  unfold tailWord_1052004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19184869040388325412105533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25579825387184433882807377 19184869040388325412105533)
  ·
    refine ⟨7194325890145622029539575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19184869040388325412105533 7194325890145622029539575)
    ·
      refine ⟨10791488835218433044309363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7194325890145622029539575 10791488835218433044309363)
      ·
        refine ⟨16187233252827649566464045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10791488835218433044309363 16187233252827649566464045)
        ·
          refine ⟨6070212469810368587424017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16187233252827649566464045 6070212469810368587424017)
          ·
            refine ⟨4552659352357776440568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6070212469810368587424017 4552659352357776440568013)
            ·
              refine ⟨1707247257134166165213005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4552659352357776440568013 1707247257134166165213005)
              ·
                refine ⟨640217721425312311954877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707247257134166165213005 640217721425312311954877)
                ·
                  refine ⟨240081645534492116983079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640217721425312311954877 240081645534492116983079)
                  ·
                    rfl

theorem cell21_1052004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1052004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052004 prefixEnd_1052004 := by exact prefixLift 1052004
  have htrace : WordTrace (prefixWord ++ tailWord_1052004) baseStart_1052004 baseEnd_1052004 := by
    simpa [prefixWord, tailWord_1052004, baseEnd_1052004] using wordTrace_append hprefix tailTrace_1052004
  have hstable : (prefixWord ++ tailWord_1052004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052004).length < 2 ^ (prefixWord ++ tailWord_1052004).sum := by decide
  have hdescent : baseEnd_1052004 < baseStart_1052004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052021 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 5]
def baseStart_1052021 : Nat := 118140960795 + 1052021 * 2 ^ 59
def prefixEnd_1052021 : Nat := 4983230072969 + 3 ^ 40 * 1052021 * 2
def baseEnd_1052021 : Nat := 240085525166103865199711

theorem tailTrace_1052021 : CollatzResearch.WordTrace tailWord_1052021 prefixEnd_1052021 240085525166103865199711 := by
  unfold tailWord_1052021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38370358121715062727579917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25580238747810041818386611 38370358121715062727579917)
  ·
    refine ⟨14388884295643148522842469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38370358121715062727579917 14388884295643148522842469)
    ·
      refine ⟨2697915805433090348032963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14388884295643148522842469 2697915805433090348032963)
      ·
        refine ⟨4046873708149635522049445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697915805433090348032963 4046873708149635522049445)
        ·
          refine ⟨758788820278056660384271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4046873708149635522049445 758788820278056660384271)
          ·
            refine ⟨1138183230417084990576407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758788820278056660384271 1138183230417084990576407)
            ·
              refine ⟨1707274845625627485864611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138183230417084990576407 1707274845625627485864611)
              ·
                refine ⟨2560912268438441228796917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707274845625627485864611 2560912268438441228796917)
                ·
                  refine ⟨240085525166103865199711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2560912268438441228796917 240085525166103865199711)
                  ·
                    rfl

theorem cell21_1052021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_1052021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052021 prefixEnd_1052021 := by exact prefixLift 1052021
  have htrace : WordTrace (prefixWord ++ tailWord_1052021) baseStart_1052021 baseEnd_1052021 := by
    simpa [prefixWord, tailWord_1052021, baseEnd_1052021] using wordTrace_append hprefix tailTrace_1052021
  have hstable : (prefixWord ++ tailWord_1052021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052021).length < 2 ^ (prefixWord ++ tailWord_1052021).sum := by decide
  have hdescent : baseEnd_1052021 < baseStart_1052021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052035 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 4]
def baseStart_1052035 : Nat := 118140960795 + 1052035 * 2 ^ 59
def prefixEnd_1052035 : Nat := 4983230072969 + 3 ^ 40 * 1052035 * 2
def baseEnd_1052035 : Nat := 240088720156842951966349

theorem tailTrace_1052035 : CollatzResearch.WordTrace tailWord_1052035 prefixEnd_1052035 240088720156842951966349 := by
  unfold tailWord_1052035
  simp only [CollatzResearch.WordTrace]
  refine ⟨38370868743664343118589559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25580579162442895412393039 38370868743664343118589559)
  ·
    refine ⟨57556303115496514677884339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38370868743664343118589559 57556303115496514677884339)
    ·
      refine ⟨86334454673244772016826509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57556303115496514677884339 86334454673244772016826509)
      ·
        refine ⟨32375420502466789506309941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86334454673244772016826509 32375420502466789506309941)
        ·
          refine ⟨3035195672106261516216557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32375420502466789506309941 3035195672106261516216557)
          ·
            refine ⟨1138198377039848068581209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3035195672106261516216557 1138198377039848068581209)
            ·
              refine ⟨853648782779886051435907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138198377039848068581209 853648782779886051435907)
              ·
                refine ⟨1280473174169829077153861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853648782779886051435907 1280473174169829077153861)
                ·
                  refine ⟨240088720156842951966349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1280473174169829077153861 240088720156842951966349)
                  ·
                    rfl

theorem cell21_1052035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_1052035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052035 prefixEnd_1052035 := by exact prefixLift 1052035
  have htrace : WordTrace (prefixWord ++ tailWord_1052035) baseStart_1052035 baseEnd_1052035 := by
    simpa [prefixWord, tailWord_1052035, baseEnd_1052035] using wordTrace_append hprefix tailTrace_1052035
  have hstable : (prefixWord ++ tailWord_1052035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052035).length < 2 ^ (prefixWord ++ tailWord_1052035).sum := by decide
  have hdescent : baseEnd_1052035 < baseStart_1052035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052184 : List Nat := [2, 1, 2, 3, 4, 2, 7]
def baseStart_1052184 : Nat := 118140960795 + 1052184 * 2 ^ 59
def prefixEnd_1052184 : Nat := 4983230072969 + 3 ^ 40 * 1052184 * 2
def baseEnd_1052184 : Nat := 26680302665205755998079

theorem tailTrace_1052184 : CollatzResearch.WordTrace tailWord_1052184 prefixEnd_1052184 26680302665205755998079 := by
  unfold tailWord_1052184
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188151610062270782881803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25584202146749694377175737 19188151610062270782881803)
  ·
    refine ⟨28782227415093406174322705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19188151610062270782881803 28782227415093406174322705)
    ·
      refine ⟨21586670561320054630742029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28782227415093406174322705 21586670561320054630742029)
      ·
        refine ⟨8095001460495020486528261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21586670561320054630742029 8095001460495020486528261)
        ·
          refine ⟨1517812773842816341224049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8095001460495020486528261 1517812773842816341224049)
          ·
            refine ⟨1138359580382112255918037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517812773842816341224049 1138359580382112255918037)
            ·
              refine ⟨26680302665205755998079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1138359580382112255918037 26680302665205755998079)
              ·
                rfl

theorem cell21_1052184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 7].length) (baseStart_1052184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052184 prefixEnd_1052184 := by exact prefixLift 1052184
  have htrace : WordTrace (prefixWord ++ tailWord_1052184) baseStart_1052184 baseEnd_1052184 := by
    simpa [prefixWord, tailWord_1052184, baseEnd_1052184] using wordTrace_append hprefix tailTrace_1052184
  have hstable : (prefixWord ++ tailWord_1052184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052184).length < 2 ^ (prefixWord ++ tailWord_1052184).sum := by decide
  have hdescent : baseEnd_1052184 < baseStart_1052184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052260 : List Nat := [2, 3, 1, 1, 2, 5, 1, 6]
def baseStart_1052260 : Nat := 118140960795 + 1052260 * 2 ^ 59
def prefixEnd_1052260 : Nat := 4983230072969 + 3 ^ 40 * 1052260 * 2
def baseEnd_1052260 : Nat := 80046689407430853571963

theorem tailTrace_1052260 : CollatzResearch.WordTrace tailWord_1052260 prefixEnd_1052260 80046689407430853571963 := by
  unfold tailWord_1052260
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189537583924603272765117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25586050111899471030353489 19189537583924603272765117)
  ·
    refine ⟨7196076593971726227286919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19189537583924603272765117 7196076593971726227286919)
    ·
      refine ⟨10794114890957589340930379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7196076593971726227286919 10794114890957589340930379)
      ·
        refine ⟨16191172336436384011395569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794114890957589340930379 16191172336436384011395569)
        ·
          refine ⟨12143379252327288008546677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16191172336436384011395569 12143379252327288008546677)
          ·
            refine ⟨1138441804905683250801251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12143379252327288008546677 1138441804905683250801251)
            ·
              refine ⟨1707662707358524876201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138441804905683250801251 1707662707358524876201877)
              ·
                refine ⟨80046689407430853571963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1707662707358524876201877 80046689407430853571963)
                ·
                  rfl

theorem cell21_1052260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_1052260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052260 prefixEnd_1052260 := by exact prefixLift 1052260
  have htrace : WordTrace (prefixWord ++ tailWord_1052260) baseStart_1052260 baseEnd_1052260 := by
    simpa [prefixWord, tailWord_1052260, baseEnd_1052260] using wordTrace_append hprefix tailTrace_1052260
  have hstable : (prefixWord ++ tailWord_1052260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052260).length < 2 ^ (prefixWord ++ tailWord_1052260).sum := by decide
  have hdescent : baseEnd_1052260 < baseStart_1052260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052274 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1052274 : Nat := 118140960795 + 1052274 * 2 ^ 59
def prefixEnd_1052274 : Nat := 4983230072969 + 3 ^ 40 * 1052274 * 2
def baseEnd_1052274 : Nat := 240143263213031647482527

theorem tailTrace_1052274 : CollatzResearch.WordTrace tailWord_1052274 prefixEnd_1052274 240143263213031647482527 := by
  unfold tailWord_1052274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594896447449621734134969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25586390526532324624359917 9594896447449621734134969)
  ·
    refine ⟨7196172335587216300601227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9594896447449621734134969 7196172335587216300601227)
    ·
      refine ⟨10794258503380824450901841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7196172335587216300601227 10794258503380824450901841)
      ·
        refine ⟨8095693877535618338176381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10794258503380824450901841 8095693877535618338176381)
        ·
          refine ⟨3035885204075856876816143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8095693877535618338176381 3035885204075856876816143)
          ·
            refine ⟨4553827806113785315224215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035885204075856876816143 4553827806113785315224215)
            ·
              refine ⟨6830741709170677972836323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4553827806113785315224215 6830741709170677972836323)
              ·
                refine ⟨10246112563756016959254485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6830741709170677972836323 10246112563756016959254485)
                ·
                  refine ⟨240143263213031647482527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10246112563756016959254485 240143263213031647482527)
                  ·
                    rfl

theorem cell21_1052274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1052274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052274 prefixEnd_1052274 := by exact prefixLift 1052274
  have htrace : WordTrace (prefixWord ++ tailWord_1052274) baseStart_1052274 baseEnd_1052274 := by
    simpa [prefixWord, tailWord_1052274, baseEnd_1052274] using wordTrace_append hprefix tailTrace_1052274
  have hstable : (prefixWord ++ tailWord_1052274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052274).length < 2 ^ (prefixWord ++ tailWord_1052274).sum := by decide
  have hdescent : baseEnd_1052274 < baseStart_1052274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052277 : List Nat := [1, 3, 4, 2, 1, 2, 3, 5]
def baseStart_1052277 : Nat := 118140960795 + 1052277 * 2 ^ 59
def prefixEnd_1052277 : Nat := 4983230072969 + 3 ^ 40 * 1052277 * 2
def baseEnd_1052277 : Nat := 80047982617968102977507

theorem tailTrace_1052277 : CollatzResearch.WordTrace tailWord_1052277 prefixEnd_1052277 80047982617968102977507 := by
  unfold tailWord_1052277
  simp only [CollatzResearch.WordTrace]
  refine ⟨38379695208787618448899085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25586463472525078965932723 38379695208787618448899085)
  ·
    refine ⟨14392385703295356918337157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38379695208787618448899085 14392385703295356918337157)
    ·
      refine ⟨2698572319367879422188217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14392385703295356918337157 2698572319367879422188217)
      ·
        refine ⟨2023929239525909566641163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2698572319367879422188217 2023929239525909566641163)
        ·
          refine ⟨3035893859288864349961745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023929239525909566641163 3035893859288864349961745)
          ·
            refine ⟨2276920394466648262471309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035893859288864349961745 2276920394466648262471309)
            ·
              refine ⟨853845147924993098426741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2276920394466648262471309 853845147924993098426741)
              ·
                refine ⟨80047982617968102977507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 853845147924993098426741 80047982617968102977507)
                ·
                  rfl

theorem cell21_1052277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 5].length) (baseStart_1052277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052277 prefixEnd_1052277 := by exact prefixLift 1052277
  have htrace : WordTrace (prefixWord ++ tailWord_1052277) baseStart_1052277 baseEnd_1052277 := by
    simpa [prefixWord, tailWord_1052277, baseEnd_1052277] using wordTrace_append hprefix tailTrace_1052277
  have hstable : (prefixWord ++ tailWord_1052277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052277).length < 2 ^ (prefixWord ++ tailWord_1052277).sum := by decide
  have hdescent : baseEnd_1052277 < baseStart_1052277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052288 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_1052288 : Nat := 118140960795 + 1052288 * 2 ^ 59
def prefixEnd_1052288 : Nat := 4983230072969 + 3 ^ 40 * 1052288 * 2
def baseEnd_1052288 : Nat := 240146458203770734249165

theorem tailTrace_1052288 : CollatzResearch.WordTrace tailWord_1052288 prefixEnd_1052288 240146458203770734249165 := by
  unfold tailWord_1052288
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190048205873883663774759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25586730941165178218366345 19190048205873883663774759)
  ·
    refine ⟨28785072308810825495662139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19190048205873883663774759 28785072308810825495662139)
    ·
      refine ⟨43177608463216238243493209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28785072308810825495662139 43177608463216238243493209)
      ·
        refine ⟨32383206347412178682619907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43177608463216238243493209 32383206347412178682619907)
        ·
          refine ⟨48574809521118268023929861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32383206347412178682619907 48574809521118268023929861)
          ·
            refine ⟨9107776785209675254486849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48574809521118268023929861 9107776785209675254486849)
            ·
              refine ⟨6830832588907256440865137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9107776785209675254486849 6830832588907256440865137)
              ·
                refine ⟨5123124441680442330648853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6830832588907256440865137 5123124441680442330648853)
                ·
                  refine ⟨240146458203770734249165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5123124441680442330648853 240146458203770734249165)
                  ·
                    rfl

theorem cell21_1052288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_1052288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052288 prefixEnd_1052288 := by exact prefixLift 1052288
  have htrace : WordTrace (prefixWord ++ tailWord_1052288) baseStart_1052288 baseEnd_1052288 := by
    simpa [prefixWord, tailWord_1052288, baseEnd_1052288] using wordTrace_append hprefix tailTrace_1052288
  have hstable : (prefixWord ++ tailWord_1052288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052288).length < 2 ^ (prefixWord ++ tailWord_1052288).sum := by decide
  have hdescent : baseEnd_1052288 < baseStart_1052288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052308 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1052308 : Nat := 118140960795 + 1052308 * 2 ^ 59
def prefixEnd_1052308 : Nat := 4983230072969 + 3 ^ 40 * 1052308 * 2
def baseEnd_1052308 : Nat := 240151022476255143915791

theorem tailTrace_1052308 : CollatzResearch.WordTrace tailWord_1052308 prefixEnd_1052308 240151022476255143915791 := by
  unfold tailWord_1052308
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190412935837655371638789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25587217247783540495518385 19190412935837655371638789)
  ·
    refine ⟨3598202425469560382182273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19190412935837655371638789 3598202425469560382182273)
    ·
      refine ⟨2698651819102170286636705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3598202425469560382182273 2698651819102170286636705)
      ·
        refine ⟨2023988864326627714977529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2698651819102170286636705 2023988864326627714977529)
        ·
          refine ⟨1517991648244970786233147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2023988864326627714977529 1517991648244970786233147)
          ·
            refine ⟨2276987472367456179349721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517991648244970786233147 2276987472367456179349721)
            ·
              refine ⟨1707740604275592134512291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276987472367456179349721 1707740604275592134512291)
              ·
                refine ⟨2561610906413388201768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707740604275592134512291 2561610906413388201768437)
                ·
                  refine ⟨240151022476255143915791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561610906413388201768437 240151022476255143915791)
                  ·
                    rfl

theorem cell21_1052308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1052308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052308 prefixEnd_1052308 := by exact prefixLift 1052308
  have htrace : WordTrace (prefixWord ++ tailWord_1052308) baseStart_1052308 baseEnd_1052308 := by
    simpa [prefixWord, tailWord_1052308, baseEnd_1052308] using wordTrace_append hprefix tailTrace_1052308
  have hstable : (prefixWord ++ tailWord_1052308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052308).length < 2 ^ (prefixWord ++ tailWord_1052308).sum := by decide
  have hdescent : baseEnd_1052308 < baseStart_1052308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052328 : List Nat := [2, 1, 7, 1, 2, 1, 2, 5]
def baseStart_1052328 : Nat := 118140960795 + 1052328 * 2 ^ 59
def prefixEnd_1052328 : Nat := 4983230072969 + 3 ^ 40 * 1052328 * 2
def baseEnd_1052328 : Nat := 80051862249579851194139

theorem tailTrace_1052328 : CollatzResearch.WordTrace tailWord_1052328 prefixEnd_1052328 80051862249579851194139 := by
  unfold tailWord_1052328
  simp only [CollatzResearch.WordTrace]
  refine ⟨19190777665801427079502819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25587703554401902772670425 19190777665801427079502819)
  ·
    refine ⟨28786166498702140619254229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19190777665801427079502819 28786166498702140619254229)
    ·
      refine ⟨674675777313331420763771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28786166498702140619254229 674675777313331420763771)
      ·
        refine ⟨1012013665969997131145657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674675777313331420763771 1012013665969997131145657)
        ·
          refine ⟨759010249477497848359243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012013665969997131145657 759010249477497848359243)
          ·
            refine ⟨1138515374216246772538865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759010249477497848359243 1138515374216246772538865)
            ·
              refine ⟨853886530662185079404149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138515374216246772538865 853886530662185079404149)
              ·
                refine ⟨80051862249579851194139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 853886530662185079404149 80051862249579851194139)
                ·
                  rfl

theorem cell21_1052328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_1052328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052328 prefixEnd_1052328 := by exact prefixLift 1052328
  have htrace : WordTrace (prefixWord ++ tailWord_1052328) baseStart_1052328 baseEnd_1052328 := by
    simpa [prefixWord, tailWord_1052328, baseEnd_1052328] using wordTrace_append hprefix tailTrace_1052328
  have hstable : (prefixWord ++ tailWord_1052328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052328).length < 2 ^ (prefixWord ++ tailWord_1052328).sum := by decide
  have hdescent : baseEnd_1052328 < baseStart_1052328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052342 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1052342 : Nat := 118140960795 + 1052342 * 2 ^ 59
def prefixEnd_1052342 : Nat := 4983230072969 + 3 ^ 40 * 1052342 * 2
def baseEnd_1052342 : Nat := 240158781739478640349055

theorem tailTrace_1052342 : CollatzResearch.WordTrace tailWord_1052342 prefixEnd_1052342 240158781739478640349055 := by
  unfold tailWord_1052342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398879122097008409375955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25588043969034756366676853 2398879122097008409375955)
  ·
    refine ⟨3598318683145512614063933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398879122097008409375955 3598318683145512614063933)
    ·
      refine ⟨1349369506179567230273975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3598318683145512614063933 1349369506179567230273975)
      ·
        refine ⟨2024054259269350845410963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349369506179567230273975 2024054259269350845410963)
        ·
          refine ⟨3036081388904026268116445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024054259269350845410963 3036081388904026268116445)
          ·
            refine ⟨1138530520839009850543667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3036081388904026268116445 1138530520839009850543667)
            ·
              refine ⟨1707795781258514775815501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138530520839009850543667 1707795781258514775815501)
              ·
                refine ⟨640423417971943040930813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1707795781258514775815501 640423417971943040930813)
                ·
                  refine ⟨240158781739478640349055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640423417971943040930813 240158781739478640349055)
                  ·
                    rfl

theorem cell21_1052342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1052342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052342 prefixEnd_1052342 := by exact prefixLift 1052342
  have htrace : WordTrace (prefixWord ++ tailWord_1052342) baseStart_1052342 baseEnd_1052342 := by
    simpa [prefixWord, tailWord_1052342, baseEnd_1052342] using wordTrace_append hprefix tailTrace_1052342
  have hstable : (prefixWord ++ tailWord_1052342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052342).length < 2 ^ (prefixWord ++ tailWord_1052342).sum := by decide
  have hdescent : baseEnd_1052342 < baseStart_1052342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052474 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_1052474 : Nat := 118140960795 + 1052474 * 2 ^ 59
def prefixEnd_1052474 : Nat := 4983230072969 + 3 ^ 40 * 1052474 * 2
def baseEnd_1052474 : Nat := 240188905937875744148785

theorem tailTrace_1052474 : CollatzResearch.WordTrace tailWord_1052474 prefixEnd_1052474 240188905937875744148785 := by
  unfold tailWord_1052474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596720097268480273455119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25591253592715947395880317 9596720097268480273455119)
  ·
    refine ⟨14395080145902720410182679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9596720097268480273455119 14395080145902720410182679)
    ·
      refine ⟨21592620218854080615274019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14395080145902720410182679 21592620218854080615274019)
      ·
        refine ⟨32388930328281120922911029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21592620218854080615274019 32388930328281120922911029)
        ·
          refine ⟨3036462218276355086522909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32388930328281120922911029 3036462218276355086522909)
          ·
            refine ⟨1138673331853633157446091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3036462218276355086522909 1138673331853633157446091)
            ·
              refine ⟨1708009997780449736169137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138673331853633157446091 1708009997780449736169137)
              ·
                refine ⟨1281007498335337302126853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708009997780449736169137 1281007498335337302126853)
                ·
                  refine ⟨240188905937875744148785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281007498335337302126853 240188905937875744148785)
                  ·
                    rfl

theorem cell21_1052474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_1052474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052474 prefixEnd_1052474 := by exact prefixLift 1052474
  have htrace : WordTrace (prefixWord ++ tailWord_1052474) baseStart_1052474 baseEnd_1052474 := by
    simpa [prefixWord, tailWord_1052474, baseEnd_1052474] using wordTrace_append hprefix tailTrace_1052474
  have hstable : (prefixWord ++ tailWord_1052474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052474).length < 2 ^ (prefixWord ++ tailWord_1052474).sum := by decide
  have hdescent : baseEnd_1052474 < baseStart_1052474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052533 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1052533 : Nat := 118140960795 + 1052533 * 2 ^ 59
def prefixEnd_1052533 : Nat := 4983230072969 + 3 ^ 40 * 1052533 * 2
def baseEnd_1052533 : Nat := 240202370541704752665331

theorem tailTrace_1052533 : CollatzResearch.WordTrace tailWord_1052533 prefixEnd_1052533 240202370541704752665331 := by
  unfold tailWord_1052533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38389032295860174170218253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25592688197240116113478835 38389032295860174170218253)
  ·
    refine ⟨14395887110947565313831845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38389032295860174170218253 14395887110947565313831845)
    ·
      refine ⟨2699228833302668496343471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14395887110947565313831845 2699228833302668496343471)
      ·
        refine ⟨4048843249954002744515207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699228833302668496343471 4048843249954002744515207)
        ·
          refine ⟨6073264874931004116772811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048843249954002744515207 6073264874931004116772811)
          ·
            refine ⟨9109897312396506175159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6073264874931004116772811 9109897312396506175159217)
            ·
              refine ⟨6832422984297379631369413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9109897312396506175159217 6832422984297379631369413)
              ·
                refine ⟨1281079309555758680881765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6832422984297379631369413 1281079309555758680881765)
                ·
                  refine ⟨240202370541704752665331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281079309555758680881765 240202370541704752665331)
                  ·
                    rfl

theorem cell21_1052533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1052533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052533 prefixEnd_1052533 := by exact prefixLift 1052533
  have htrace : WordTrace (prefixWord ++ tailWord_1052533) baseStart_1052533 baseEnd_1052533 := by
    simpa [prefixWord, tailWord_1052533, baseEnd_1052533] using wordTrace_append hprefix tailTrace_1052533
  have hstable : (prefixWord ++ tailWord_1052533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052533).length < 2 ^ (prefixWord ++ tailWord_1052533).sum := by decide
  have hdescent : baseEnd_1052533 < baseStart_1052533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052547 : List Nat := [1, 1, 1, 3, 4, 3, 2, 6]
def baseStart_1052547 : Nat := 118140960795 + 1052547 * 2 ^ 59
def prefixEnd_1052547 : Nat := 4983230072969 + 3 ^ 40 * 1052547 * 2
def baseEnd_1052547 : Nat := 80068521844147946477323

theorem tailTrace_1052547 : CollatzResearch.WordTrace tailWord_1052547 prefixEnd_1052547 80068521844147946477323 := by
  unfold tailWord_1052547
  simp only [CollatzResearch.WordTrace]
  refine ⟨38389542917809454561227895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25593028611872969707485263 38389542917809454561227895)
  ·
    refine ⟨57584314376714181841841843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38389542917809454561227895 57584314376714181841841843)
    ·
      refine ⟨86376471565071272762762765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57584314376714181841841843 86376471565071272762762765)
      ·
        refine ⟨32391176836901727286036037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86376471565071272762762765 32391176836901727286036037)
        ·
          refine ⟨6073345656919073866131757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32391176836901727286036037 6073345656919073866131757)
          ·
            refine ⟨2277504621344652699799409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6073345656919073866131757 2277504621344652699799409)
            ·
              refine ⟨1708128466008489524849557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2277504621344652699799409 1708128466008489524849557)
              ·
                refine ⟨80068521844147946477323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1708128466008489524849557 80068521844147946477323)
                ·
                  rfl

theorem cell21_1052547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_1052547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052547 prefixEnd_1052547 := by exact prefixLift 1052547
  have htrace : WordTrace (prefixWord ++ tailWord_1052547) baseStart_1052547 baseEnd_1052547 := by
    simpa [prefixWord, tailWord_1052547, baseEnd_1052547] using wordTrace_append hprefix tailTrace_1052547
  have hstable : (prefixWord ++ tailWord_1052547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052547).length < 2 ^ (prefixWord ++ tailWord_1052547).sum := by decide
  have hdescent : baseEnd_1052547 < baseStart_1052547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052561 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 5]
def baseStart_1052561 : Nat := 118140960795 + 1052561 * 2 ^ 59
def prefixEnd_1052561 : Nat := 4983230072969 + 3 ^ 40 * 1052561 * 2
def baseEnd_1052561 : Nat := 240208760523182926198607

theorem tailTrace_1052561 : CollatzResearch.WordTrace tailWord_1052561 prefixEnd_1052561 240208760523182926198607 := by
  unfold tailWord_1052561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38390053539758734952237537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25593369026505823301491691 38390053539758734952237537)
  ·
    refine ⟨28792540154819051214178153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38390053539758734952237537 28792540154819051214178153)
    ·
      refine ⟨21594405116114288410633615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28792540154819051214178153 21594405116114288410633615)
      ·
        refine ⟨32391607674171432615950423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21594405116114288410633615 32391607674171432615950423)
        ·
          refine ⟨48587411511257148923925635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32391607674171432615950423 48587411511257148923925635)
          ·
            refine ⟨72881117266885723385888453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48587411511257148923925635 72881117266885723385888453)
            ·
              refine ⟨13665209487541073134854085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72881117266885723385888453 13665209487541073134854085)
              ·
                refine ⟨2562226778913951212785141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13665209487541073134854085 2562226778913951212785141)
                ·
                  refine ⟨240208760523182926198607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562226778913951212785141 240208760523182926198607)
                  ·
                    rfl

theorem cell21_1052561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_1052561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052561 prefixEnd_1052561 := by exact prefixLift 1052561
  have htrace : WordTrace (prefixWord ++ tailWord_1052561) baseStart_1052561 baseEnd_1052561 := by
    simpa [prefixWord, tailWord_1052561, baseEnd_1052561] using wordTrace_append hprefix tailTrace_1052561
  have hstable : (prefixWord ++ tailWord_1052561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052561).length < 2 ^ (prefixWord ++ tailWord_1052561).sum := by decide
  have hdescent : baseEnd_1052561 < baseStart_1052561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052623 : List Nat := [1, 1, 2, 1, 1, 5, 5, 5]
def baseStart_1052623 : Nat := 118140960795 + 1052623 * 2 ^ 59
def prefixEnd_1052623 : Nat := 4983230072969 + 3 ^ 40 * 1052623 * 2
def baseEnd_1052623 : Nat := 80074303255961532055049

theorem tailTrace_1052623 : CollatzResearch.WordTrace tailWord_1052623 prefixEnd_1052623 80074303255961532055049 := by
  unfold tailWord_1052623
  simp only [CollatzResearch.WordTrace]
  refine ⟨38392314865534119540994523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25594876577022746360663015 38392314865534119540994523)
  ·
    refine ⟨57588472298301179311491785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38392314865534119540994523 57588472298301179311491785)
    ·
      refine ⟨43191354223725884483618839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57588472298301179311491785 43191354223725884483618839)
      ·
        refine ⟨64787031335588826725428259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43191354223725884483618839 64787031335588826725428259)
        ·
          refine ⟨97180547003383240088142389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64787031335588826725428259 97180547003383240088142389)
          ·
            refine ⟨9110676281567178758263349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97180547003383240088142389 9110676281567178758263349)
            ·
              refine ⟨854125901396923008587189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9110676281567178758263349 854125901396923008587189)
              ·
                refine ⟨80074303255961532055049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 854125901396923008587189 80074303255961532055049)
                ·
                  rfl

theorem cell21_1052623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].length) (baseStart_1052623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052623 prefixEnd_1052623 := by exact prefixLift 1052623
  have htrace : WordTrace (prefixWord ++ tailWord_1052623) baseStart_1052623 baseEnd_1052623 := by
    simpa [prefixWord, tailWord_1052623, baseEnd_1052623] using wordTrace_append hprefix tailTrace_1052623
  have hstable : (prefixWord ++ tailWord_1052623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052623).length < 2 ^ (prefixWord ++ tailWord_1052623).sum := by decide
  have hdescent : baseEnd_1052623 < baseStart_1052623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052654 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_1052654 : Nat := 118140960795 + 1052654 * 2 ^ 59
def prefixEnd_1052654 : Nat := 4983230072969 + 3 ^ 40 * 1052654 * 2
def baseEnd_1052654 : Nat := 240229984390235431148417

theorem tailTrace_1052654 : CollatzResearch.WordTrace tailWord_1052654 prefixEnd_1052654 240229984390235431148417 := by
  unfold tailWord_1052654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799180691052726479421627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25595630352281207890248677 4799180691052726479421627)
  ·
    refine ⟨7198771036579089719132441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4799180691052726479421627 7198771036579089719132441)
    ·
      refine ⟨5399078277434317289349331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7198771036579089719132441 5399078277434317289349331)
      ·
        refine ⟨8098617416151475934023997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399078277434317289349331 8098617416151475934023997)
        ·
          refine ⟨3036981531056803475258999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8098617416151475934023997 3036981531056803475258999)
          ·
            refine ⟨4555472296585205212888499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036981531056803475258999 4555472296585205212888499)
            ·
              refine ⟨6833208444877807819332749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555472296585205212888499 6833208444877807819332749)
              ·
                refine ⟨2562453166829177932249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6833208444877807819332749 2562453166829177932249781)
                ·
                  refine ⟨240229984390235431148417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562453166829177932249781 240229984390235431148417)
                  ·
                    rfl

theorem cell21_1052654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_1052654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052654 prefixEnd_1052654 := by exact prefixLift 1052654
  have htrace : WordTrace (prefixWord ++ tailWord_1052654) baseStart_1052654 baseEnd_1052654 := by
    simpa [prefixWord, tailWord_1052654, baseEnd_1052654] using wordTrace_append hprefix tailTrace_1052654
  have hstable : (prefixWord ++ tailWord_1052654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052654).length < 2 ^ (prefixWord ++ tailWord_1052654).sum := by decide
  have hdescent : baseEnd_1052654 < baseStart_1052654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052764 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_1052764 : Nat := 118140960795 + 1052764 * 2 ^ 59
def prefixEnd_1052764 : Nat := 4983230072969 + 3 ^ 40 * 1052764 * 2
def baseEnd_1052764 : Nat := 240255087888899684314859

theorem tailTrace_1052764 : CollatzResearch.WordTrace tailWord_1052764 prefixEnd_1052764 240255087888899684314859 := by
  unfold tailWord_1052764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19198728779011650310938673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25598305038682200414584897 19198728779011650310938673)
  ·
    refine ⟨14399046584258737733204005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19198728779011650310938673 14399046584258737733204005)
    ·
      refine ⟨2699821234548513324975751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14399046584258737733204005 2699821234548513324975751)
      ·
        refine ⟨4049731851822769987463627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699821234548513324975751 4049731851822769987463627)
        ·
          refine ⟨6074597777734154981195441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4049731851822769987463627 6074597777734154981195441)
          ·
            refine ⟨4555948333300616235896581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6074597777734154981195441 4555948333300616235896581)
            ·
              refine ⟨854240312493865544230609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4555948333300616235896581 854240312493865544230609)
              ·
                refine ⟨640680234370399158172957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854240312493865544230609 640680234370399158172957)
                ·
                  refine ⟨240255087888899684314859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640680234370399158172957 240255087888899684314859)
                  ·
                    rfl

theorem cell21_1052764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_1052764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052764 prefixEnd_1052764 := by exact prefixLift 1052764
  have htrace : WordTrace (prefixWord ++ tailWord_1052764) baseStart_1052764 baseEnd_1052764 := by
    simpa [prefixWord, tailWord_1052764, baseEnd_1052764] using wordTrace_append hprefix tailTrace_1052764
  have hstable : (prefixWord ++ tailWord_1052764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052764).length < 2 ^ (prefixWord ++ tailWord_1052764).sum := by decide
  have hdescent : baseEnd_1052764 < baseStart_1052764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052837 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 4]
def baseStart_1052837 : Nat := 118140960795 + 1052837 * 2 ^ 59
def prefixEnd_1052837 : Nat := 4983230072969 + 3 ^ 40 * 1052837 * 2
def baseEnd_1052837 : Nat := 240271747483467779598043

theorem tailTrace_1052837 : CollatzResearch.WordTrace tailWord_1052837 prefixEnd_1052837 240271747483467779598043 := by
  unfold tailWord_1052837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38400120086758834089284765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25600080057839222726189843 38400120086758834089284765)
  ·
    refine ⟨14400045032534562783481787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38400120086758834089284765 14400045032534562783481787)
    ·
      refine ⟨21600067548801844175222681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14400045032534562783481787 21600067548801844175222681)
      ·
        refine ⟨16200050661601383131417011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21600067548801844175222681 16200050661601383131417011)
        ·
          refine ⟨24300075992402074697125517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16200050661601383131417011 24300075992402074697125517)
          ·
            refine ⟨9112528497150778011422069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24300075992402074697125517 9112528497150778011422069)
            ·
              refine ⟨854299546607885438570819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9112528497150778011422069 854299546607885438570819)
              ·
                refine ⟨1281449319911828157856229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854299546607885438570819 1281449319911828157856229)
                ·
                  refine ⟨240271747483467779598043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281449319911828157856229 240271747483467779598043)
                  ·
                    rfl

theorem cell21_1052837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_1052837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052837 prefixEnd_1052837 := by exact prefixLift 1052837
  have htrace : WordTrace (prefixWord ++ tailWord_1052837) baseStart_1052837 baseEnd_1052837 := by
    simpa [prefixWord, tailWord_1052837, baseEnd_1052837] using wordTrace_append hprefix tailTrace_1052837
  have hstable : (prefixWord ++ tailWord_1052837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052837).length < 2 ^ (prefixWord ++ tailWord_1052837).sum := by decide
  have hdescent : baseEnd_1052837 < baseStart_1052837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052879 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 6]
def baseStart_1052879 : Nat := 118140960795 + 1052879 * 2 ^ 59
def prefixEnd_1052879 : Nat := 4983230072969 + 3 ^ 40 * 1052879 * 2
def baseEnd_1052879 : Nat := 240281332455685039897957

theorem tailTrace_1052879 : CollatzResearch.WordTrace tailWord_1052879 prefixEnd_1052879 240281332455685039897957 := by
  unfold tailWord_1052879
  simp only [CollatzResearch.WordTrace]
  refine ⟨38401651952606675262313691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25601101301737783508209127 38401651952606675262313691)
  ·
    refine ⟨57602477928910012893470537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38401651952606675262313691 57602477928910012893470537)
    ·
      refine ⟨43201858446682509670102903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57602477928910012893470537 43201858446682509670102903)
      ·
        refine ⟨64802787670023764505154355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43201858446682509670102903 64802787670023764505154355)
        ·
          refine ⟨97204181505035646757731533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64802787670023764505154355 97204181505035646757731533)
          ·
            refine ⟨36451568064388367534149325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97204181505035646757731533 36451568064388367534149325)
            ·
              refine ⟨13669338024145637825305997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36451568064388367534149325 13669338024145637825305997)
              ·
                refine ⟨5126001759054614184489749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13669338024145637825305997 5126001759054614184489749)
                ·
                  refine ⟨240281332455685039897957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5126001759054614184489749 240281332455685039897957)
                  ·
                    rfl

theorem cell21_1052879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_1052879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052879 prefixEnd_1052879 := by exact prefixLift 1052879
  have htrace : WordTrace (prefixWord ++ tailWord_1052879) baseStart_1052879 baseEnd_1052879 := by
    simpa [prefixWord, tailWord_1052879, baseEnd_1052879] using wordTrace_append hprefix tailTrace_1052879
  have hstable : (prefixWord ++ tailWord_1052879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052879).length < 2 ^ (prefixWord ++ tailWord_1052879).sum := by decide
  have hdescent : baseEnd_1052879 < baseStart_1052879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052882 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1052882 : Nat := 118140960795 + 1052882 * 2 ^ 59
def prefixEnd_1052882 : Nat := 4983230072969 + 3 ^ 40 * 1052882 * 2
def baseEnd_1052882 : Nat := 240282017096557701347951

theorem tailTrace_1052882 : CollatzResearch.WordTrace tailWord_1052882 prefixEnd_1052882 240282017096557701347951 := by
  unfold tailWord_1052882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600440342898951693668225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25601174247730537849781933 9600440342898951693668225)
  ·
    refine ⟨7200330257174213770251169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9600440342898951693668225 7200330257174213770251169)
    ·
      refine ⟨5400247692880660327688377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7200330257174213770251169 5400247692880660327688377)
      ·
        refine ⟨4050185769660495245766283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5400247692880660327688377 4050185769660495245766283)
        ·
          refine ⟨6075278654490742868649425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4050185769660495245766283 6075278654490742868649425)
          ·
            refine ⟨4556458990868057151487069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6075278654490742868649425 4556458990868057151487069)
            ·
              refine ⟨1708672121575521431807651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4556458990868057151487069 1708672121575521431807651)
              ·
                refine ⟨2563008182363282147711477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708672121575521431807651 2563008182363282147711477)
                ·
                  refine ⟨240282017096557701347951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2563008182363282147711477 240282017096557701347951)
                  ·
                    rfl

theorem cell21_1052882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1052882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052882 prefixEnd_1052882 := by exact prefixLift 1052882
  have htrace : WordTrace (prefixWord ++ tailWord_1052882) baseStart_1052882 baseEnd_1052882 := by
    simpa [prefixWord, tailWord_1052882, baseEnd_1052882] using wordTrace_append hprefix tailTrace_1052882
  have hstable : (prefixWord ++ tailWord_1052882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052882).length < 2 ^ (prefixWord ++ tailWord_1052882).sum := by decide
  have hdescent : baseEnd_1052882 < baseStart_1052882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052896 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_1052896 : Nat := 118140960795 + 1052896 * 2 ^ 59
def prefixEnd_1052896 : Nat := 4983230072969 + 3 ^ 40 * 1052896 * 2
def baseEnd_1052896 : Nat := 240285212087296788114589

theorem tailTrace_1052896 : CollatzResearch.WordTrace tailWord_1052896 prefixEnd_1052896 240285212087296788114589 := by
  unfold tailWord_1052896
  simp only [CollatzResearch.WordTrace]
  refine ⟨19201135996772543582841271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25601514662363391443788361 19201135996772543582841271)
  ·
    refine ⟨28801703995158815374261907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19201135996772543582841271 28801703995158815374261907)
    ·
      refine ⟨43202555992738223061392861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28801703995158815374261907 43202555992738223061392861)
      ·
        refine ⟨16200958497276833648022323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43202555992738223061392861 16200958497276833648022323)
        ·
          refine ⟨24301437745915250472033485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16200958497276833648022323 24301437745915250472033485)
          ·
            refine ⟨9113039154718218927012557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24301437745915250472033485 9113039154718218927012557)
            ·
              refine ⟨3417389683019332097629709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9113039154718218927012557 3417389683019332097629709)
              ·
                refine ⟨1281521131132249536611141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3417389683019332097629709 1281521131132249536611141)
                ·
                  refine ⟨240285212087296788114589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281521131132249536611141 240285212087296788114589)
                  ·
                    rfl

theorem cell21_1052896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_1052896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052896 prefixEnd_1052896 := by exact prefixLift 1052896
  have htrace : WordTrace (prefixWord ++ tailWord_1052896) baseStart_1052896 baseEnd_1052896 := by
    simpa [prefixWord, tailWord_1052896, baseEnd_1052896] using wordTrace_append hprefix tailTrace_1052896
  have hstable : (prefixWord ++ tailWord_1052896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052896).length < 2 ^ (prefixWord ++ tailWord_1052896).sum := by decide
  have hdescent : baseEnd_1052896 < baseStart_1052896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052930 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1052930 : Nat := 118140960795 + 1052930 * 2 ^ 59
def prefixEnd_1052930 : Nat := 4983230072969 + 3 ^ 40 * 1052930 * 2
def baseEnd_1052930 : Nat := 240292971350520284547853

theorem tailTrace_1052930 : CollatzResearch.WordTrace tailWord_1052930 prefixEnd_1052930 240292971350520284547853 := by
  unfold tailWord_1052930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600878018855477743105061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25602341383614607314946829 9600878018855477743105061)
  ·
    refine ⟨1800164628535402076832199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9600878018855477743105061 1800164628535402076832199)
    ·
      refine ⟨2700246942803103115248299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800164628535402076832199 2700246942803103115248299)
      ·
        refine ⟨4050370414204654672872449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700246942803103115248299 4050370414204654672872449)
        ·
          refine ⟨3037777810653491004654337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4050370414204654672872449 3037777810653491004654337)
          ·
            refine ⟨2278333357990118253490753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037777810653491004654337 2278333357990118253490753)
            ·
              refine ⟨1708750018492588690118065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278333357990118253490753 1708750018492588690118065)
              ·
                refine ⟨1281562513869441517588549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1708750018492588690118065 1281562513869441517588549)
                ·
                  refine ⟨240292971350520284547853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281562513869441517588549 240292971350520284547853)
                  ·
                    rfl

theorem cell21_1052930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1052930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052930 prefixEnd_1052930 := by exact prefixLift 1052930
  have htrace : WordTrace (prefixWord ++ tailWord_1052930) baseStart_1052930 baseEnd_1052930 := by
    simpa [prefixWord, tailWord_1052930, baseEnd_1052930] using wordTrace_append hprefix tailTrace_1052930
  have hstable : (prefixWord ++ tailWord_1052930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052930).length < 2 ^ (prefixWord ++ tailWord_1052930).sum := by decide
  have hdescent : baseEnd_1052930 < baseStart_1052930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052986 : List Nat := [3, 1, 1, 1, 4, 3, 8]
def baseStart_1052986 : Nat := 118140960795 + 1052986 * 2 ^ 59
def prefixEnd_1052986 : Nat := 4983230072969 + 3 ^ 40 * 1052986 * 2
def baseEnd_1052986 : Nat := 26700639034830736846045

theorem tailTrace_1052986 : CollatzResearch.WordTrace tailWord_1052986 prefixEnd_1052986 26700639034830736846045 := by
  unfold tailWord_1052986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601388640804758134114703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25603703042146021690972541 9601388640804758134114703)
  ·
    refine ⟨14402082961207137201172055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9601388640804758134114703 14402082961207137201172055)
    ·
      refine ⟨21603124441810705801758083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14402082961207137201172055 21603124441810705801758083)
      ·
        refine ⟨32404686662716058702637125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21603124441810705801758083 32404686662716058702637125)
        ·
          refine ⟨6075878749259261006744461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32404686662716058702637125 6075878749259261006744461)
          ·
            refine ⟨2278454530972222877529173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6075878749259261006744461 2278454530972222877529173)
            ·
              refine ⟨26700639034830736846045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2278454530972222877529173 26700639034830736846045)
              ·
                rfl

theorem cell21_1052986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 8].length) (baseStart_1052986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1052986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1052986 prefixEnd_1052986 := by exact prefixLift 1052986
  have htrace : WordTrace (prefixWord ++ tailWord_1052986) baseStart_1052986 baseEnd_1052986 := by
    simpa [prefixWord, tailWord_1052986, baseEnd_1052986] using wordTrace_append hprefix tailTrace_1052986
  have hstable : (prefixWord ++ tailWord_1052986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052986).length < 2 ^ (prefixWord ++ tailWord_1052986).sum := by decide
  have hdescent : baseEnd_1052986 < baseStart_1052986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053020 : List Nat := [2, 2, 4, 3, 1, 1, 1, 7]
def baseStart_1053020 : Nat := 118140960795 + 1053020 * 2 ^ 59
def prefixEnd_1053020 : Nat := 4983230072969 + 3 ^ 40 * 1053020 * 2
def baseEnd_1053020 : Nat := 80104503525566709349223

theorem tailTrace_1053020 : CollatzResearch.WordTrace tailWord_1053020 prefixEnd_1053020 80104503525566709349223 := by
  unfold tailWord_1053020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19203397322547928171598257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25604529763397237562131009 19203397322547928171598257)
  ·
    refine ⟨14402547991910946128698693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19203397322547928171598257 14402547991910946128698693)
    ·
      refine ⟨2700477748483302399131005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14402547991910946128698693 2700477748483302399131005)
      ·
        refine ⟨1012679155681238399674127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2700477748483302399131005 1012679155681238399674127)
        ·
          refine ⟨1519018733521857599511191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012679155681238399674127 1519018733521857599511191)
          ·
            refine ⟨2278528100282786399266787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519018733521857599511191 2278528100282786399266787)
            ·
              refine ⟨3417792150424179598900181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278528100282786399266787 3417792150424179598900181)
              ·
                refine ⟨80104503525566709349223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3417792150424179598900181 80104503525566709349223)
                ·
                  rfl

theorem cell21_1053020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_1053020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053020 prefixEnd_1053020 := by exact prefixLift 1053020
  have htrace : WordTrace (prefixWord ++ tailWord_1053020) baseStart_1053020 baseEnd_1053020 := by
    simpa [prefixWord, tailWord_1053020, baseEnd_1053020] using wordTrace_append hprefix tailTrace_1053020
  have hstable : (prefixWord ++ tailWord_1053020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053020).length < 2 ^ (prefixWord ++ tailWord_1053020).sum := by decide
  have hdescent : baseEnd_1053020 < baseStart_1053020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053051 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 3]
def baseStart_1053051 : Nat := 118140960795 + 1053051 * 2 ^ 59
def prefixEnd_1053051 : Nat := 4983230072969 + 3 ^ 40 * 1053051 * 2
def baseEnd_1053051 : Nat := 240320585199050963030939

theorem tailTrace_1053051 : CollatzResearch.WordTrace tailWord_1053051 prefixEnd_1053051 240320585199050963030939 := by
  unfold tailWord_1053051
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407925307983548637575007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25605283538655699091716671 38407925307983548637575007)
  ·
    refine ⟨57611887961975322956362511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38407925307983548637575007 57611887961975322956362511)
    ·
      refine ⟨86417831942962984434543767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57611887961975322956362511 86417831942962984434543767)
      ·
        refine ⟨129626747914444476651815651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86417831942962984434543767 129626747914444476651815651)
        ·
          refine ⟨194440121871666714977723477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129626747914444476651815651 194440121871666714977723477)
          ·
            refine ⟨2278595178183594316145197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 194440121871666714977723477 2278595178183594316145197)
            ·
              refine ⟨854473191818847868554449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2278595178183594316145197 854473191818847868554449)
              ·
                refine ⟨640854893864135901415837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854473191818847868554449 640854893864135901415837)
                ·
                  refine ⟨240320585199050963030939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640854893864135901415837 240320585199050963030939)
                  ·
                    rfl

theorem cell21_1053051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 3].length) (baseStart_1053051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053051 prefixEnd_1053051 := by exact prefixLift 1053051
  have htrace : WordTrace (prefixWord ++ tailWord_1053051) baseStart_1053051 baseEnd_1053051 := by
    simpa [prefixWord, tailWord_1053051, baseEnd_1053051] using wordTrace_append hprefix tailTrace_1053051
  have hstable : (prefixWord ++ tailWord_1053051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053051).length < 2 ^ (prefixWord ++ tailWord_1053051).sum := by decide
  have hdescent : baseEnd_1053051 < baseStart_1053051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053065 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 4]
def baseStart_1053065 : Nat := 118140960795 + 1053065 * 2 ^ 59
def prefixEnd_1053065 : Nat := 4983230072969 + 3 ^ 40 * 1053065 * 2
def baseEnd_1053065 : Nat := 240323780189790049797577

theorem tailTrace_1053065 : CollatzResearch.WordTrace tailWord_1053065 prefixEnd_1053065 240323780189790049797577 := by
  unfold tailWord_1053065
  simp only [CollatzResearch.WordTrace]
  refine ⟨38408435929932829028584649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25605623953288552685723099 38408435929932829028584649)
  ·
    refine ⟨28806326947449621771438487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38408435929932829028584649 28806326947449621771438487)
    ·
      refine ⟨43209490421174432657157731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28806326947449621771438487 43209490421174432657157731)
      ·
        refine ⟨64814235631761648985736597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43209490421174432657157731 64814235631761648985736597)
        ·
          refine ⟨3038167295238827296206403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64814235631761648985736597 3038167295238827296206403)
          ·
            refine ⟨4557250942858240944309605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038167295238827296206403 4557250942858240944309605)
            ·
              refine ⟨854484551785920177058051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4557250942858240944309605 854484551785920177058051)
              ·
                refine ⟨1281726827678880265587077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854484551785920177058051 1281726827678880265587077)
                ·
                  refine ⟨240323780189790049797577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281726827678880265587077 240323780189790049797577)
                  ·
                    rfl

theorem cell21_1053065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_1053065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053065 prefixEnd_1053065 := by exact prefixLift 1053065
  have htrace : WordTrace (prefixWord ++ tailWord_1053065) baseStart_1053065 baseEnd_1053065 := by
    simpa [prefixWord, tailWord_1053065, baseEnd_1053065] using wordTrace_append hprefix tailTrace_1053065
  have hstable : (prefixWord ++ tailWord_1053065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053065).length < 2 ^ (prefixWord ++ tailWord_1053065).sum := by decide
  have hdescent : baseEnd_1053065 < baseStart_1053065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053152 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_1053152 : Nat := 118140960795 + 1053152 * 2 ^ 59
def prefixEnd_1053152 : Nat := 4983230072969 + 3 ^ 40 * 1053152 * 2
def baseEnd_1053152 : Nat := 240343634775097231847399

theorem tailTrace_1053152 : CollatzResearch.WordTrace tailWord_1053152 prefixEnd_1053152 240343634775097231847399 := by
  unfold tailWord_1053152
  simp only [CollatzResearch.WordTrace]
  refine ⟨19205804540308821443500855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25607739387078428591334473 19205804540308821443500855)
  ·
    refine ⟨28808706810463232165251283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19205804540308821443500855 28808706810463232165251283)
    ·
      refine ⟨43213060215694848247876925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28808706810463232165251283 43213060215694848247876925)
      ·
        refine ⟨16204897580885568092953847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43213060215694848247876925 16204897580885568092953847)
        ·
          refine ⟨24307346371328352139430771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16204897580885568092953847 24307346371328352139430771)
          ·
            refine ⟨36461019556992528209146157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24307346371328352139430771 36461019556992528209146157)
            ·
              refine ⟨13672882333872198078429809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36461019556992528209146157 13672882333872198078429809)
              ·
                refine ⟨10254661750404148558822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13672882333872198078429809 10254661750404148558822357)
                ·
                  refine ⟨240343634775097231847399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10254661750404148558822357 240343634775097231847399)
                  ·
                    rfl

theorem cell21_1053152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_1053152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053152 prefixEnd_1053152 := by exact prefixLift 1053152
  have htrace : WordTrace (prefixWord ++ tailWord_1053152) baseStart_1053152 baseEnd_1053152 := by
    simpa [prefixWord, tailWord_1053152, baseEnd_1053152] using wordTrace_append hprefix tailTrace_1053152
  have hstable : (prefixWord ++ tailWord_1053152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053152).length < 2 ^ (prefixWord ++ tailWord_1053152).sum := by decide
  have hdescent : baseEnd_1053152 < baseStart_1053152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053169 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_1053169 : Nat := 118140960795 + 1053169 * 2 ^ 59
def prefixEnd_1053169 : Nat := 4983230072969 + 3 ^ 40 * 1053169 * 2
def baseEnd_1053169 : Nat := 240347514406708980064031

theorem tailTrace_1053169 : CollatzResearch.WordTrace tailWord_1053169 prefixEnd_1053169 240347514406708980064031 := by
  unfold tailWord_1053169
  simp only [CollatzResearch.WordTrace]
  refine ⟨38412229121556054790370561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25608152747704036526913707 38412229121556054790370561)
  ·
    refine ⟨28809171841167041092777921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38412229121556054790370561 28809171841167041092777921)
    ·
      refine ⟨21606878880875280819583441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28809171841167041092777921 21606878880875280819583441)
      ·
        refine ⟨16205159160656460614687581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21606878880875280819583441 16205159160656460614687581)
        ·
          refine ⟨6076934685246172730507843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16205159160656460614687581 6076934685246172730507843)
          ·
            refine ⟨9115402027869259095761765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076934685246172730507843 9115402027869259095761765)
            ·
              refine ⟨1709137880225486080455331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9115402027869259095761765 1709137880225486080455331)
              ·
                refine ⟨2563706820338229120682997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709137880225486080455331 2563706820338229120682997)
                ·
                  refine ⟨240347514406708980064031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2563706820338229120682997 240347514406708980064031)
                  ·
                    rfl

theorem cell21_1053169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_1053169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053169 prefixEnd_1053169 := by exact prefixLift 1053169
  have htrace : WordTrace (prefixWord ++ tailWord_1053169) baseStart_1053169 baseEnd_1053169 := by
    simpa [prefixWord, tailWord_1053169, baseEnd_1053169] using wordTrace_append hprefix tailTrace_1053169
  have hstable : (prefixWord ++ tailWord_1053169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053169).length < 2 ^ (prefixWord ++ tailWord_1053169).sum := by decide
  have hdescent : baseEnd_1053169 < baseStart_1053169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053220 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_1053220 : Nat := 118140960795 + 1053220 * 2 ^ 59
def prefixEnd_1053220 : Nat := 4983230072969 + 3 ^ 40 * 1053220 * 2
def baseEnd_1053220 : Nat := 240359153301544224713927

theorem tailTrace_1053220 : CollatzResearch.WordTrace tailWord_1053220 prefixEnd_1053220 240359153301544224713927 := by
  unfold tailWord_1053220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19207044622185645250238557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25609392829580860333651409 19207044622185645250238557)
  ·
    refine ⟨7202641733319616968839459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19207044622185645250238557 7202641733319616968839459)
    ·
      refine ⟨10803962599979425453259189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7202641733319616968839459 10803962599979425453259189)
      ·
        refine ⟨1012871493748071136243049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10803962599979425453259189 1012871493748071136243049)
        ·
          refine ⟨759653620311053352182287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012871493748071136243049 759653620311053352182287)
          ·
            refine ⟨1139480430466580028273431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759653620311053352182287 1139480430466580028273431)
            ·
              refine ⟨1709220645699870042410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139480430466580028273431 1709220645699870042410147)
              ·
                refine ⟨2563830968549805063615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709220645699870042410147 2563830968549805063615221)
                ·
                  refine ⟨240359153301544224713927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2563830968549805063615221 240359153301544224713927)
                  ·
                    rfl

theorem cell21_1053220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_1053220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053220 prefixEnd_1053220 := by exact prefixLift 1053220
  have htrace : WordTrace (prefixWord ++ tailWord_1053220) baseStart_1053220 baseEnd_1053220 := by
    simpa [prefixWord, tailWord_1053220, baseEnd_1053220] using wordTrace_append hprefix tailTrace_1053220
  have hstable : (prefixWord ++ tailWord_1053220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053220).length < 2 ^ (prefixWord ++ tailWord_1053220).sum := by decide
  have hdescent : baseEnd_1053220 < baseStart_1053220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053304 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_1053304 : Nat := 118140960795 + 1053304 * 2 ^ 59
def prefixEnd_1053304 : Nat := 4983230072969 + 3 ^ 40 * 1053304 * 2
def baseEnd_1053304 : Nat := 240378323245978745313755

theorem tailTrace_1053304 : CollatzResearch.WordTrace tailWord_1053304 prefixEnd_1053304 240378323245978745313755 := by
  unfold tailWord_1053304
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208576488033486423267483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25611435317377981897689977 19208576488033486423267483)
  ·
    refine ⟨28812864732050229634901225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19208576488033486423267483 28812864732050229634901225)
    ·
      refine ⟨21609648549037672226175919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28812864732050229634901225 21609648549037672226175919)
      ·
        refine ⟨32414472823556508339263879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21609648549037672226175919 32414472823556508339263879)
        ·
          refine ⟨48621709235334762508895819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32414472823556508339263879 48621709235334762508895819)
          ·
            refine ⟨72932563853002143763343729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48621709235334762508895819 72932563853002143763343729)
            ·
              refine ⟨54699422889751607822507797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72932563853002143763343729 54699422889751607822507797)
              ·
                refine ⟨2564035447957106616680053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54699422889751607822507797 2564035447957106616680053)
                ·
                  refine ⟨240378323245978745313755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2564035447957106616680053 240378323245978745313755)
                  ·
                    rfl

theorem cell21_1053304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_1053304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053304 prefixEnd_1053304 := by exact prefixLift 1053304
  have htrace : WordTrace (prefixWord ++ tailWord_1053304) baseStart_1053304 baseEnd_1053304 := by
    simpa [prefixWord, tailWord_1053304, baseEnd_1053304] using wordTrace_append hprefix tailTrace_1053304
  have hstable : (prefixWord ++ tailWord_1053304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053304).length < 2 ^ (prefixWord ++ tailWord_1053304).sum := by decide
  have hdescent : baseEnd_1053304 < baseStart_1053304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053335 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 6]
def baseStart_1053335 : Nat := 118140960795 + 1053335 * 2 ^ 59
def prefixEnd_1053335 : Nat := 4983230072969 + 3 ^ 40 * 1053335 * 2
def baseEnd_1053335 : Nat := 240385397868329580297025

theorem tailTrace_1053335 : CollatzResearch.WordTrace tailWord_1053335 prefixEnd_1053335 240385397868329580297025 := by
  unfold tailWord_1053335
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418283638954665140913459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25612189092636443427275639 38418283638954665140913459)
  ·
    refine ⟨57627425458431997711370189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38418283638954665140913459 57627425458431997711370189)
    ·
      refine ⟨21610284546911999141763821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57627425458431997711370189 21610284546911999141763821)
      ·
        refine ⟨8103856705091999678161433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21610284546911999141763821 8103856705091999678161433)
        ·
          refine ⟨6077892528818999758621075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8103856705091999678161433 6077892528818999758621075)
          ·
            refine ⟨9116838793228499637931613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077892528818999758621075 9116838793228499637931613)
            ·
              refine ⟨3418814547460687364224355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9116838793228499637931613 3418814547460687364224355)
              ·
                refine ⟨5128221821191031046336533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418814547460687364224355 5128221821191031046336533)
                ·
                  refine ⟨240385397868329580297025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5128221821191031046336533 240385397868329580297025)
                  ·
                    rfl

theorem cell21_1053335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_1053335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053335 prefixEnd_1053335 := by exact prefixLift 1053335
  have htrace : WordTrace (prefixWord ++ tailWord_1053335) baseStart_1053335 baseEnd_1053335 := by
    simpa [prefixWord, tailWord_1053335, baseEnd_1053335] using wordTrace_append hprefix tailTrace_1053335
  have hstable : (prefixWord ++ tailWord_1053335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053335).length < 2 ^ (prefixWord ++ tailWord_1053335).sum := by decide
  have hdescent : baseEnd_1053335 < baseStart_1053335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053349 : List Nat := [1, 3, 1, 2, 1, 2, 1, 10]
def baseStart_1053349 : Nat := 118140960795 + 1053349 * 2 ^ 59
def prefixEnd_1053349 : Nat := 4983230072969 + 3 ^ 40 * 1053349 * 2
def baseEnd_1053349 : Nat := 80129530953022889021221

theorem tailTrace_1053349 : CollatzResearch.WordTrace tailWord_1053349 prefixEnd_1053349 80129530953022889021221 := by
  unfold tailWord_1053349
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418794260903945531923101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25612529507269297021282067 38418794260903945531923101)
  ·
    refine ⟨14407047847838979574471163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38418794260903945531923101 14407047847838979574471163)
    ·
      refine ⟨21610571771758469361706745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14407047847838979574471163 21610571771758469361706745)
      ·
        refine ⟨16207928828818852021280059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21610571771758469361706745 16207928828818852021280059)
        ·
          refine ⟨24311893243228278031920089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16207928828818852021280059 24311893243228278031920089)
          ·
            refine ⟨18233919932421208523940067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24311893243228278031920089 18233919932421208523940067)
            ·
              refine ⟨27350879898631812785910101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18233919932421208523940067 27350879898631812785910101)
              ·
                refine ⟨80129530953022889021221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27350879898631812785910101 80129530953022889021221)
                ·
                  rfl

theorem cell21_1053349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_1053349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053349 prefixEnd_1053349 := by exact prefixLift 1053349
  have htrace : WordTrace (prefixWord ++ tailWord_1053349) baseStart_1053349 baseEnd_1053349 := by
    simpa [prefixWord, tailWord_1053349, baseEnd_1053349] using wordTrace_append hprefix tailTrace_1053349
  have hstable : (prefixWord ++ tailWord_1053349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053349).length < 2 ^ (prefixWord ++ tailWord_1053349).sum := by decide
  have hdescent : baseEnd_1053349 < baseStart_1053349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053389 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1053389 : Nat := 118140960795 + 1053389 * 2 ^ 59
def prefixEnd_1053389 : Nat := 4983230072969 + 3 ^ 40 * 1053389 * 2
def baseEnd_1053389 : Nat := 240397721404037486396915

theorem tailTrace_1053389 : CollatzResearch.WordTrace tailWord_1053389 prefixEnd_1053389 240397721404037486396915 := by
  unfold tailWord_1053389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38420253180759032363379221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25613502120506021575586147 38420253180759032363379221)
  ·
    refine ⟨1800949367848079642033401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38420253180759032363379221 1800949367848079642033401)
    ·
      refine ⟨1350712025886059731525051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1800949367848079642033401 1350712025886059731525051)
      ·
        refine ⟨2026068038829089597287577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350712025886059731525051 2026068038829089597287577)
        ·
          refine ⟨1519551029121817197965683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2026068038829089597287577 1519551029121817197965683)
          ·
            refine ⟨2279326543682725796948525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519551029121817197965683 2279326543682725796948525)
            ·
              refine ⟨854747453881022173855697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2279326543682725796948525 854747453881022173855697)
              ·
                refine ⟨641060590410766630391773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854747453881022173855697 641060590410766630391773)
                ·
                  refine ⟨240397721404037486396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641060590410766630391773 240397721404037486396915)
                  ·
                    rfl

theorem cell21_1053389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1053389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053389 prefixEnd_1053389 := by exact prefixLift 1053389
  have htrace : WordTrace (prefixWord ++ tailWord_1053389) baseStart_1053389 baseEnd_1053389 := by
    simpa [prefixWord, tailWord_1053389, baseEnd_1053389] using wordTrace_append hprefix tailTrace_1053389
  have hstable : (prefixWord ++ tailWord_1053389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053389).length < 2 ^ (prefixWord ++ tailWord_1053389).sum := by decide
  have hdescent : baseEnd_1053389 < baseStart_1053389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053425 : List Nat := [1, 2, 2, 2, 2, 2, 1, 9]
def baseStart_1053425 : Nat := 118140960795 + 1053425 * 2 ^ 59
def prefixEnd_1053425 : Nat := 4983230072969 + 3 ^ 40 * 1053425 * 2
def baseEnd_1053425 : Nat := 80135312364836474598947

theorem tailTrace_1053425 : CollatzResearch.WordTrace tailWord_1053425 prefixEnd_1053425 80135312364836474598947 := by
  unfold tailWord_1053425
  simp only [CollatzResearch.WordTrace]
  refine ⟨38421566208628610511689729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25614377472419073674459819 38421566208628610511689729)
  ·
    refine ⟨28816174656471457883767297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38421566208628610511689729 28816174656471457883767297)
    ·
      refine ⟨21612130992353593412825473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28816174656471457883767297 21612130992353593412825473)
      ·
        refine ⟨16209098244265195059619105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21612130992353593412825473 16209098244265195059619105)
        ·
          refine ⟨12156823683198896294714329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16209098244265195059619105 12156823683198896294714329)
          ·
            refine ⟨9117617762399172221035747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12156823683198896294714329 9117617762399172221035747)
            ·
              refine ⟨13676426643598758331553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9117617762399172221035747 13676426643598758331553621)
              ·
                refine ⟨80135312364836474598947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13676426643598758331553621 80135312364836474598947)
                ·
                  rfl

theorem cell21_1053425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 9].length) (baseStart_1053425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053425 prefixEnd_1053425 := by exact prefixLift 1053425
  have htrace : WordTrace (prefixWord ++ tailWord_1053425) baseStart_1053425 baseEnd_1053425 := by
    simpa [prefixWord, tailWord_1053425, baseEnd_1053425] using wordTrace_append hprefix tailTrace_1053425
  have hstable : (prefixWord ++ tailWord_1053425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053425).length < 2 ^ (prefixWord ++ tailWord_1053425).sum := by decide
  have hdescent : baseEnd_1053425 < baseStart_1053425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053442 : List Nat := [3, 4, 1, 1, 1, 11]
def baseStart_1053442 : Nat := 118140960795 + 1053442 * 2 ^ 59
def prefixEnd_1053442 : Nat := 4983230072969 + 3 ^ 40 * 1053442 * 2
def baseEnd_1053442 : Nat := 8904067286152636000499

theorem tailTrace_1053442 : CollatzResearch.WordTrace tailWord_1053442 prefixEnd_1053442 8904067286152636000499 := by
  unfold tailWord_1053442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605546562391755603764645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25614790833044681610039053 9605546562391755603764645)
  ·
    refine ⟨1801039980448454175705871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9605546562391755603764645 1801039980448454175705871)
    ·
      refine ⟨2701559970672681263558807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801039980448454175705871 2701559970672681263558807)
      ·
        refine ⟨4052339956009021895338211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701559970672681263558807 4052339956009021895338211)
        ·
          refine ⟨6078509934013532843007317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052339956009021895338211 6078509934013532843007317)
          ·
            refine ⟨8904067286152636000499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6078509934013532843007317 8904067286152636000499)
            ·
              rfl

theorem cell21_1053442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 11].length) (baseStart_1053442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053442 prefixEnd_1053442 := by exact prefixLift 1053442
  have htrace : WordTrace (prefixWord ++ tailWord_1053442) baseStart_1053442 baseEnd_1053442 := by
    simpa [prefixWord, tailWord_1053442, baseEnd_1053442] using wordTrace_append hprefix tailTrace_1053442
  have hstable : (prefixWord ++ tailWord_1053442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053442).length < 2 ^ (prefixWord ++ tailWord_1053442).sum := by decide
  have hdescent : baseEnd_1053442 < baseStart_1053442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053490 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1053490 : Nat := 118140960795 + 1053490 * 2 ^ 59
def prefixEnd_1053490 : Nat := 4983230072969 + 3 ^ 40 * 1053490 * 2
def baseEnd_1053490 : Nat := 240420770980083755213375

theorem tailTrace_1053490 : CollatzResearch.WordTrace tailWord_1053490 prefixEnd_1053490 240420770980083755213375 := by
  unfold tailWord_1053490
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605984238348281653201481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25615957968928751075203949 9605984238348281653201481)
  ·
    refine ⟨7204488178761211239901111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9605984238348281653201481 7204488178761211239901111)
    ·
      refine ⟨10806732268141816859851667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204488178761211239901111 10806732268141816859851667)
      ·
        refine ⟨16210098402212725289777501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806732268141816859851667 16210098402212725289777501)
        ·
          refine ⟨6078786900829771983666563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16210098402212725289777501 6078786900829771983666563)
          ·
            refine ⟨9118180351244657975499845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078786900829771983666563 9118180351244657975499845)
            ·
              refine ⟨1709658815858373370406221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9118180351244657975499845 1709658815858373370406221)
              ·
                refine ⟨641122055946890013902333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1709658815858373370406221 641122055946890013902333)
                ·
                  refine ⟨240420770980083755213375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641122055946890013902333 240420770980083755213375)
                  ·
                    rfl

theorem cell21_1053490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1053490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053490 prefixEnd_1053490 := by exact prefixLift 1053490
  have htrace : WordTrace (prefixWord ++ tailWord_1053490) baseStart_1053490 baseEnd_1053490 := by
    simpa [prefixWord, tailWord_1053490, baseEnd_1053490] using wordTrace_append hprefix tailTrace_1053490
  have hstable : (prefixWord ++ tailWord_1053490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053490).length < 2 ^ (prefixWord ++ tailWord_1053490).sum := by decide
  have hdescent : baseEnd_1053490 < baseStart_1053490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053521 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 4]
def baseStart_1053521 : Nat := 118140960795 + 1053521 * 2 ^ 59
def prefixEnd_1053521 : Nat := 4983230072969 + 3 ^ 40 * 1053521 * 2
def baseEnd_1053521 : Nat := 240427845602434590196645

theorem tailTrace_1053521 : CollatzResearch.WordTrace tailWord_1053521 prefixEnd_1053521 240427845602434590196645 := by
  unfold tailWord_1053521
  simp only [CollatzResearch.WordTrace]
  refine ⟨38425067616280818907184417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25616711744187212604789611 38425067616280818907184417)
  ·
    refine ⟨28818800712210614180388313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38425067616280818907184417 28818800712210614180388313)
    ·
      refine ⟨21614100534157960635291235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28818800712210614180388313 21614100534157960635291235)
      ·
        refine ⟨32421150801236940952936853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21614100534157960635291235 32421150801236940952936853)
        ·
          refine ⟨1519741443807981607168915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32421150801236940952936853 1519741443807981607168915)
          ·
            refine ⟨2279612165711972410753373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519741443807981607168915 2279612165711972410753373)
            ·
              refine ⟨854854562141989654032515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2279612165711972410753373 854854562141989654032515)
              ·
                refine ⟨1282281843212984481048773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854854562141989654032515 1282281843212984481048773)
                ·
                  refine ⟨240427845602434590196645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282281843212984481048773 240427845602434590196645)
                  ·
                    rfl

theorem cell21_1053521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_1053521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053521 prefixEnd_1053521 := by exact prefixLift 1053521
  have htrace : WordTrace (prefixWord ++ tailWord_1053521) baseStart_1053521 baseEnd_1053521 := by
    simpa [prefixWord, tailWord_1053521, baseEnd_1053521] using wordTrace_append hprefix tailTrace_1053521
  have hstable : (prefixWord ++ tailWord_1053521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053521).length < 2 ^ (prefixWord ++ tailWord_1053521).sum := by decide
  have hdescent : baseEnd_1053521 < baseStart_1053521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053577 : List Nat := [1, 2, 1, 1, 5, 2, 1, 8]
def baseStart_1053577 : Nat := 118140960795 + 1053577 * 2 ^ 59
def prefixEnd_1053577 : Nat := 4983230072969 + 3 ^ 40 * 1053577 * 2
def baseEnd_1053577 : Nat := 80146875188463645754399

theorem tailTrace_1053577 : CollatzResearch.WordTrace tailWord_1053577 prefixEnd_1053577 80146875188463645754399 := by
  unfold tailWord_1053577
  simp only [CollatzResearch.WordTrace]
  refine ⟨38427110104077940471222985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25618073402718626980815323 38427110104077940471222985)
  ·
    refine ⟨28820332578058455353417239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38427110104077940471222985 28820332578058455353417239)
    ·
      refine ⟨43230498867087683030125859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28820332578058455353417239 43230498867087683030125859)
      ·
        refine ⟨64845748300631524545188789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43230498867087683030125859 64845748300631524545188789)
        ·
          refine ⟨6079288903184205426111449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64845748300631524545188789 6079288903184205426111449)
          ·
            refine ⟨4559466677388154069583587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6079288903184205426111449 4559466677388154069583587)
            ·
              refine ⟨6839200016082231104375381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559466677388154069583587 6839200016082231104375381)
              ·
                refine ⟨80146875188463645754399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6839200016082231104375381 80146875188463645754399)
                ·
                  rfl

theorem cell21_1053577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_1053577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053577 prefixEnd_1053577 := by exact prefixLift 1053577
  have htrace : WordTrace (prefixWord ++ tailWord_1053577) baseStart_1053577 baseEnd_1053577 := by
    simpa [prefixWord, tailWord_1053577, baseEnd_1053577] using wordTrace_append hprefix tailTrace_1053577
  have hstable : (prefixWord ++ tailWord_1053577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053577).length < 2 ^ (prefixWord ++ tailWord_1053577).sum := by decide
  have hdescent : baseEnd_1053577 < baseStart_1053577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053580 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_1053580 : Nat := 118140960795 + 1053580 * 2 ^ 59
def prefixEnd_1053580 : Nat := 4983230072969 + 3 ^ 40 * 1053580 * 2
def baseEnd_1053580 : Nat := 240441310206263598713191

theorem tailTrace_1053580 : CollatzResearch.WordTrace tailWord_1053580 prefixEnd_1053580 240441310206263598713191 := by
  unfold tailWord_1053580
  simp only [CollatzResearch.WordTrace]
  refine ⟨19213609761533535991791097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25618146348711381322388129 19213609761533535991791097)
  ·
    refine ⟨14410207321150151993843323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19213609761533535991791097 14410207321150151993843323)
    ·
      refine ⟨21615310981725227990764985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14410207321150151993843323 21615310981725227990764985)
      ·
        refine ⟨16211483236293920993073739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21615310981725227990764985 16211483236293920993073739)
        ·
          refine ⟨24317224854440881489610609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16211483236293920993073739 24317224854440881489610609)
          ·
            refine ⟨18237918640830661117207957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24317224854440881489610609 18237918640830661117207957)
            ·
              refine ⟨854902436288937239869123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18237918640830661117207957 854902436288937239869123)
              ·
                refine ⟨1282353654433405859803685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854902436288937239869123 1282353654433405859803685)
                ·
                  refine ⟨240441310206263598713191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282353654433405859803685 240441310206263598713191)
                  ·
                    rfl

theorem cell21_1053580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_1053580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053580 prefixEnd_1053580 := by exact prefixLift 1053580
  have htrace : WordTrace (prefixWord ++ tailWord_1053580) baseStart_1053580 baseEnd_1053580 := by
    simpa [prefixWord, tailWord_1053580, baseEnd_1053580] using wordTrace_append hprefix tailTrace_1053580
  have hstable : (prefixWord ++ tailWord_1053580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053580).length < 2 ^ (prefixWord ++ tailWord_1053580).sum := by decide
  have hdescent : baseEnd_1053580 < baseStart_1053580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053639 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_1053639 : Nat := 118140960795 + 1053639 * 2 ^ 59
def prefixEnd_1053639 : Nat := 4983230072969 + 3 ^ 40 * 1053639 * 2
def baseEnd_1053639 : Nat := 240454774810092607229737

theorem tailTrace_1053639 : CollatzResearch.WordTrace tailWord_1053639 prefixEnd_1053639 240454774810092607229737 := by
  unfold tailWord_1053639
  simp only [CollatzResearch.WordTrace]
  refine ⟨38429371429853325059979971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25619580953235550039986647 38429371429853325059979971)
  ·
    refine ⟨57644057144779987589969957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38429371429853325059979971 57644057144779987589969957)
    ·
      refine ⟨10808260714646247673119367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57644057144779987589969957 10808260714646247673119367)
      ·
        refine ⟨16212391071969371509679051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10808260714646247673119367 16212391071969371509679051)
        ·
          refine ⟨24318586607954057264518577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16212391071969371509679051 24318586607954057264518577)
          ·
            refine ⟨18238939955965542948388933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24318586607954057264518577 18238939955965542948388933)
            ·
              refine ⟨3419801241743539302822925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18238939955965542948388933 3419801241743539302822925)
              ·
                refine ⟨1282425465653827238558597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3419801241743539302822925 1282425465653827238558597)
                ·
                  refine ⟨240454774810092607229737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282425465653827238558597 240454774810092607229737)
                  ·
                    rfl

theorem cell21_1053639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_1053639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053639 prefixEnd_1053639 := by exact prefixLift 1053639
  have htrace : WordTrace (prefixWord ++ tailWord_1053639) baseStart_1053639 baseEnd_1053639 := by
    simpa [prefixWord, tailWord_1053639, baseEnd_1053639] using wordTrace_append hprefix tailTrace_1053639
  have hstable : (prefixWord ++ tailWord_1053639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053639).length < 2 ^ (prefixWord ++ tailWord_1053639).sum := by decide
  have hdescent : baseEnd_1053639 < baseStart_1053639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053729 : List Nat := [1, 2, 3, 2, 3, 1, 9]
def baseStart_1053729 : Nat := 118140960795 + 1053729 * 2 ^ 59
def prefixEnd_1053729 : Nat := 4983230072969 + 3 ^ 40 * 1053729 * 2
def baseEnd_1053729 : Nat := 26719479337363605636617

theorem tailTrace_1053729 : CollatzResearch.WordTrace tailWord_1053729 prefixEnd_1053729 26719479337363605636617 := by
  unfold tailWord_1053729
  simp only [CollatzResearch.WordTrace]
  refine ⟨38432653999527270430756241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25621769333018180287170827 38432653999527270430756241)
  ·
    refine ⟨28824490499645452823067181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38432653999527270430756241 28824490499645452823067181)
    ·
      refine ⟨10809183937367044808650193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28824490499645452823067181 10809183937367044808650193)
      ·
        refine ⟨8106887953025283606487645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10809183937367044808650193 8106887953025283606487645)
        ·
          refine ⟨3040082982384481352432867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8106887953025283606487645 3040082982384481352432867)
          ·
            refine ⟨4560124473576722028649301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040082982384481352432867 4560124473576722028649301)
            ·
              refine ⟨26719479337363605636617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4560124473576722028649301 26719479337363605636617)
              ·
                rfl

theorem cell21_1053729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 9].length) (baseStart_1053729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053729 prefixEnd_1053729 := by exact prefixLift 1053729
  have htrace : WordTrace (prefixWord ++ tailWord_1053729) baseStart_1053729 baseEnd_1053729 := by
    simpa [prefixWord, tailWord_1053729, baseEnd_1053729] using wordTrace_append hprefix tailTrace_1053729
  have hstable : (prefixWord ++ tailWord_1053729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053729).length < 2 ^ (prefixWord ++ tailWord_1053729).sum := by decide
  have hdescent : baseEnd_1053729 < baseStart_1053729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053791 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_1053791 : Nat := 118140960795 + 1053791 * 2 ^ 59
def prefixEnd_1053791 : Nat := 4983230072969 + 3 ^ 40 * 1053791 * 2
def baseEnd_1053791 : Nat := 240489463280974120696093

theorem tailTrace_1053791 : CollatzResearch.WordTrace tailWord_1053791 prefixEnd_1053791 240489463280974120696093 := by
  unfold tailWord_1053791
  simp only [CollatzResearch.WordTrace]
  refine ⟨38434915325302655019513227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25623276883535103346342151 38434915325302655019513227)
  ·
    refine ⟨57652372987953982529269841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38434915325302655019513227 57652372987953982529269841)
    ·
      refine ⟨43239279740965486896952381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57652372987953982529269841 43239279740965486896952381)
      ·
        refine ⟨16214729902862057586357143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43239279740965486896952381 16214729902862057586357143)
        ·
          refine ⟨24322094854293086379535715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16214729902862057586357143 24322094854293086379535715)
          ·
            refine ⟨36483142281439629569303573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24322094854293086379535715 36483142281439629569303573)
            ·
              refine ⟨1710147294442482636061105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36483142281439629569303573 1710147294442482636061105)
              ·
                refine ⟨1282610470831861977045829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710147294442482636061105 1282610470831861977045829)
                ·
                  refine ⟨240489463280974120696093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282610470831861977045829 240489463280974120696093)
                  ·
                    rfl

theorem cell21_1053791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_1053791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053791 prefixEnd_1053791 := by exact prefixLift 1053791
  have htrace : WordTrace (prefixWord ++ tailWord_1053791) baseStart_1053791 baseEnd_1053791 := by
    simpa [prefixWord, tailWord_1053791, baseEnd_1053791] using wordTrace_append hprefix tailTrace_1053791
  have hstable : (prefixWord ++ tailWord_1053791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053791).length < 2 ^ (prefixWord ++ tailWord_1053791).sum := by decide
  have hdescent : baseEnd_1053791 < baseStart_1053791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053853 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1053853 : Nat := 118140960795 + 1053853 * 2 ^ 59
def prefixEnd_1053853 : Nat := 4983230072969 + 3 ^ 40 * 1053853 * 2
def baseEnd_1053853 : Nat := 240503612525675790662633

theorem tailTrace_1053853 : CollatzResearch.WordTrace tailWord_1053853 prefixEnd_1053853 240503612525675790662633 := by
  unfold tailWord_1053853
  simp only [CollatzResearch.WordTrace]
  refine ⟨38437176651078039608270213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25624784434052026405513475 38437176651078039608270213)
  ·
    refine ⟨7206970622077132426550665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38437176651078039608270213 7206970622077132426550665)
    ·
      refine ⟨5405227966557849319912999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7206970622077132426550665 5405227966557849319912999)
      ·
        refine ⟨8107841949836773979869499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405227966557849319912999 8107841949836773979869499)
        ·
          refine ⟨12161762924755160969804249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107841949836773979869499 12161762924755160969804249)
          ·
            refine ⟨9121322193566370727353187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12161762924755160969804249 9121322193566370727353187)
            ·
              refine ⟨13681983290349556091029781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9121322193566370727353187 13681983290349556091029781)
              ·
                refine ⟨641342966735135441767021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13681983290349556091029781 641342966735135441767021)
                ·
                  refine ⟨240503612525675790662633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641342966735135441767021 240503612525675790662633)
                  ·
                    rfl

theorem cell21_1053853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1053853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053853 prefixEnd_1053853 := by exact prefixLift 1053853
  have htrace : WordTrace (prefixWord ++ tailWord_1053853) baseStart_1053853 baseEnd_1053853 := by
    simpa [prefixWord, tailWord_1053853, baseEnd_1053853] using wordTrace_append hprefix tailTrace_1053853
  have hstable : (prefixWord ++ tailWord_1053853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053853).length < 2 ^ (prefixWord ++ tailWord_1053853).sum := by decide
  have hdescent : baseEnd_1053853 < baseStart_1053853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053881 : List Nat := [1, 2, 1, 4, 1, 4, 1, 7]
def baseStart_1053881 : Nat := 118140960795 + 1053881 * 2 ^ 59
def prefixEnd_1053881 : Nat := 4983230072969 + 3 ^ 40 * 1053881 * 2
def baseEnd_1053881 : Nat := 80170000835717988065303

theorem tailTrace_1053881 : CollatzResearch.WordTrace tailWord_1053881 prefixEnd_1053881 80170000835717988065303 := by
  unfold tailWord_1053881
  simp only [CollatzResearch.WordTrace]
  refine ⟨38438197894976600390289497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25625465263317733593526331 38438197894976600390289497)
  ·
    refine ⟨28828648421232450292717123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38438197894976600390289497 28828648421232450292717123)
    ·
      refine ⟨43242972631848675439075685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28828648421232450292717123 43242972631848675439075685)
      ·
        refine ⟨8108057368471626644826691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43242972631848675439075685 8108057368471626644826691)
        ·
          refine ⟨12162086052707439967240037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108057368471626644826691 12162086052707439967240037)
          ·
            refine ⟨2280391134882644993857507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12162086052707439967240037 2280391134882644993857507)
            ·
              refine ⟨3420586702323967490786261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280391134882644993857507 3420586702323967490786261)
              ·
                refine ⟨80170000835717988065303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3420586702323967490786261 80170000835717988065303)
                ·
                  rfl

theorem cell21_1053881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_1053881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053881 prefixEnd_1053881 := by exact prefixLift 1053881
  have htrace : WordTrace (prefixWord ++ tailWord_1053881) baseStart_1053881 baseEnd_1053881 := by
    simpa [prefixWord, tailWord_1053881, baseEnd_1053881] using wordTrace_append hprefix tailTrace_1053881
  have hstable : (prefixWord ++ tailWord_1053881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053881).length < 2 ^ (prefixWord ++ tailWord_1053881).sum := by decide
  have hdescent : baseEnd_1053881 < baseStart_1053881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053895 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_1053895 : Nat := 118140960795 + 1053895 * 2 ^ 59
def prefixEnd_1053895 : Nat := 4983230072969 + 3 ^ 40 * 1053895 * 2
def baseEnd_1053895 : Nat := 240513197497893050962547

theorem tailTrace_1053895 : CollatzResearch.WordTrace tailWord_1053895 prefixEnd_1053895 240513197497893050962547 := by
  unfold tailWord_1053895
  simp only [CollatzResearch.WordTrace]
  refine ⟨38438708516925880781299139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25625805677950587187532759 38438708516925880781299139)
  ·
    refine ⟨57658062775388821171948709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38438708516925880781299139 57658062775388821171948709)
    ·
      refine ⟨10810886770385403969740383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57658062775388821171948709 10810886770385403969740383)
      ·
        refine ⟨16216330155578105954610575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10810886770385403969740383 16216330155578105954610575)
        ·
          refine ⟨24324495233367158931915863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16216330155578105954610575 24324495233367158931915863)
          ·
            refine ⟨36486742850050738397873795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24324495233367158931915863 36486742850050738397873795)
            ·
              refine ⟨54730114275076107596810693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36486742850050738397873795 54730114275076107596810693)
              ·
                refine ⟨10261896426576770174402005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54730114275076107596810693 10261896426576770174402005)
                ·
                  refine ⟨240513197497893050962547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10261896426576770174402005 240513197497893050962547)
                  ·
                    rfl

theorem cell21_1053895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_1053895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053895 prefixEnd_1053895 := by exact prefixLift 1053895
  have htrace : WordTrace (prefixWord ++ tailWord_1053895) baseStart_1053895 baseEnd_1053895 := by
    simpa [prefixWord, tailWord_1053895, baseEnd_1053895] using wordTrace_append hprefix tailTrace_1053895
  have hstable : (prefixWord ++ tailWord_1053895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053895).length < 2 ^ (prefixWord ++ tailWord_1053895).sum := by decide
  have hdescent : baseEnd_1053895 < baseStart_1053895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053960 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1053960 : Nat := 118140960795 + 1053960 * 2 ^ 59
def prefixEnd_1053960 : Nat := 4983230072969 + 3 ^ 40 * 1053960 * 2
def baseEnd_1053960 : Nat := 240528031383467382379081

theorem tailTrace_1053960 : CollatzResearch.WordTrace tailWord_1053960 prefixEnd_1053960 240528031383467382379081 := by
  unfold tailWord_1053960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19220539630845198441207667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25627386174460264588276889 19220539630845198441207667)
  ·
    refine ⟨28830809446267797661811501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19220539630845198441207667 28830809446267797661811501)
    ·
      refine ⟨10811553542350424123179313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28830809446267797661811501 10811553542350424123179313)
      ·
        refine ⟨8108665156762818092384485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10811553542350424123179313 8108665156762818092384485)
        ·
          refine ⟨1520374716893028392322091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8108665156762818092384485 1520374716893028392322091)
          ·
            refine ⟨2280562075339542588483137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520374716893028392322091 2280562075339542588483137)
            ·
              refine ⟨1710421556504656941362353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280562075339542588483137 1710421556504656941362353)
              ·
                refine ⟨1282816167378492706021765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710421556504656941362353 1282816167378492706021765)
                ·
                  refine ⟨240528031383467382379081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282816167378492706021765 240528031383467382379081)
                  ·
                    rfl

theorem cell21_1053960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1053960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053960 prefixEnd_1053960 := by exact prefixLift 1053960
  have htrace : WordTrace (prefixWord ++ tailWord_1053960) baseStart_1053960 baseEnd_1053960 := by
    simpa [prefixWord, tailWord_1053960, baseEnd_1053960] using wordTrace_append hprefix tailTrace_1053960
  have hstable : (prefixWord ++ tailWord_1053960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053960).length < 2 ^ (prefixWord ++ tailWord_1053960).sum := by decide
  have hdescent : baseEnd_1053960 < baseStart_1053960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053988 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_1053988 : Nat := 118140960795 + 1053988 * 2 ^ 59
def prefixEnd_1053988 : Nat := 4983230072969 + 3 ^ 40 * 1053988 * 2
def baseEnd_1053988 : Nat := 240534421364945555912357

theorem tailTrace_1053988 : CollatzResearch.WordTrace tailWord_1053988 prefixEnd_1053988 240534421364945555912357 := by
  unfold tailWord_1053988
  simp only [CollatzResearch.WordTrace]
  refine ⟨19221050252794478832217309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25628067003725971776289745 19221050252794478832217309)
  ·
    refine ⟨7207893844797929562081491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19221050252794478832217309 7207893844797929562081491)
    ·
      refine ⟨10811840767196894343122237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207893844797929562081491 10811840767196894343122237)
      ·
        refine ⟨4054440287698835378670839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10811840767196894343122237 4054440287698835378670839)
        ·
          refine ⟨6081660431548253068006259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054440287698835378670839 6081660431548253068006259)
          ·
            refine ⟨9122490647322379602009389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081660431548253068006259 9122490647322379602009389)
            ·
              refine ⟨3420933992745892350753521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9122490647322379602009389 3420933992745892350753521)
              ·
                refine ⟨2565700494559419263065141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420933992745892350753521 2565700494559419263065141)
                ·
                  refine ⟨240534421364945555912357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2565700494559419263065141 240534421364945555912357)
                  ·
                    rfl

theorem cell21_1053988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_1053988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1053988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1053988 prefixEnd_1053988 := by exact prefixLift 1053988
  have htrace : WordTrace (prefixWord ++ tailWord_1053988) baseStart_1053988 baseEnd_1053988 := by
    simpa [prefixWord, tailWord_1053988, baseEnd_1053988] using wordTrace_append hprefix tailTrace_1053988
  have hstable : (prefixWord ++ tailWord_1053988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053988).length < 2 ^ (prefixWord ++ tailWord_1053988).sum := by decide
  have hdescent : baseEnd_1053988 < baseStart_1053988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054005 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1054005 : Nat := 118140960795 + 1054005 * 2 ^ 59
def prefixEnd_1054005 : Nat := 4983230072969 + 3 ^ 40 * 1054005 * 2
def baseEnd_1054005 : Nat := 240538300996557304128989

theorem tailTrace_1054005 : CollatzResearch.WordTrace tailWord_1054005 prefixEnd_1054005 240538300996557304128989 := by
  unfold tailWord_1054005
  simp only [CollatzResearch.WordTrace]
  refine ⟨38442720546527369567803469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25628480364351579711868979 38442720546527369567803469)
  ·
    refine ⟨14416020204947763587926301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38442720546527369567803469 14416020204947763587926301)
    ·
      refine ⟨5406007576855411345472363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14416020204947763587926301 5406007576855411345472363)
      ·
        refine ⟨8109011365283117018208545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406007576855411345472363 8109011365283117018208545)
        ·
          refine ⟨6081758523962337763656409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8109011365283117018208545 6081758523962337763656409)
          ·
            refine ⟨4561318892971753322742307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081758523962337763656409 4561318892971753322742307)
            ·
              refine ⟨6841978339457629984113461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561318892971753322742307 6841978339457629984113461)
              ·
                refine ⟨641435469324152811010637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6841978339457629984113461 641435469324152811010637)
                ·
                  refine ⟨240538300996557304128989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641435469324152811010637 240538300996557304128989)
                  ·
                    rfl

theorem cell21_1054005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1054005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054005 prefixEnd_1054005 := by exact prefixLift 1054005
  have htrace : WordTrace (prefixWord ++ tailWord_1054005) baseStart_1054005 baseEnd_1054005 := by
    simpa [prefixWord, tailWord_1054005, baseEnd_1054005] using wordTrace_append hprefix tailTrace_1054005
  have hstable : (prefixWord ++ tailWord_1054005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054005).length < 2 ^ (prefixWord ++ tailWord_1054005).sum := by decide
  have hdescent : baseEnd_1054005 < baseStart_1054005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054016 : List Nat := [2, 1, 1, 2, 2, 1, 12]
def baseStart_1054016 : Nat := 118140960795 + 1054016 * 2 ^ 59
def prefixEnd_1054016 : Nat := 4983230072969 + 3 ^ 40 * 1054016 * 2
def baseEnd_1054016 : Nat := 26726756816269303271737

theorem tailTrace_1054016 : CollatzResearch.WordTrace tailWord_1054016 prefixEnd_1054016 26726756816269303271737 := by
  unfold tailWord_1054016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19221560874743759223226951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25628747832991678964302601 19221560874743759223226951)
  ·
    refine ⟨28832341312115638834840427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19221560874743759223226951 28832341312115638834840427)
    ·
      refine ⟨43248511968173458252260641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28832341312115638834840427 43248511968173458252260641)
      ·
        refine ⟨32436383976130093689195481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43248511968173458252260641 32436383976130093689195481)
        ·
          refine ⟨24327287982097570266896611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32436383976130093689195481 24327287982097570266896611)
          ·
            refine ⟨36490931973146355400344917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24327287982097570266896611 36490931973146355400344917)
            ·
              refine ⟨26726756816269303271737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36490931973146355400344917 26726756816269303271737)
              ·
                rfl

theorem cell21_1054016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 12].length) (baseStart_1054016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054016 prefixEnd_1054016 := by exact prefixLift 1054016
  have htrace : WordTrace (prefixWord ++ tailWord_1054016) baseStart_1054016 baseEnd_1054016 := by
    simpa [prefixWord, tailWord_1054016, baseEnd_1054016] using wordTrace_append hprefix tailTrace_1054016
  have hstable : (prefixWord ++ tailWord_1054016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054016).length < 2 ^ (prefixWord ++ tailWord_1054016).sum := by decide
  have hdescent : baseEnd_1054016 < baseStart_1054016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054036 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1054036 : Nat := 118140960795 + 1054036 * 2 ^ 59
def prefixEnd_1054036 : Nat := 4983230072969 + 3 ^ 40 * 1054036 * 2
def baseEnd_1054036 : Nat := 240545375618908139112259

theorem tailTrace_1054036 : CollatzResearch.WordTrace tailWord_1054036 prefixEnd_1054036 240545375618908139112259 := by
  unfold tailWord_1054036
  simp only [CollatzResearch.WordTrace]
  refine ⟨19221925604707530931090981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25629234139610041241454641 19221925604707530931090981)
  ·
    refine ⟨3604111050882662049579559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19221925604707530931090981 3604111050882662049579559)
    ·
      refine ⟨5406166576323993074369339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604111050882662049579559 5406166576323993074369339)
      ·
        refine ⟨8109249864485989611554009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406166576323993074369339 8109249864485989611554009)
        ·
          refine ⟨6081937398364492208665507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8109249864485989611554009 6081937398364492208665507)
          ·
            refine ⟨9122906097546738312998261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081937398364492208665507 9122906097546738312998261)
            ·
              refine ⟨855272446645006716843587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9122906097546738312998261 855272446645006716843587)
              ·
                refine ⟨1282908669967510075265381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855272446645006716843587 1282908669967510075265381)
                ·
                  refine ⟨240545375618908139112259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282908669967510075265381 240545375618908139112259)
                  ·
                    rfl

theorem cell21_1054036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1054036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054036 prefixEnd_1054036 := by exact prefixLift 1054036
  have htrace : WordTrace (prefixWord ++ tailWord_1054036) baseStart_1054036 baseEnd_1054036 := by
    simpa [prefixWord, tailWord_1054036, baseEnd_1054036] using wordTrace_append hprefix tailTrace_1054036
  have hstable : (prefixWord ++ tailWord_1054036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054036).length < 2 ^ (prefixWord ++ tailWord_1054036).sum := by decide
  have hdescent : baseEnd_1054036 < baseStart_1054036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054109 : List Nat := [1, 4, 2, 1, 3, 1, 2, 7]
def baseStart_1054109 : Nat := 118140960795 + 1054109 * 2 ^ 59
def prefixEnd_1054109 : Nat := 4983230072969 + 3 ^ 40 * 1054109 * 2
def baseEnd_1054109 : Nat := 80187345071158744798481

theorem tailTrace_1054109 : CollatzResearch.WordTrace tailWord_1054109 prefixEnd_1054109 80187345071158744798481 := by
  unfold tailWord_1054109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38446513738150595329589381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25631009158767063553059587 38446513738150595329589381)
  ·
    refine ⟨7208721325903236624298009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38446513738150595329589381 7208721325903236624298009)
    ·
      refine ⟨5406540994427427468223507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7208721325903236624298009 5406540994427427468223507)
      ·
        refine ⟨8109811491641141202335261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406540994427427468223507 8109811491641141202335261)
        ·
          refine ⟨3041179309365427950875723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8109811491641141202335261 3041179309365427950875723)
          ·
            refine ⟨4561768964048141926313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041179309365427950875723 4561768964048141926313585)
            ·
              refine ⟨3421326723036106444735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561768964048141926313585 3421326723036106444735189)
              ·
                refine ⟨80187345071158744798481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3421326723036106444735189 80187345071158744798481)
                ·
                  rfl

theorem cell21_1054109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 7].length) (baseStart_1054109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054109 prefixEnd_1054109 := by exact prefixLift 1054109
  have htrace : WordTrace (prefixWord ++ tailWord_1054109) baseStart_1054109 baseEnd_1054109 := by
    simpa [prefixWord, tailWord_1054109, baseEnd_1054109] using wordTrace_append hprefix tailTrace_1054109
  have hstable : (prefixWord ++ tailWord_1054109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054109).length < 2 ^ (prefixWord ++ tailWord_1054109).sum := by decide
  have hdescent : baseEnd_1054109 < baseStart_1054109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054168 : List Nat := [2, 1, 2, 2, 2, 1, 2, 9]
def baseStart_1054168 : Nat := 118140960795 + 1054168 * 2 ^ 59
def prefixEnd_1054168 : Nat := 4983230072969 + 3 ^ 40 * 1054168 * 2
def baseEnd_1054168 : Nat := 80191833272435080970663

theorem tailTrace_1054168 : CollatzResearch.WordTrace tailWord_1054168 prefixEnd_1054168 80191833272435080970663 := by
  unfold tailWord_1054168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224332822468424202993579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25632443763291232270658105 19224332822468424202993579)
  ·
    refine ⟨28836499233702636304490369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224332822468424202993579 28836499233702636304490369)
    ·
      refine ⟨21627374425276977228367777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28836499233702636304490369 21627374425276977228367777)
      ·
        refine ⟨16220530818957732921275833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21627374425276977228367777 16220530818957732921275833)
        ·
          refine ⟨12165398114218299690956875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16220530818957732921275833 12165398114218299690956875)
          ·
            refine ⟨18248097171327449536435313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12165398114218299690956875 18248097171327449536435313)
            ·
              refine ⟨13686072878495587152326485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18248097171327449536435313 13686072878495587152326485)
              ·
                refine ⟨80191833272435080970663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13686072878495587152326485 80191833272435080970663)
                ·
                  rfl

theorem cell21_1054168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_1054168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054168 prefixEnd_1054168 := by exact prefixLift 1054168
  have htrace : WordTrace (prefixWord ++ tailWord_1054168) baseStart_1054168 baseEnd_1054168 := by
    simpa [prefixWord, tailWord_1054168, baseEnd_1054168] using wordTrace_append hprefix tailTrace_1054168
  have hstable : (prefixWord ++ tailWord_1054168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054168).length < 2 ^ (prefixWord ++ tailWord_1054168).sum := by decide
  have hdescent : baseEnd_1054168 < baseStart_1054168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054219 : List Nat := [1, 1, 1, 1, 9, 1, 2, 5]
def baseStart_1054219 : Nat := 118140960795 + 1054219 * 2 ^ 59
def prefixEnd_1054219 : Nat := 4983230072969 + 3 ^ 40 * 1054219 * 2
def baseEnd_1054219 : Nat := 80195712904046829187295

theorem tailTrace_1054219 : CollatzResearch.WordTrace tailWord_1054219 prefixEnd_1054219 80195712904046829187295 := by
  unfold tailWord_1054219
  simp only [CollatzResearch.WordTrace]
  refine ⟨38450525767752084116093711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25633683845168056077395807 38450525767752084116093711)
  ·
    refine ⟨57675788651628126174140567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38450525767752084116093711 57675788651628126174140567)
    ·
      refine ⟨86513682977442189261210851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57675788651628126174140567 86513682977442189261210851)
      ·
        refine ⟨129770524466163283891816277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86513682977442189261210851 129770524466163283891816277)
        ·
          refine ⟨760374166793925491553611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 129770524466163283891816277 760374166793925491553611)
          ·
            refine ⟨1140561250190888237330417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760374166793925491553611 1140561250190888237330417)
            ·
              refine ⟨855420937643166177997813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140561250190888237330417 855420937643166177997813)
              ·
                refine ⟨80195712904046829187295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855420937643166177997813 80195712904046829187295)
                ·
                  rfl

theorem cell21_1054219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].length) (baseStart_1054219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054219 prefixEnd_1054219 := by exact prefixLift 1054219
  have htrace : WordTrace (prefixWord ++ tailWord_1054219) baseStart_1054219 baseEnd_1054219 := by
    simpa [prefixWord, tailWord_1054219, baseEnd_1054219] using wordTrace_append hprefix tailTrace_1054219
  have hstable : (prefixWord ++ tailWord_1054219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054219).length < 2 ^ (prefixWord ++ tailWord_1054219).sum := by decide
  have hdescent : baseEnd_1054219 < baseStart_1054219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054250 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_1054250 : Nat := 118140960795 + 1054250 * 2 ^ 59
def prefixEnd_1054250 : Nat := 4983230072969 + 3 ^ 40 * 1054250 * 2
def baseEnd_1054250 : Nat := 240594213334491322545155

theorem tailTrace_1054250 : CollatzResearch.WordTrace tailWord_1054250 prefixEnd_1054250 240594213334491322545155 := by
  unfold tailWord_1054250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612914107659944102618051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25634437620426517606981469 9612914107659944102618051)
  ·
    refine ⟨14419371161489916153927077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9612914107659944102618051 14419371161489916153927077)
    ·
      refine ⟨2703632092779359278861327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14419371161489916153927077 2703632092779359278861327)
      ·
        refine ⟨4055448139169038918291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703632092779359278861327 4055448139169038918291991)
        ·
          refine ⟨6083172208753558377437987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055448139169038918291991 6083172208753558377437987)
          ·
            refine ⟨9124758313130337566156981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083172208753558377437987 9124758313130337566156981)
            ·
              refine ⟨855446091855969146827217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9124758313130337566156981 855446091855969146827217)
              ·
                refine ⟨641584568891976860120413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855446091855969146827217 641584568891976860120413)
                ·
                  refine ⟨240594213334491322545155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641584568891976860120413 240594213334491322545155)
                  ·
                    rfl

theorem cell21_1054250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_1054250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054250 prefixEnd_1054250 := by exact prefixLift 1054250
  have htrace : WordTrace (prefixWord ++ tailWord_1054250) baseStart_1054250 baseEnd_1054250 := by
    simpa [prefixWord, tailWord_1054250, baseEnd_1054250] using wordTrace_append hprefix tailTrace_1054250
  have hstable : (prefixWord ++ tailWord_1054250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054250).length < 2 ^ (prefixWord ++ tailWord_1054250).sum := by decide
  have hdescent : baseEnd_1054250 < baseStart_1054250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054261 : List Nat := [1, 3, 3, 1, 1, 4, 2, 6]
def baseStart_1054261 : Nat := 118140960795 + 1054261 * 2 ^ 59
def prefixEnd_1054261 : Nat := 4983230072969 + 3 ^ 40 * 1054261 * 2
def baseEnd_1054261 : Nat := 80198907894785915953933

theorem tailTrace_1054261 : CollatzResearch.WordTrace tailWord_1054261 prefixEnd_1054261 80198907894785915953933 := by
  unfold tailWord_1054261
  simp only [CollatzResearch.WordTrace]
  refine ⟨38452057633599925289122637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25634705089066616859415091 38452057633599925289122637)
  ·
    refine ⟨14419521612599971983420989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38452057633599925289122637 14419521612599971983420989)
    ·
      refine ⟨5407320604724989493782871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14419521612599971983420989 5407320604724989493782871)
      ·
        refine ⟨8110980907087484240674307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5407320604724989493782871 8110980907087484240674307)
        ·
          refine ⟨12166471360631226361011461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110980907087484240674307 12166471360631226361011461)
          ·
            refine ⟨2281213380118354942689649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12166471360631226361011461 2281213380118354942689649)
            ·
              refine ⟨1710910035088766207017237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281213380118354942689649 1710910035088766207017237)
              ·
                refine ⟨80198907894785915953933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1710910035088766207017237 80198907894785915953933)
                ·
                  rfl

theorem cell21_1054261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_1054261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054261 prefixEnd_1054261 := by exact prefixLift 1054261
  have htrace : WordTrace (prefixWord ++ tailWord_1054261) baseStart_1054261 baseEnd_1054261 := by
    simpa [prefixWord, tailWord_1054261, baseEnd_1054261] using wordTrace_append hprefix tailTrace_1054261
  have hstable : (prefixWord ++ tailWord_1054261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054261).length < 2 ^ (prefixWord ++ tailWord_1054261).sum := by decide
  have hdescent : baseEnd_1054261 < baseStart_1054261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054264 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_1054264 : Nat := 118140960795 + 1054264 * 2 ^ 59
def prefixEnd_1054264 : Nat := 4983230072969 + 3 ^ 40 * 1054264 * 2
def baseEnd_1054264 : Nat := 240597408325230409311793

theorem tailTrace_1054264 : CollatzResearch.WordTrace tailWord_1054264 prefixEnd_1054264 240597408325230409311793 := by
  unfold tailWord_1054264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19226083526294528400740923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25634778035059371200987897 19226083526294528400740923)
  ·
    refine ⟨28839125289441792601111385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19226083526294528400740923 28839125289441792601111385)
    ·
      refine ⟨21629343967081344450833539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28839125289441792601111385 21629343967081344450833539)
      ·
        refine ⟨32444015950622016676250309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21629343967081344450833539 32444015950622016676250309)
        ·
          refine ⟨6083252990741628126796933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32444015950622016676250309 6083252990741628126796933)
          ·
            refine ⟨1140609935764055273774425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6083252990741628126796933 1140609935764055273774425)
            ·
              refine ⟨855457451823041455330819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140609935764055273774425 855457451823041455330819)
              ·
                refine ⟨1283186177734562182996229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855457451823041455330819 1283186177734562182996229)
                ·
                  refine ⟨240597408325230409311793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283186177734562182996229 240597408325230409311793)
                  ·
                    rfl

theorem cell21_1054264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_1054264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054264 prefixEnd_1054264 := by exact prefixLift 1054264
  have htrace : WordTrace (prefixWord ++ tailWord_1054264) baseStart_1054264 baseEnd_1054264 := by
    simpa [prefixWord, tailWord_1054264, baseEnd_1054264] using wordTrace_append hprefix tailTrace_1054264
  have hstable : (prefixWord ++ tailWord_1054264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054264).length < 2 ^ (prefixWord ++ tailWord_1054264).sum := by decide
  have hdescent : baseEnd_1054264 < baseStart_1054264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054301 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1054301 : Nat := 118140960795 + 1054301 * 2 ^ 59
def prefixEnd_1054301 : Nat := 4983230072969 + 3 ^ 40 * 1054301 * 2
def baseEnd_1054301 : Nat := 240605852229326567195051

theorem tailTrace_1054301 : CollatzResearch.WordTrace tailWord_1054301 prefixEnd_1054301 240605852229326567195051 := by
  unfold tailWord_1054301
  simp only [CollatzResearch.WordTrace]
  refine ⟨38453516553455012120578757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25635677702303341413719171 38453516553455012120578757)
  ·
    refine ⟨7210034353772814772608517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38453516553455012120578757 7210034353772814772608517)
    ·
      refine ⟨1351881441332402769864097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7210034353772814772608517 1351881441332402769864097)
      ·
        refine ⟨1013911080999302077398073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351881441332402769864097 1013911080999302077398073)
        ·
          refine ⟨760433310749476558048555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013911080999302077398073 760433310749476558048555)
          ·
            refine ⟨1140649966124214837072833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760433310749476558048555 1140649966124214837072833)
            ·
              refine ⟨855487474593161127804625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140649966124214837072833 855487474593161127804625)
              ·
                refine ⟨641615605944870845853469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855487474593161127804625 641615605944870845853469)
                ·
                  refine ⟨240605852229326567195051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641615605944870845853469 240605852229326567195051)
                  ·
                    rfl

theorem cell21_1054301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1054301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054301 prefixEnd_1054301 := by exact prefixLift 1054301
  have htrace : WordTrace (prefixWord ++ tailWord_1054301) baseStart_1054301 baseEnd_1054301 := by
    simpa [prefixWord, tailWord_1054301, baseEnd_1054301] using wordTrace_append hprefix tailTrace_1054301
  have hstable : (prefixWord ++ tailWord_1054301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054301).length < 2 ^ (prefixWord ++ tailWord_1054301).sum := by decide
  have hdescent : baseEnd_1054301 < baseStart_1054301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054309 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1054309 : Nat := 118140960795 + 1054309 * 2 ^ 59
def prefixEnd_1054309 : Nat := 4983230072969 + 3 ^ 40 * 1054309 * 2
def baseEnd_1054309 : Nat := 240607677938320331061701

theorem tailTrace_1054309 : CollatzResearch.WordTrace tailWord_1054309 prefixEnd_1054309 240607677938320331061701 := by
  unfold tailWord_1054309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38453808337426029486869981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25635872224950686324579987 38453808337426029486869981)
  ·
    refine ⟨14420178126534761057576243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38453808337426029486869981 14420178126534761057576243)
    ·
      refine ⟨21630267189802141586364365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14420178126534761057576243 21630267189802141586364365)
      ·
        refine ⟨8111350196175803094886637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21630267189802141586364365 8111350196175803094886637)
        ·
          refine ⟨3041756323565926160582489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8111350196175803094886637 3041756323565926160582489)
          ·
            refine ⟨2281317242674444620436867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041756323565926160582489 2281317242674444620436867)
            ·
              refine ⟨3421975864011666930655301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281317242674444620436867 3421975864011666930655301)
              ·
                refine ⟨641620474502187549497869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3421975864011666930655301 641620474502187549497869)
                ·
                  refine ⟨240607677938320331061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641620474502187549497869 240607677938320331061701)
                  ·
                    rfl

theorem cell21_1054309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1054309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054309 prefixEnd_1054309 := by exact prefixLift 1054309
  have htrace : WordTrace (prefixWord ++ tailWord_1054309) baseStart_1054309 baseEnd_1054309 := by
    simpa [prefixWord, tailWord_1054309, baseEnd_1054309] using wordTrace_append hprefix tailTrace_1054309
  have hstable : (prefixWord ++ tailWord_1054309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054309).length < 2 ^ (prefixWord ++ tailWord_1054309).sum := by decide
  have hdescent : baseEnd_1054309 < baseStart_1054309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054368 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_1054368 : Nat := 118140960795 + 1054368 * 2 ^ 59
def prefixEnd_1054368 : Nat := 4983230072969 + 3 ^ 40 * 1054368 * 2
def baseEnd_1054368 : Nat := 240621142542149339578247

theorem tailTrace_1054368 : CollatzResearch.WordTrace tailWord_1054368 prefixEnd_1054368 240621142542149339578247 := by
  unfold tailWord_1054368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19227980122106141281633879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25637306829474855042178505 19227980122106141281633879)
  ·
    refine ⟨28841970183159211922450819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19227980122106141281633879 28841970183159211922450819)
    ·
      refine ⟨43262955274738817883676229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28841970183159211922450819 43262955274738817883676229)
      ·
        refine ⟨8111804114013528353189293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43262955274738817883676229 8111804114013528353189293)
        ·
          refine ⟨3041926542755073132445985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8111804114013528353189293 3041926542755073132445985)
          ·
            refine ⟨2281444907066304849334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041926542755073132445985 2281444907066304849334489)
            ·
              refine ⟨1711083680299728637000867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281444907066304849334489 1711083680299728637000867)
              ·
                refine ⟨2566625520449592955501301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711083680299728637000867 2566625520449592955501301)
                ·
                  refine ⟨240621142542149339578247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2566625520449592955501301 240621142542149339578247)
                  ·
                    rfl

theorem cell21_1054368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_1054368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054368 prefixEnd_1054368 := by exact prefixLift 1054368
  have htrace : WordTrace (prefixWord ++ tailWord_1054368) baseStart_1054368 baseEnd_1054368 := by
    simpa [prefixWord, tailWord_1054368, baseEnd_1054368] using wordTrace_append hprefix tailTrace_1054368
  have hstable : (prefixWord ++ tailWord_1054368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054368).length < 2 ^ (prefixWord ++ tailWord_1054368).sum := by decide
  have hdescent : baseEnd_1054368 < baseStart_1054368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054433 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 4]
def baseStart_1054433 : Nat := 118140960795 + 1054433 * 2 ^ 59
def prefixEnd_1054433 : Nat := 4983230072969 + 3 ^ 40 * 1054433 * 2
def baseEnd_1054433 : Nat := 240635976427723670994781

theorem tailTrace_1054433 : CollatzResearch.WordTrace tailWord_1054433 prefixEnd_1054433 240635976427723670994781 := by
  unfold tailWord_1054433
  simp only [CollatzResearch.WordTrace]
  refine ⟨38458330988976798664383953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25638887325984532442922635 38458330988976798664383953)
  ·
    refine ⟨28843748241732598998287965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38458330988976798664383953 28843748241732598998287965)
    ·
      refine ⟨10816405590649724624357987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28843748241732598998287965 10816405590649724624357987)
      ·
        refine ⟨16224608385974586936536981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10816405590649724624357987 16224608385974586936536981)
        ·
          refine ⟨760528518092558762650171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16224608385974586936536981 760528518092558762650171)
          ·
            refine ⟨1140792777138838143975257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760528518092558762650171 1140792777138838143975257)
            ·
              refine ⟨855594582854128607981443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140792777138838143975257 855594582854128607981443)
              ·
                refine ⟨1283391874281192911972165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855594582854128607981443 1283391874281192911972165)
                ·
                  refine ⟨240635976427723670994781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283391874281192911972165 240635976427723670994781)
                  ·
                    rfl

theorem cell21_1054433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_1054433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054433 prefixEnd_1054433 := by exact prefixLift 1054433
  have htrace : WordTrace (prefixWord ++ tailWord_1054433) baseStart_1054433 baseEnd_1054433 := by
    simpa [prefixWord, tailWord_1054433, baseEnd_1054433] using wordTrace_append hprefix tailTrace_1054433
  have hstable : (prefixWord ++ tailWord_1054433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054433).length < 2 ^ (prefixWord ++ tailWord_1054433).sum := by decide
  have hdescent : baseEnd_1054433 < baseStart_1054433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054520 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_1054520 : Nat := 118140960795 + 1054520 * 2 ^ 59
def prefixEnd_1054520 : Nat := 4983230072969 + 3 ^ 40 * 1054520 * 2
def baseEnd_1054520 : Nat := 240655831013030853044603

theorem tailTrace_1054520 : CollatzResearch.WordTrace tailWord_1054520 prefixEnd_1054520 240655831013030853044603 := by
  unfold tailWord_1054520
  simp only [CollatzResearch.WordTrace]
  refine ⟨19230752069830806261400507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25641002759774408348534009 19230752069830806261400507)
  ·
    refine ⟨28846128104746209392100761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19230752069830806261400507 28846128104746209392100761)
    ·
      refine ⟨21634596078559657044075571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28846128104746209392100761 21634596078559657044075571)
      ·
        refine ⟨32451894117839485566113357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21634596078559657044075571 32451894117839485566113357)
        ·
          refine ⟨12169460294189807087292509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32451894117839485566113357 12169460294189807087292509)
          ·
            refine ⟨4563547610321177657734691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12169460294189807087292509 4563547610321177657734691)
            ·
              refine ⟨6845321415481766486602037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563547610321177657734691 6845321415481766486602037)
              ·
                refine ⟨641748882701415608118941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6845321415481766486602037 641748882701415608118941)
                ·
                  refine ⟨240655831013030853044603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641748882701415608118941 240655831013030853044603)
                  ·
                    rfl

theorem cell21_1054520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_1054520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054520 prefixEnd_1054520 := by exact prefixLift 1054520
  have htrace : WordTrace (prefixWord ++ tailWord_1054520) baseStart_1054520 baseEnd_1054520 := by
    simpa [prefixWord, tailWord_1054520, baseEnd_1054520] using wordTrace_append hprefix tailTrace_1054520
  have hstable : (prefixWord ++ tailWord_1054520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054520).length < 2 ^ (prefixWord ++ tailWord_1054520).sum := by decide
  have hdescent : baseEnd_1054520 < baseStart_1054520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054582 : List Nat := [5, 1, 1, 3, 2, 2, 7]
def baseStart_1054582 : Nat := 118140960795 + 1054582 * 2 ^ 59
def prefixEnd_1054582 : Nat := 4983230072969 + 3 ^ 40 * 1054582 * 2
def baseEnd_1054582 : Nat := 26741108917525835890127

theorem tailTrace_1054582 : CollatzResearch.WordTrace tailWord_1054582 prefixEnd_1054582 26741108917525835890127 := by
  unfold tailWord_1054582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403985341589812319472375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25642510310291331407705333 2403985341589812319472375)
  ·
    refine ⟨3605978012384718479208563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2403985341589812319472375 3605978012384718479208563)
    ·
      refine ⟨5408967018577077718812845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3605978012384718479208563 5408967018577077718812845)
      ·
        refine ⟨2028362631966404144554817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5408967018577077718812845 2028362631966404144554817)
        ·
          refine ⟨1521271973974803108416113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028362631966404144554817 1521271973974803108416113)
          ·
            refine ⟨1140953980481102331312085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521271973974803108416113 1140953980481102331312085)
            ·
              refine ⟨26741108917525835890127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1140953980481102331312085 26741108917525835890127)
              ·
                rfl

theorem cell21_1054582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 7].length) (baseStart_1054582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054582 prefixEnd_1054582 := by exact prefixLift 1054582
  have htrace : WordTrace (prefixWord ++ tailWord_1054582) baseStart_1054582 baseEnd_1054582 := by
    simpa [prefixWord, tailWord_1054582, baseEnd_1054582] using wordTrace_append hprefix tailTrace_1054582
  have hstable : (prefixWord ++ tailWord_1054582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054582).length < 2 ^ (prefixWord ++ tailWord_1054582).sum := by decide
  have hdescent : baseEnd_1054582 < baseStart_1054582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054596 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1054596 : Nat := 118140960795 + 1054596 * 2 ^ 59
def prefixEnd_1054596 : Nat := 4983230072969 + 3 ^ 40 * 1054596 * 2
def baseEnd_1054596 : Nat := 240673175248471609777781

theorem tailTrace_1054596 : CollatzResearch.WordTrace tailWord_1054596 prefixEnd_1054596 240673175248471609777781 := by
  unfold tailWord_1054596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19232138043693138751283821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25642850724924185001711761 19232138043693138751283821)
  ·
    refine ⟨7212051766384927031731433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19232138043693138751283821 7212051766384927031731433)
    ·
      refine ⟨5409038824788695273798575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7212051766384927031731433 5409038824788695273798575)
      ·
        refine ⟨8113558237183042910697863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409038824788695273798575 8113558237183042910697863)
        ·
          refine ⟨12170337355774564366046795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8113558237183042910697863 12170337355774564366046795)
          ·
            refine ⟨18255506033661846549070193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12170337355774564366046795 18255506033661846549070193)
            ·
              refine ⟨13691629525246384911802645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18255506033661846549070193 13691629525246384911802645)
              ·
                refine ⟨641795133995924292740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13691629525246384911802645 641795133995924292740749)
                ·
                  refine ⟨240673175248471609777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641795133995924292740749 240673175248471609777781)
                  ·
                    rfl

theorem cell21_1054596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1054596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054596 prefixEnd_1054596 := by exact prefixLift 1054596
  have htrace : WordTrace (prefixWord ++ tailWord_1054596) baseStart_1054596 baseEnd_1054596 := by
    simpa [prefixWord, tailWord_1054596, baseEnd_1054596] using wordTrace_append hprefix tailTrace_1054596
  have hstable : (prefixWord ++ tailWord_1054596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054596).length < 2 ^ (prefixWord ++ tailWord_1054596).sum := by decide
  have hdescent : baseEnd_1054596 < baseStart_1054596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054726 : List Nat := [6, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1054726 : Nat := 118140960795 + 1054726 * 2 ^ 59
def prefixEnd_1054726 : Nat := 4983230072969 + 3 ^ 40 * 1054726 * 2
def baseEnd_1054726 : Nat := 80234281006540090870283

theorem tailTrace_1054726 : CollatzResearch.WordTrace tailWord_1054726 prefixEnd_1054726 80234281006540090870283 := by
  unfold tailWord_1054726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202156799278603428275001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25646011717943539803200021 1202156799278603428275001)
  ·
    refine ⟨901617599458952571206251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1202156799278603428275001 901617599458952571206251)
    ·
      refine ⟨1352426399188428856809377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901617599458952571206251 1352426399188428856809377)
      ·
        refine ⟨1014319799391321642607033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352426399188428856809377 1014319799391321642607033)
        ·
          refine ⟨760739849543491231955275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014319799391321642607033 760739849543491231955275)
          ·
            refine ⟨1141109774315236847932913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760739849543491231955275 1141109774315236847932913)
            ·
              refine ⟨855832330736427635949685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141109774315236847932913 855832330736427635949685)
              ·
                refine ⟨80234281006540090870283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855832330736427635949685 80234281006540090870283)
                ·
                  rfl

theorem cell21_1054726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1054726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054726 prefixEnd_1054726 := by exact prefixLift 1054726
  have htrace : WordTrace (prefixWord ++ tailWord_1054726) baseStart_1054726 baseEnd_1054726 := by
    simpa [prefixWord, tailWord_1054726, baseEnd_1054726] using wordTrace_append hprefix tailTrace_1054726
  have hstable : (prefixWord ++ tailWord_1054726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054726).length < 2 ^ (prefixWord ++ tailWord_1054726).sum := by decide
  have hdescent : baseEnd_1054726 < baseStart_1054726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054740 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1054740 : Nat := 118140960795 + 1054740 * 2 ^ 59
def prefixEnd_1054740 : Nat := 4983230072969 + 3 ^ 40 * 1054740 * 2
def baseEnd_1054740 : Nat := 240706038010359359377487

theorem tailTrace_1054740 : CollatzResearch.WordTrace tailWord_1054740 prefixEnd_1054740 240706038010359359377487 := by
  unfold tailWord_1054740
  simp only [CollatzResearch.WordTrace]
  refine ⟨19234764099432295047904837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25646352132576393397206449 19234764099432295047904837)
  ·
    refine ⟨3606518268643555321482157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19234764099432295047904837 3606518268643555321482157)
    ·
      refine ⟨1352444350741333245555809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3606518268643555321482157 1352444350741333245555809)
      ·
        refine ⟨1014333263055999934166857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352444350741333245555809 1014333263055999934166857)
        ·
          refine ⟨760749947291999950625143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014333263055999934166857 760749947291999950625143)
          ·
            refine ⟨1141124920937999925937715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760749947291999950625143 1141124920937999925937715)
            ·
              refine ⟨1711687381406999888906573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141124920937999925937715 1711687381406999888906573)
              ·
                refine ⟨641882768027624958339965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711687381406999888906573 641882768027624958339965)
                ·
                  refine ⟨240706038010359359377487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 641882768027624958339965 240706038010359359377487)
                  ·
                    rfl

theorem cell21_1054740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1054740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054740 prefixEnd_1054740 := by exact prefixLift 1054740
  have htrace : WordTrace (prefixWord ++ tailWord_1054740) baseStart_1054740 baseEnd_1054740 := by
    simpa [prefixWord, tailWord_1054740, baseEnd_1054740] using wordTrace_append hprefix tailTrace_1054740
  have hstable : (prefixWord ++ tailWord_1054740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054740).length < 2 ^ (prefixWord ++ tailWord_1054740).sum := by decide
  have hdescent : baseEnd_1054740 < baseStart_1054740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054762 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1054762 : Nat := 118140960795 + 1054762 * 2 ^ 59
def prefixEnd_1054762 : Nat := 4983230072969 + 3 ^ 40 * 1054762 * 2
def baseEnd_1054762 : Nat := 240711058710092210010775

theorem tailTrace_1054762 : CollatzResearch.WordTrace tailWord_1054762 prefixEnd_1054762 240711058710092210010775 := by
  unfold tailWord_1054762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9617582651196221963277635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25646887069856591902073693 9617582651196221963277635)
  ·
    refine ⟨14426373976794332944916453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9617582651196221963277635 14426373976794332944916453)
    ·
      refine ⟨2704945120648937427171835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14426373976794332944916453 2704945120648937427171835)
      ·
        refine ⟨4057417680973406140757753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704945120648937427171835 4057417680973406140757753)
        ·
          refine ⟨3043063260730054605568315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4057417680973406140757753 3043063260730054605568315)
          ·
            refine ⟨4564594891095081908352473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043063260730054605568315 4564594891095081908352473)
            ·
              refine ⟨3423446168321311431264355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4564594891095081908352473 3423446168321311431264355)
              ·
                refine ⟨5135169252481967146896533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423446168321311431264355 5135169252481967146896533)
                ·
                  refine ⟨240711058710092210010775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5135169252481967146896533 240711058710092210010775)
                  ·
                    rfl

theorem cell21_1054762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1054762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054762 prefixEnd_1054762 := by exact prefixLift 1054762
  have htrace : WordTrace (prefixWord ++ tailWord_1054762) baseStart_1054762 baseEnd_1054762 := by
    simpa [prefixWord, tailWord_1054762, baseEnd_1054762] using wordTrace_append hprefix tailTrace_1054762
  have hstable : (prefixWord ++ tailWord_1054762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054762).length < 2 ^ (prefixWord ++ tailWord_1054762).sum := by decide
  have hdescent : baseEnd_1054762 < baseStart_1054762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054872 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_1054872 : Nat := 118140960795 + 1054872 * 2 ^ 59
def prefixEnd_1054872 : Nat := 4983230072969 + 3 ^ 40 * 1054872 * 2
def baseEnd_1054872 : Nat := 240736162208756463177217

theorem tailTrace_1054872 : CollatzResearch.WordTrace tailWord_1054872 prefixEnd_1054872 240736162208756463177217 := by
  unfold tailWord_1054872
  simp only [CollatzResearch.WordTrace]
  refine ⟨19237171317193188319807435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25649561756257584426409913 19237171317193188319807435)
  ·
    refine ⟨28855756975789782479711153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19237171317193188319807435 28855756975789782479711153)
    ·
      refine ⟨21641817731842336859783365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28855756975789782479711153 21641817731842336859783365)
      ·
        refine ⟨4057840824720438161209381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21641817731842336859783365 4057840824720438161209381)
        ·
          refine ⟨760845154635082155226759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4057840824720438161209381 760845154635082155226759)
          ·
            refine ⟨1141267731952623232840139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760845154635082155226759 1141267731952623232840139)
            ·
              refine ⟨1711901597928934849260209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141267731952623232840139 1711901597928934849260209)
              ·
                refine ⟨1283926198446701136945157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711901597928934849260209 1283926198446701136945157)
                ·
                  refine ⟨240736162208756463177217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283926198446701136945157 240736162208756463177217)
                  ·
                    rfl

theorem cell21_1054872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_1054872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054872 prefixEnd_1054872 := by exact prefixLift 1054872
  have htrace : WordTrace (prefixWord ++ tailWord_1054872) baseStart_1054872 baseEnd_1054872 := by
    simpa [prefixWord, tailWord_1054872, baseEnd_1054872] using wordTrace_append hprefix tailTrace_1054872
  have hstable : (prefixWord ++ tailWord_1054872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054872).length < 2 ^ (prefixWord ++ tailWord_1054872).sum := by decide
  have hdescent : baseEnd_1054872 < baseStart_1054872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054990 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1054990 : Nat := 118140960795 + 1054990 * 2 ^ 59
def prefixEnd_1054990 : Nat := 4983230072969 + 3 ^ 40 * 1054990 * 2
def baseEnd_1054990 : Nat := 240763091416414480210309

theorem tailTrace_1054990 : CollatzResearch.WordTrace tailWord_1054990 prefixEnd_1054990 240763091416414480210309 := by
  unfold tailWord_1054990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809830805994860349051303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25652430965305921861606949 4809830805994860349051303)
  ·
    refine ⟨7214746208992290523576955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4809830805994860349051303 7214746208992290523576955)
    ·
      refine ⟨10822119313488435785365433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214746208992290523576955 10822119313488435785365433)
      ·
        refine ⟨8116589485116326839024075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10822119313488435785365433 8116589485116326839024075)
        ·
          refine ⟨12174884227674490258536113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8116589485116326839024075 12174884227674490258536113)
          ·
            refine ⟨9131163170755867693902085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12174884227674490258536113 9131163170755867693902085)
            ·
              refine ⟨1712093094516725192606641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9131163170755867693902085 1712093094516725192606641)
              ·
                refine ⟨1284069820887543894454981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712093094516725192606641 1284069820887543894454981)
                ·
                  refine ⟨240763091416414480210309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284069820887543894454981 240763091416414480210309)
                  ·
                    rfl

theorem cell21_1054990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1054990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054990 prefixEnd_1054990 := by exact prefixLift 1054990
  have htrace : WordTrace (prefixWord ++ tailWord_1054990) baseStart_1054990 baseEnd_1054990 := by
    simpa [prefixWord, tailWord_1054990, baseEnd_1054990] using wordTrace_append hprefix tailTrace_1054990
  have hstable : (prefixWord ++ tailWord_1054990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054990).length < 2 ^ (prefixWord ++ tailWord_1054990).sum := by decide
  have hdescent : baseEnd_1054990 < baseStart_1054990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054993 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 3]
def baseStart_1054993 : Nat := 118140960795 + 1054993 * 2 ^ 59
def prefixEnd_1054993 : Nat := 4983230072969 + 3 ^ 40 * 1054993 * 2
def baseEnd_1054993 : Nat := 240763776057287141660303

theorem tailTrace_1054993 : CollatzResearch.WordTrace tailWord_1054993 prefixEnd_1054993 240763776057287141660303 := by
  unfold tailWord_1054993
  simp only [CollatzResearch.WordTrace]
  refine ⟨38478755866948014304769633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25652503911298676203179755 38478755866948014304769633)
  ·
    refine ⟨28859066900211010728577225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38478755866948014304769633 28859066900211010728577225)
    ·
      refine ⟨21644300175158258046432919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28859066900211010728577225 21644300175158258046432919)
      ·
        refine ⟨32466450262737387069649379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644300175158258046432919 32466450262737387069649379)
        ·
          refine ⟨48699675394106080604474069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32466450262737387069649379 48699675394106080604474069)
          ·
            refine ⟨1141398642049361264167361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 48699675394106080604474069 1141398642049361264167361)
            ·
              refine ⟨856048981537020948125521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141398642049361264167361 856048981537020948125521)
              ·
                refine ⟨642036736152765711094141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856048981537020948125521 642036736152765711094141)
                ·
                  refine ⟨240763776057287141660303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642036736152765711094141 240763776057287141660303)
                  ·
                    rfl

theorem cell21_1054993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_1054993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1054993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1054993 prefixEnd_1054993 := by exact prefixLift 1054993
  have htrace : WordTrace (prefixWord ++ tailWord_1054993) baseStart_1054993 baseEnd_1054993 := by
    simpa [prefixWord, tailWord_1054993, baseEnd_1054993] using wordTrace_append hprefix tailTrace_1054993
  have hstable : (prefixWord ++ tailWord_1054993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054993).length < 2 ^ (prefixWord ++ tailWord_1054993).sum := by decide
  have hdescent : baseEnd_1054993 < baseStart_1054993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055063 : List Nat := [1, 1, 3, 2, 3, 1, 2, 8]
def baseStart_1055063 : Nat := 118140960795 + 1055063 * 2 ^ 59
def prefixEnd_1055063 : Nat := 4983230072969 + 3 ^ 40 * 1055063 * 2
def baseEnd_1055063 : Nat := 80259917003660858497831

theorem tailTrace_1055063 : CollatzResearch.WordTrace tailWord_1055063 prefixEnd_1055063 80259917003660858497831 := by
  unfold tailWord_1055063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38481308976694416259817843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25654205984462944173211895 38481308976694416259817843)
  ·
    refine ⟨57721963465041624389726765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38481308976694416259817843 57721963465041624389726765)
    ·
      refine ⟨21645736299390609146147537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57721963465041624389726765 21645736299390609146147537)
      ·
        refine ⟨16234302224542956859610653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21645736299390609146147537 16234302224542956859610653)
        ·
          refine ⟨6087863334203608822353995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16234302224542956859610653 6087863334203608822353995)
          ·
            refine ⟨9131795001305413233530993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087863334203608822353995 9131795001305413233530993)
            ·
              refine ⟨6848846250979059925148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9131795001305413233530993 6848846250979059925148245)
              ·
                refine ⟨80259917003660858497831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6848846250979059925148245 80259917003660858497831)
                ·
                  rfl

theorem cell21_1055063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_1055063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055063 prefixEnd_1055063 := by exact prefixLift 1055063
  have htrace : WordTrace (prefixWord ++ tailWord_1055063) baseStart_1055063 baseEnd_1055063 := by
    simpa [prefixWord, tailWord_1055063, baseEnd_1055063] using wordTrace_append hprefix tailTrace_1055063
  have hstable : (prefixWord ++ tailWord_1055063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055063).length < 2 ^ (prefixWord ++ tailWord_1055063).sum := by decide
  have hdescent : baseEnd_1055063 < baseStart_1055063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055080 : List Nat := [2, 1, 4, 2, 2, 2, 1, 7]
def baseStart_1055080 : Nat := 118140960795 + 1055080 * 2 ^ 59
def prefixEnd_1055080 : Nat := 4983230072969 + 3 ^ 40 * 1055080 * 2
def baseEnd_1055080 : Nat := 80261210214198107903375

theorem tailTrace_1055080 : CollatzResearch.WordTrace tailWord_1055080 prefixEnd_1055080 80261210214198107903375 := by
  unfold tailWord_1055080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19240964508816414081593347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25654619345088552108791129 19240964508816414081593347)
  ·
    refine ⟨28861446763224621122390021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19240964508816414081593347 28861446763224621122390021)
    ·
      refine ⟨5411521268104616460448129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28861446763224621122390021 5411521268104616460448129)
      ·
        refine ⟨4058640951078462345336097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5411521268104616460448129 4058640951078462345336097)
        ·
          refine ⟨3043980713308846759002073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4058640951078462345336097 3043980713308846759002073)
          ·
            refine ⟨2282985534981635069251555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043980713308846759002073 2282985534981635069251555)
            ·
              refine ⟨3424478302472452603877333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282985534981635069251555 3424478302472452603877333)
              ·
                refine ⟨80261210214198107903375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3424478302472452603877333 80261210214198107903375)
                ·
                  rfl

theorem cell21_1055080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_1055080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055080 prefixEnd_1055080 := by exact prefixLift 1055080
  have htrace : WordTrace (prefixWord ++ tailWord_1055080) baseStart_1055080 baseEnd_1055080 := by
    simpa [prefixWord, tailWord_1055080, baseEnd_1055080] using wordTrace_append hprefix tailTrace_1055080
  have hstable : (prefixWord ++ tailWord_1055080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055080).length < 2 ^ (prefixWord ++ tailWord_1055080).sum := by decide
  have hdescent : baseEnd_1055080 < baseStart_1055080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055139 : List Nat := [1, 1, 1, 4, 1, 4, 2, 7]
def baseStart_1055139 : Nat := 118140960795 + 1055139 * 2 ^ 59
def prefixEnd_1055139 : Nat := 4983230072969 + 3 ^ 40 * 1055139 * 2
def baseEnd_1055139 : Nat := 80265698415474444075557

theorem tailTrace_1055139 : CollatzResearch.WordTrace tailWord_1055139 prefixEnd_1055139 80265698415474444075557 := by
  unfold tailWord_1055139
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484080924419081239584471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656053949612720826389647 38484080924419081239584471)
  ·
    refine ⟨57726121386628621859376707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38484080924419081239584471 57726121386628621859376707)
    ·
      refine ⟨86589182079942932789065061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57726121386628621859376707 86589182079942932789065061)
      ·
        refine ⟨16235471639989299897949699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86589182079942932789065061 16235471639989299897949699)
        ·
          refine ⟨24353207459983949846924549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16235471639989299897949699 24353207459983949846924549)
          ·
            refine ⟨4566226398746990596298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24353207459983949846924549 4566226398746990596298353)
            ·
              refine ⟨3424669799060242947223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566226398746990596298353 3424669799060242947223765)
              ·
                refine ⟨80265698415474444075557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3424669799060242947223765 80265698415474444075557)
                ·
                  rfl

theorem cell21_1055139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_1055139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055139 prefixEnd_1055139 := by exact prefixLift 1055139
  have htrace : WordTrace (prefixWord ++ tailWord_1055139) baseStart_1055139 baseEnd_1055139 := by
    simpa [prefixWord, tailWord_1055139, baseEnd_1055139] using wordTrace_append hprefix tailTrace_1055139
  have hstable : (prefixWord ++ tailWord_1055139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055139).length < 2 ^ (prefixWord ++ tailWord_1055139).sum := by decide
  have hdescent : baseEnd_1055139 < baseStart_1055139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055218 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1055218 : Nat := 118140960795 + 1055218 * 2 ^ 59
def prefixEnd_1055218 : Nat := 4983230072969 + 3 ^ 40 * 1055218 * 2
def baseEnd_1055218 : Nat := 240815124122736750409843

theorem tailTrace_1055218 : CollatzResearch.WordTrace tailWord_1055218 prefixEnd_1055218 240815124122736750409843 := by
  unfold tailWord_1055218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621740572783219432927577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25657974860755251821140205 9621740572783219432927577)
  ·
    refine ⟨7216305429587414574695683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9621740572783219432927577 7216305429587414574695683)
    ·
      refine ⟨10824458144381121862043525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216305429587414574695683 10824458144381121862043525)
      ·
        refine ⟨2029585902071460349133161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10824458144381121862043525 2029585902071460349133161)
        ·
          refine ⟨1522189426553595261849871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029585902071460349133161 1522189426553595261849871)
          ·
            refine ⟨2283284139830392892774807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522189426553595261849871 2283284139830392892774807)
            ·
              refine ⟨3424926209745589339162211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283284139830392892774807 3424926209745589339162211)
              ·
                refine ⟨5137389314618384008743317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424926209745589339162211 5137389314618384008743317)
                ·
                  refine ⟨240815124122736750409843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5137389314618384008743317 240815124122736750409843)
                  ·
                    rfl

theorem cell21_1055218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1055218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055218 prefixEnd_1055218 := by exact prefixLift 1055218
  have htrace : WordTrace (prefixWord ++ tailWord_1055218) baseStart_1055218 baseEnd_1055218 := by
    simpa [prefixWord, tailWord_1055218, baseEnd_1055218] using wordTrace_append hprefix tailTrace_1055218
  have hstable : (prefixWord ++ tailWord_1055218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055218).length < 2 ^ (prefixWord ++ tailWord_1055218).sum := by decide
  have hdescent : baseEnd_1055218 < baseStart_1055218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055353 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_1055353 : Nat := 118140960795 + 1055353 * 2 ^ 59
def prefixEnd_1055353 : Nat := 4983230072969 + 3 ^ 40 * 1055353 * 2
def baseEnd_1055353 : Nat := 240845932962006515659567

theorem tailTrace_1055353 : CollatzResearch.WordTrace tailWord_1055353 prefixEnd_1055353 240845932962006515659567 := by
  unfold tailWord_1055353
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491886145643795787874713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25661257430429197191916475 38491886145643795787874713)
  ·
    refine ⟨28868914609232846840906035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38491886145643795787874713 28868914609232846840906035)
    ·
      refine ⟨43303371913849270261359053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28868914609232846840906035 43303371913849270261359053)
      ·
        refine ⟨16238764467693476348009645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43303371913849270261359053 16238764467693476348009645)
        ·
          refine ⟨6089536675385053630503617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16238764467693476348009645 6089536675385053630503617)
          ·
            refine ⟨4567152506538790222877713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6089536675385053630503617 4567152506538790222877713)
            ·
              refine ⟨3425364379904092667158285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567152506538790222877713 3425364379904092667158285)
              ·
                refine ⟨1284511642464034750184357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3425364379904092667158285 1284511642464034750184357)
                ·
                  refine ⟨240845932962006515659567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284511642464034750184357 240845932962006515659567)
                  ·
                    rfl

theorem cell21_1055353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_1055353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055353 prefixEnd_1055353 := by exact prefixLift 1055353
  have htrace : WordTrace (prefixWord ++ tailWord_1055353) baseStart_1055353 baseEnd_1055353 := by
    simpa [prefixWord, tailWord_1055353, baseEnd_1055353] using wordTrace_append hprefix tailTrace_1055353
  have hstable : (prefixWord ++ tailWord_1055353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055353).length < 2 ^ (prefixWord ++ tailWord_1055353).sum := by decide
  have hdescent : baseEnd_1055353 < baseStart_1055353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055432 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_1055432 : Nat := 118140960795 + 1055432 * 2 ^ 59
def prefixEnd_1055432 : Nat := 4983230072969 + 3 ^ 40 * 1055432 * 2
def baseEnd_1055432 : Nat := 240863961838319933842739

theorem tailTrace_1055432 : CollatzResearch.WordTrace tailWord_1055432 prefixEnd_1055432 240863961838319933842739 := by
  unfold tailWord_1055432
  simp only [CollatzResearch.WordTrace]
  refine ⟨19247383756178796140000275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25663178341571728186667033 19247383756178796140000275)
  ·
    refine ⟨28871075634268194210000413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19247383756178796140000275 28871075634268194210000413)
    ·
      refine ⟨10826653362850572828750155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28871075634268194210000413 10826653362850572828750155)
      ·
        refine ⟨16239980044275859243125233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10826653362850572828750155 16239980044275859243125233)
        ·
          refine ⟨12179985033206894432343925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16239980044275859243125233 12179985033206894432343925)
          ·
            refine ⟨1141873596863146353032243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12179985033206894432343925 1141873596863146353032243)
            ·
              refine ⟨1712810395294719529548365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141873596863146353032243 1712810395294719529548365)
              ·
                refine ⟨642303898235519823580637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712810395294719529548365 642303898235519823580637)
                ·
                  refine ⟨240863961838319933842739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642303898235519823580637 240863961838319933842739)
                  ·
                    rfl

theorem cell21_1055432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_1055432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055432 prefixEnd_1055432 := by exact prefixLift 1055432
  have htrace : WordTrace (prefixWord ++ tailWord_1055432) baseStart_1055432 baseEnd_1055432 := by
    simpa [prefixWord, tailWord_1055432, baseEnd_1055432] using wordTrace_append hprefix tailTrace_1055432
  have hstable : (prefixWord ++ tailWord_1055432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055432).length < 2 ^ (prefixWord ++ tailWord_1055432).sum := by decide
  have hdescent : baseEnd_1055432 < baseStart_1055432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055519 : List Nat := [1, 1, 2, 4, 2, 2, 3, 6]
def baseStart_1055519 : Nat := 118140960795 + 1055519 * 2 ^ 59
def prefixEnd_1055519 : Nat := 4983230072969 + 3 ^ 40 * 1055519 * 2
def baseEnd_1055519 : Nat := 80294605474542371964187

theorem tailTrace_1055519 : CollatzResearch.WordTrace tailWord_1055519 prefixEnd_1055519 80294605474542371964187 := by
  unfold tailWord_1055519
  simp only [CollatzResearch.WordTrace]
  refine ⟨38497940663042406138417611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25665293775361604092278407 38497940663042406138417611)
  ·
    refine ⟨57746910994563609207626417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38497940663042406138417611 57746910994563609207626417)
    ·
      refine ⟨43310183245922706905719813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57746910994563609207626417 43310183245922706905719813)
      ·
        refine ⟨8120659358610507544822465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43310183245922706905719813 8120659358610507544822465)
        ·
          refine ⟨6090494518957880658616849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8120659358610507544822465 6090494518957880658616849)
          ·
            refine ⟨4567870889218410493962637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6090494518957880658616849 4567870889218410493962637)
            ·
              refine ⟨1712951583456903935235989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4567870889218410493962637 1712951583456903935235989)
              ·
                refine ⟨80294605474542371964187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1712951583456903935235989 80294605474542371964187)
                ·
                  rfl

theorem cell21_1055519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_1055519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055519 prefixEnd_1055519 := by exact prefixLift 1055519
  have htrace : WordTrace (prefixWord ++ tailWord_1055519) baseStart_1055519 baseEnd_1055519 := by
    simpa [prefixWord, tailWord_1055519, baseEnd_1055519] using wordTrace_append hprefix tailTrace_1055519
  have hstable : (prefixWord ++ tailWord_1055519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055519).length < 2 ^ (prefixWord ++ tailWord_1055519).sum := by decide
  have hdescent : baseEnd_1055519 < baseStart_1055519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055556 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1055556 : Nat := 118140960795 + 1055556 * 2 ^ 59
def prefixEnd_1055556 : Nat := 4983230072969 + 3 ^ 40 * 1055556 * 2
def baseEnd_1055556 : Nat := 240892260327723273775819

theorem tailTrace_1055556 : CollatzResearch.WordTrace tailWord_1055556 prefixEnd_1055556 240892260327723273775819 := by
  unfold tailWord_1055556
  simp only [CollatzResearch.WordTrace]
  refine ⟨19249645081954180728757261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25666193442605574305009681 19249645081954180728757261)
  ·
    refine ⟨7218616905732817773283973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19249645081954180728757261 7218616905732817773283973)
    ·
      refine ⟨1353490669824903332490745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7218616905732817773283973 1353490669824903332490745)
      ·
        refine ⟨1015118002368677499368059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1353490669824903332490745 1015118002368677499368059)
        ·
          refine ⟨1522677003553016249052089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015118002368677499368059 1522677003553016249052089)
          ·
            refine ⟨1142007752664762186789067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522677003553016249052089 1142007752664762186789067)
            ·
              refine ⟨1713011628997143280183601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142007752664762186789067 1713011628997143280183601)
              ·
                refine ⟨1284758721747857460137701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713011628997143280183601 1284758721747857460137701)
                ·
                  refine ⟨240892260327723273775819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284758721747857460137701 240892260327723273775819)
                  ·
                    rfl

theorem cell21_1055556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1055556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055556 prefixEnd_1055556 := by exact prefixLift 1055556
  have htrace : WordTrace (prefixWord ++ tailWord_1055556) baseStart_1055556 baseEnd_1055556 := by
    simpa [prefixWord, tailWord_1055556, baseEnd_1055556] using wordTrace_append hprefix tailTrace_1055556
  have hstable : (prefixWord ++ tailWord_1055556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055556).length < 2 ^ (prefixWord ++ tailWord_1055556).sum := by decide
  have hdescent : baseEnd_1055556 < baseStart_1055556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055595 : List Nat := [1, 1, 1, 1, 2, 2, 8, 5]
def baseStart_1055595 : Nat := 118140960795 + 1055595 * 2 ^ 59
def prefixEnd_1055595 : Nat := 4983230072969 + 3 ^ 40 * 1055595 * 2
def baseEnd_1055595 : Nat := 80300386886355957541913

theorem tailTrace_1055595 : CollatzResearch.WordTrace tailWord_1055595 prefixEnd_1055595 80300386886355957541913 := by
  unfold tailWord_1055595
  simp only [CollatzResearch.WordTrace]
  refine ⟨38500712610767071118184239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25667141740511380745456159 38500712610767071118184239)
  ·
    refine ⟨57751068916150606677276359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38500712610767071118184239 57751068916150606677276359)
    ·
      refine ⟨86626603374225910015914539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57751068916150606677276359 86626603374225910015914539)
      ·
        refine ⟨129939905061338865023871809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86626603374225910015914539 129939905061338865023871809)
        ·
          refine ⟨97454928796004148767903857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129939905061338865023871809 97454928796004148767903857)
          ·
            refine ⟨73091196597003111575927893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97454928796004148767903857 73091196597003111575927893)
            ·
              refine ⟨856537460121130213780405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 73091196597003111575927893 856537460121130213780405)
              ·
                refine ⟨80300386886355957541913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856537460121130213780405 80300386886355957541913)
                ·
                  rfl

theorem cell21_1055595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 5].length) (baseStart_1055595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055595 prefixEnd_1055595 := by exact prefixLift 1055595
  have htrace : WordTrace (prefixWord ++ tailWord_1055595) baseStart_1055595 baseEnd_1055595 := by
    simpa [prefixWord, tailWord_1055595, baseEnd_1055595] using wordTrace_append hprefix tailTrace_1055595
  have hstable : (prefixWord ++ tailWord_1055595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055595).length < 2 ^ (prefixWord ++ tailWord_1055595).sum := by decide
  have hdescent : baseEnd_1055595 < baseStart_1055595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055618 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1055618 : Nat := 118140960795 + 1055618 * 2 ^ 59
def prefixEnd_1055618 : Nat := 4983230072969 + 3 ^ 40 * 1055618 * 2
def baseEnd_1055618 : Nat := 240906409572424943742359

theorem tailTrace_1055618 : CollatzResearch.WordTrace tailWord_1055618 prefixEnd_1055618 240906409572424943742359 := by
  unfold tailWord_1055618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625387872420936511567877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25667700993122497364181005 9625387872420936511567877)
  ·
    refine ⟨1804760226078925595918977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9625387872420936511567877 1804760226078925595918977)
    ·
      refine ⟨1353570169559194196939233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1804760226078925595918977 1353570169559194196939233)
      ·
        refine ⟨1015177627169395647704425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1353570169559194196939233 1015177627169395647704425)
        ·
          refine ⟨761383220377046735778319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015177627169395647704425 761383220377046735778319)
          ·
            refine ⟨1142074830565570103667479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761383220377046735778319 1142074830565570103667479)
            ·
              refine ⟨1713112245848355155501219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142074830565570103667479 1713112245848355155501219)
              ·
                refine ⟨2569668368772532733251829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713112245848355155501219 2569668368772532733251829)
                ·
                  refine ⟨240906409572424943742359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569668368772532733251829 240906409572424943742359)
                  ·
                    rfl

theorem cell21_1055618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1055618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055618 prefixEnd_1055618 := by exact prefixLift 1055618
  have htrace : WordTrace (prefixWord ++ tailWord_1055618) baseStart_1055618 baseEnd_1055618 := by
    simpa [prefixWord, tailWord_1055618, baseEnd_1055618] using wordTrace_append hprefix tailTrace_1055618
  have hstable : (prefixWord ++ tailWord_1055618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055618).length < 2 ^ (prefixWord ++ tailWord_1055618).sum := by decide
  have hdescent : baseEnd_1055618 < baseStart_1055618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055677 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1055677 : Nat := 118140960795 + 1055677 * 2 ^ 59
def prefixEnd_1055677 : Nat := 4983230072969 + 3 ^ 40 * 1055677 * 2
def baseEnd_1055677 : Nat := 240919874176253952258905

theorem tailTrace_1055677 : CollatzResearch.WordTrace tailWord_1055677 prefixEnd_1055677 240919874176253952258905 := by
  unfold tailWord_1055677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38503703396469999122669285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25669135597646666081779523 38503703396469999122669285)
  ·
    refine ⟨7219444386838124835500491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38503703396469999122669285 7219444386838124835500491)
    ·
      refine ⟨10829166580257187253250737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219444386838124835500491 10829166580257187253250737)
      ·
        refine ⟨8121874935192890439938053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10829166580257187253250737 8121874935192890439938053)
        ·
          refine ⟨1522851550348666957488385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8121874935192890439938053 1522851550348666957488385)
          ·
            refine ⟨1142138662761500218116289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522851550348666957488385 1142138662761500218116289)
            ·
              refine ⟨856603997071125163587217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142138662761500218116289 856603997071125163587217)
              ·
                refine ⟨642452997803343872690413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856603997071125163587217 642452997803343872690413)
                ·
                  refine ⟨240919874176253952258905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642452997803343872690413 240919874176253952258905)
                  ·
                    rfl

theorem cell21_1055677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1055677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055677 prefixEnd_1055677 := by exact prefixLift 1055677
  have htrace : WordTrace (prefixWord ++ tailWord_1055677) baseStart_1055677 baseEnd_1055677 := by
    simpa [prefixWord, tailWord_1055677, baseEnd_1055677] using wordTrace_append hprefix tailTrace_1055677
  have hstable : (prefixWord ++ tailWord_1055677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055677).length < 2 ^ (prefixWord ++ tailWord_1055677).sum := by decide
  have hdescent : baseEnd_1055677 < baseStart_1055677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055688 : List Nat := [2, 1, 3, 1, 5, 2, 1, 6]
def baseStart_1055688 : Nat := 118140960795 + 1055688 * 2 ^ 59
def prefixEnd_1055688 : Nat := 4983230072969 + 3 ^ 40 * 1055688 * 2
def baseEnd_1055688 : Nat := 80307461508706792525183

theorem tailTrace_1055688 : CollatzResearch.WordTrace tailWord_1055688 prefixEnd_1055688 80307461508706792525183 := by
  unfold tailWord_1055688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19252052299715074000659859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25669403066286765334213145 19252052299715074000659859)
  ·
    refine ⟨28878078449572611000989789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19252052299715074000659859 28878078449572611000989789)
    ·
      refine ⟨10829279418589729125371171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28878078449572611000989789 10829279418589729125371171)
      ·
        refine ⟨16243919127884593688056757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10829279418589729125371171 16243919127884593688056757)
        ·
          refine ⟨1522867418239180658255321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16243919127884593688056757 1522867418239180658255321)
          ·
            refine ⟨1142150563679385493691491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522867418239180658255321 1142150563679385493691491)
            ·
              refine ⟨1713225845519078240537237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142150563679385493691491 1713225845519078240537237)
              ·
                refine ⟨80307461508706792525183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1713225845519078240537237 80307461508706792525183)
                ·
                  rfl

theorem cell21_1055688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_1055688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055688 prefixEnd_1055688 := by exact prefixLift 1055688
  have htrace : WordTrace (prefixWord ++ tailWord_1055688) baseStart_1055688 baseEnd_1055688 := by
    simpa [prefixWord, tailWord_1055688, baseEnd_1055688] using wordTrace_append hprefix tailTrace_1055688
  have hstable : (prefixWord ++ tailWord_1055688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055688).length < 2 ^ (prefixWord ++ tailWord_1055688).sum := by decide
  have hdescent : baseEnd_1055688 < baseStart_1055688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055719 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 3]
def baseStart_1055719 : Nat := 118140960795 + 1055719 * 2 ^ 59
def prefixEnd_1055719 : Nat := 4983230072969 + 3 ^ 40 * 1055719 * 2
def baseEnd_1055719 : Nat := 240929459148471212558819

theorem tailTrace_1055719 : CollatzResearch.WordTrace tailWord_1055719 prefixEnd_1055719 240929459148471212558819 := by
  unfold tailWord_1055719
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505235262317840295698211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25670156841545226863798807 38505235262317840295698211)
  ·
    refine ⟨57757852893476760443547317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38505235262317840295698211 57757852893476760443547317)
    ·
      refine ⟨5414798708763446291582561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57757852893476760443547317 5414798708763446291582561)
      ·
        refine ⟨4061099031572584718686921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5414798708763446291582561 4061099031572584718686921)
        ·
          refine ⟨3045824273679438539015191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061099031572584718686921 3045824273679438539015191)
          ·
            refine ⟨4568736410519157808522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3045824273679438539015191 4568736410519157808522787)
            ·
              refine ⟨6853104615778736712784181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4568736410519157808522787 6853104615778736712784181)
              ·
                refine ⟨642478557729256566823517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6853104615778736712784181 642478557729256566823517)
                ·
                  refine ⟨240929459148471212558819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642478557729256566823517 240929459148471212558819)
                  ·
                    rfl

theorem cell21_1055719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].length) (baseStart_1055719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055719 prefixEnd_1055719 := by exact prefixLift 1055719
  have htrace : WordTrace (prefixWord ++ tailWord_1055719) baseStart_1055719 baseEnd_1055719 := by
    simpa [prefixWord, tailWord_1055719, baseEnd_1055719] using wordTrace_append hprefix tailTrace_1055719
  have hstable : (prefixWord ++ tailWord_1055719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055719).length < 2 ^ (prefixWord ++ tailWord_1055719).sum := by decide
  have hdescent : baseEnd_1055719 < baseStart_1055719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055792 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_1055792 : Nat := 118140960795 + 1055792 * 2 ^ 59
def prefixEnd_1055792 : Nat := 4983230072969 + 3 ^ 40 * 1055792 * 2
def baseEnd_1055792 : Nat := 240946118743039307842003

theorem tailTrace_1055792 : CollatzResearch.WordTrace tailWord_1055792 prefixEnd_1055792 240946118743039307842003 := by
  unfold tailWord_1055792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19253948895526686881552815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25671931860702249175403753 19253948895526686881552815)
  ·
    refine ⟨28880923343290030322329223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19253948895526686881552815 28880923343290030322329223)
    ·
      refine ⟨43321385014935045483493835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28880923343290030322329223 43321385014935045483493835)
      ·
        refine ⟨64982077522402568225240753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43321385014935045483493835 64982077522402568225240753)
        ·
          refine ⟨48736558141801926168930565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64982077522402568225240753 48736558141801926168930565)
          ·
            refine ⟨9138104651587861156674481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48736558141801926168930565 9138104651587861156674481)
            ·
              refine ⟨6853578488690895867505861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9138104651587861156674481 6853578488690895867505861)
              ·
                refine ⟨1285045966629542975157349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6853578488690895867505861 1285045966629542975157349)
                ·
                  refine ⟨240946118743039307842003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285045966629542975157349 240946118743039307842003)
                  ·
                    rfl

theorem cell21_1055792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_1055792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055792 prefixEnd_1055792 := by exact prefixLift 1055792
  have htrace : WordTrace (prefixWord ++ tailWord_1055792) baseStart_1055792 baseEnd_1055792 := by
    simpa [prefixWord, tailWord_1055792, baseEnd_1055792] using wordTrace_append hprefix tailTrace_1055792
  have hstable : (prefixWord ++ tailWord_1055792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055792).length < 2 ^ (prefixWord ++ tailWord_1055792).sum := by decide
  have hdescent : baseEnd_1055792 < baseStart_1055792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055868 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1055868 : Nat := 118140960795 + 1055868 * 2 ^ 59
def prefixEnd_1055868 : Nat := 4983230072969 + 3 ^ 40 * 1055868 * 2
def baseEnd_1055868 : Nat := 240963462978480064575181

theorem tailTrace_1055868 : CollatzResearch.WordTrace tailWord_1055868 prefixEnd_1055868 240963462978480064575181 := by
  unfold tailWord_1055868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255334869389019371436129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25673779825852025828581505 19255334869389019371436129)
  ·
    refine ⟨14441501152041764528577097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19255334869389019371436129 14441501152041764528577097)
    ·
      refine ⟨10831125864031323396432823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14441501152041764528577097 10831125864031323396432823)
      ·
        refine ⟨16246688796046985094649235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10831125864031323396432823 16246688796046985094649235)
        ·
          refine ⟨24370033194070477641973853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16246688796046985094649235 24370033194070477641973853)
          ·
            refine ⟨9138762447776429115740195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24370033194070477641973853 9138762447776429115740195)
            ·
              refine ⟨13708143671664643673610293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138762447776429115740195 13708143671664643673610293)
              ·
                refine ⟨1285138469218560344400965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13708143671664643673610293 1285138469218560344400965)
                ·
                  refine ⟨240963462978480064575181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285138469218560344400965 240963462978480064575181)
                  ·
                    rfl

theorem cell21_1055868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1055868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055868 prefixEnd_1055868 := by exact prefixLift 1055868
  have htrace : WordTrace (prefixWord ++ tailWord_1055868) baseStart_1055868 baseEnd_1055868 := by
    simpa [prefixWord, tailWord_1055868, baseEnd_1055868] using wordTrace_append hprefix tailTrace_1055868
  have hstable : (prefixWord ++ tailWord_1055868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055868).length < 2 ^ (prefixWord ++ tailWord_1055868).sum := by decide
  have hdescent : baseEnd_1055868 < baseStart_1055868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055902 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1055902 : Nat := 118140960795 + 1055902 * 2 ^ 59
def prefixEnd_1055902 : Nat := 4983230072969 + 3 ^ 40 * 1055902 * 2
def baseEnd_1055902 : Nat := 240971222241703561008445

theorem tailTrace_1055902 : CollatzResearch.WordTrace tailWord_1055902 prefixEnd_1055902 240971222241703561008445 := by
  unfold tailWord_1055902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813988727581857818701245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25674606547103241699739973 4813988727581857818701245)
  ·
    refine ⟨1805245772843196682012967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4813988727581857818701245 1805245772843196682012967)
    ·
      refine ⟨2707868659264795023019451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805245772843196682012967 2707868659264795023019451)
      ·
        refine ⟨4061802988897192534529177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2707868659264795023019451 4061802988897192534529177)
        ·
          refine ⟨3046352241672894400896883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061802988897192534529177 3046352241672894400896883)
          ·
            refine ⟨4569528362509341601345325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046352241672894400896883 4569528362509341601345325)
            ·
              refine ⟨1713573135941003100504497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4569528362509341601345325 1713573135941003100504497)
              ·
                refine ⟨1285179851955752325378373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713573135941003100504497 1285179851955752325378373)
                ·
                  refine ⟨240971222241703561008445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285179851955752325378373 240971222241703561008445)
                  ·
                    rfl

theorem cell21_1055902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1055902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055902 prefixEnd_1055902 := by exact prefixLift 1055902
  have htrace : WordTrace (prefixWord ++ tailWord_1055902) baseStart_1055902 baseEnd_1055902 := by
    simpa [prefixWord, tailWord_1055902, baseEnd_1055902] using wordTrace_append hprefix tailTrace_1055902
  have hstable : (prefixWord ++ tailWord_1055902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055902).length < 2 ^ (prefixWord ++ tailWord_1055902).sum := by decide
  have hdescent : baseEnd_1055902 < baseStart_1055902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055978 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_1055978 : Nat := 118140960795 + 1055978 * 2 ^ 59
def prefixEnd_1055978 : Nat := 4983230072969 + 3 ^ 40 * 1055978 * 2
def baseEnd_1055978 : Nat := 240988566477144317741623

theorem tailTrace_1055978 : CollatzResearch.WordTrace tailWord_1055978 prefixEnd_1055978 240988566477144317741623 := by
  unfold tailWord_1055978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628670442094881882344147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25676454512253018352917725 9628670442094881882344147)
  ·
    refine ⟨14443005663142322823516221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628670442094881882344147 14443005663142322823516221)
    ·
      refine ⟨5416127123678371058818583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14443005663142322823516221 5416127123678371058818583)
      ·
        refine ⟨8124190685517556588227875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416127123678371058818583 8124190685517556588227875)
        ·
          refine ⟨12186286028276334882341813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124190685517556588227875 12186286028276334882341813)
          ·
            refine ⟨1142464315150906395219545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12186286028276334882341813 1142464315150906395219545)
            ·
              refine ⟨856848236363179796414659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142464315150906395219545 856848236363179796414659)
              ·
                refine ⟨1285272354544769694621989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856848236363179796414659 1285272354544769694621989)
                ·
                  refine ⟨240988566477144317741623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285272354544769694621989 240988566477144317741623)
                  ·
                    rfl

theorem cell21_1055978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_1055978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1055978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1055978 prefixEnd_1055978 := by exact prefixLift 1055978
  have htrace : WordTrace (prefixWord ++ tailWord_1055978) baseStart_1055978 baseEnd_1055978 := by
    simpa [prefixWord, tailWord_1055978, baseEnd_1055978] using wordTrace_append hprefix tailTrace_1055978
  have hstable : (prefixWord ++ tailWord_1055978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055978).length < 2 ^ (prefixWord ++ tailWord_1055978).sum := by decide
  have hdescent : baseEnd_1055978 < baseStart_1055978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056051 : List Nat := [1, 1, 1, 2, 5, 3, 3, 5]
def baseStart_1056051 : Nat := 118140960795 + 1056051 * 2 ^ 59
def prefixEnd_1056051 : Nat := 4983230072969 + 3 ^ 40 * 1056051 * 2
def baseEnd_1056051 : Nat := 80335075357237471008269

theorem tailTrace_1056051 : CollatzResearch.WordTrace tailWord_1056051 prefixEnd_1056051 80335075357237471008269 := by
  unfold tailWord_1056051
  simp only [CollatzResearch.WordTrace]
  refine ⟨38517344297115060996784007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25678229531410040664522671 38517344297115060996784007)
  ·
    refine ⟨57776016445672591495176011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38517344297115060996784007 57776016445672591495176011)
    ·
      refine ⟨86664024668508887242764017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57776016445672591495176011 86664024668508887242764017)
      ·
        refine ⟨64998018501381665432073013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86664024668508887242764017 64998018501381665432073013)
        ·
          refine ⟨6093564234504531134256845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64998018501381665432073013 6093564234504531134256845)
          ·
            refine ⟨2285086587939199175346317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6093564234504531134256845 2285086587939199175346317)
            ·
              refine ⟨856907470477199690754869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285086587939199175346317 856907470477199690754869)
              ·
                refine ⟨80335075357237471008269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856907470477199690754869 80335075357237471008269)
                ·
                  rfl

theorem cell21_1056051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 5].length) (baseStart_1056051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056051 prefixEnd_1056051 := by exact prefixLift 1056051
  have htrace : WordTrace (prefixWord ++ tailWord_1056051) baseStart_1056051 baseEnd_1056051 := by
    simpa [prefixWord, tailWord_1056051, baseEnd_1056051] using wordTrace_append hprefix tailTrace_1056051
  have hstable : (prefixWord ++ tailWord_1056051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056051).length < 2 ^ (prefixWord ++ tailWord_1056051).sum := by decide
  have hdescent : baseEnd_1056051 < baseStart_1056051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056217 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1056217 : Nat := 118140960795 + 1056217 * 2 ^ 59
def prefixEnd_1056217 : Nat := 4983230072969 + 3 ^ 40 * 1056217 * 2
def baseEnd_1056217 : Nat := 241043109533333013257801

theorem tailTrace_1056217 : CollatzResearch.WordTrace tailWord_1056217 prefixEnd_1056217 241043109533333013257801 := by
  unfold tailWord_1056217
  simp only [CollatzResearch.WordTrace]
  refine ⟨38523398814513671347326905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25682265876342447564884603 38523398814513671347326905)
  ·
    refine ⟨28892549110885253510495179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38523398814513671347326905 28892549110885253510495179)
    ·
      refine ⟨43338823666327880265742769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28892549110885253510495179 43338823666327880265742769)
      ·
        refine ⟨32504117749745910199307077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43338823666327880265742769 32504117749745910199307077)
        ·
          refine ⟨6094522078077358162370077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32504117749745910199307077 6094522078077358162370077)
          ·
            refine ⟨2285445779279009310888779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6094522078077358162370077 2285445779279009310888779)
            ·
              refine ⟨3428168668918513966333169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285445779279009310888779 3428168668918513966333169)
              ·
                refine ⟨2571126501688885474749877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428168668918513966333169 2571126501688885474749877)
                ·
                  refine ⟨241043109533333013257801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2571126501688885474749877 241043109533333013257801)
                  ·
                    rfl

theorem cell21_1056217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1056217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056217 prefixEnd_1056217 := by exact prefixLift 1056217
  have htrace : WordTrace (prefixWord ++ tailWord_1056217) baseStart_1056217 baseEnd_1056217 := by
    simpa [prefixWord, tailWord_1056217, baseEnd_1056217] using wordTrace_append hprefix tailTrace_1056217
  have hstable : (prefixWord ++ tailWord_1056217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056217).length < 2 ^ (prefixWord ++ tailWord_1056217).sum := by decide
  have hdescent : baseEnd_1056217 < baseStart_1056217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056248 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_1056248 : Nat := 118140960795 + 1056248 * 2 ^ 59
def prefixEnd_1056248 : Nat := 4983230072969 + 3 ^ 40 * 1056248 * 2
def baseEnd_1056248 : Nat := 241050184155683848241071

theorem tailTrace_1056248 : CollatzResearch.WordTrace tailWord_1056248 prefixEnd_1056248 241050184155683848241071 := by
  unfold tailWord_1056248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19262264738700681820852699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25683019651600909094470265 19262264738700681820852699)
  ·
    refine ⟨28893397108051022731279049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19262264738700681820852699 28893397108051022731279049)
    ·
      refine ⟨21670047831038267048459287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28893397108051022731279049 21670047831038267048459287)
      ·
        refine ⟨32505071746557400572688931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21670047831038267048459287 32505071746557400572688931)
        ·
          refine ⟨48757607619836100859033397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32505071746557400572688931 48757607619836100859033397)
          ·
            refine ⟨4571025714359634455534381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48757607619836100859033397 4571025714359634455534381)
            ·
              refine ⟨1714134642884862920825393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4571025714359634455534381 1714134642884862920825393)
              ·
                refine ⟨1285600982163647190619045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714134642884862920825393 1285600982163647190619045)
                ·
                  refine ⟨241050184155683848241071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285600982163647190619045 241050184155683848241071)
                  ·
                    rfl

theorem cell21_1056248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_1056248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056248 prefixEnd_1056248 := by exact prefixLift 1056248
  have htrace : WordTrace (prefixWord ++ tailWord_1056248) baseStart_1056248 baseEnd_1056248 := by
    simpa [prefixWord, tailWord_1056248, baseEnd_1056248] using wordTrace_append hprefix tailTrace_1056248
  have hstable : (prefixWord ++ tailWord_1056248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056248).length < 2 ^ (prefixWord ++ tailWord_1056248).sum := by decide
  have hdescent : baseEnd_1056248 < baseStart_1056248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056296 : List Nat := [2, 1, 5, 2, 3, 1, 7]
def baseStart_1056296 : Nat := 118140960795 + 1056296 * 2 ^ 59
def prefixEnd_1056296 : Nat := 4983230072969 + 3 ^ 40 * 1056296 * 2
def baseEnd_1056296 : Nat := 26784570934405159048997

theorem tailTrace_1056296 : CollatzResearch.WordTrace tailWord_1056296 prefixEnd_1056296 26784570934405159048997 := by
  unfold tailWord_1056296
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263140090613733919726371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25684186787484978559635161 19263140090613733919726371)
  ·
    refine ⟨28894710135920600879589557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263140090613733919726371 28894710135920600879589557)
    ·
      refine ⟨2708879075242556332461521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28894710135920600879589557 2708879075242556332461521)
      ·
        refine ⟨2031659306431917249346141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2708879075242556332461521 2031659306431917249346141)
        ·
          refine ⟨761872239911968968504803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2031659306431917249346141 761872239911968968504803)
          ·
            refine ⟨1142808359867953452757205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761872239911968968504803 1142808359867953452757205)
            ·
              refine ⟨26784570934405159048997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1142808359867953452757205 26784570934405159048997)
              ·
                rfl

theorem cell21_1056296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 7].length) (baseStart_1056296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056296 prefixEnd_1056296 := by exact prefixLift 1056296
  have htrace : WordTrace (prefixWord ++ tailWord_1056296) baseStart_1056296 baseEnd_1056296 := by
    simpa [prefixWord, tailWord_1056296, baseEnd_1056296] using wordTrace_append hprefix tailTrace_1056296
  have hstable : (prefixWord ++ tailWord_1056296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056296).length < 2 ^ (prefixWord ++ tailWord_1056296).sum := by decide
  have hdescent : baseEnd_1056296 < baseStart_1056296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056307 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_1056307 : Nat := 118140960795 + 1056307 * 2 ^ 59
def prefixEnd_1056307 : Nat := 4983230072969 + 3 ^ 40 * 1056307 * 2
def baseEnd_1056307 : Nat := 241063648759512856757617

theorem tailTrace_1056307 : CollatzResearch.WordTrace tailWord_1056307 prefixEnd_1056307 241063648759512856757617 := by
  unfold tailWord_1056307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38526681384187616718103175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25684454256125077812068783 38526681384187616718103175)
  ·
    refine ⟨57790022076281425077154763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38526681384187616718103175 57790022076281425077154763)
    ·
      refine ⟨86685033114422137615732145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57790022076281425077154763 86685033114422137615732145)
      ·
        refine ⟨65013774835816603211799109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86685033114422137615732145 65013774835816603211799109)
        ·
          refine ⟨12190082781715613102212333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65013774835816603211799109 12190082781715613102212333)
          ·
            refine ⟨4571281043143354913329625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12190082781715613102212333 4571281043143354913329625)
            ·
              refine ⟨3428460782357516184997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4571281043143354913329625 3428460782357516184997219)
              ·
                refine ⟨5142691173536274277495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428460782357516184997219 5142691173536274277495829)
                ·
                  refine ⟨241063648759512856757617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5142691173536274277495829 241063648759512856757617)
                  ·
                    rfl

theorem cell21_1056307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_1056307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056307 prefixEnd_1056307 := by exact prefixLift 1056307
  have htrace : WordTrace (prefixWord ++ tailWord_1056307) baseStart_1056307 baseEnd_1056307 := by
    simpa [prefixWord, tailWord_1056307, baseEnd_1056307] using wordTrace_append hprefix tailTrace_1056307
  have hstable : (prefixWord ++ tailWord_1056307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056307).length < 2 ^ (prefixWord ++ tailWord_1056307).sum := by decide
  have hdescent : baseEnd_1056307 < baseStart_1056307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056338 : List Nat := [3, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1056338 : Nat := 118140960795 + 1056338 * 2 ^ 59
def prefixEnd_1056338 : Nat := 4983230072969 + 3 ^ 40 * 1056338 * 2
def baseEnd_1056338 : Nat := 80356907793954563913629

theorem tailTrace_1056338 : CollatzResearch.WordTrace tailWord_1056338 prefixEnd_1056338 80356907793954563913629 := by
  unfold tailWord_1056338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631953011768827253120417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25685208031383539341654445 9631953011768827253120417)
  ·
    refine ⟨7223964758826620439840313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9631953011768827253120417 7223964758826620439840313)
    ·
      refine ⟨5417973569119965329880235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7223964758826620439840313 5417973569119965329880235)
      ·
        refine ⟨8126960353679947994820353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5417973569119965329880235 8126960353679947994820353)
        ·
          refine ⟨6095220265259960996115265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126960353679947994820353 6095220265259960996115265)
          ·
            refine ⟨4571415198944970747086449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6095220265259960996115265 4571415198944970747086449)
            ·
              refine ⟨3428561399208728060314837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4571415198944970747086449 3428561399208728060314837)
              ·
                refine ⟨80356907793954563913629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3428561399208728060314837 80356907793954563913629)
                ·
                  rfl

theorem cell21_1056338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1056338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1056338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1056338 prefixEnd_1056338 := by exact prefixLift 1056338
  have htrace : WordTrace (prefixWord ++ tailWord_1056338) baseStart_1056338 baseEnd_1056338 := by
    simpa [prefixWord, tailWord_1056338, baseEnd_1056338] using wordTrace_append hprefix tailTrace_1056338
  have hstable : (prefixWord ++ tailWord_1056338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056338).length < 2 ^ (prefixWord ++ tailWord_1056338).sum := by decide
  have hdescent : baseEnd_1056338 < baseStart_1056338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
