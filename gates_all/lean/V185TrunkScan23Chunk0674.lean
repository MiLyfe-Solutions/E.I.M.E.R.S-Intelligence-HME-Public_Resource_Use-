import V185TrunkScan23Chunk0673

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3985169 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_3985169 : Nat := 118140960795 + 3985169 * 2 ^ 59
def prefixEnd_3985169 : Nat := 4983230072969 + 3 ^ 40 * 3985169 * 2
def baseEnd_3985169 : Nat := 682102395465874580553349

theorem tailTrace_3985169 : CollatzResearch.WordTrace tailWord_3985169 prefixEnd_3985169 682102395465874580553349 := by
  unfold tailWord_3985169
  simp only [CollatzResearch.WordTrace]
  refine ⟨145351054499420800523966561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96900702999613867015977707 145351054499420800523966561)
  ·
    refine ⟨109013290874565600392974921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145351054499420800523966561 109013290874565600392974921)
    ·
      refine ⟨81759968155924200294731191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109013290874565600392974921 81759968155924200294731191)
      ·
        refine ⟨122639952233886300442096787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81759968155924200294731191 122639952233886300442096787)
        ·
          refine ⟨183959928350829450663145181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122639952233886300442096787 183959928350829450663145181)
          ·
            refine ⟨68984973131561043998679443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183959928350829450663145181 68984973131561043998679443)
            ·
              refine ⟨103477459697341565998019165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68984973131561043998679443 103477459697341565998019165)
              ·
                refine ⟨38804047386503087249257187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103477459697341565998019165 38804047386503087249257187)
                ·
                  refine ⟨58206071079754630873885781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38804047386503087249257187 58206071079754630873885781)
                  ·
                    refine ⟨682102395465874580553349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58206071079754630873885781 682102395465874580553349)
                    ·
                      rfl

theorem cell23_3985169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_3985169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985169 prefixEnd_3985169 := by exact prefixLift 3985169
  have htrace : WordTrace (prefixWord ++ tailWord_3985169) baseStart_3985169 baseEnd_3985169 := by
    simpa [prefixWord, tailWord_3985169, baseEnd_3985169] using wordTrace_append hprefix tailTrace_3985169
  have hstable : (prefixWord ++ tailWord_3985169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985169).length < 2 ^ (prefixWord ++ tailWord_3985169).sum := by decide
  have hdescent : baseEnd_3985169 < baseStart_3985169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985179 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_3985179 : Nat := 118140960795 + 3985179 * 2 ^ 59
def prefixEnd_3985179 : Nat := 4983230072969 + 3 ^ 40 * 3985179 * 2
def baseEnd_3985179 : Nat := 2046312321204168702535001

theorem tailTrace_3985179 : CollatzResearch.WordTrace tailWord_3985179 prefixEnd_3985179 2046312321204168702535001 := by
  unfold tailWord_3985179
  simp only [CollatzResearch.WordTrace]
  refine ⟨145351419229384572231830591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96900946152923048154553727 145351419229384572231830591)
  ·
    refine ⟨218027128844076858347745887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145351419229384572231830591 218027128844076858347745887)
    ·
      refine ⟨327040693266115287521618831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218027128844076858347745887 327040693266115287521618831)
      ·
        refine ⟨490561039899172931282428247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327040693266115287521618831 490561039899172931282428247)
        ·
          refine ⟨735841559848759396923642371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490561039899172931282428247 735841559848759396923642371)
          ·
            refine ⟨1103762339773139095385463557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735841559848759396923642371 1103762339773139095385463557)
            ·
              refine ⟨206955438707463580384774417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1103762339773139095385463557 206955438707463580384774417)
              ·
                refine ⟨155216579030597685288580813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206955438707463580384774417 155216579030597685288580813)
                ·
                  refine ⟨58206217136474131983217805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155216579030597685288580813 58206217136474131983217805)
                  ·
                    refine ⟨21827331426177799493706677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58206217136474131983217805 21827331426177799493706677)
                    ·
                      refine ⟨2046312321204168702535001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21827331426177799493706677 2046312321204168702535001)
                      ·
                        rfl

theorem cell23_3985179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_3985179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985179 prefixEnd_3985179 := by exact prefixLift 3985179
  have htrace : WordTrace (prefixWord ++ tailWord_3985179) baseStart_3985179 baseEnd_3985179 := by
    simpa [prefixWord, tailWord_3985179, baseEnd_3985179] using wordTrace_append hprefix tailTrace_3985179
  have hstable : (prefixWord ++ tailWord_3985179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985179).length < 2 ^ (prefixWord ++ tailWord_3985179).sum := by decide
  have hdescent : baseEnd_3985179 < baseStart_3985179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985196 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_3985196 : Nat := 118140960795 + 3985196 * 2 ^ 59
def prefixEnd_3985196 : Nat := 4983230072969 + 3 ^ 40 * 3985196 * 2
def baseEnd_3985196 : Nat := 2046321050375295136022423

theorem tailTrace_3985196 : CollatzResearch.WordTrace tailWord_3985196 prefixEnd_3985196 2046321050375295136022423 := by
  unfold tailWord_3985196
  simp only [CollatzResearch.WordTrace]
  refine ⟨72676019635161492067599721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96901359513548656090132961 72676019635161492067599721)
  ·
    refine ⟨54507014726371119050699791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72676019635161492067599721 54507014726371119050699791)
    ·
      refine ⟨81760522089556678576049687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54507014726371119050699791 81760522089556678576049687)
      ·
        refine ⟨122640783134335017864074531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81760522089556678576049687 122640783134335017864074531)
        ·
          refine ⟨183961174701502526796111797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122640783134335017864074531 183961174701502526796111797)
          ·
            refine ⟨17246360128265861887135481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183961174701502526796111797 17246360128265861887135481)
            ·
              refine ⟨12934770096199396415351611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246360128265861887135481 12934770096199396415351611)
              ·
                refine ⟨19402155144299094623027417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12934770096199396415351611 19402155144299094623027417)
                ·
                  refine ⟨14551616358224320967270563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19402155144299094623027417 14551616358224320967270563)
                  ·
                    refine ⟨21827424537336481450905845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14551616358224320967270563 21827424537336481450905845)
                    ·
                      refine ⟨2046321050375295136022423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21827424537336481450905845 2046321050375295136022423)
                      ·
                        rfl

theorem cell23_3985196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_3985196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985196 prefixEnd_3985196 := by exact prefixLift 3985196
  have htrace : WordTrace (prefixWord ++ tailWord_3985196) baseStart_3985196 baseEnd_3985196 := by
    simpa [prefixWord, tailWord_3985196, baseEnd_3985196] using wordTrace_append hprefix tailTrace_3985196
  have hstable : (prefixWord ++ tailWord_3985196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985196).length < 2 ^ (prefixWord ++ tailWord_3985196).sum := by decide
  have hdescent : baseEnd_3985196 < baseStart_3985196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985199 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 9]
def baseStart_3985199 : Nat := 118140960795 + 3985199 * 2 ^ 59
def prefixEnd_3985199 : Nat := 4983230072969 + 3 ^ 40 * 3985199 * 2
def baseEnd_3985199 : Nat := 227369176757473180476101

theorem tailTrace_3985199 : CollatzResearch.WordTrace tailWord_3985199 prefixEnd_3985199 227369176757473180476101 := by
  unfold tailWord_3985199
  simp only [CollatzResearch.WordTrace]
  refine ⟨145352148689312115647558651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96901432459541410431705767 145352148689312115647558651)
  ·
    refine ⟨218028223033968173471337977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145352148689312115647558651 218028223033968173471337977)
    ·
      refine ⟨163521167275476130103503483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218028223033968173471337977 163521167275476130103503483)
      ·
        refine ⟨245281750913214195155255225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163521167275476130103503483 245281750913214195155255225)
        ·
          refine ⟨183961313184910646366441419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245281750913214195155255225 183961313184910646366441419)
          ·
            refine ⟨275941969777365969549662129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183961313184910646366441419 275941969777365969549662129)
            ·
              refine ⟨206956477333024477162246597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275941969777365969549662129 206956477333024477162246597)
              ·
                refine ⟨38804339499942089467921237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206956477333024477162246597 38804339499942089467921237)
                ·
                  refine ⟨227369176757473180476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38804339499942089467921237 227369176757473180476101)
                  ·
                    rfl

theorem cell23_3985199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 9].length) (baseStart_3985199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985199 prefixEnd_3985199 := by exact prefixLift 3985199
  have htrace : WordTrace (prefixWord ++ tailWord_3985199) baseStart_3985199 baseEnd_3985199 := by
    simpa [prefixWord, tailWord_3985199, baseEnd_3985199] using wordTrace_append hprefix tailTrace_3985199
  have hstable : (prefixWord ++ tailWord_3985199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985199).length < 2 ^ (prefixWord ++ tailWord_3985199).sum := by decide
  have hdescent : baseEnd_3985199 < baseStart_3985199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985213 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3985213 : Nat := 118140960795 + 3985213 * 2 ^ 59
def prefixEnd_3985213 : Nat := 4983230072969 + 3 ^ 40 * 3985213 * 2
def baseEnd_3985213 : Nat := 2046329779546421569509845

theorem tailTrace_3985213 : CollatzResearch.WordTrace tailWord_3985213 prefixEnd_3985213 2046329779546421569509845 := by
  unfold tailWord_3985213
  simp only [CollatzResearch.WordTrace]
  refine ⟨145352659311261396038568293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96901772874174264025712195 145352659311261396038568293)
  ·
    refine ⟨27253623620861511757231555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145352659311261396038568293 27253623620861511757231555)
    ·
      refine ⟨40880435431292267635847333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27253623620861511757231555 40880435431292267635847333)
      ·
        refine ⟨7665081643367300181721375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40880435431292267635847333 7665081643367300181721375)
        ·
          refine ⟨11497622465050950272582063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665081643367300181721375 11497622465050950272582063)
          ·
            refine ⟨17246433697576425408873095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497622465050950272582063 17246433697576425408873095)
            ·
              refine ⟨25869650546364638113309643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246433697576425408873095 25869650546364638113309643)
              ·
                refine ⟨38804475819546957169964465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25869650546364638113309643 38804475819546957169964465)
                ·
                  refine ⟨29103356864660217877473349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38804475819546957169964465 29103356864660217877473349)
                  ·
                    refine ⟨5456879412123790852026253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29103356864660217877473349 5456879412123790852026253)
                    ·
                      refine ⟨2046329779546421569509845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5456879412123790852026253 2046329779546421569509845)
                      ·
                        rfl

theorem cell23_3985213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3985213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985213 prefixEnd_3985213 := by exact prefixLift 3985213
  have htrace : WordTrace (prefixWord ++ tailWord_3985213) baseStart_3985213 baseEnd_3985213 := by
    simpa [prefixWord, tailWord_3985213, baseEnd_3985213] using wordTrace_append hprefix tailTrace_3985213
  have hstable : (prefixWord ++ tailWord_3985213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985213).length < 2 ^ (prefixWord ++ tailWord_3985213).sum := by decide
  have hdescent : baseEnd_3985213 < baseStart_3985213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985250 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_3985250 : Nat := 118140960795 + 3985250 * 2 ^ 59
def prefixEnd_3985250 : Nat := 4983230072969 + 3 ^ 40 * 3985250 * 2
def baseEnd_3985250 : Nat := 227372086481181991638575

theorem tailTrace_3985250 : CollatzResearch.WordTrace tailWord_3985250 prefixEnd_3985250 227372086481181991638575 := by
  unfold tailWord_3985250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36338502203031837839416301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96902672541418234238443469 36338502203031837839416301)
  ·
    refine ⟨13626938326136939189781113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36338502203031837839416301 13626938326136939189781113)
    ·
      refine ⟨10220203744602704392335835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13626938326136939189781113 10220203744602704392335835)
      ·
        refine ⟨15330305616904056588503753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10220203744602704392335835 15330305616904056588503753)
        ·
          refine ⟨11497729212678042441377815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15330305616904056588503753 11497729212678042441377815)
          ·
            refine ⟨17246593819017063662066723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11497729212678042441377815 17246593819017063662066723)
            ·
              refine ⟨25869890728525595493100085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17246593819017063662066723 25869890728525595493100085)
              ·
                refine ⟨2425302255799274577478133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25869890728525595493100085 2425302255799274577478133)
                ·
                  refine ⟨227372086481181991638575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425302255799274577478133 227372086481181991638575)
                  ·
                    rfl

theorem cell23_3985250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_3985250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985250 prefixEnd_3985250 := by exact prefixLift 3985250
  have htrace : WordTrace (prefixWord ++ tailWord_3985250) baseStart_3985250 baseEnd_3985250 := by
    simpa [prefixWord, tailWord_3985250, baseEnd_3985250] using wordTrace_append hprefix tailTrace_3985250
  have hstable : (prefixWord ++ tailWord_3985250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985250).length < 2 ^ (prefixWord ++ tailWord_3985250).sum := by decide
  have hdescent : baseEnd_3985250 < baseStart_3985250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985303 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3985303 : Nat := 118140960795 + 3985303 * 2 ^ 59
def prefixEnd_3985303 : Nat := 4983230072969 + 3 ^ 40 * 3985303 * 2
def baseEnd_3985303 : Nat := 2046375992805326217384431

theorem tailTrace_3985303 : CollatzResearch.WordTrace tailWord_3985303 prefixEnd_3985303 2046375992805326217384431 := by
  unfold tailWord_3985303
  simp only [CollatzResearch.WordTrace]
  refine ⟨145355941880935341409344563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96903961253956894272896375 145355941880935341409344563)
  ·
    refine ⟨218033912821403012114016845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145355941880935341409344563 218033912821403012114016845)
    ·
      refine ⟨81762717308026129542756317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218033912821403012114016845 81762717308026129542756317)
      ·
        refine ⟨30661018990509798578533619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81762717308026129542756317 30661018990509798578533619)
        ·
          refine ⟨45991528485764697867800429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30661018990509798578533619 45991528485764697867800429)
          ·
            refine ⟨17246823182161761700425161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45991528485764697867800429 17246823182161761700425161)
            ·
              refine ⟨12935117386621321275318871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17246823182161761700425161 12935117386621321275318871)
              ·
                refine ⟨19402676079931981912978307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935117386621321275318871 19402676079931981912978307)
                ·
                  refine ⟨29104014119897972869467461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19402676079931981912978307 29104014119897972869467461)
                  ·
                    refine ⟨5457002647480869913025149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29104014119897972869467461 5457002647480869913025149)
                    ·
                      refine ⟨2046375992805326217384431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457002647480869913025149 2046375992805326217384431)
                      ·
                        rfl

theorem cell23_3985303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3985303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985303 prefixEnd_3985303 := by exact prefixLift 3985303
  have htrace : WordTrace (prefixWord ++ tailWord_3985303) baseStart_3985303 baseEnd_3985303 := by
    simpa [prefixWord, tailWord_3985303, baseEnd_3985303] using wordTrace_append hprefix tailTrace_3985303
  have hstable : (prefixWord ++ tailWord_3985303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985303).length < 2 ^ (prefixWord ++ tailWord_3985303).sum := by decide
  have hdescent : baseEnd_3985303 < baseStart_3985303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985327 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 1, 4]
def baseStart_3985327 : Nat := 118140960795 + 3985327 * 2 ^ 59
def prefixEnd_3985327 : Nat := 4983230072969 + 3 ^ 40 * 3985327 * 2
def baseEnd_3985327 : Nat := 682129438780344707828107

theorem tailTrace_3985327 : CollatzResearch.WordTrace tailWord_3985327 prefixEnd_3985327 682129438780344707828107 := by
  unfold tailWord_3985327
  simp only [CollatzResearch.WordTrace]
  refine ⟨145356817232848393508218235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96904544821898929005478823 145356817232848393508218235)
  ·
    refine ⟨218035225849272590262327353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145356817232848393508218235 218035225849272590262327353)
    ·
      refine ⟨163526419386954442696745515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218035225849272590262327353 163526419386954442696745515)
      ·
        refine ⟨245289629080431664045118273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163526419386954442696745515 245289629080431664045118273)
        ·
          refine ⟨183967221810323748033838705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245289629080431664045118273 183967221810323748033838705)
          ·
            refine ⟨137975416357742811025379029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183967221810323748033838705 137975416357742811025379029)
            ·
              refine ⟨3233798820884597133407321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 137975416357742811025379029 3233798820884597133407321)
              ·
                refine ⟨2425349115663447850055491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233798820884597133407321 2425349115663447850055491)
                ·
                  refine ⟨3638023673495171775083237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425349115663447850055491 3638023673495171775083237)
                  ·
                    refine ⟨682129438780344707828107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638023673495171775083237 682129438780344707828107)
                    ·
                      rfl

theorem cell23_3985327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_3985327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985327 prefixEnd_3985327 := by exact prefixLift 3985327
  have htrace : WordTrace (prefixWord ++ tailWord_3985327) baseStart_3985327 baseEnd_3985327 := by
    simpa [prefixWord, tailWord_3985327, baseEnd_3985327] using wordTrace_append hprefix tailTrace_3985327
  have hstable : (prefixWord ++ tailWord_3985327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985327).length < 2 ^ (prefixWord ++ tailWord_3985327).sum := by decide
  have hdescent : baseEnd_3985327 < baseStart_3985327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985360 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2]
def baseStart_3985360 : Nat := 118140960795 + 3985360 * 2 ^ 59
def prefixEnd_3985360 : Nat := 4983230072969 + 3 ^ 40 * 3985360 * 2
def baseEnd_3985360 : Nat := 2046405261202632494371669

theorem tailTrace_3985360 : CollatzResearch.WordTrace tailWord_3985360 prefixEnd_3985360 2046405261202632494371669 := by
  unfold tailWord_3985360
  simp only [CollatzResearch.WordTrace]
  refine ⟨72679010420864420072084767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96905347227819226762779689 72679010420864420072084767)
  ·
    refine ⟨109018515631296630108127151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72679010420864420072084767 109018515631296630108127151)
    ·
      refine ⟨163527773446944945162190727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109018515631296630108127151 163527773446944945162190727)
      ·
        refine ⟨245291660170417417743286091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163527773446944945162190727 245291660170417417743286091)
        ·
          refine ⟨367937490255626126614929137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245291660170417417743286091 367937490255626126614929137)
          ·
            refine ⟨275953117691719594961196853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367937490255626126614929137 275953117691719594961196853)
            ·
              refine ⟨25870604783598712027612205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275953117691719594961196853 25870604783598712027612205)
              ·
                refine ⟨9701476793849517010354577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25870604783598712027612205 9701476793849517010354577)
                ·
                  refine ⟨7276107595387137757765933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9701476793849517010354577 7276107595387137757765933)
                  ·
                    refine ⟨2728540348270176659162225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7276107595387137757765933 2728540348270176659162225)
                    ·
                      refine ⟨2046405261202632494371669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728540348270176659162225 2046405261202632494371669)
                      ·
                        rfl

theorem cell23_3985360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 3, 2].length) (baseStart_3985360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985360 prefixEnd_3985360 := by exact prefixLift 3985360
  have htrace : WordTrace (prefixWord ++ tailWord_3985360) baseStart_3985360 baseEnd_3985360 := by
    simpa [prefixWord, tailWord_3985360, baseEnd_3985360] using wordTrace_append hprefix tailTrace_3985360
  have hstable : (prefixWord ++ tailWord_3985360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985360).length < 2 ^ (prefixWord ++ tailWord_3985360).sum := by decide
  have hdescent : baseEnd_3985360 < baseStart_3985360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985367 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_3985367 : Nat := 118140960795 + 3985367 * 2 ^ 59
def prefixEnd_3985367 : Nat := 4983230072969 + 3 ^ 40 * 3985367 * 2
def baseEnd_3985367 : Nat := 2046408855567213966984137

theorem tailTrace_3985367 : CollatzResearch.WordTrace tailWord_3985367 prefixEnd_3985367 2046408855567213966984137 := by
  unfold tailWord_3985367
  simp only [CollatzResearch.WordTrace]
  refine ⟨145358276152703480339674355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96905517435135653559782903 145358276152703480339674355)
  ·
    refine ⟨218037414229055220509511533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145358276152703480339674355 218037414229055220509511533)
    ·
      refine ⟨81764030335895707691066825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218037414229055220509511533 81764030335895707691066825)
      ·
        refine ⟨61323022751921780768300119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81764030335895707691066825 61323022751921780768300119)
        ·
          refine ⟨91984534127882671152450179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61323022751921780768300119 91984534127882671152450179)
          ·
            refine ⟨137976801191824006728675269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91984534127882671152450179 137976801191824006728675269)
            ·
              refine ⟨25870650223467001261626613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137976801191824006728675269 25870650223467001261626613)
              ·
                refine ⟨2425373458450031368277495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25870650223467001261626613 2425373458450031368277495)
                ·
                  refine ⟨3638060187675047052416243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425373458450031368277495 3638060187675047052416243)
                  ·
                    refine ⟨5457090281512570578624365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638060187675047052416243 5457090281512570578624365)
                    ·
                      refine ⟨2046408855567213966984137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457090281512570578624365 2046408855567213966984137)
                      ·
                        rfl

theorem cell23_3985367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_3985367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985367 prefixEnd_3985367 := by exact prefixLift 3985367
  have htrace : WordTrace (prefixWord ++ tailWord_3985367) baseStart_3985367 baseEnd_3985367 := by
    simpa [prefixWord, tailWord_3985367, baseEnd_3985367] using wordTrace_append hprefix tailTrace_3985367
  have hstable : (prefixWord ++ tailWord_3985367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985367).length < 2 ^ (prefixWord ++ tailWord_3985367).sum := by decide
  have hdescent : baseEnd_3985367 < baseStart_3985367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985378 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3985378 : Nat := 118140960795 + 3985378 * 2 ^ 59
def prefixEnd_3985378 : Nat := 4983230072969 + 3 ^ 40 * 3985378 * 2
def baseEnd_3985378 : Nat := 682138167951471141315529

theorem tailTrace_3985378 : CollatzResearch.WordTrace tailWord_3985378 prefixEnd_3985378 682138167951471141315529 := by
  unfold tailWord_3985378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36339669338915907304581197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96905784903775752812216525 36339669338915907304581197)
  ·
    refine ⟨13627376002093465239217949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36339669338915907304581197 13627376002093465239217949)
    ·
      refine ⟨5110266000785049464706731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13627376002093465239217949 5110266000785049464706731)
      ·
        refine ⟨7665399001177574197060097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110266000785049464706731 7665399001177574197060097)
        ·
          refine ⟨5749049250883180647795073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7665399001177574197060097 5749049250883180647795073)
          ·
            refine ⟨4311786938162385485846305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5749049250883180647795073 4311786938162385485846305)
            ·
              refine ⟨3233840203621789114384729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311786938162385485846305 3233840203621789114384729)
              ·
                refine ⟨2425380152716341835788547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233840203621789114384729 2425380152716341835788547)
                ·
                  refine ⟨3638070229074512753682821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425380152716341835788547 3638070229074512753682821)
                  ·
                    refine ⟨682138167951471141315529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638070229074512753682821 682138167951471141315529)
                    ·
                      rfl

theorem cell23_3985378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3985378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985378 prefixEnd_3985378 := by exact prefixLift 3985378
  have htrace : WordTrace (prefixWord ++ tailWord_3985378) baseStart_3985378 baseEnd_3985378 := by
    simpa [prefixWord, tailWord_3985378, baseEnd_3985378] using wordTrace_append hprefix tailTrace_3985378
  have hstable : (prefixWord ++ tailWord_3985378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985378).length < 2 ^ (prefixWord ++ tailWord_3985378).sum := by decide
  have hdescent : baseEnd_3985378 < baseStart_3985378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985390 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3985390 : Nat := 118140960795 + 3985390 * 2 ^ 59
def prefixEnd_3985390 : Nat := 4983230072969 + 3 ^ 40 * 3985390 * 2
def baseEnd_3985390 : Nat := 2046420665622267376996531

theorem tailTrace_3985390 : CollatzResearch.WordTrace tailWord_3985390 prefixEnd_3985390 2046420665622267376996531 := by
  unfold tailWord_3985390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169889378952519408470203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96906076687746770178507749 18169889378952519408470203)
  ·
    refine ⟨27254834068428779112705305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18169889378952519408470203 27254834068428779112705305)
    ·
      refine ⟨20441125551321584334528979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27254834068428779112705305 20441125551321584334528979)
      ·
        refine ⟨30661688326982376501793469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20441125551321584334528979 30661688326982376501793469)
        ·
          refine ⟨11498133122618391188172551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30661688326982376501793469 11498133122618391188172551)
          ·
            refine ⟨17247199683927586782258827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498133122618391188172551 17247199683927586782258827)
            ·
              refine ⟨25870799525891380173388241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17247199683927586782258827 25870799525891380173388241)
              ·
                refine ⟨19403099644418535130041181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25870799525891380173388241 19403099644418535130041181)
                ·
                  refine ⟨7276162366656950673765443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19403099644418535130041181 7276162366656950673765443)
                  ·
                    refine ⟨10914243549985426010648165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7276162366656950673765443 10914243549985426010648165)
                    ·
                      refine ⟨2046420665622267376996531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10914243549985426010648165 2046420665622267376996531)
                      ·
                        rfl

theorem cell23_3985390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3985390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985390 prefixEnd_3985390 := by exact prefixLift 3985390
  have htrace : WordTrace (prefixWord ++ tailWord_3985390) baseStart_3985390 baseEnd_3985390 := by
    simpa [prefixWord, tailWord_3985390, baseEnd_3985390] using wordTrace_append hprefix tailTrace_3985390
  have hstable : (prefixWord ++ tailWord_3985390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985390).length < 2 ^ (prefixWord ++ tailWord_3985390).sum := by decide
  have hdescent : baseEnd_3985390 < baseStart_3985390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985400 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_3985400 : Nat := 118140960795 + 3985400 * 2 ^ 59
def prefixEnd_3985400 : Nat := 4983230072969 + 3 ^ 40 * 3985400 * 2
def baseEnd_3985400 : Nat := 682141933476270779290495

theorem tailTrace_3985400 : CollatzResearch.WordTrace tailWord_3985400 prefixEnd_3985400 682141933476270779290495 := by
  unfold tailWord_3985400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72679739880791963487812827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96906319841055951317083769 72679739880791963487812827)
  ·
    refine ⟨109019609821187945231719241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72679739880791963487812827 109019609821187945231719241)
    ·
      refine ⟨81764707365890958923789431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109019609821187945231719241 81764707365890958923789431)
      ·
        refine ⟨122647061048836438385684147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81764707365890958923789431 122647061048836438385684147)
        ·
          refine ⟨183970591573254657578526221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122647061048836438385684147 183970591573254657578526221)
          ·
            refine ⟨68988971839970496591947333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183970591573254657578526221 68988971839970496591947333)
            ·
              refine ⟨12935432219994468110990125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68988971839970496591947333 12935432219994468110990125)
              ·
                refine ⟨4850787082497925541621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935432219994468110990125 4850787082497925541621297)
                ·
                  refine ⟨3638090311873444156215973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850787082497925541621297 3638090311873444156215973)
                  ·
                    refine ⟨682141933476270779290495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638090311873444156215973 682141933476270779290495)
                    ·
                      rfl

theorem cell23_3985400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_3985400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985400 prefixEnd_3985400 := by exact prefixLift 3985400
  have htrace : WordTrace (prefixWord ++ tailWord_3985400) baseStart_3985400 baseEnd_3985400 := by
    simpa [prefixWord, tailWord_3985400, baseEnd_3985400] using wordTrace_append hprefix tailTrace_3985400
  have hstable : (prefixWord ++ tailWord_3985400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985400).length < 2 ^ (prefixWord ++ tailWord_3985400).sum := by decide
  have hdescent : baseEnd_3985400 < baseStart_3985400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985403 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4]
def baseStart_3985403 : Nat := 118140960795 + 3985403 * 2 ^ 59
def prefixEnd_3985403 : Nat := 4983230072969 + 3 ^ 40 * 3985403 * 2
def baseEnd_3985403 : Nat := 2046427340870775826133971

theorem tailTrace_3985403 : CollatzResearch.WordTrace tailWord_3985403 prefixEnd_3985403 2046427340870775826133971 := by
  unfold tailWord_3985403
  simp only [CollatzResearch.WordTrace]
  refine ⟨145359589180573058487984863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96906392787048705658656575 145359589180573058487984863)
  ·
    refine ⟨218039383770859587731977295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145359589180573058487984863 218039383770859587731977295)
    ·
      refine ⟨327059075656289381597965943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218039383770859587731977295 327059075656289381597965943)
      ·
        refine ⟨490588613484434072396948915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327059075656289381597965943 490588613484434072396948915)
        ·
          refine ⟨735882920226651108595423373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490588613484434072396948915 735882920226651108595423373)
          ·
            refine ⟨275956095084994165723283765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 735882920226651108595423373 275956095084994165723283765)
            ·
              refine ⟨25870883914218203036557853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275956095084994165723283765 25870883914218203036557853)
              ·
                refine ⟨9701581467831826138709195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25870883914218203036557853 9701581467831826138709195)
                ·
                  refine ⟨14552372201747739208063793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701581467831826138709195 14552372201747739208063793)
                  ·
                    refine ⟨10914279151310804406047845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14552372201747739208063793 10914279151310804406047845)
                    ·
                      refine ⟨2046427340870775826133971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10914279151310804406047845 2046427340870775826133971)
                      ·
                        rfl

theorem cell23_3985403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 4].length) (baseStart_3985403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985403 prefixEnd_3985403 := by exact prefixLift 3985403
  have htrace : WordTrace (prefixWord ++ tailWord_3985403) baseStart_3985403 baseEnd_3985403 := by
    simpa [prefixWord, tailWord_3985403, baseEnd_3985403] using wordTrace_append hprefix tailTrace_3985403
  have hstable : (prefixWord ++ tailWord_3985403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985403).length < 2 ^ (prefixWord ++ tailWord_3985403).sum := by decide
  have hdescent : baseEnd_3985403 < baseStart_3985403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985421 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3985421 : Nat := 118140960795 + 3985421 * 2 ^ 59
def prefixEnd_3985421 : Nat := 4983230072969 + 3 ^ 40 * 3985421 * 2
def baseEnd_3985421 : Nat := 682145527840852251902963

theorem tailTrace_3985421 : CollatzResearch.WordTrace tailWord_3985421 prefixEnd_3985421 682145527840852251902963 := by
  unfold tailWord_3985421
  simp only [CollatzResearch.WordTrace]
  refine ⟨145360245694507847562140117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96906830463005231708093411 145360245694507847562140117)
  ·
    refine ⟨3406880758465027677237659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 145360245694507847562140117 3406880758465027677237659)
    ·
      refine ⟨5110321137697541515856489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406880758465027677237659 5110321137697541515856489)
      ·
        refine ⟨3832740853273156136892367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110321137697541515856489 3832740853273156136892367)
        ·
          refine ⟨5749111279909734205338551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832740853273156136892367 5749111279909734205338551)
          ·
            refine ⟨8623666919864601308007827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749111279909734205338551 8623666919864601308007827)
            ·
              refine ⟨12935500379796901962011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623666919864601308007827 12935500379796901962011741)
              ·
                refine ⟨4850812642423838235754403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12935500379796901962011741 4850812642423838235754403)
                ·
                  refine ⟨7276218963635757353631605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850812642423838235754403 7276218963635757353631605)
                  ·
                    refine ⟨682145527840852251902963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7276218963635757353631605 682145527840852251902963)
                    ·
                      rfl

theorem cell23_3985421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3985421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985421 prefixEnd_3985421 := by exact prefixLift 3985421
  have htrace : WordTrace (prefixWord ++ tailWord_3985421) baseStart_3985421 baseEnd_3985421 := by
    simpa [prefixWord, tailWord_3985421, baseEnd_3985421] using wordTrace_append hprefix tailTrace_3985421
  have hstable : (prefixWord ++ tailWord_3985421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985421).length < 2 ^ (prefixWord ++ tailWord_3985421).sum := by decide
  have hdescent : baseEnd_3985421 < baseStart_3985421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985427 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 1, 2, 3]
def baseStart_3985427 : Nat := 118140960795 + 3985427 * 2 ^ 59
def prefixEnd_3985427 : Nat := 4983230072969 + 3 ^ 40 * 3985427 * 2
def baseEnd_3985427 : Nat := 2046439664406483732233861

theorem tailTrace_3985427 : CollatzResearch.WordTrace tailWord_3985427 prefixEnd_3985427 2046439664406483732233861 := by
  unfold tailWord_3985427
  simp only [CollatzResearch.WordTrace]
  refine ⟨145360464532486110586858535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96906976354990740391239023 145360464532486110586858535)
  ·
    refine ⟨218040696798729165880287803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145360464532486110586858535 218040696798729165880287803)
    ·
      refine ⟨327061045198093748820431705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218040696798729165880287803 327061045198093748820431705)
      ·
        refine ⟨245295783898570311615323779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327061045198093748820431705 245295783898570311615323779)
        ·
          refine ⟨367943675847855467422985669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245295783898570311615323779 367943675847855467422985669)
          ·
            refine ⟨68989439221472900141809813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367943675847855467422985669 68989439221472900141809813)
            ·
              refine ⟨3233879963506542194147335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68989439221472900141809813 3233879963506542194147335)
              ·
                refine ⟨4850819945259813291221003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233879963506542194147335 4850819945259813291221003)
                ·
                  refine ⟨7276229917889719936831505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4850819945259813291221003 7276229917889719936831505)
                  ·
                    refine ⟨5457172438417289952623629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7276229917889719936831505 5457172438417289952623629)
                    ·
                      refine ⟨2046439664406483732233861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457172438417289952623629 2046439664406483732233861)
                      ·
                        rfl

theorem cell23_3985427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 2, 3].length) (baseStart_3985427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985427 prefixEnd_3985427 := by exact prefixLift 3985427
  have htrace : WordTrace (prefixWord ++ tailWord_3985427) baseStart_3985427 baseEnd_3985427 := by
    simpa [prefixWord, tailWord_3985427, baseEnd_3985427] using wordTrace_append hprefix tailTrace_3985427
  have hstable : (prefixWord ++ tailWord_3985427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985427).length < 2 ^ (prefixWord ++ tailWord_3985427).sum := by decide
  have hdescent : baseEnd_3985427 < baseStart_3985427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985457 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3985457 : Nat := 118140960795 + 3985457 * 2 ^ 59
def prefixEnd_3985457 : Nat := 4983230072969 + 3 ^ 40 * 3985457 * 2
def baseEnd_3985457 : Nat := 2046455068826118614858723

theorem tailTrace_3985457 : CollatzResearch.WordTrace tailWord_3985457 prefixEnd_3985457 2046455068826118614858723 := by
  unfold tailWord_3985457
  simp only [CollatzResearch.WordTrace]
  refine ⟨145361558722377425710450625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96907705814918283806967083 145361558722377425710450625)
  ·
    refine ⟨109021169041783069282837969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145361558722377425710450625 109021169041783069282837969)
    ·
      refine ⟨81765876781337301962128477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109021169041783069282837969 81765876781337301962128477)
      ·
        refine ⟨30662203793001488235798179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81765876781337301962128477 30662203793001488235798179)
        ·
          refine ⟨45993305689502232353697269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30662203793001488235798179 45993305689502232353697269)
          ·
            refine ⟨4311872408390834283159119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45993305689502232353697269 4311872408390834283159119)
            ·
              refine ⟨6467808612586251424738679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4311872408390834283159119 6467808612586251424738679)
              ·
                refine ⟨9701712918879377137108019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6467808612586251424738679 9701712918879377137108019)
                ·
                  refine ⟨14552569378319065705662029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9701712918879377137108019 14552569378319065705662029)
                  ·
                    refine ⟨5457213516869649639623261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14552569378319065705662029 5457213516869649639623261)
                    ·
                      refine ⟨2046455068826118614858723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457213516869649639623261 2046455068826118614858723)
                      ·
                        rfl

theorem cell23_3985457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3985457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985457 prefixEnd_3985457 := by exact prefixLift 3985457
  have htrace : WordTrace (prefixWord ++ tailWord_3985457) baseStart_3985457 baseEnd_3985457 := by
    simpa [prefixWord, tailWord_3985457, baseEnd_3985457] using wordTrace_append hprefix tailTrace_3985457
  have hstable : (prefixWord ++ tailWord_3985457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985457).length < 2 ^ (prefixWord ++ tailWord_3985457).sum := by decide
  have hdescent : baseEnd_3985457 < baseStart_3985457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985463 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3985463 : Nat := 118140960795 + 3985463 * 2 ^ 59
def prefixEnd_3985463 : Nat := 4983230072969 + 3 ^ 40 * 3985463 * 2
def baseEnd_3985463 : Nat := 2046458149710045591383695

theorem tailTrace_3985463 : CollatzResearch.WordTrace tailWord_3985463 prefixEnd_3985463 2046458149710045591383695 := by
  unfold tailWord_3985463
  simp only [CollatzResearch.WordTrace]
  refine ⟨145361777560355688735169043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96907851706903792490112695 145361777560355688735169043)
  ·
    refine ⟨218042666340533533102753565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145361777560355688735169043 218042666340533533102753565)
    ·
      refine ⟨81765999877700074913532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218042666340533533102753565 81765999877700074913532587)
      ·
        refine ⟨122648999816550112370298881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81765999877700074913532587 122648999816550112370298881)
        ·
          refine ⟨91986749862412584277724161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122648999816550112370298881 91986749862412584277724161)
          ·
            refine ⟨68990062396809438208293121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91986749862412584277724161 68990062396809438208293121)
            ·
              refine ⟨51742546797607078656219841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68990062396809438208293121 51742546797607078656219841)
              ·
                refine ⟨38806910098205308992164881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51742546797607078656219841 38806910098205308992164881)
                ·
                  refine ⟨29105182573653981744123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38806910098205308992164881 29105182573653981744123661)
                  ·
                    refine ⟨10914443465120243154046373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29105182573653981744123661 10914443465120243154046373)
                    ·
                      refine ⟨2046458149710045591383695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10914443465120243154046373 2046458149710045591383695)
                      ·
                        rfl

theorem cell23_3985463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3985463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985463 prefixEnd_3985463 := by exact prefixLift 3985463
  have htrace : WordTrace (prefixWord ++ tailWord_3985463) baseStart_3985463 baseEnd_3985463 := by
    simpa [prefixWord, tailWord_3985463, baseEnd_3985463] using wordTrace_append hprefix tailTrace_3985463
  have hstable : (prefixWord ++ tailWord_3985463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985463).length < 2 ^ (prefixWord ++ tailWord_3985463).sum := by decide
  have hdescent : baseEnd_3985463 < baseStart_3985463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985483 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5]
def baseStart_3985483 : Nat := 118140960795 + 3985483 * 2 ^ 59
def prefixEnd_3985483 : Nat := 4983230072969 + 3 ^ 40 * 3985483 * 2
def baseEnd_3985483 : Nat := 2046468419323135513133603

theorem tailTrace_3985483 : CollatzResearch.WordTrace tailWord_3985483 prefixEnd_3985483 2046468419323135513133603 := by
  unfold tailWord_3985483
  simp only [CollatzResearch.WordTrace]
  refine ⟨145362507020283232150897103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96908338013522154767264735 145362507020283232150897103)
  ·
    refine ⟨218043760530424848226345655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145362507020283232150897103 218043760530424848226345655)
    ·
      refine ⟨327065640795637272339518483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218043760530424848226345655 327065640795637272339518483)
      ·
        refine ⟨490598461193455908509277725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327065640795637272339518483 490598461193455908509277725)
        ·
          refine ⟨183974422947545965690979147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490598461193455908509277725 183974422947545965690979147)
          ·
            refine ⟨275961634421318948536468721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183974422947545965690979147 275961634421318948536468721)
            ·
              refine ⟨206971225815989211402351541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275961634421318948536468721 206971225815989211402351541)
              ·
                refine ⟨19403552420248988568970457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206971225815989211402351541 19403552420248988568970457)
                ·
                  refine ⟨14552664315186741426727843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403552420248988568970457 14552664315186741426727843)
                  ·
                    refine ⟨21828996472780112140091765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14552664315186741426727843 21828996472780112140091765)
                    ·
                      refine ⟨2046468419323135513133603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21828996472780112140091765 2046468419323135513133603)
                      ·
                        rfl

theorem cell23_3985483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_3985483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985483 prefixEnd_3985483 := by exact prefixLift 3985483
  have htrace : WordTrace (prefixWord ++ tailWord_3985483) baseStart_3985483 baseEnd_3985483 := by
    simpa [prefixWord, tailWord_3985483, baseEnd_3985483] using wordTrace_append hprefix tailTrace_3985483
  have hstable : (prefixWord ++ tailWord_3985483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985483).length < 2 ^ (prefixWord ++ tailWord_3985483).sum := by decide
  have hdescent : baseEnd_3985483 < baseStart_3985483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985497 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 4, 2, 2]
def baseStart_3985497 : Nat := 118140960795 + 3985497 * 2 ^ 59
def prefixEnd_3985497 : Nat := 4983230072969 + 3 ^ 40 * 3985497 * 2
def baseEnd_3985497 : Nat := 2046475608052298458358539

theorem tailTrace_3985497 : CollatzResearch.WordTrace tailWord_3985497 prefixEnd_3985497 2046475608052298458358539 := by
  unfold tailWord_3985497
  simp only [CollatzResearch.WordTrace]
  refine ⟨145363017642232512541906745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96908678428155008361271163 145363017642232512541906745)
  ·
    refine ⟨109022263231674384406430059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145363017642232512541906745 109022263231674384406430059)
    ·
      refine ⟨163533394847511576609645089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109022263231674384406430059 163533394847511576609645089)
      ·
        refine ⟨122650046135633682457233817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163533394847511576609645089 122650046135633682457233817)
        ·
          refine ⟨91987534601725261842925363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122650046135633682457233817 91987534601725261842925363)
          ·
            refine ⟨137981301902587892764388045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91987534601725261842925363 137981301902587892764388045)
            ·
              refine ⟨51742988213470459786645517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137981301902587892764388045 51742988213470459786645517)
              ·
                refine ⟨19403620580051422419992069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51742988213470459786645517 19403620580051422419992069)
                ·
                  refine ⟨3638178858759641703748513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19403620580051422419992069 3638178858759641703748513)
                  ·
                    refine ⟨2728634144069731277811385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638178858759641703748513 2728634144069731277811385)
                    ·
                      refine ⟨2046475608052298458358539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728634144069731277811385 2046475608052298458358539)
                      ·
                        rfl

theorem cell23_3985497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_3985497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985497 prefixEnd_3985497 := by exact prefixLift 3985497
  have htrace : WordTrace (prefixWord ++ tailWord_3985497) baseStart_3985497 baseEnd_3985497 := by
    simpa [prefixWord, tailWord_3985497, baseEnd_3985497] using wordTrace_append hprefix tailTrace_3985497
  have hstable : (prefixWord ++ tailWord_3985497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985497).length < 2 ^ (prefixWord ++ tailWord_3985497).sum := by decide
  have hdescent : baseEnd_3985497 < baseStart_3985497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985503 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 7]
def baseStart_3985503 : Nat := 118140960795 + 3985503 * 2 ^ 59
def prefixEnd_3985503 : Nat := 4983230072969 + 3 ^ 40 * 3985503 * 2
def baseEnd_3985503 : Nat := 227386520992913937209279

theorem tailTrace_3985503 : CollatzResearch.WordTrace tailWord_3985503 prefixEnd_3985503 227386520992913937209279 := by
  unfold tailWord_3985503
  simp only [CollatzResearch.WordTrace]
  refine ⟨145363236480210775566625163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96908824320140517044416775 145363236480210775566625163)
  ·
    refine ⟨218044854720316163349937745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145363236480210775566625163 218044854720316163349937745)
    ·
      refine ⟨163533641040237122512453309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218044854720316163349937745 163533641040237122512453309)
      ·
        refine ⟨61325115390088920942169991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163533641040237122512453309 61325115390088920942169991)
        ·
          refine ⟨91987673085133381413254987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61325115390088920942169991 91987673085133381413254987)
          ·
            refine ⟨137981509627700072119882481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91987673085133381413254987 137981509627700072119882481)
            ·
              refine ⟨103486132220775054089911861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137981509627700072119882481 103486132220775054089911861)
              ·
                refine ⟨9701824895697661320929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103486132220775054089911861 9701824895697661320929237)
                ·
                  refine ⟨227386520992913937209279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9701824895697661320929237 227386520992913937209279)
                  ·
                    rfl

theorem cell23_3985503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 7].length) (baseStart_3985503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985503 prefixEnd_3985503 := by exact prefixLift 3985503
  have htrace : WordTrace (prefixWord ++ tailWord_3985503) baseStart_3985503 baseEnd_3985503 := by
    simpa [prefixWord, tailWord_3985503, baseEnd_3985503] using wordTrace_append hprefix tailTrace_3985503
  have hstable : (prefixWord ++ tailWord_3985503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985503).length < 2 ^ (prefixWord ++ tailWord_3985503).sum := by decide
  have hdescent : baseEnd_3985503 < baseStart_3985503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985558 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3985558 : Nat := 118140960795 + 3985558 * 2 ^ 59
def prefixEnd_3985558 : Nat := 4983230072969 + 3 ^ 40 * 3985558 * 2
def baseEnd_3985558 : Nat := 682168976790740906565253

theorem tailTrace_3985558 : CollatzResearch.WordTrace tailWord_3985558 prefixEnd_3985558 682168976790740906565253 := by
  unfold tailWord_3985558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085327655938219997492333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96910161663341013306584885 9085327655938219997492333)
  ·
    refine ⟨3406997870976832499059625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9085327655938219997492333 3406997870976832499059625)
    ·
      refine ⟨2555248403232624374294719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3406997870976832499059625 2555248403232624374294719)
      ·
        refine ⟨3832872604848936561442079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555248403232624374294719 3832872604848936561442079)
        ·
          refine ⟨5749308907273404842163119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832872604848936561442079 5749308907273404842163119)
          ·
            refine ⟨8623963360910107263244679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749308907273404842163119 8623963360910107263244679)
            ·
              refine ⟨12935945041365160894867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8623963360910107263244679 12935945041365160894867019)
              ·
                refine ⟨19403917562047741342300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12935945041365160894867019 19403917562047741342300529)
                ·
                  refine ⟨14552938171535806006725397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19403917562047741342300529 14552938171535806006725397)
                  ·
                    refine ⟨682168976790740906565253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14552938171535806006725397 682168976790740906565253)
                    ·
                      rfl

theorem cell23_3985558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3985558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985558 prefixEnd_3985558 := by exact prefixLift 3985558
  have htrace : WordTrace (prefixWord ++ tailWord_3985558) baseStart_3985558 baseEnd_3985558 := by
    simpa [prefixWord, tailWord_3985558, baseEnd_3985558] using wordTrace_append hprefix tailTrace_3985558
  have hstable : (prefixWord ++ tailWord_3985558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985558).length < 2 ^ (prefixWord ++ tailWord_3985558).sum := by decide
  have hdescent : baseEnd_3985558 < baseStart_3985558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985600 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3985600 : Nat := 118140960795 + 3985600 * 2 ^ 59
def prefixEnd_3985600 : Nat := 4983230072969 + 3 ^ 40 * 3985600 * 2
def baseEnd_3985600 : Nat := 2046528496559711555370565

theorem tailTrace_3985600 : CollatzResearch.WordTrace tailWord_3985600 prefixEnd_3985600 2046528496559711555370565 := by
  unfold tailWord_3985600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72683387180429680566453127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96911182907239574088604169 72683387180429680566453127)
  ·
    refine ⟨109025080770644520849679691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72683387180429680566453127 109025080770644520849679691)
    ·
      refine ⟨163537621155966781274519537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109025080770644520849679691 163537621155966781274519537)
      ·
        refine ⟨122653215866975085955889653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163537621155966781274519537 122653215866975085955889653)
        ·
          refine ⟨11498738987528914308364655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122653215866975085955889653 11498738987528914308364655)
          ·
            refine ⟨17248108481293371462546983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498738987528914308364655 17248108481293371462546983)
            ·
              refine ⟨25872162721940057193820475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248108481293371462546983 25872162721940057193820475)
              ·
                refine ⟨38808244082910085790730713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25872162721940057193820475 38808244082910085790730713)
                ·
                  refine ⟨29106183062182564343048035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38808244082910085790730713 29106183062182564343048035)
                  ·
                    refine ⟨43659274593273846514572053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29106183062182564343048035 43659274593273846514572053)
                    ·
                      refine ⟨2046528496559711555370565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43659274593273846514572053 2046528496559711555370565)
                      ·
                        rfl

theorem cell23_3985600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3985600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985600 prefixEnd_3985600 := by exact prefixLift 3985600
  have htrace : WordTrace (prefixWord ++ tailWord_3985600) baseStart_3985600 baseEnd_3985600 := by
    simpa [prefixWord, tailWord_3985600, baseEnd_3985600] using wordTrace_append hprefix tailTrace_3985600
  have hstable : (prefixWord ++ tailWord_3985600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985600).length < 2 ^ (prefixWord ++ tailWord_3985600).sum := by decide
  have hdescent : baseEnd_3985600 < baseStart_3985600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985604 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3985604 : Nat := 118140960795 + 3985604 * 2 ^ 59
def prefixEnd_3985604 : Nat := 4983230072969 + 3 ^ 40 * 3985604 * 2
def baseEnd_3985604 : Nat := 2046530550482329539720547

theorem tailTrace_3985604 : CollatzResearch.WordTrace tailWord_3985604 prefixEnd_3985604 2046530550482329539720547 := by
  unfold tailWord_3985604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72683460126422434908025933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96911280168563246544034577 72683460126422434908025933)
  ·
    refine ⟨27256297547408413090509725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72683460126422434908025933 27256297547408413090509725)
    ·
      refine ⟨10221111580278154908941147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27256297547408413090509725 10221111580278154908941147)
      ·
        refine ⟨15331667370417232363411721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221111580278154908941147 15331667370417232363411721)
        ·
          refine ⟨11498750527812924272558791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15331667370417232363411721 11498750527812924272558791)
          ·
            refine ⟨17248125791719386408838187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11498750527812924272558791 17248125791719386408838187)
            ·
              refine ⟨25872188687579079613257281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17248125791719386408838187 25872188687579079613257281)
              ·
                refine ⟨19404141515684309709942961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25872188687579079613257281 19404141515684309709942961)
                ·
                  refine ⟨14553106136763232282457221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19404141515684309709942961 14553106136763232282457221)
                  ·
                    refine ⟨2728707400643106052960729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14553106136763232282457221 2728707400643106052960729)
                    ·
                      refine ⟨2046530550482329539720547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728707400643106052960729 2046530550482329539720547)
                      ·
                        rfl

theorem cell23_3985604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3985604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985604 prefixEnd_3985604 := by exact prefixLift 3985604
  have htrace : WordTrace (prefixWord ++ tailWord_3985604) baseStart_3985604 baseEnd_3985604 := by
    simpa [prefixWord, tailWord_3985604, baseEnd_3985604] using wordTrace_append hprefix tailTrace_3985604
  have hstable : (prefixWord ++ tailWord_3985604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985604).length < 2 ^ (prefixWord ++ tailWord_3985604).sum := by decide
  have hdescent : baseEnd_3985604 < baseStart_3985604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985610 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_3985610 : Nat := 118140960795 + 3985610 * 2 ^ 59
def prefixEnd_3985610 : Nat := 4983230072969 + 3 ^ 40 * 3985610 * 2
def baseEnd_3985610 : Nat := 227392625707361835138391

theorem tailTrace_3985610 : CollatzResearch.WordTrace tailWord_3985610 prefixEnd_3985610 227392625707361835138391 := by
  unfold tailWord_3985610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36341784772705783210192571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96911426060548755227180189 36341784772705783210192571)
  ·
    refine ⟨54512677159058674815288857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36341784772705783210192571 54512677159058674815288857)
    ·
      refine ⟨40884507869294006111466643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54512677159058674815288857 40884507869294006111466643)
      ·
        refine ⟨61326761803941009167199965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40884507869294006111466643 61326761803941009167199965)
        ·
          refine ⟨22997535676477878437699987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61326761803941009167199965 22997535676477878437699987)
          ·
            refine ⟨34496303514716817656549981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22997535676477878437699987 34496303514716817656549981)
            ·
              refine ⟨12936113818018806621206243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34496303514716817656549981 12936113818018806621206243)
              ·
                refine ⟨19404170727028209931809365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12936113818018806621206243 19404170727028209931809365)
                ·
                  refine ⟨227392625707361835138391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19404170727028209931809365 227392625707361835138391)
                  ·
                    rfl

theorem cell23_3985610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_3985610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985610 prefixEnd_3985610 := by exact prefixLift 3985610
  have htrace : WordTrace (prefixWord ++ tailWord_3985610) baseStart_3985610 baseEnd_3985610 := by
    simpa [prefixWord, tailWord_3985610, baseEnd_3985610] using wordTrace_append hprefix tailTrace_3985610
  have hstable : (prefixWord ++ tailWord_3985610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985610).length < 2 ^ (prefixWord ++ tailWord_3985610).sum := by decide
  have hdescent : baseEnd_3985610 < baseStart_3985610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985614 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3985614 : Nat := 118140960795 + 3985614 * 2 ^ 59
def prefixEnd_3985614 : Nat := 4983230072969 + 3 ^ 40 * 3985614 * 2
def baseEnd_3985614 : Nat := 682178561762958166865167

theorem tailTrace_3985614 : CollatzResearch.WordTrace tailWord_3985614 prefixEnd_3985614 682178561762958166865167 := by
  unfold tailWord_3985614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18170910622851080190489487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96911523321872427682610597 18170910622851080190489487)
  ·
    refine ⟨27256365934276620285734231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18170910622851080190489487 27256365934276620285734231)
    ·
      refine ⟨40884548901414930428601347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27256365934276620285734231 40884548901414930428601347)
      ·
        refine ⟨61326823352122395642902021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40884548901414930428601347 61326823352122395642902021)
        ·
          refine ⟨11498779378522949183044129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61326823352122395642902021 11498779378522949183044129)
          ·
            refine ⟨8624084533892211887283097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11498779378522949183044129 8624084533892211887283097)
            ·
              refine ⟨6468063400419158915462323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624084533892211887283097 6468063400419158915462323)
              ·
                refine ⟨9702095100628738373193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468063400419158915462323 9702095100628738373193485)
                ·
                  refine ⟨3638285662735776889947557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9702095100628738373193485 3638285662735776889947557)
                  ·
                    refine ⟨682178561762958166865167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638285662735776889947557 682178561762958166865167)
                    ·
                      rfl

theorem cell23_3985614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3985614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985614 prefixEnd_3985614 := by exact prefixLift 3985614
  have htrace : WordTrace (prefixWord ++ tailWord_3985614) baseStart_3985614 baseEnd_3985614 := by
    simpa [prefixWord, tailWord_3985614, baseEnd_3985614] using wordTrace_append hprefix tailTrace_3985614
  have hstable : (prefixWord ++ tailWord_3985614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985614).length < 2 ^ (prefixWord ++ tailWord_3985614).sum := by decide
  have hdescent : baseEnd_3985614 < baseStart_3985614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985654 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3985654 : Nat := 118140960795 + 3985654 * 2 ^ 59
def prefixEnd_3985654 : Nat := 4983230072969 + 3 ^ 40 * 3985654 * 2
def baseEnd_3985654 : Nat := 2046556224515054344095317

theorem tailTrace_3985654 : CollatzResearch.WordTrace tailWord_3985654 prefixEnd_3985654 2046556224515054344095317 := by
  unfold tailWord_3985654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085546493916483022210751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96912495935109152236914677 9085546493916483022210751)
  ·
    refine ⟨13628319740874724533316127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9085546493916483022210751 13628319740874724533316127)
    ·
      refine ⟨20442479611312086799974191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13628319740874724533316127 20442479611312086799974191)
      ·
        refine ⟨30663719416968130199961287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20442479611312086799974191 30663719416968130199961287)
        ·
          refine ⟨45995579125452195299941931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30663719416968130199961287 45995579125452195299941931)
          ·
            refine ⟨68993368688178292949912897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45995579125452195299941931 68993368688178292949912897)
            ·
              refine ⟨51745026516133719712434673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68993368688178292949912897 51745026516133719712434673)
              ·
                refine ⟨38808769887100289784326005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51745026516133719712434673 38808769887100289784326005)
                ·
                  refine ⟨3638322176915652167280563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38808769887100289784326005 3638322176915652167280563)
                  ·
                    refine ⟨5457483265373478250920845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638322176915652167280563 5457483265373478250920845)
                    ·
                      refine ⟨2046556224515054344095317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457483265373478250920845 2046556224515054344095317)
                      ·
                        rfl

theorem cell23_3985654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3985654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985654 prefixEnd_3985654 := by exact prefixLift 3985654
  have htrace : WordTrace (prefixWord ++ tailWord_3985654) baseStart_3985654 baseEnd_3985654 := by
    simpa [prefixWord, tailWord_3985654, baseEnd_3985654] using wordTrace_append hprefix tailTrace_3985654
  have hstable : (prefixWord ++ tailWord_3985654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985654).length < 2 ^ (prefixWord ++ tailWord_3985654).sum := by decide
  have hdescent : baseEnd_3985654 < baseStart_3985654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985704 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3985704 : Nat := 118140960795 + 3985704 * 2 ^ 59
def prefixEnd_3985704 : Nat := 4983230072969 + 3 ^ 40 * 3985704 * 2
def baseEnd_3985704 : Nat := 682193966182593049490029

theorem tailTrace_3985704 : CollatzResearch.WordTrace tailWord_3985704 prefixEnd_3985704 682193966182593049490029 := by
  unfold tailWord_3985704
  simp only [CollatzResearch.WordTrace]
  refine ⟨72685283776241293447346083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96913711701655057929794777 72685283776241293447346083)
  ·
    refine ⟨109027925664361940171019125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72685283776241293447346083 109027925664361940171019125)
    ·
      refine ⟨10221368031033931891033043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109027925664361940171019125 10221368031033931891033043)
      ·
        refine ⟨15332052046550897836549565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10221368031033931891033043 15332052046550897836549565)
        ·
          refine ⟨5749519517456586688706087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15332052046550897836549565 5749519517456586688706087)
          ·
            refine ⟨8624279276184880033059131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749519517456586688706087 8624279276184880033059131)
            ·
              refine ⟨12936418914277320049588697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624279276184880033059131 12936418914277320049588697)
              ·
                refine ⟨9702314185707990037191523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12936418914277320049588697 9702314185707990037191523)
                ·
                  refine ⟨14553471278561985055787285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702314185707990037191523 14553471278561985055787285)
                  ·
                    refine ⟨682193966182593049490029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14553471278561985055787285 682193966182593049490029)
                    ·
                      rfl

theorem cell23_3985704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3985704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985704 prefixEnd_3985704 := by exact prefixLift 3985704
  have htrace : WordTrace (prefixWord ++ tailWord_3985704) baseStart_3985704 baseEnd_3985704 := by
    simpa [prefixWord, tailWord_3985704, baseEnd_3985704] using wordTrace_append hprefix tailTrace_3985704
  have hstable : (prefixWord ++ tailWord_3985704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985704).length < 2 ^ (prefixWord ++ tailWord_3985704).sum := by decide
  have hdescent : baseEnd_3985704 < baseStart_3985704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985721 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_3985721 : Nat := 118140960795 + 3985721 * 2 ^ 59
def prefixEnd_3985721 : Nat := 4983230072969 + 3 ^ 40 * 3985721 * 2
def baseEnd_3985721 : Nat := 682196875906301860652503

theorem tailTrace_3985721 : CollatzResearch.WordTrace tailWord_3985721 prefixEnd_3985721 682196875906301860652503 := by
  unfold tailWord_3985721
  simp only [CollatzResearch.WordTrace]
  refine ⟨145371187593420998798061017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96914125062280665865374011 145371187593420998798061017)
  ·
    refine ⟨109028390695065749098545763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145371187593420998798061017 109028390695065749098545763)
    ·
      refine ⟨163542586042598623647818645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109028390695065749098545763 163542586042598623647818645)
      ·
        refine ⟨7666058720746810483491499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163542586042598623647818645 7666058720746810483491499)
        ·
          refine ⟨11499088081120215725237249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666058720746810483491499 11499088081120215725237249)
          ·
            refine ⟨8624316060840161793927937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11499088081120215725237249 8624316060840161793927937)
            ·
              refine ⟨6468237045630121345445953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624316060840161793927937 6468237045630121345445953)
              ·
                refine ⟨4851177784222591009084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468237045630121345445953 4851177784222591009084465)
                ·
                  refine ⟨3638383338166943256813349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851177784222591009084465 3638383338166943256813349)
                  ·
                    refine ⟨682196875906301860652503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638383338166943256813349 682196875906301860652503)
                    ·
                      rfl

theorem cell23_3985721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_3985721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985721 prefixEnd_3985721 := by exact prefixLift 3985721
  have htrace : WordTrace (prefixWord ++ tailWord_3985721) baseStart_3985721 baseEnd_3985721 := by
    simpa [prefixWord, tailWord_3985721, baseEnd_3985721] using wordTrace_append hprefix tailTrace_3985721
  have hstable : (prefixWord ++ tailWord_3985721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985721).length < 2 ^ (prefixWord ++ tailWord_3985721).sum := by decide
  have hdescent : baseEnd_3985721 < baseStart_3985721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985727 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_3985727 : Nat := 118140960795 + 3985727 * 2 ^ 59
def prefixEnd_3985727 : Nat := 4983230072969 + 3 ^ 40 * 3985727 * 2
def baseEnd_3985727 : Nat := 2046593708602832558482481

theorem tailTrace_3985727 : CollatzResearch.WordTrace tailWord_3985727 prefixEnd_3985727 2046593708602832558482481 := by
  unfold tailWord_3985727
  simp only [CollatzResearch.WordTrace]
  refine ⟨145371406431399261822779435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96914270954266174548519623 145371406431399261822779435)
  ·
    refine ⟨218057109647098892734169153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145371406431399261822779435 218057109647098892734169153)
    ·
      refine ⟨163542832235324169550626865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218057109647098892734169153 163542832235324169550626865)
      ·
        refine ⟨122657124176493127162970149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163542832235324169550626865 122657124176493127162970149)
        ·
          refine ⟨22998210783092461343056903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122657124176493127162970149 22998210783092461343056903)
          ·
            refine ⟨34497316174638692014585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22998210783092461343056903 34497316174638692014585355)
            ·
              refine ⟨51745974261958038021878033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34497316174638692014585355 51745974261958038021878033)
              ·
                refine ⟨38809480696468528516408525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51745974261958038021878033 38809480696468528516408525)
                ·
                  refine ⟨14553555261175698193653197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38809480696468528516408525 14553555261175698193653197)
                  ·
                    refine ⟨5457583222940886822619949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553555261175698193653197 5457583222940886822619949)
                    ·
                      refine ⟨2046593708602832558482481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457583222940886822619949 2046593708602832558482481)
                      ·
                        rfl

theorem cell23_3985727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_3985727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985727 prefixEnd_3985727 := by exact prefixLift 3985727
  have htrace : WordTrace (prefixWord ++ tailWord_3985727) baseStart_3985727 baseEnd_3985727 := by
    simpa [prefixWord, tailWord_3985727, baseEnd_3985727] using wordTrace_append hprefix tailTrace_3985727
  have hstable : (prefixWord ++ tailWord_3985727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985727).length < 2 ^ (prefixWord ++ tailWord_3985727).sum := by decide
  have hdescent : baseEnd_3985727 < baseStart_3985727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985744 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_3985744 : Nat := 118140960795 + 3985744 * 2 ^ 59
def prefixEnd_3985744 : Nat := 4983230072969 + 3 ^ 40 * 3985744 * 2
def baseEnd_3985744 : Nat := 2046602437773958991969903

theorem tailTrace_3985744 : CollatzResearch.WordTrace tailWord_3985744 prefixEnd_3985744 2046602437773958991969903 := by
  unfold tailWord_3985744
  simp only [CollatzResearch.WordTrace]
  refine ⟨72686013236168836863074143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96914684314891782484098857 72686013236168836863074143)
  ·
    refine ⟨109029019854253255294611215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72686013236168836863074143 109029019854253255294611215)
    ·
      refine ⟨163543529781379882941916823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109029019854253255294611215 163543529781379882941916823)
      ·
        refine ⟨245315294672069824412875235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163543529781379882941916823 245315294672069824412875235)
        ·
          refine ⟨367972942008104736619312853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245315294672069824412875235 367972942008104736619312853)
          ·
            refine ⟨8624365828314954764515145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367972942008104736619312853 8624365828314954764515145)
            ·
              refine ⟨6468274371236216073386359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624365828314954764515145 6468274371236216073386359)
              ·
                refine ⟨9702411556854324110079539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468274371236216073386359 9702411556854324110079539)
                ·
                  refine ⟨14553617335281486165119309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702411556854324110079539 14553617335281486165119309)
                  ·
                    refine ⟨5457606500730557311919741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14553617335281486165119309 5457606500730557311919741)
                    ·
                      refine ⟨2046602437773958991969903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457606500730557311919741 2046602437773958991969903)
                      ·
                        rfl

theorem cell23_3985744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_3985744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985744 prefixEnd_3985744 := by exact prefixLift 3985744
  have htrace : WordTrace (prefixWord ++ tailWord_3985744) baseStart_3985744 baseEnd_3985744 := by
    simpa [prefixWord, tailWord_3985744, baseEnd_3985744] using wordTrace_append hprefix tailTrace_3985744
  have hstable : (prefixWord ++ tailWord_3985744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985744).length < 2 ^ (prefixWord ++ tailWord_3985744).sum := by decide
  have hdescent : baseEnd_3985744 < baseStart_3985744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985778 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3985778 : Nat := 118140960795 + 3985778 * 2 ^ 59
def prefixEnd_3985778 : Nat := 4983230072969 + 3 ^ 40 * 3985778 * 2
def baseEnd_3985778 : Nat := 2046619896116211858944747

theorem tailTrace_3985778 : CollatzResearch.WordTrace tailWord_3985778 prefixEnd_3985778 2046619896116211858944747 := by
  unfold tailWord_3985778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36343316638553624383221497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96915511036142998355257325 36343316638553624383221497)
  ·
    refine ⟨27257487478915218287416123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36343316638553624383221497 27257487478915218287416123)
    ·
      refine ⟨40886231218372827431124185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27257487478915218287416123 40886231218372827431124185)
      ·
        refine ⟨30664673413779620573343139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40886231218372827431124185 30664673413779620573343139)
        ·
          refine ⟨45997010120669430860014709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30664673413779620573343139 45997010120669430860014709)
          ·
            refine ⟨4312219698812759143126379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45997010120669430860014709 4312219698812759143126379)
            ·
              refine ⟨6468329548219138714689569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312219698812759143126379 6468329548219138714689569)
              ·
                refine ⟨4851247161164354036017177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468329548219138714689569 4851247161164354036017177)
                ·
                  refine ⟨3638435370873265527012883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851247161164354036017177 3638435370873265527012883)
                  ·
                    refine ⟨5457653056309898290519325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638435370873265527012883 5457653056309898290519325)
                    ·
                      refine ⟨2046619896116211858944747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457653056309898290519325 2046619896116211858944747)
                      ·
                        rfl

theorem cell23_3985778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3985778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985778 prefixEnd_3985778 := by exact prefixLift 3985778
  have htrace : WordTrace (prefixWord ++ tailWord_3985778) baseStart_3985778 baseEnd_3985778 := by
    simpa [prefixWord, tailWord_3985778, baseEnd_3985778] using wordTrace_append hprefix tailTrace_3985778
  have hstable : (prefixWord ++ tailWord_3985778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985778).length < 2 ^ (prefixWord ++ tailWord_3985778).sum := by decide
  have hdescent : baseEnd_3985778 < baseStart_3985778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985801 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 1, 4, 2]
def baseStart_3985801 : Nat := 118140960795 + 3985801 * 2 ^ 59
def prefixEnd_3985801 : Nat := 4983230072969 + 3 ^ 40 * 3985801 * 2
def baseEnd_3985801 : Nat := 2046631706171265268957141

theorem tailTrace_3985801 : CollatzResearch.WordTrace tailWord_3985801 prefixEnd_3985801 2046631706171265268957141 := by
  unfold tailWord_3985801
  simp only [CollatzResearch.WordTrace]
  refine ⟨145374105433131172460973257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96916070288754114973982171 145374105433131172460973257)
  ·
    refine ⟨109030579074848379345729943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145374105433131172460973257 109030579074848379345729943)
    ·
      refine ⟨163545868612272569018594915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109030579074848379345729943 163545868612272569018594915)
      ·
        refine ⟨245318802918408853527892373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163545868612272569018594915 245318802918408853527892373)
        ·
          refine ⟨11499318886800415009119955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245318802918408853527892373 11499318886800415009119955)
          ·
            refine ⟨17248978330200622513679933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11499318886800415009119955 17248978330200622513679933)
            ·
              refine ⟨6468366873825233442629975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17248978330200622513679933 6468366873825233442629975)
              ·
                refine ⟨9702550310737850163944963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468366873825233442629975 9702550310737850163944963)
                ·
                  refine ⟨14553825466106775245917445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9702550310737850163944963 14553825466106775245917445)
                  ·
                    refine ⟨2728842274895020358609521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14553825466106775245917445 2728842274895020358609521)
                    ·
                      refine ⟨2046631706171265268957141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728842274895020358609521 2046631706171265268957141)
                      ·
                        rfl

theorem cell23_3985801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4, 2].length) (baseStart_3985801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985801 prefixEnd_3985801 := by exact prefixLift 3985801
  have htrace : WordTrace (prefixWord ++ tailWord_3985801) baseStart_3985801 baseEnd_3985801 := by
    simpa [prefixWord, tailWord_3985801, baseEnd_3985801] using wordTrace_append hprefix tailTrace_3985801
  have hstable : (prefixWord ++ tailWord_3985801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985801).length < 2 ^ (prefixWord ++ tailWord_3985801).sum := by decide
  have hdescent : baseEnd_3985801 < baseStart_3985801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985847 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3985847 : Nat := 118140960795 + 3985847 * 2 ^ 59
def prefixEnd_3985847 : Nat := 4983230072969 + 3 ^ 40 * 3985847 * 2
def baseEnd_3985847 : Nat := 2046655326281372088981929

theorem tailTrace_3985847 : CollatzResearch.WordTrace tailWord_3985847 prefixEnd_3985847 2046655326281372088981929 := by
  unfold tailWord_3985847
  simp only [CollatzResearch.WordTrace]
  refine ⟨145375783190964522317147795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96917188793976348211431863 145375783190964522317147795)
  ·
    refine ⟨218063674786446783475721693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145375783190964522317147795 218063674786446783475721693)
    ·
      refine ⟨81773878044917543803395635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218063674786446783475721693 81773878044917543803395635)
      ·
        refine ⟨122660817067376315705093453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81773878044917543803395635 122660817067376315705093453)
        ·
          refine ⟨45997806400266118389410045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122660817067376315705093453 45997806400266118389410045)
          ·
            refine ⟨17249177400099794396028767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45997806400266118389410045 17249177400099794396028767)
            ·
              refine ⟨25873766100149691594043151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17249177400099794396028767 25873766100149691594043151)
              ·
                refine ⟨38810649150224537391064727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25873766100149691594043151 38810649150224537391064727)
                ·
                  refine ⟨58215973725336806086597091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38810649150224537391064727 58215973725336806086597091)
                  ·
                    refine ⟨87323960588005209129895637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58215973725336806086597091 87323960588005209129895637)
                    ·
                      refine ⟨2046655326281372088981929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87323960588005209129895637 2046655326281372088981929)
                      ·
                        rfl

theorem cell23_3985847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3985847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985847 prefixEnd_3985847 := by exact prefixLift 3985847
  have htrace : WordTrace (prefixWord ++ tailWord_3985847) baseStart_3985847 baseEnd_3985847 := by
    simpa [prefixWord, tailWord_3985847, baseEnd_3985847] using wordTrace_append hprefix tailTrace_3985847
  have hstable : (prefixWord ++ tailWord_3985847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985847).length < 2 ^ (prefixWord ++ tailWord_3985847).sum := by decide
  have hdescent : baseEnd_3985847 < baseStart_3985847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985852 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3985852 : Nat := 118140960795 + 3985852 * 2 ^ 59
def prefixEnd_3985852 : Nat := 4983230072969 + 3 ^ 40 * 3985852 * 2
def baseEnd_3985852 : Nat := 2046657893684644569419407

theorem tailTrace_3985852 : CollatzResearch.WordTrace tailWord_3985852 prefixEnd_3985852 2046657893684644569419407 := by
  unfold tailWord_3985852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72687982777973204085539905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96917310370630938780719873 72687982777973204085539905)
  ·
    refine ⟨54515987083479903064154929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72687982777973204085539905 54515987083479903064154929)
    ·
      refine ⟨40886990312609927298116197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54515987083479903064154929 40886990312609927298116197)
      ·
        refine ⟨7666310683614361368396787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40886990312609927298116197 7666310683614361368396787)
        ·
          refine ⟨11499466025421542052595181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666310683614361368396787 11499466025421542052595181)
          ·
            refine ⟨4312299759533078269723193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11499466025421542052595181 4312299759533078269723193)
            ·
              refine ⟨3234224819649808702292395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312299759533078269723193 3234224819649808702292395)
              ·
                refine ⟨4851337229474713053438593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234224819649808702292395 4851337229474713053438593)
                ·
                  refine ⟨3638502922106034790078945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851337229474713053438593 3638502922106034790078945)
                  ·
                    refine ⟨2728877191579526092559209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638502922106034790078945 2728877191579526092559209)
                    ·
                      refine ⟨2046657893684644569419407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728877191579526092559209 2046657893684644569419407)
                      ·
                        rfl

theorem cell23_3985852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3985852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985852 prefixEnd_3985852 := by exact prefixLift 3985852
  have htrace : WordTrace (prefixWord ++ tailWord_3985852) baseStart_3985852 baseEnd_3985852 := by
    simpa [prefixWord, tailWord_3985852, baseEnd_3985852] using wordTrace_append hprefix tailTrace_3985852
  have hstable : (prefixWord ++ tailWord_3985852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985852).length < 2 ^ (prefixWord ++ tailWord_3985852).sum := by decide
  have hdescent : baseEnd_3985852 < baseStart_3985852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985941 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3985941 : Nat := 118140960795 + 3985941 * 2 ^ 59
def prefixEnd_3985941 : Nat := 4983230072969 + 3 ^ 40 * 3985941 * 2
def baseEnd_3985941 : Nat := 2046703593462894721206497

theorem tailTrace_3985941 : CollatzResearch.WordTrace tailWord_3985941 prefixEnd_3985941 2046703593462894721206497 := by
  unfold tailWord_3985941
  simp only [CollatzResearch.WordTrace]
  refine ⟨145379211652623976371069677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96919474435082650914046451 145379211652623976371069677)
  ·
    refine ⟨54517204369733991139151129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145379211652623976371069677 54517204369733991139151129)
    ·
      refine ⟨40887903277300493354363347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54517204369733991139151129 40887903277300493354363347)
      ·
        refine ⟨61331854915950740031545021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40887903277300493354363347 61331854915950740031545021)
        ·
          refine ⟨22999445593481527511829383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61331854915950740031545021 22999445593481527511829383)
          ·
            refine ⟨34499168390222291267744075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22999445593481527511829383 34499168390222291267744075)
            ·
              refine ⟨51748752585333436901616113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34499168390222291267744075 51748752585333436901616113)
              ·
                refine ⟨38811564439000077676212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51748752585333436901616113 38811564439000077676212085)
                ·
                  refine ⟨3638584166156257282144883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38811564439000077676212085 3638584166156257282144883)
                  ·
                    refine ⟨5457876249234385923217325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638584166156257282144883 5457876249234385923217325)
                    ·
                      refine ⟨2046703593462894721206497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5457876249234385923217325 2046703593462894721206497)
                      ·
                        rfl

theorem cell23_3985941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3985941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985941 prefixEnd_3985941 := by exact prefixLift 3985941
  have htrace : WordTrace (prefixWord ++ tailWord_3985941) baseStart_3985941 baseEnd_3985941 := by
    simpa [prefixWord, tailWord_3985941, baseEnd_3985941] using wordTrace_append hprefix tailTrace_3985941
  have hstable : (prefixWord ++ tailWord_3985941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985941).length < 2 ^ (prefixWord ++ tailWord_3985941).sum := by decide
  have hdescent : baseEnd_3985941 < baseStart_3985941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985951 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 4, 3, 2]
def baseStart_3985951 : Nat := 118140960795 + 3985951 * 2 ^ 59
def prefixEnd_3985951 : Nat := 4983230072969 + 3 ^ 40 * 3985951 * 2
def baseEnd_3985951 : Nat := 2046708728269439682081451

theorem tailTrace_3985951 : CollatzResearch.WordTrace tailWord_3985951 prefixEnd_3985951 2046708728269439682081451 := by
  unfold tailWord_3985951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145379576382587748078933707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96919717588391832052622471 145379576382587748078933707)
  ·
    refine ⟨218069364573881622118400561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145379576382587748078933707 218069364573881622118400561)
    ·
      refine ⟨163552023430411216588800421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218069364573881622118400561 163552023430411216588800421)
      ·
        refine ⟨30666004393202103110400079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163552023430411216588800421 30666004393202103110400079)
        ·
          refine ⟨45999006589803154665600119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30666004393202103110400079 45999006589803154665600119)
          ·
            refine ⟨68998509884704731998400179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45999006589803154665600119 68998509884704731998400179)
            ·
              refine ⟨103497764827057097997600269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68998509884704731998400179 103497764827057097997600269)
              ·
                refine ⟨38811661810146411749100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103497764827057097997600269 38811661810146411749100101)
                ·
                  refine ⟨7277186589402452202956269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38811661810146411749100101 7277186589402452202956269)
                  ·
                    refine ⟨2728944971025919576108601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7277186589402452202956269 2728944971025919576108601)
                    ·
                      refine ⟨2046708728269439682081451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728944971025919576108601 2046708728269439682081451)
                      ·
                        rfl

theorem cell23_3985951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_3985951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985951 prefixEnd_3985951 := by exact prefixLift 3985951
  have htrace : WordTrace (prefixWord ++ tailWord_3985951) baseStart_3985951 baseEnd_3985951 := by
    simpa [prefixWord, tailWord_3985951, baseEnd_3985951] using wordTrace_append hprefix tailTrace_3985951
  have hstable : (prefixWord ++ tailWord_3985951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985951).length < 2 ^ (prefixWord ++ tailWord_3985951).sum := by decide
  have hdescent : baseEnd_3985951 < baseStart_3985951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985964 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_3985964 : Nat := 118140960795 + 3985964 * 2 ^ 59
def prefixEnd_3985964 : Nat := 4983230072969 + 3 ^ 40 * 3985964 * 2
def baseEnd_3985964 : Nat := 2046715403517948131218891

theorem tailTrace_3985964 : CollatzResearch.WordTrace tailWord_3985964 prefixEnd_3985964 2046715403517948131218891 := by
  unfold tailWord_3985964
  simp only [CollatzResearch.WordTrace]
  refine ⟨72690025265770325649578473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96920033687693767532771297 72690025265770325649578473)
  ·
    refine ⟨54517518949327744237183855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72690025265770325649578473 54517518949327744237183855)
    ·
      refine ⟨81776278423991616355775783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54517518949327744237183855 81776278423991616355775783)
      ·
        refine ⟨122664417635987424533663675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81776278423991616355775783 122664417635987424533663675)
        ·
          refine ⟨183996626453981136800495513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122664417635987424533663675 183996626453981136800495513)
          ·
            refine ⟨137997469840485852600371635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183996626453981136800495513 137997469840485852600371635)
            ·
              refine ⟨206996204760728778900557453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137997469840485852600371635 206996204760728778900557453)
              ·
                refine ⟨77623576785273292087709045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206996204760728778900557453 77623576785273292087709045)
                ·
                  refine ⟨7277210323619371133222723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77623576785273292087709045 7277210323619371133222723)
                  ·
                    refine ⟨10915815485429056699834085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7277210323619371133222723 10915815485429056699834085)
                    ·
                      refine ⟨2046715403517948131218891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10915815485429056699834085 2046715403517948131218891)
                      ·
                        rfl

theorem cell23_3985964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_3985964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985964 prefixEnd_3985964 := by exact prefixLift 3985964
  have htrace : WordTrace (prefixWord ++ tailWord_3985964) baseStart_3985964 baseEnd_3985964 := by
    simpa [prefixWord, tailWord_3985964, baseEnd_3985964] using wordTrace_append hprefix tailTrace_3985964
  have hstable : (prefixWord ++ tailWord_3985964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985964).length < 2 ^ (prefixWord ++ tailWord_3985964).sum := by decide
  have hdescent : baseEnd_3985964 < baseStart_3985964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985991 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 4, 4]
def baseStart_3985991 : Nat := 118140960795 + 3985991 * 2 ^ 59
def prefixEnd_3985991 : Nat := 4983230072969 + 3 ^ 40 * 3985991 * 2
def baseEnd_3985991 : Nat := 682243089165206508527089

theorem tailTrace_3985991 : CollatzResearch.WordTrace tailWord_3985991 prefixEnd_3985991 682243089165206508527089 := by
  unfold tailWord_3985991
  simp only [CollatzResearch.WordTrace]
  refine ⟨145381035302442834910389827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96920690201628556606926551 145381035302442834910389827)
  ·
    refine ⟨218071552953664252365584741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145381035302442834910389827 218071552953664252365584741)
    ·
      refine ⟨40888416178812047318547139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218071552953664252365584741 40888416178812047318547139)
      ·
        refine ⟨61332624268218070977820709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888416178812047318547139 61332624268218070977820709)
        ·
          refine ⟨11499867050290888308341383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61332624268218070977820709 11499867050290888308341383)
          ·
            refine ⟨17249800575436332462512075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11499867050290888308341383 17249800575436332462512075)
            ·
              refine ⟨25874700863154498693768113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17249800575436332462512075 25874700863154498693768113)
              ·
                refine ⟨19406025647365874020326085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25874700863154498693768113 19406025647365874020326085)
                ·
                  refine ⟨3638629808881101378811141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19406025647365874020326085 3638629808881101378811141)
                  ·
                    refine ⟨682243089165206508527089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638629808881101378811141 682243089165206508527089)
                    ·
                      rfl

theorem cell23_3985991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_3985991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985991 prefixEnd_3985991 := by exact prefixLift 3985991
  have htrace : WordTrace (prefixWord ++ tailWord_3985991) baseStart_3985991 baseEnd_3985991 := by
    simpa [prefixWord, tailWord_3985991, baseEnd_3985991] using wordTrace_append hprefix tailTrace_3985991
  have hstable : (prefixWord ++ tailWord_3985991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985991).length < 2 ^ (prefixWord ++ tailWord_3985991).sum := by decide
  have hdescent : baseEnd_3985991 < baseStart_3985991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3985998 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_3985998 : Nat := 118140960795 + 3985998 * 2 ^ 59
def prefixEnd_3985998 : Nat := 4983230072969 + 3 ^ 40 * 3985998 * 2
def baseEnd_3985998 : Nat := 2046732861860200998193735

theorem tailTrace_3985998 : CollatzResearch.WordTrace tailWord_3985998 prefixEnd_3985998 2046732861860200998193735 := by
  unfold tailWord_3985998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172661326677184388236831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96920860408944983403929765 18172661326677184388236831)
  ·
    refine ⟨27258991990015776582355247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18172661326677184388236831 27258991990015776582355247)
    ·
      refine ⟨40888487985023664873532871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27258991990015776582355247 40888487985023664873532871)
      ·
        refine ⟨61332731977535497310299307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888487985023664873532871 61332731977535497310299307)
        ·
          refine ⟨91999097966303245965448961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61332731977535497310299307 91999097966303245965448961)
          ·
            refine ⟨68999323474727434474086721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91999097966303245965448961 68999323474727434474086721)
            ·
              refine ⟨51749492606045575855565041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68999323474727434474086721 51749492606045575855565041)
              ·
                refine ⟨38812119454534181891673781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51749492606045575855565041 38812119454534181891673781)
                ·
                  refine ⟨3638636198862579552344417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38812119454534181891673781 3638636198862579552344417)
                  ·
                    refine ⟨2728977149146934664258313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638636198862579552344417 2728977149146934664258313)
                    ·
                      refine ⟨2046732861860200998193735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728977149146934664258313 2046732861860200998193735)
                      ·
                        rfl

theorem cell23_3985998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_3985998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3985998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3985998 prefixEnd_3985998 := by exact prefixLift 3985998
  have htrace : WordTrace (prefixWord ++ tailWord_3985998) baseStart_3985998 baseEnd_3985998 := by
    simpa [prefixWord, tailWord_3985998, baseEnd_3985998] using wordTrace_append hprefix tailTrace_3985998
  have hstable : (prefixWord ++ tailWord_3985998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3985998).length < 2 ^ (prefixWord ++ tailWord_3985998).sum := by decide
  have hdescent : baseEnd_3985998 < baseStart_3985998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3985998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986001 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_3986001 : Nat := 118140960795 + 3986001 * 2 ^ 59
def prefixEnd_3986001 : Nat := 4983230072969 + 3 ^ 40 * 3986001 * 2
def baseEnd_3986001 : Nat := 2046734402302164486456221

theorem tailTrace_3986001 : CollatzResearch.WordTrace tailWord_3986001 prefixEnd_3986001 2046734402302164486456221 := by
  unfold tailWord_3986001
  simp only [CollatzResearch.WordTrace]
  refine ⟨145381400032406606618253857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96920933354937737745502571 145381400032406606618253857)
  ·
    refine ⟨109036050024304954963690393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145381400032406606618253857 109036050024304954963690393)
    ·
      refine ⟨81777037518228716222767795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109036050024304954963690393 81777037518228716222767795)
      ·
        refine ⟨122665556277343074334151693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81777037518228716222767795 122665556277343074334151693)
        ·
          refine ⟨45999583604003652875306885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122665556277343074334151693 45999583604003652875306885)
          ·
            refine ⟨8624921925750684914120041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45999583604003652875306885 8624921925750684914120041)
            ·
              refine ⟨6468691444313013685590031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624921925750684914120041 6468691444313013685590031)
              ·
                refine ⟨9703037166469520528385047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6468691444313013685590031 9703037166469520528385047)
                ·
                  refine ⟨14554555749704280792577571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703037166469520528385047 14554555749704280792577571)
                  ·
                    refine ⟨21831833624556421188866357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14554555749704280792577571 21831833624556421188866357)
                    ·
                      refine ⟨2046734402302164486456221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21831833624556421188866357 2046734402302164486456221)
                      ·
                        rfl

theorem cell23_3986001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_3986001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986001 prefixEnd_3986001 := by exact prefixLift 3986001
  have htrace : WordTrace (prefixWord ++ tailWord_3986001) baseStart_3986001 baseEnd_3986001 := by
    simpa [prefixWord, tailWord_3986001, baseEnd_3986001] using wordTrace_append hprefix tailTrace_3986001
  have hstable : (prefixWord ++ tailWord_3986001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986001).length < 2 ^ (prefixWord ++ tailWord_3986001).sum := by decide
  have hdescent : baseEnd_3986001 < baseStart_3986001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986004 : List Nat := [2, 4, 1, 1, 1, 3, 11]
def baseStart_3986004 : Nat := 118140960795 + 3986004 * 2 ^ 59
def prefixEnd_3986004 : Nat := 4983230072969 + 3 ^ 40 * 3986004 * 2
def baseEnd_3986004 : Nat := 25268344972149728082947

theorem tailTrace_3986004 : CollatzResearch.WordTrace tailWord_3986004 prefixEnd_3986004 25268344972149728082947 := by
  unfold tailWord_3986004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72690754725697869065306533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96921006300930492087075377 72690754725697869065306533)
  ·
    refine ⟨13629516511068350449744975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72690754725697869065306533 13629516511068350449744975)
    ·
      refine ⟨20444274766602525674617463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13629516511068350449744975 20444274766602525674617463)
      ·
        refine ⟨30666412149903788511926195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20444274766602525674617463 30666412149903788511926195)
        ·
          refine ⟨45999618224855682767889293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30666412149903788511926195 45999618224855682767889293)
          ·
            refine ⟨17249856834320881037958485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45999618224855682767889293 17249856834320881037958485)
            ·
              refine ⟨25268344972149728082947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17249856834320881037958485 25268344972149728082947)
              ·
                rfl

theorem cell23_3986004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 11].length) (baseStart_3986004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986004 prefixEnd_3986004 := by exact prefixLift 3986004
  have htrace : WordTrace (prefixWord ++ tailWord_3986004) baseStart_3986004 baseEnd_3986004 := by
    simpa [prefixWord, tailWord_3986004, baseEnd_3986004] using wordTrace_append hprefix tailTrace_3986004
  have hstable : (prefixWord ++ tailWord_3986004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986004).length < 2 ^ (prefixWord ++ tailWord_3986004).sum := by decide
  have hdescent : baseEnd_3986004 < baseStart_3986004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986015 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 1, 2, 2]
def baseStart_3986015 : Nat := 118140960795 + 3986015 * 2 ^ 59
def prefixEnd_3986015 : Nat := 4983230072969 + 3 ^ 40 * 3986015 * 2
def baseEnd_3986015 : Nat := 2046741591031327431681157

theorem tailTrace_3986015 : CollatzResearch.WordTrace tailWord_3986015 prefixEnd_3986015 2046741591031327431681157 := by
  unfold tailWord_3986015
  simp only [CollatzResearch.WordTrace]
  refine ⟨145381910654355887009263499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96921273769570591339508999 145381910654355887009263499)
  ·
    refine ⟨218072865981533830513895249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145381910654355887009263499 218072865981533830513895249)
    ·
      refine ⟨163554649486150372885421437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218072865981533830513895249 163554649486150372885421437)
      ·
        refine ⟨61332993557306389832033039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163554649486150372885421437 61332993557306389832033039)
        ·
          refine ⟨91999490335959584748049559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61332993557306389832033039 91999490335959584748049559)
          ·
            refine ⟨137999235503939377122074339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91999490335959584748049559 137999235503939377122074339)
            ·
              refine ⟨206998853255909065683111509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137999235503939377122074339 206998853255909065683111509)
              ·
                refine ⟨2425767811592684363473963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 206998853255909065683111509 2425767811592684363473963)
                ·
                  refine ⟨3638651717389026545210945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425767811592684363473963 3638651717389026545210945)
                  ·
                    refine ⟨2728988788041769908908209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638651717389026545210945 2728988788041769908908209)
                    ·
                      refine ⟨2046741591031327431681157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2728988788041769908908209 2046741591031327431681157)
                      ·
                        rfl

theorem cell23_3986015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_3986015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986015 prefixEnd_3986015 := by exact prefixLift 3986015
  have htrace : WordTrace (prefixWord ++ tailWord_3986015) baseStart_3986015 baseEnd_3986015 := by
    simpa [prefixWord, tailWord_3986015, baseEnd_3986015] using wordTrace_append hprefix tailTrace_3986015
  have hstable : (prefixWord ++ tailWord_3986015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986015).length < 2 ^ (prefixWord ++ tailWord_3986015).sum := by decide
  have hdescent : baseEnd_3986015 < baseStart_3986015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986021 : List Nat := [1, 3, 1, 3, 4, 1, 2, 8]
def baseStart_3986021 : Nat := 118140960795 + 3986021 * 2 ^ 59
def prefixEnd_3986021 : Nat := 4983230072969 + 3 ^ 40 * 3986021 * 2
def baseEnd_3986021 : Nat := 75805358219083496600227

theorem tailTrace_3986021 : CollatzResearch.WordTrace tailWord_3986021 prefixEnd_3986021 75805358219083496600227 := by
  unfold tailWord_3986021
  simp only [CollatzResearch.WordTrace]
  refine ⟨145382129492334150033981917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96921419661556100022654611 145382129492334150033981917)
  ·
    refine ⟨54518298559625306262743219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145382129492334150033981917 54518298559625306262743219)
    ·
      refine ⟨81777447839437959394114829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54518298559625306262743219 81777447839437959394114829)
      ·
        refine ⟨30666542939789234772793061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81777447839437959394114829 30666542939789234772793061)
        ·
          refine ⟨5749976801210481519898699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30666542939789234772793061 5749976801210481519898699)
          ·
            refine ⟨8624965201815722279848049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749976801210481519898699 8624965201815722279848049)
            ·
              refine ⟨6468723901361791709886037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8624965201815722279848049 6468723901361791709886037)
              ·
                refine ⟨75805358219083496600227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6468723901361791709886037 75805358219083496600227)
                ·
                  rfl

theorem cell23_3986021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 8].length) (baseStart_3986021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986021 prefixEnd_3986021 := by exact prefixLift 3986021
  have htrace : WordTrace (prefixWord ++ tailWord_3986021) baseStart_3986021 baseEnd_3986021 := by
    simpa [prefixWord, tailWord_3986021, baseEnd_3986021] using wordTrace_append hprefix tailTrace_3986021
  have hstable : (prefixWord ++ tailWord_3986021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986021).length < 2 ^ (prefixWord ++ tailWord_3986021).sum := by decide
  have hdescent : baseEnd_3986021 < baseStart_3986021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986044 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_3986044 : Nat := 118140960795 + 3986044 * 2 ^ 59
def prefixEnd_3986044 : Nat := 4983230072969 + 3 ^ 40 * 3986044 * 2
def baseEnd_3986044 : Nat := 2046756481970307818218523

theorem tailTrace_3986044 : CollatzResearch.WordTrace tailWord_3986044 prefixEnd_3986044 2046756481970307818218523 := by
  unfold tailWord_3986044
  simp only [CollatzResearch.WordTrace]
  refine ⟨72691484185625412481034593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96921978914167216641379457 72691484185625412481034593)
  ·
    refine ⟨54518613139219059360775945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72691484185625412481034593 54518613139219059360775945)
    ·
      refine ⟨40888959854414294520581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54518613139219059360775945 40888959854414294520581959)
      ·
        refine ⟨61333439781621441780872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40888959854414294520581959 61333439781621441780872939)
        ·
          refine ⟨92000159672432162671309409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61333439781621441780872939 92000159672432162671309409)
          ·
            refine ⟨69000119754324122003482057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92000159672432162671309409 69000119754324122003482057)
            ·
              refine ⟨51750089815743091502611543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69000119754324122003482057 51750089815743091502611543)
              ·
                refine ⟨77625134723614637253917315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51750089815743091502611543 77625134723614637253917315)
                ·
                  refine ⟨116437702085421955880875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77625134723614637253917315 116437702085421955880875973)
                  ·
                    refine ⟨21832069141016616727664245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116437702085421955880875973 21832069141016616727664245)
                    ·
                      refine ⟨2046756481970307818218523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21832069141016616727664245 2046756481970307818218523)
                      ·
                        rfl

theorem cell23_3986044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3986044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986044 prefixEnd_3986044 := by exact prefixLift 3986044
  have htrace : WordTrace (prefixWord ++ tailWord_3986044) baseStart_3986044 baseEnd_3986044 := by
    simpa [prefixWord, tailWord_3986044, baseEnd_3986044] using wordTrace_append hprefix tailTrace_3986044
  have hstable : (prefixWord ++ tailWord_3986044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986044).length < 2 ^ (prefixWord ++ tailWord_3986044).sum := by decide
  have hdescent : baseEnd_3986044 < baseStart_3986044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986066 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3986066 : Nat := 118140960795 + 3986066 * 2 ^ 59
def prefixEnd_3986066 : Nat := 4983230072969 + 3 ^ 40 * 3986066 * 2
def baseEnd_3986066 : Nat := 2046767778544706732143423

theorem tailTrace_3986066 : CollatzResearch.WordTrace tailWord_3986066 prefixEnd_3986066 2046767778544706732143423 := by
  unfold tailWord_3986066
  simp only [CollatzResearch.WordTrace]
  refine ⟨36345942694292780679842513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96922513851447415146246701 36345942694292780679842513)
  ·
    refine ⟨27259457020719585509881885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36345942694292780679842513 27259457020719585509881885)
    ·
      refine ⟨10222296382769844566205707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27259457020719585509881885 10222296382769844566205707)
      ·
        refine ⟨15333444574154766849308561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222296382769844566205707 15333444574154766849308561)
        ·
          refine ⟨11500083430616075136981421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15333444574154766849308561 11500083430616075136981421)
          ·
            refine ⟨4312531286481028176368033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11500083430616075136981421 4312531286481028176368033)
            ·
              refine ⟨3234398464860771132276025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312531286481028176368033 3234398464860771132276025)
              ·
                refine ⟨2425798848645578349207019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234398464860771132276025 2425798848645578349207019)
                ·
                  refine ⟨3638698272968367523810529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425798848645578349207019 3638698272968367523810529)
                  ·
                    refine ⟨2729023704726275642857897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638698272968367523810529 2729023704726275642857897)
                    ·
                      refine ⟨2046767778544706732143423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729023704726275642857897 2046767778544706732143423)
                      ·
                        rfl

theorem cell23_3986066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3986066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986066 prefixEnd_3986066 := by exact prefixLift 3986066
  have htrace : WordTrace (prefixWord ++ tailWord_3986066) baseStart_3986066 baseEnd_3986066 := by
    simpa [prefixWord, tailWord_3986066, baseEnd_3986066] using wordTrace_append hprefix tailTrace_3986066
  have hstable : (prefixWord ++ tailWord_3986066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986066).length < 2 ^ (prefixWord ++ tailWord_3986066).sum := by decide
  have hdescent : baseEnd_3986066 < baseStart_3986066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986104 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_3986104 : Nat := 118140960795 + 3986104 * 2 ^ 59
def prefixEnd_3986104 : Nat := 4983230072969 + 3 ^ 40 * 3986104 * 2
def baseEnd_3986104 : Nat := 2046787290809577583468247

theorem tailTrace_3986104 : CollatzResearch.WordTrace tailWord_3986104 prefixEnd_3986104 2046787290809577583468247 := by
  unfold tailWord_3986104
  simp only [CollatzResearch.WordTrace]
  refine ⟨72692578375516727604626683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96923437834022303472835577 72692578375516727604626683)
  ·
    refine ⟨109038867563275091406940025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72692578375516727604626683 109038867563275091406940025)
    ·
      refine ⟨81779150672456318555205019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109038867563275091406940025 81779150672456318555205019)
      ·
        refine ⟨122668726008684477832807529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81779150672456318555205019 122668726008684477832807529)
        ·
          refine ⟨92001544506513358374605647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122668726008684477832807529 92001544506513358374605647)
          ·
            refine ⟨138002316759770037561908471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92001544506513358374605647 138002316759770037561908471)
            ·
              refine ⟨207003475139655056342862707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138002316759770037561908471 207003475139655056342862707)
              ·
                refine ⟨310505212709482584514294061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207003475139655056342862707 310505212709482584514294061)
                ·
                  refine ⟨116439454766055969192860273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310505212709482584514294061 116439454766055969192860273)
                  ·
                    refine ⟨87329591074541976894645205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116439454766055969192860273 87329591074541976894645205)
                    ·
                      refine ⟨2046787290809577583468247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87329591074541976894645205 2046787290809577583468247)
                      ·
                        rfl

theorem cell23_3986104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_3986104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986104 prefixEnd_3986104 := by exact prefixLift 3986104
  have htrace : WordTrace (prefixWord ++ tailWord_3986104) baseStart_3986104 baseEnd_3986104 := by
    simpa [prefixWord, tailWord_3986104, baseEnd_3986104] using wordTrace_append hprefix tailTrace_3986104
  have hstable : (prefixWord ++ tailWord_3986104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986104).length < 2 ^ (prefixWord ++ tailWord_3986104).sum := by decide
  have hdescent : baseEnd_3986104 < baseStart_3986104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986122 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_3986122 : Nat := 118140960795 + 3986122 * 2 ^ 59
def prefixEnd_3986122 : Nat := 4983230072969 + 3 ^ 40 * 3986122 * 2
def baseEnd_3986122 : Nat := 2046796533461358513043165

theorem tailTrace_3986122 : CollatzResearch.WordTrace tailWord_3986122 prefixEnd_3986122 2046796533461358513043165 := by
  unfold tailWord_3986122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346453316242061070852155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96923875509978829522272413 36346453316242061070852155)
  ·
    refine ⟨54519679974363091606278233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36346453316242061070852155 54519679974363091606278233)
    ·
      refine ⟨40889759980772318704708675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54519679974363091606278233 40889759980772318704708675)
      ·
        refine ⟨61334639971158478057063013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40889759980772318704708675 61334639971158478057063013)
        ·
          refine ⟨11500244994592214635699315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61334639971158478057063013 11500244994592214635699315)
          ·
            refine ⟨17250367491888321953548973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500244994592214635699315 17250367491888321953548973)
            ·
              refine ⟨6468887809458120732580865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17250367491888321953548973 6468887809458120732580865)
              ·
                refine ⟨4851665857093590549435649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6468887809458120732580865 4851665857093590549435649)
                ·
                  refine ⟨3638749392820192912076737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851665857093590549435649 3638749392820192912076737)
                  ·
                    refine ⟨2729062044615144684057553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638749392820192912076737 2729062044615144684057553)
                    ·
                      refine ⟨2046796533461358513043165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729062044615144684057553 2046796533461358513043165)
                      ·
                        rfl

theorem cell23_3986122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_3986122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986122 prefixEnd_3986122 := by exact prefixLift 3986122
  have htrace : WordTrace (prefixWord ++ tailWord_3986122) baseStart_3986122 baseEnd_3986122 := by
    simpa [prefixWord, tailWord_3986122, baseEnd_3986122] using wordTrace_append hprefix tailTrace_3986122
  have hstable : (prefixWord ++ tailWord_3986122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986122).length < 2 ^ (prefixWord ++ tailWord_3986122).sum := by decide
  have hdescent : baseEnd_3986122 < baseStart_3986122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986161 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_3986161 : Nat := 118140960795 + 3986161 * 2 ^ 59
def prefixEnd_3986161 : Nat := 4983230072969 + 3 ^ 40 * 3986161 * 2
def baseEnd_3986161 : Nat := 2046816559206883860455485

theorem tailTrace_3986161 : CollatzResearch.WordTrace tailWord_3986161 prefixEnd_3986161 2046816559206883860455485 := by
  unfold tailWord_3986161
  simp only [CollatzResearch.WordTrace]
  refine ⟨145387235711826953944078337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96924823807884635962718891 145387235711826953944078337)
  ·
    refine ⟨109040426783870215458058753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145387235711826953944078337 109040426783870215458058753)
    ·
      refine ⟨81780320087902661593544065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109040426783870215458058753 81780320087902661593544065)
      ·
        refine ⟨61335240065926996195158049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81780320087902661593544065 61335240065926996195158049)
        ·
          refine ⟨46001430049445247146368537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61335240065926996195158049 46001430049445247146368537)
          ·
            refine ⟨34501072537083935359776403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46001430049445247146368537 34501072537083935359776403)
            ·
              refine ⟨51751608805625903039664605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34501072537083935359776403 51751608805625903039664605)
              ·
                refine ⟨19406853302109713639874227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51751608805625903039664605 19406853302109713639874227)
                ·
                  refine ⟨29110279953164570459811341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19406853302109713639874227 29110279953164570459811341)
                  ·
                    refine ⟨10916354982436713922429253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29110279953164570459811341 10916354982436713922429253)
                    ·
                      refine ⟨2046816559206883860455485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10916354982436713922429253 2046816559206883860455485)
                      ·
                        rfl

theorem cell23_3986161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_3986161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986161 prefixEnd_3986161 := by exact prefixLift 3986161
  have htrace : WordTrace (prefixWord ++ tailWord_3986161) baseStart_3986161 baseEnd_3986161 := by
    simpa [prefixWord, tailWord_3986161, baseEnd_3986161] using wordTrace_append hprefix tailTrace_3986161
  have hstable : (prefixWord ++ tailWord_3986161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986161).length < 2 ^ (prefixWord ++ tailWord_3986161).sum := by decide
  have hdescent : baseEnd_3986161 < baseStart_3986161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986239 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 1, 4]
def baseStart_3986239 : Nat := 118140960795 + 3986239 * 2 ^ 59
def prefixEnd_3986239 : Nat := 4983230072969 + 3 ^ 40 * 3986239 * 2
def baseEnd_3986239 : Nat := 682285536899311518426709

theorem tailTrace_3986239 : CollatzResearch.WordTrace tailWord_3986239 prefixEnd_3986239 682285536899311518426709 := by
  unfold tailWord_3986239
  simp only [CollatzResearch.WordTrace]
  refine ⟨145390080605544373265417771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96926720403696248843611847 145390080605544373265417771)
  ·
    refine ⟨218085120908316559898126657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145390080605544373265417771 218085120908316559898126657)
    ·
      refine ⟨163563840681237419923594993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218085120908316559898126657 163563840681237419923594993)
      ·
        refine ⟨122672880510928064942696245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163563840681237419923594993 122672880510928064942696245)
        ·
          refine ⟨11500582547899506088377773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122672880510928064942696245 11500582547899506088377773)
          ·
            refine ⟨4312718455462314783141665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11500582547899506088377773 4312718455462314783141665)
            ·
              refine ⟨3234538841596736087356249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312718455462314783141665 3234538841596736087356249)
              ·
                refine ⟨2425904131197552065517187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234538841596736087356249 2425904131197552065517187)
                ·
                  refine ⟨3638856196796328098275781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425904131197552065517187 3638856196796328098275781)
                  ·
                    refine ⟨682285536899311518426709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3638856196796328098275781 682285536899311518426709)
                    ·
                      rfl

theorem cell23_3986239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_3986239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986239 prefixEnd_3986239 := by exact prefixLift 3986239
  have htrace : WordTrace (prefixWord ++ tailWord_3986239) baseStart_3986239 baseEnd_3986239 := by
    simpa [prefixWord, tailWord_3986239, baseEnd_3986239] using wordTrace_append hprefix tailTrace_3986239
  have hstable : (prefixWord ++ tailWord_3986239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986239).length < 2 ^ (prefixWord ++ tailWord_3986239).sum := by decide
  have hdescent : baseEnd_3986239 < baseStart_3986239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986279 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_3986279 : Nat := 118140960795 + 3986279 * 2 ^ 59
def prefixEnd_3986279 : Nat := 4983230072969 + 3 ^ 40 * 3986279 * 2
def baseEnd_3986279 : Nat := 2046877149924114398779943

theorem tailTrace_3986279 : CollatzResearch.WordTrace tailWord_3986279 prefixEnd_3986279 2046877149924114398779943 := by
  unfold tailWord_3986279
  simp only [CollatzResearch.WordTrace]
  refine ⟨145391539525399460096873891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96927693016932973397915927 145391539525399460096873891)
  ·
    refine ⟨218087309288099190145310837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145391539525399460096873891 218087309288099190145310837)
    ·
      refine ⟨20445685245759299076122891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218087309288099190145310837 20445685245759299076122891)
      ·
        refine ⟨30668527868638948614184337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20445685245759299076122891 30668527868638948614184337)
        ·
          refine ⟨23001395901479211460638253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30668527868638948614184337 23001395901479211460638253)
          ·
            refine ⟨8625523463054704297739345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23001395901479211460638253 8625523463054704297739345)
            ·
              refine ⟨6469142597291028223304509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625523463054704297739345 6469142597291028223304509)
              ·
                refine ⟨2425928473984135583739191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6469142597291028223304509 2425928473984135583739191)
                ·
                  refine ⟨3638892710976203375608787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425928473984135583739191 3638892710976203375608787)
                  ·
                    refine ⟨5458339066464305063413181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3638892710976203375608787 5458339066464305063413181)
                    ·
                      refine ⟨2046877149924114398779943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458339066464305063413181 2046877149924114398779943)
                      ·
                        rfl

theorem cell23_3986279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_3986279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986279 prefixEnd_3986279 := by exact prefixLift 3986279
  have htrace : WordTrace (prefixWord ++ tailWord_3986279) baseStart_3986279 baseEnd_3986279 := by
    simpa [prefixWord, tailWord_3986279, baseEnd_3986279] using wordTrace_append hprefix tailTrace_3986279
  have hstable : (prefixWord ++ tailWord_3986279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986279).length < 2 ^ (prefixWord ++ tailWord_3986279).sum := by decide
  have hdescent : baseEnd_3986279 < baseStart_3986279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_3986281 : Nat := 118140960795 + 3986281 * 2 ^ 59
def prefixEnd_3986281 : Nat := 4983230072969 + 3 ^ 40 * 3986281 * 2
def baseEnd_3986281 : Nat := 2046878176885423390954933

theorem tailTrace_3986281 : CollatzResearch.WordTrace tailWord_3986281 prefixEnd_3986281 2046878176885423390954933 := by
  unfold tailWord_3986281
  simp only [CollatzResearch.WordTrace]
  refine ⟨145391612471392214438446697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96927741647594809625631131 145391612471392214438446697)
  ·
    refine ⟨109043709353544160828835023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145391612471392214438446697 109043709353544160828835023)
    ·
      refine ⟨163565564030316241243252535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109043709353544160828835023 163565564030316241243252535)
      ·
        refine ⟨245348346045474361864878803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163565564030316241243252535 245348346045474361864878803)
        ·
          refine ⟨368022519068211542797318205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245348346045474361864878803 368022519068211542797318205)
          ·
            refine ⟨138008444650579328548994327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368022519068211542797318205 138008444650579328548994327)
            ·
              refine ⟨207012666975868992823491491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138008444650579328548994327 207012666975868992823491491)
              ·
                refine ⟨310519000463803489235237237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207012666975868992823491491 310519000463803489235237237)
                ·
                  refine ⟨29111156293481577115803491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310519000463803489235237237 29111156293481577115803491)
                  ·
                    refine ⟨43666734440222365673705237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29111156293481577115803491 43666734440222365673705237)
                    ·
                      refine ⟨2046878176885423390954933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43666734440222365673705237 2046878176885423390954933)
                      ·
                        rfl

theorem cell23_3986281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_3986281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986281 prefixEnd_3986281 := by exact prefixLift 3986281
  have htrace : WordTrace (prefixWord ++ tailWord_3986281) baseStart_3986281 baseEnd_3986281 := by
    simpa [prefixWord, tailWord_3986281, baseEnd_3986281] using wordTrace_append hprefix tailTrace_3986281
  have hstable : (prefixWord ++ tailWord_3986281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986281).length < 2 ^ (prefixWord ++ tailWord_3986281).sum := by decide
  have hdescent : baseEnd_3986281 < baseStart_3986281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986325 : List Nat := [1, 3, 2, 1, 1, 6, 2, 7]
def baseStart_3986325 : Nat := 118140960795 + 3986325 * 2 ^ 59
def prefixEnd_3986325 : Nat := 4983230072969 + 3 ^ 40 * 3986325 * 2
def baseEnd_3986325 : Nat := 75811139630897082177953

theorem tailTrace_3986325 : CollatzResearch.WordTrace tailWord_3986325 prefixEnd_3986325 75811139630897082177953 := by
  unfold tailWord_3986325
  simp only [CollatzResearch.WordTrace]
  refine ⟨145393217283232809953048429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96928811522155206635365619 145393217283232809953048429)
  ·
    refine ⟨54522456481212303732393161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145393217283232809953048429 54522456481212303732393161)
    ·
      refine ⟨40891842360909227799294871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54522456481212303732393161 40891842360909227799294871)
      ·
        refine ⟨61337763541363841698942307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40891842360909227799294871 61337763541363841698942307)
        ·
          refine ⟨92006645312045762548413461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61337763541363841698942307 92006645312045762548413461)
          ·
            refine ⟨4312811499002145119456881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92006645312045762548413461 4312811499002145119456881)
            ·
              refine ⟨3234608624251608839592661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312811499002145119456881 3234608624251608839592661)
              ·
                refine ⟨75811139630897082177953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3234608624251608839592661 75811139630897082177953)
                ·
                  rfl

theorem cell23_3986325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 7].length) (baseStart_3986325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986325 prefixEnd_3986325 := by exact prefixLift 3986325
  have htrace : WordTrace (prefixWord ++ tailWord_3986325) baseStart_3986325 baseEnd_3986325 := by
    simpa [prefixWord, tailWord_3986325, baseEnd_3986325] using wordTrace_append hprefix tailTrace_3986325
  have hstable : (prefixWord ++ tailWord_3986325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986325).length < 2 ^ (prefixWord ++ tailWord_3986325).sum := by decide
  have hdescent : baseEnd_3986325 < baseStart_3986325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986331 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11]
def baseStart_3986331 : Nat := 118140960795 + 3986331 * 2 ^ 59
def prefixEnd_3986331 : Nat := 4983230072969 + 3 ^ 40 * 3986331 * 2
def baseEnd_3986331 : Nat := 2046903850918148195329703

theorem tailTrace_3986331 : CollatzResearch.WordTrace tailWord_3986331 prefixEnd_3986331 2046903850918148195329703 := by
  unfold tailWord_3986331
  simp only [CollatzResearch.WordTrace]
  refine ⟨145393436121211072977766847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96928957414140715318511231 145393436121211072977766847)
  ·
    refine ⟨218090154181816609466650271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145393436121211072977766847 218090154181816609466650271)
    ·
      refine ⟨327135231272724914199975407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218090154181816609466650271 327135231272724914199975407)
      ·
        refine ⟨490702846909087371299963111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327135231272724914199975407 490702846909087371299963111)
        ·
          refine ⟨736054270363631056949944667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490702846909087371299963111 736054270363631056949944667)
          ·
            refine ⟨1104081405545446585424917001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736054270363631056949944667 1104081405545446585424917001)
            ·
              refine ⟨828061054159084939068687751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104081405545446585424917001 828061054159084939068687751)
              ·
                refine ⟨1242091581238627408603031627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828061054159084939068687751 1242091581238627408603031627)
                ·
                  refine ⟨1863137371857941112904547441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242091581238627408603031627 1863137371857941112904547441)
                  ·
                    refine ⟨1397353028893455834678410581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863137371857941112904547441 1397353028893455834678410581)
                    ·
                      refine ⟨2046903850918148195329703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1397353028893455834678410581 2046903850918148195329703)
                      ·
                        rfl

theorem cell23_3986331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_3986331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986331 prefixEnd_3986331 := by exact prefixLift 3986331
  have htrace : WordTrace (prefixWord ++ tailWord_3986331) baseStart_3986331 baseEnd_3986331 := by
    simpa [prefixWord, tailWord_3986331, baseEnd_3986331] using wordTrace_append hprefix tailTrace_3986331
  have hstable : (prefixWord ++ tailWord_3986331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986331).length < 2 ^ (prefixWord ++ tailWord_3986331).sum := by decide
  have hdescent : baseEnd_3986331 < baseStart_3986331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986353 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_3986353 : Nat := 118140960795 + 3986353 * 2 ^ 59
def prefixEnd_3986353 : Nat := 4983230072969 + 3 ^ 40 * 3986353 * 2
def baseEnd_3986353 : Nat := 2046915147492547109254603

theorem tailTrace_3986353 : CollatzResearch.WordTrace tailWord_3986353 prefixEnd_3986353 2046915147492547109254603 := by
  unfold tailWord_3986353
  simp only [CollatzResearch.WordTrace]
  refine ⟨145394238527131370735067713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96929492351420913823378475 145394238527131370735067713)
  ·
    refine ⟨109045678895348528051300785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145394238527131370735067713 109045678895348528051300785)
    ·
      refine ⟨81784259171511396038475589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109045678895348528051300785 81784259171511396038475589)
      ·
        refine ⟨15334548594658386757214173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81784259171511396038475589 15334548594658386757214173)
        ·
          refine ⟨5750455722996895033955315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15334548594658386757214173 5750455722996895033955315)
          ·
            refine ⟨8625683584495342550932973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750455722996895033955315 8625683584495342550932973)
            ·
              refine ⟨3234631344185753456599865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8625683584495342550932973 3234631344185753456599865)
              ·
                refine ⟨2425973508139315092449899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234631344185753456599865 2425973508139315092449899)
                ·
                  refine ⟨3638960262208972638674849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2425973508139315092449899 3638960262208972638674849)
                  ·
                    refine ⟨2729220196656729479006137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638960262208972638674849 2729220196656729479006137)
                    ·
                      refine ⟨2046915147492547109254603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729220196656729479006137 2046915147492547109254603)
                      ·
                        rfl

theorem cell23_3986353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_3986353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986353 prefixEnd_3986353 := by exact prefixLift 3986353
  have htrace : WordTrace (prefixWord ++ tailWord_3986353) baseStart_3986353 baseEnd_3986353 := by
    simpa [prefixWord, tailWord_3986353, baseEnd_3986353] using wordTrace_append hprefix tailTrace_3986353
  have hstable : (prefixWord ++ tailWord_3986353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986353).length < 2 ^ (prefixWord ++ tailWord_3986353).sum := by decide
  have hdescent : baseEnd_3986353 < baseStart_3986353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986379 : List Nat := [1, 1, 1, 1, 3, 7, 1, 2, 1, 3, 2]
def baseStart_3986379 : Nat := 118140960795 + 3986379 * 2 ^ 59
def prefixEnd_3986379 : Nat := 4983230072969 + 3 ^ 40 * 3986379 * 2
def baseEnd_3986379 : Nat := 2046928497989564007529483

theorem tailTrace_3986379 : CollatzResearch.WordTrace tailWord_3986379 prefixEnd_3986379 2046928497989564007529483 := by
  unfold tailWord_3986379
  simp only [CollatzResearch.WordTrace]
  refine ⟨145395186825037177175514191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96930124550024784783676127 145395186825037177175514191)
  ·
    refine ⟨218092780237555765763271287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145395186825037177175514191 218092780237555765763271287)
    ·
      refine ⟨327139170356333648644906931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218092780237555765763271287 327139170356333648644906931)
      ·
        refine ⟨490708755534500472967360397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327139170356333648644906931 490708755534500472967360397)
        ·
          refine ⟨184015783325437677362760149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490708755534500472967360397 184015783325437677362760149)
          ·
            refine ⟨4312869921689945563189691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 184015783325437677362760149 4312869921689945563189691)
            ·
              refine ⟨6469304882534918344784537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312869921689945563189691 6469304882534918344784537)
              ·
                refine ⟨4851978661901188758588403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469304882534918344784537 4851978661901188758588403)
                ·
                  refine ⟨7277967992851783137882605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851978661901188758588403 7277967992851783137882605)
                  ·
                    refine ⟨2729237997319418676705977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7277967992851783137882605 2729237997319418676705977)
                    ·
                      refine ⟨2046928497989564007529483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729237997319418676705977 2046928497989564007529483)
                      ·
                        rfl

theorem cell23_3986379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3, 2].length) (baseStart_3986379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986379 prefixEnd_3986379 := by exact prefixLift 3986379
  have htrace : WordTrace (prefixWord ++ tailWord_3986379) baseStart_3986379 baseEnd_3986379 := by
    simpa [prefixWord, tailWord_3986379, baseEnd_3986379] using wordTrace_append hprefix tailTrace_3986379
  have hstable : (prefixWord ++ tailWord_3986379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986379).length < 2 ^ (prefixWord ++ tailWord_3986379).sum := by decide
  have hdescent : baseEnd_3986379 < baseStart_3986379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986392 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_3986392 : Nat := 118140960795 + 3986392 * 2 ^ 59
def prefixEnd_3986392 : Nat := 4983230072969 + 3 ^ 40 * 3986392 * 2
def baseEnd_3986392 : Nat := 2046935173238072456666923

theorem tailTrace_3986392 : CollatzResearch.WordTrace tailWord_3986392 prefixEnd_3986392 2046935173238072456666923 := by
  unfold tailWord_3986392
  simp only [CollatzResearch.WordTrace]
  refine ⟨72697830486995040197868715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96930440649326720263824953 72697830486995040197868715)
  ·
    refine ⟨109046745730492560296803073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72697830486995040197868715 109046745730492560296803073)
    ·
      refine ⟨81785059297869420222602305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109046745730492560296803073 81785059297869420222602305)
      ·
        refine ⟨61338794473402065166951729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81785059297869420222602305 61338794473402065166951729)
        ·
          refine ⟨46004095855051548875213797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61338794473402065166951729 46004095855051548875213797)
          ·
            refine ⟨8625767972822165414102587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46004095855051548875213797 8625767972822165414102587)
            ·
              refine ⟨12938651959233248121153881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625767972822165414102587 12938651959233248121153881)
              ·
                refine ⟨9703988969424936090865411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938651959233248121153881 9703988969424936090865411)
                ·
                  refine ⟨14555983454137404136298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9703988969424936090865411 14555983454137404136298117)
                  ·
                    refine ⟨2729246897650763275555897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14555983454137404136298117 2729246897650763275555897)
                    ·
                      refine ⟨2046935173238072456666923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729246897650763275555897 2046935173238072456666923)
                      ·
                        rfl

theorem cell23_3986392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_3986392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986392 prefixEnd_3986392 := by exact prefixLift 3986392
  have htrace : WordTrace (prefixWord ++ tailWord_3986392) baseStart_3986392 baseEnd_3986392 := by
    simpa [prefixWord, tailWord_3986392, baseEnd_3986392] using wordTrace_append hprefix tailTrace_3986392
  have hstable : (prefixWord ++ tailWord_3986392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986392).length < 2 ^ (prefixWord ++ tailWord_3986392).sum := by decide
  have hdescent : baseEnd_3986392 < baseStart_3986392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986408 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3986408 : Nat := 118140960795 + 3986408 * 2 ^ 59
def prefixEnd_3986408 : Nat := 4983230072969 + 3 ^ 40 * 3986408 * 2
def baseEnd_3986408 : Nat := 2046943388928544394066849

theorem tailTrace_3986408 : CollatzResearch.WordTrace tailWord_3986408 prefixEnd_3986408 2046943388928544394066849 := by
  unfold tailWord_3986408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72698122270966057564159939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96930829694621410085546585 72698122270966057564159939)
  ·
    refine ⟨109047183406449086346239909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72698122270966057564159939 109047183406449086346239909)
    ·
      refine ⟨20446346888709203689919983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109047183406449086346239909 20446346888709203689919983)
      ·
        refine ⟨30669520333063805534879975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20446346888709203689919983 30669520333063805534879975)
        ·
          refine ⟨46004280499595708302319963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30669520333063805534879975 46004280499595708302319963)
          ·
            refine ⟨69006420749393562453479945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46004280499595708302319963 69006420749393562453479945)
            ·
              refine ⟨51754815562045171840109959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69006420749393562453479945 51754815562045171840109959)
              ·
                refine ⟨77632223343067757760164939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51754815562045171840109959 77632223343067757760164939)
                ·
                  refine ⟨116448335014601636640247409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77632223343067757760164939 116448335014601636640247409)
                  ·
                    refine ⟨87336251260951227480185557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116448335014601636640247409 87336251260951227480185557)
                    ·
                      refine ⟨2046943388928544394066849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87336251260951227480185557 2046943388928544394066849)
                      ·
                        rfl

theorem cell23_3986408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3986408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986408 prefixEnd_3986408 := by exact prefixLift 3986408
  have htrace : WordTrace (prefixWord ++ tailWord_3986408) baseStart_3986408 baseEnd_3986408 := by
    simpa [prefixWord, tailWord_3986408, baseEnd_3986408] using wordTrace_append hprefix tailTrace_3986408
  have hstable : (prefixWord ++ tailWord_3986408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986408).length < 2 ^ (prefixWord ++ tailWord_3986408).sum := by decide
  have hdescent : baseEnd_3986408 < baseStart_3986408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986422 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3986422 : Nat := 118140960795 + 3986422 * 2 ^ 59
def prefixEnd_3986422 : Nat := 4983230072969 + 3 ^ 40 * 3986422 * 2
def baseEnd_3986422 : Nat := 2046950577657707339291785

theorem tailTrace_3986422 : CollatzResearch.WordTrace tailWord_3986422 prefixEnd_3986422 2046950577657707339291785 := by
  unfold tailWord_3986422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087297197742587219958095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96931170109254263679553013 9087297197742587219958095)
  ·
    refine ⟨13630945796613880829937143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9087297197742587219958095 13630945796613880829937143)
    ·
      refine ⟨20446418694920821244905715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630945796613880829937143 20446418694920821244905715)
      ·
        refine ⟨30669628042381231867358573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20446418694920821244905715 30669628042381231867358573)
        ·
          refine ⟨11501110515892961950259465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30669628042381231867358573 11501110515892961950259465)
          ·
            refine ⟨8625832886919721462694599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11501110515892961950259465 8625832886919721462694599)
            ·
              refine ⟨12938749330379582194041899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8625832886919721462694599 12938749330379582194041899)
              ·
                refine ⟨19408123995569373291062849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12938749330379582194041899 19408123995569373291062849)
                ·
                  refine ⟨14556092996677029968297137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19408123995569373291062849 14556092996677029968297137)
                  ·
                    refine ⟨10917069747507772476222853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14556092996677029968297137 10917069747507772476222853)
                    ·
                      refine ⟨2046950577657707339291785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10917069747507772476222853 2046950577657707339291785)
                      ·
                        rfl

theorem cell23_3986422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3986422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986422 prefixEnd_3986422 := by exact prefixLift 3986422
  have htrace : WordTrace (prefixWord ++ tailWord_3986422) baseStart_3986422 baseEnd_3986422 := by
    simpa [prefixWord, tailWord_3986422, baseEnd_3986422] using wordTrace_append hprefix tailTrace_3986422
  have hstable : (prefixWord ++ tailWord_3986422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986422).length < 2 ^ (prefixWord ++ tailWord_3986422).sum := by decide
  have hdescent : baseEnd_3986422 < baseStart_3986422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986425 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3986425 : Nat := 118140960795 + 3986425 * 2 ^ 59
def prefixEnd_3986425 : Nat := 4983230072969 + 3 ^ 40 * 3986425 * 2
def baseEnd_3986425 : Nat := 2046952118099670827554271

theorem tailTrace_3986425 : CollatzResearch.WordTrace tailWord_3986425 prefixEnd_3986425 2046952118099670827554271 := by
  unfold tailWord_3986425
  simp only [CollatzResearch.WordTrace]
  refine ⟨145396864582870527031688729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96931243055247018021125819 145396864582870527031688729)
  ·
    refine ⟨109047648437152895273766547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145396864582870527031688729 109047648437152895273766547)
    ·
      refine ⟨163571472655729342910649821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109047648437152895273766547 163571472655729342910649821)
      ·
        refine ⟨61339302245898503591493683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163571472655729342910649821 61339302245898503591493683)
        ·
          refine ⟨92008953368847755387240525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61339302245898503591493683 92008953368847755387240525)
          ·
            refine ⟨34503357513317908270215197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92008953368847755387240525 34503357513317908270215197)
            ·
              refine ⟨12938759067494215601330699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34503357513317908270215197 12938759067494215601330699)
              ·
                refine ⟨19408138601241323401996049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12938759067494215601330699 19408138601241323401996049)
                ·
                  refine ⟨14556103950930992551497037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19408138601241323401996049 14556103950930992551497037)
                  ·
                    refine ⟨5458538981599122206811389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14556103950930992551497037 5458538981599122206811389)
                    ·
                      refine ⟨2046952118099670827554271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458538981599122206811389 2046952118099670827554271)
                      ·
                        rfl

theorem cell23_3986425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3986425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986425 prefixEnd_3986425 := by exact prefixLift 3986425
  have htrace : WordTrace (prefixWord ++ tailWord_3986425) baseStart_3986425 baseEnd_3986425 := by
    simpa [prefixWord, tailWord_3986425, baseEnd_3986425] using wordTrace_append hprefix tailTrace_3986425
  have hstable : (prefixWord ++ tailWord_3986425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986425).length < 2 ^ (prefixWord ++ tailWord_3986425).sum := by decide
  have hdescent : baseEnd_3986425 < baseStart_3986425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986482 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_3986482 : Nat := 118140960795 + 3986482 * 2 ^ 59
def prefixEnd_3986482 : Nat := 4983230072969 + 3 ^ 40 * 3986482 * 2
def baseEnd_3986482 : Nat := 2046981386496977104541509

theorem tailTrace_3986482 : CollatzResearch.WordTrace tailWord_3986482 prefixEnd_3986482 2046981386496977104541509 := by
  unfold tailWord_3986482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36349735885916006441628425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96932629029109350511009133 36349735885916006441628425)
  ·
    refine ⟨27262301914437004831221319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36349735885916006441628425 27262301914437004831221319)
    ·
      refine ⟨40893452871655507246831979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27262301914437004831221319 40893452871655507246831979)
      ·
        refine ⟨61340179307483260870247969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40893452871655507246831979 61340179307483260870247969)
        ·
          refine ⟨46005134480612445652685977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61340179307483260870247969 46005134480612445652685977)
          ·
            refine ⟨34503850860459334239514483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46005134480612445652685977 34503850860459334239514483)
            ·
              refine ⟨51755776290689001359271725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34503850860459334239514483 51755776290689001359271725)
              ·
                refine ⟨19408416109008375509726897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51755776290689001359271725 19408416109008375509726897)
                ·
                  refine ⟨14556312081756281632295173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19408416109008375509726897 14556312081756281632295173)
                  ·
                    refine ⟨2729308515329302806055345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14556312081756281632295173 2729308515329302806055345)
                    ·
                      refine ⟨2046981386496977104541509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729308515329302806055345 2046981386496977104541509)
                      ·
                        rfl

theorem cell23_3986482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_3986482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986482 prefixEnd_3986482 := by exact prefixLift 3986482
  have htrace : WordTrace (prefixWord ++ tailWord_3986482) baseStart_3986482 baseEnd_3986482 := by
    simpa [prefixWord, tailWord_3986482, baseEnd_3986482] using wordTrace_append hprefix tailTrace_3986482
  have hstable : (prefixWord ++ tailWord_3986482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986482).length < 2 ^ (prefixWord ++ tailWord_3986482).sum := by decide
  have hdescent : baseEnd_3986482 < baseStart_3986482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986492 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3986492 : Nat := 118140960795 + 3986492 * 2 ^ 59
def prefixEnd_3986492 : Nat := 4983230072969 + 3 ^ 40 * 3986492 * 2
def baseEnd_3986492 : Nat := 682328840434507355138821

theorem tailTrace_3986492 : CollatzResearch.WordTrace tailWord_3986492 prefixEnd_3986492 682328840434507355138821 := by
  unfold tailWord_3986492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72699654136813898737188865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96932872182418531649585153 72699654136813898737188865)
  ·
    refine ⟨54524740602610424052891649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72699654136813898737188865 54524740602610424052891649)
    ·
      refine ⟨40893555451957818039668737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54524740602610424052891649 40893555451957818039668737)
      ·
        refine ⟨30670166588968363529751553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40893555451957818039668737 30670166588968363529751553)
        ·
          refine ⟨23002624941726272647313665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30670166588968363529751553 23002624941726272647313665)
          ·
            refine ⟨17251968706294704485485249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23002624941726272647313665 17251968706294704485485249)
            ·
              refine ⟨12938976529721028364113937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17251968706294704485485249 12938976529721028364113937)
              ·
                refine ⟨9704232397290771273085453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12938976529721028364113937 9704232397290771273085453)
                ·
                  refine ⟨3639087148984039227407045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9704232397290771273085453 3639087148984039227407045)
                  ·
                    refine ⟨682328840434507355138821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639087148984039227407045 682328840434507355138821)
                    ·
                      rfl

theorem cell23_3986492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3986492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986492 prefixEnd_3986492 := by exact prefixLift 3986492
  have htrace : WordTrace (prefixWord ++ tailWord_3986492) baseStart_3986492 baseEnd_3986492 := by
    simpa [prefixWord, tailWord_3986492, baseEnd_3986492] using wordTrace_append hprefix tailTrace_3986492
  have hstable : (prefixWord ++ tailWord_3986492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986492).length < 2 ^ (prefixWord ++ tailWord_3986492).sum := by decide
  have hdescent : baseEnd_3986492 < baseStart_3986492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986552 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_3986552 : Nat := 118140960795 + 3986552 * 2 ^ 59
def prefixEnd_3986552 : Nat := 4983230072969 + 3 ^ 40 * 3986552 * 2
def baseEnd_3986552 : Nat := 682339110047597276888729

theorem tailTrace_3986552 : CollatzResearch.WordTrace tailWord_3986552 prefixEnd_3986552 682339110047597276888729 := by
  unfold tailWord_3986552
  simp only [CollatzResearch.WordTrace]
  refine ⟨72700748326705213860780955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96934331102273618481041273 72700748326705213860780955)
  ·
    refine ⟨109051122490057820791171433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72700748326705213860780955 109051122490057820791171433)
    ·
      refine ⟨81788341867543365593378575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109051122490057820791171433 81788341867543365593378575)
      ·
        refine ⟨122682512801315048390067863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81788341867543365593378575 122682512801315048390067863)
        ·
          refine ⟨184023769201972572585101795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122682512801315048390067863 184023769201972572585101795)
          ·
            refine ⟨276035653802958858877652693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184023769201972572585101795 276035653802958858877652693)
            ·
              refine ⟨6469585636006848254944985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276035653802958858877652693 6469585636006848254944985)
              ·
                refine ⟨4852189227005136191208739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6469585636006848254944985 4852189227005136191208739)
                ·
                  refine ⟨7278283840507704286813109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852189227005136191208739 7278283840507704286813109)
                  ·
                    refine ⟨682339110047597276888729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7278283840507704286813109 682339110047597276888729)
                    ·
                      rfl

theorem cell23_3986552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_3986552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986552 prefixEnd_3986552 := by exact prefixLift 3986552
  have htrace : WordTrace (prefixWord ++ tailWord_3986552) baseStart_3986552 baseEnd_3986552 := by
    simpa [prefixWord, tailWord_3986552, baseEnd_3986552] using wordTrace_append hprefix tailTrace_3986552
  have hstable : (prefixWord ++ tailWord_3986552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986552).length < 2 ^ (prefixWord ++ tailWord_3986552).sum := by decide
  have hdescent : baseEnd_3986552 < baseStart_3986552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986569 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_3986569 : Nat := 118140960795 + 3986569 * 2 ^ 59
def prefixEnd_3986569 : Nat := 4983230072969 + 3 ^ 40 * 3986569 * 2
def baseEnd_3986569 : Nat := 682342019771306088051203

theorem tailTrace_3986569 : CollatzResearch.WordTrace tailWord_3986569 prefixEnd_3986569 682342019771306088051203 := by
  unfold tailWord_3986569
  simp only [CollatzResearch.WordTrace]
  refine ⟨145402116694348839624930761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96934744462899226416620507 145402116694348839624930761)
  ·
    refine ⟨109051587520761629718698071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145402116694348839624930761 109051587520761629718698071)
    ·
      refine ⟨163577381281142444578047107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109051587520761629718698071 163577381281142444578047107)
      ·
        refine ⟨245366071921713666867070661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163577381281142444578047107 245366071921713666867070661)
        ·
          refine ⟨46006138485321312537575749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245366071921713666867070661 46006138485321312537575749)
          ·
            refine ⟨8626150965997746100795453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46006138485321312537575749 8626150965997746100795453)
            ·
              refine ⟨3234806612249154787798295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8626150965997746100795453 3234806612249154787798295)
              ·
                refine ⟨4852209918373732181697443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234806612249154787798295 4852209918373732181697443)
                ·
                  refine ⟨7278314877560598272546165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852209918373732181697443 7278314877560598272546165)
                  ·
                    refine ⟨682342019771306088051203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7278314877560598272546165 682342019771306088051203)
                    ·
                      rfl

theorem cell23_3986569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_3986569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986569 prefixEnd_3986569 := by exact prefixLift 3986569
  have htrace : WordTrace (prefixWord ++ tailWord_3986569) baseStart_3986569 baseEnd_3986569 := by
    simpa [prefixWord, tailWord_3986569, baseEnd_3986569] using wordTrace_append hprefix tailTrace_3986569
  have hstable : (prefixWord ++ tailWord_3986569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986569).length < 2 ^ (prefixWord ++ tailWord_3986569).sum := by decide
  have hdescent : baseEnd_3986569 < baseStart_3986569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986572 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3986572 : Nat := 118140960795 + 3986572 * 2 ^ 59
def prefixEnd_3986572 : Nat := 4983230072969 + 3 ^ 40 * 3986572 * 2
def baseEnd_3986572 : Nat := 2047027599755881752416095

theorem tailTrace_3986572 : CollatzResearch.WordTrace tailWord_3986572 prefixEnd_3986572 2047027599755881752416095 := by
  unfold tailWord_3986572
  simp only [CollatzResearch.WordTrace]
  refine ⟨72701113056668985568644985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96934817408891980758193313 72701113056668985568644985)
  ·
    refine ⟨54525834792501739176483739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72701113056668985568644985 54525834792501739176483739)
    ·
      refine ⟨81788752188752608764725609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54525834792501739176483739 81788752188752608764725609)
      ·
        refine ⟨61341564141564456573544207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81788752188752608764725609 61341564141564456573544207)
        ·
          refine ⟨92012346212346684860316311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61341564141564456573544207 92012346212346684860316311)
          ·
            refine ⟨138018519318520027290474467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92012346212346684860316311 138018519318520027290474467)
            ·
              refine ⟨207027778977780040935711701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138018519318520027290474467 207027778977780040935711701)
              ·
                refine ⟨4852213569791719709430743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207027778977780040935711701 4852213569791719709430743)
                ·
                  refine ⟨7278320354687579564146115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852213569791719709430743 7278320354687579564146115)
                  ·
                    refine ⟨10917480532031369346219173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7278320354687579564146115 10917480532031369346219173)
                    ·
                      refine ⟨2047027599755881752416095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10917480532031369346219173 2047027599755881752416095)
                      ·
                        rfl

theorem cell23_3986572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3986572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986572 prefixEnd_3986572 := by exact prefixLift 3986572
  have htrace : WordTrace (prefixWord ++ tailWord_3986572) baseStart_3986572 baseEnd_3986572 := by
    simpa [prefixWord, tailWord_3986572, baseEnd_3986572] using wordTrace_append hprefix tailTrace_3986572
  have hstable : (prefixWord ++ tailWord_3986572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986572).length < 2 ^ (prefixWord ++ tailWord_3986572).sum := by decide
  have hdescent : baseEnd_3986572 < baseStart_3986572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_3986575 : Nat := 118140960795 + 3986575 * 2 ^ 59
def prefixEnd_3986575 : Nat := 4983230072969 + 3 ^ 40 * 3986575 * 2
def baseEnd_3986575 : Nat := 2047029140197845240678581

theorem tailTrace_3986575 : CollatzResearch.WordTrace tailWord_3986575 prefixEnd_3986575 2047029140197845240678581 := by
  unfold tailWord_3986575
  simp only [CollatzResearch.WordTrace]
  refine ⟨145402335532327102649649179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96934890354884735099766119 145402335532327102649649179)
  ·
    refine ⟨218103503298490653974473769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145402335532327102649649179 218103503298490653974473769)
    ·
      refine ⟨163577627473867990480855327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218103503298490653974473769 163577627473867990480855327)
      ·
        refine ⟨245366441210801985721282991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163577627473867990480855327 245366441210801985721282991)
        ·
          refine ⟨368049661816202978581924487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245366441210801985721282991 368049661816202978581924487)
          ·
            refine ⟨552074492724304467872886731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368049661816202978581924487 552074492724304467872886731)
            ·
              refine ⟨828111739086456701809330097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552074492724304467872886731 828111739086456701809330097)
              ·
                refine ⟨621083804314842526356997573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828111739086456701809330097 621083804314842526356997573)
                ·
                  refine ⟨116453213309032973691937045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621083804314842526356997573 116453213309032973691937045)
                  ·
                    refine ⟨5458744373860920641809549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116453213309032973691937045 5458744373860920641809549)
                    ·
                      refine ⟨2047029140197845240678581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458744373860920641809549 2047029140197845240678581)
                      ·
                        rfl

theorem cell23_3986575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_3986575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986575 prefixEnd_3986575 := by exact prefixLift 3986575
  have htrace : WordTrace (prefixWord ++ tailWord_3986575) baseStart_3986575 baseEnd_3986575 := by
    simpa [prefixWord, tailWord_3986575, baseEnd_3986575] using wordTrace_append hprefix tailTrace_3986575
  have hstable : (prefixWord ++ tailWord_3986575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986575).length < 2 ^ (prefixWord ++ tailWord_3986575).sum := by decide
  have hdescent : baseEnd_3986575 < baseStart_3986575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986583 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3986583 : Nat := 118140960795 + 3986583 * 2 ^ 59
def prefixEnd_3986583 : Nat := 4983230072969 + 3 ^ 40 * 3986583 * 2
def baseEnd_3986583 : Nat := 2047033248043081209378545

theorem tailTrace_3986583 : CollatzResearch.WordTrace tailWord_3986583 prefixEnd_3986583 2047033248043081209378545 := by
  unfold tailWord_3986583
  simp only [CollatzResearch.WordTrace]
  refine ⟨145402627316298120015940403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96935084877532080010626935 145402627316298120015940403)
  ·
    refine ⟨218103940974447180023910605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145402627316298120015940403 218103940974447180023910605)
    ·
      refine ⟨81788977865417692508966477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218103940974447180023910605 81788977865417692508966477)
      ·
        refine ⟨30670866699531634690862429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81788977865417692508966477 30670866699531634690862429)
        ·
          refine ⟨11501575012324363009073411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30670866699531634690862429 11501575012324363009073411)
          ·
            refine ⟨17252362518486544513610117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501575012324363009073411 17252362518486544513610117)
            ·
              refine ⟨3234817972216227096301897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17252362518486544513610117 3234817972216227096301897)
              ·
                refine ⟨2426113479162170322226423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234817972216227096301897 2426113479162170322226423)
                ·
                  refine ⟨3639170218743255483339635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426113479162170322226423 3639170218743255483339635)
                  ·
                    refine ⟨5458755328114883225009453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3639170218743255483339635 5458755328114883225009453)
                    ·
                      refine ⟨2047033248043081209378545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458755328114883225009453 2047033248043081209378545)
                      ·
                        rfl

theorem cell23_3986583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3986583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986583 prefixEnd_3986583 := by exact prefixLift 3986583
  have htrace : WordTrace (prefixWord ++ tailWord_3986583) baseStart_3986583 baseEnd_3986583 := by
    simpa [prefixWord, tailWord_3986583, baseEnd_3986583] using wordTrace_append hprefix tailTrace_3986583
  have hstable : (prefixWord ++ tailWord_3986583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986583).length < 2 ^ (prefixWord ++ tailWord_3986583).sum := by decide
  have hdescent : baseEnd_3986583 < baseStart_3986583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986592 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3986592 : Nat := 118140960795 + 3986592 * 2 ^ 59
def prefixEnd_3986592 : Nat := 4983230072969 + 3 ^ 40 * 3986592 * 2
def baseEnd_3986592 : Nat := 2047037869368971674166003

theorem tailTrace_3986592 : CollatzResearch.WordTrace tailWord_3986592 prefixEnd_3986592 2047037869368971674166003 := by
  unfold tailWord_3986592
  simp only [CollatzResearch.WordTrace]
  refine ⟨72701477786632757276509015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96935303715510343035345353 72701477786632757276509015)
  ·
    refine ⟨109052216679949135914763523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72701477786632757276509015 109052216679949135914763523)
    ·
      refine ⟨163578325019923703872145285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109052216679949135914763523 163578325019923703872145285)
      ·
        refine ⟨30670935941235694476027241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163578325019923703872145285 30670935941235694476027241)
        ·
          refine ⟨23003201955926770857020431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30670935941235694476027241 23003201955926770857020431)
          ·
            refine ⟨34504802933890156285530647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23003201955926770857020431 34504802933890156285530647)
            ·
              refine ⟨51757204400835234428295971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34504802933890156285530647 51757204400835234428295971)
              ·
                refine ⟨77635806601252851642443957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51757204400835234428295971 77635806601252851642443957)
                ·
                  refine ⟨7278356868867454841479121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77635806601252851642443957 7278356868867454841479121)
                  ·
                    refine ⟨5458767651650591131109341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278356868867454841479121 5458767651650591131109341)
                    ·
                      refine ⟨2047037869368971674166003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458767651650591131109341 2047037869368971674166003)
                      ·
                        rfl

theorem cell23_3986592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3986592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986592 prefixEnd_3986592 := by exact prefixLift 3986592
  have htrace : WordTrace (prefixWord ++ tailWord_3986592) baseStart_3986592 baseEnd_3986592 := by
    simpa [prefixWord, tailWord_3986592, baseEnd_3986592] using wordTrace_append hprefix tailTrace_3986592
  have hstable : (prefixWord ++ tailWord_3986592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986592).length < 2 ^ (prefixWord ++ tailWord_3986592).sum := by decide
  have hdescent : baseEnd_3986592 < baseStart_3986592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986599 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3986599 : Nat := 118140960795 + 3986599 * 2 ^ 59
def prefixEnd_3986599 : Nat := 4983230072969 + 3 ^ 40 * 3986599 * 2
def baseEnd_3986599 : Nat := 682347154577851048926157

theorem tailTrace_3986599 : CollatzResearch.WordTrace tailWord_3986599 prefixEnd_3986599 682347154577851048926157 := by
  unfold tailWord_3986599
  simp only [CollatzResearch.WordTrace]
  refine ⟨145403210884240154748522851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96935473922826769832348567 145403210884240154748522851)
  ·
    refine ⟨218104816326360232122784277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145403210884240154748522851 218104816326360232122784277)
    ·
      refine ⟨10223663265298135880755513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218104816326360232122784277 10223663265298135880755513)
      ·
        refine ⟨7667747448973601910566635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10223663265298135880755513 7667747448973601910566635)
        ·
          refine ⟨11501621173460402865849953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667747448973601910566635 11501621173460402865849953)
          ·
            refine ⟨8626215880095302149387465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11501621173460402865849953 8626215880095302149387465)
            ·
              refine ⟨6469661910071476612040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8626215880095302149387465 6469661910071476612040599)
              ·
                refine ⟨9704492865107214918060899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469661910071476612040599 9704492865107214918060899)
                ·
                  refine ⟨14556739297660822377091349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704492865107214918060899 14556739297660822377091349)
                  ·
                    refine ⟨682347154577851048926157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14556739297660822377091349 682347154577851048926157)
                    ·
                      rfl

theorem cell23_3986599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3986599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986599 prefixEnd_3986599 := by exact prefixLift 3986599
  have htrace : WordTrace (prefixWord ++ tailWord_3986599) baseStart_3986599 baseEnd_3986599 := by
    simpa [prefixWord, tailWord_3986599, baseEnd_3986599] using wordTrace_append hprefix tailTrace_3986599
  have hstable : (prefixWord ++ tailWord_3986599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986599).length < 2 ^ (prefixWord ++ tailWord_3986599).sum := by decide
  have hdescent : baseEnd_3986599 < baseStart_3986599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986609 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3986609 : Nat := 118140960795 + 3986609 * 2 ^ 59
def prefixEnd_3986609 : Nat := 4983230072969 + 3 ^ 40 * 3986609 * 2
def baseEnd_3986609 : Nat := 2047046598540098107653425

theorem tailTrace_3986609 : CollatzResearch.WordTrace tailWord_3986609 prefixEnd_3986609 2047046598540098107653425 := by
  unfold tailWord_3986609
  simp only [CollatzResearch.WordTrace]
  refine ⟨145403575614203926456386881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96935717076135950970924587 145403575614203926456386881)
  ·
    refine ⟨109052681710652944842290161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145403575614203926456386881 109052681710652944842290161)
    ·
      refine ⟨81789511282989708631717621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109052681710652944842290161 81789511282989708631717621)
      ·
        refine ⟨7667766682780285184223527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81789511282989708631717621 7667766682780285184223527)
        ·
          refine ⟨11501650024170427776335291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7667766682780285184223527 11501650024170427776335291)
          ·
            refine ⟨17252475036255641664502937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501650024170427776335291 17252475036255641664502937)
            ·
              refine ⟨12939356277191731248377203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17252475036255641664502937 12939356277191731248377203)
              ·
                refine ⟨19409034415787596872565805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939356277191731248377203 19409034415787596872565805)
                ·
                  refine ⟨7278387905920348827212177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19409034415787596872565805 7278387905920348827212177)
                  ·
                    refine ⟨5458790929440261620409133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7278387905920348827212177 5458790929440261620409133)
                    ·
                      refine ⟨2047046598540098107653425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458790929440261620409133 2047046598540098107653425)
                      ·
                        rfl

theorem cell23_3986609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3986609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986609 prefixEnd_3986609 := by exact prefixLift 3986609
  have htrace : WordTrace (prefixWord ++ tailWord_3986609) baseStart_3986609 baseEnd_3986609 := by
    simpa [prefixWord, tailWord_3986609, baseEnd_3986609] using wordTrace_append hprefix tailTrace_3986609
  have hstable : (prefixWord ++ tailWord_3986609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986609).length < 2 ^ (prefixWord ++ tailWord_3986609).sum := by decide
  have hdescent : baseEnd_3986609 < baseStart_3986609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986635 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_3986635 : Nat := 118140960795 + 3986635 * 2 ^ 59
def prefixEnd_3986635 : Nat := 4983230072969 + 3 ^ 40 * 3986635 * 2
def baseEnd_3986635 : Nat := 2047059949037115005928305

theorem tailTrace_3986635 : CollatzResearch.WordTrace tailWord_3986635 prefixEnd_3986635 2047059949037115005928305 := by
  unfold tailWord_3986635
  simp only [CollatzResearch.WordTrace]
  refine ⟨145404523912109732896833359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96936349274739821931222239 145404523912109732896833359)
  ·
    refine ⟨218106785868164599345250039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145404523912109732896833359 218106785868164599345250039)
    ·
      refine ⟨327160178802246899017875059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218106785868164599345250039 327160178802246899017875059)
      ·
        refine ⟨490740268203370348526812589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327160178802246899017875059 490740268203370348526812589)
        ·
          refine ⟨184027600576263880697554721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490740268203370348526812589 184027600576263880697554721)
          ·
            refine ⟨138020700432197910523166041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184027600576263880697554721 138020700432197910523166041)
            ·
              refine ⟨103515525324148432892374531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138020700432197910523166041 103515525324148432892374531)
              ·
                refine ⟨155273287986222649338561797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103515525324148432892374531 155273287986222649338561797)
                ·
                  refine ⟨29113741497416746750980337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155273287986222649338561797 29113741497416746750980337)
                  ·
                    refine ⟨21835306123062560063235253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29113741497416746750980337 21835306123062560063235253)
                    ·
                      refine ⟨2047059949037115005928305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21835306123062560063235253 2047059949037115005928305)
                      ·
                        rfl

theorem cell23_3986635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_3986635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986635 prefixEnd_3986635 := by exact prefixLift 3986635
  have htrace : WordTrace (prefixWord ++ tailWord_3986635) baseStart_3986635 baseEnd_3986635 := by
    simpa [prefixWord, tailWord_3986635, baseEnd_3986635] using wordTrace_append hprefix tailTrace_3986635
  have hstable : (prefixWord ++ tailWord_3986635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986635).length < 2 ^ (prefixWord ++ tailWord_3986635).sum := by decide
  have hdescent : baseEnd_3986635 < baseStart_3986635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986639 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_3986639 : Nat := 118140960795 + 3986639 * 2 ^ 59
def prefixEnd_3986639 : Nat := 4983230072969 + 3 ^ 40 * 3986639 * 2
def baseEnd_3986639 : Nat := 2047062002959732990278287

theorem tailTrace_3986639 : CollatzResearch.WordTrace tailWord_3986639 prefixEnd_3986639 2047062002959732990278287 := by
  unfold tailWord_3986639
  simp only [CollatzResearch.WordTrace]
  refine ⟨145404669804095241579978971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96936446536063494386652647 145404669804095241579978971)
  ·
    refine ⟨218107004706142862369968457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145404669804095241579978971 218107004706142862369968457)
    ·
      refine ⟨163580253529607146777476343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218107004706142862369968457 163580253529607146777476343)
      ·
        refine ⟨245370380294410720166214515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163580253529607146777476343 245370380294410720166214515)
        ·
          refine ⟨368055570441616080249321773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245370380294410720166214515 368055570441616080249321773)
          ·
            refine ⟨138020838915606030093495665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368055570441616080249321773 138020838915606030093495665)
            ·
              refine ⟨103515629186704522570121749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138020838915606030093495665 103515629186704522570121749)
              ·
                refine ⟨4852295118126774495474457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103515629186704522570121749 4852295118126774495474457)
                ·
                  refine ⟨3639221338595080871605843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4852295118126774495474457 3639221338595080871605843)
                  ·
                    refine ⟨5458832007892621307408765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3639221338595080871605843 5458832007892621307408765)
                    ·
                      refine ⟨2047062002959732990278287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5458832007892621307408765 2047062002959732990278287)
                      ·
                        rfl

theorem cell23_3986639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_3986639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986639 prefixEnd_3986639 := by exact prefixLift 3986639
  have htrace : WordTrace (prefixWord ++ tailWord_3986639) baseStart_3986639 baseEnd_3986639 := by
    simpa [prefixWord, tailWord_3986639, baseEnd_3986639] using wordTrace_append hprefix tailTrace_3986639
  have hstable : (prefixWord ++ tailWord_3986639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986639).length < 2 ^ (prefixWord ++ tailWord_3986639).sum := by decide
  have hdescent : baseEnd_3986639 < baseStart_3986639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986653 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3986653 : Nat := 118140960795 + 3986653 * 2 ^ 59
def prefixEnd_3986653 : Nat := 4983230072969 + 3 ^ 40 * 3986653 * 2
def baseEnd_3986653 : Nat := 2047069191688895935503223

theorem tailTrace_3986653 : CollatzResearch.WordTrace tailWord_3986653 prefixEnd_3986653 2047069191688895935503223 := by
  unfold tailWord_3986653
  simp only [CollatzResearch.WordTrace]
  refine ⟨145405180426044521970988613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96936786950696347980659075 145405180426044521970988613)
  ·
    refine ⟨27263471329883347869560365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145405180426044521970988613 27263471329883347869560365)
    ·
      refine ⟨10223801748706255451085137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27263471329883347869560365 10223801748706255451085137)
      ·
        refine ⟨7667851311529691588313853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10223801748706255451085137 7667851311529691588313853)
        ·
          refine ⟨2875444241823634345617695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7667851311529691588313853 2875444241823634345617695)
          ·
            refine ⟨4313166362735451518426543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875444241823634345617695 4313166362735451518426543)
            ·
              refine ⟨6469749544103177277639815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313166362735451518426543 6469749544103177277639815)
              ·
                refine ⟨9704624316154765916459723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469749544103177277639815 9704624316154765916459723)
                ·
                  refine ⟨14556936474232148874689585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704624316154765916459723 14556936474232148874689585)
                  ·
                    refine ⟨10917702355674111656017189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14556936474232148874689585 10917702355674111656017189)
                    ·
                      refine ⟨2047069191688895935503223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10917702355674111656017189 2047069191688895935503223)
                      ·
                        rfl

theorem cell23_3986653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3986653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986653 prefixEnd_3986653 := by exact prefixLift 3986653
  have htrace : WordTrace (prefixWord ++ tailWord_3986653) baseStart_3986653 baseEnd_3986653 := by
    simpa [prefixWord, tailWord_3986653, baseEnd_3986653] using wordTrace_append hprefix tailTrace_3986653
  have hstable : (prefixWord ++ tailWord_3986653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986653).length < 2 ^ (prefixWord ++ tailWord_3986653).sum := by decide
  have hdescent : baseEnd_3986653 < baseStart_3986653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986666 : List Nat := [3, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_3986666 : Nat := 118140960795 + 3986666 * 2 ^ 59
def prefixEnd_3986666 : Nat := 4983230072969 + 3 ^ 40 * 3986666 * 2
def baseEnd_3986666 : Nat := 2047075866937404384640663

theorem tailTrace_3986666 : CollatzResearch.WordTrace tailWord_3986666 prefixEnd_3986666 2047075866937404384640663 := by
  unfold tailWord_3986666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36351413643749356297802963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96937103049998283460807901 36351413643749356297802963)
  ·
    refine ⟨54527120465624034446704445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36351413643749356297802963 54527120465624034446704445)
    ·
      refine ⟨20447670174609012917514167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54527120465624034446704445 20447670174609012917514167)
      ·
        refine ⟨30671505261913519376271251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20447670174609012917514167 30671505261913519376271251)
        ·
          refine ⟨46007257892870279064406877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30671505261913519376271251 46007257892870279064406877)
          ·
            refine ⟨17252721709826354649152579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46007257892870279064406877 17252721709826354649152579)
            ·
              refine ⟨25879082564739531973728869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17252721709826354649152579 25879082564739531973728869)
              ·
                refine ⟨4852327980888662245074163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25879082564739531973728869 4852327980888662245074163)
                ·
                  refine ⟨7278491971332993367611245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852327980888662245074163 7278491971332993367611245)
                  ·
                    refine ⟨2729434489249872512854217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7278491971332993367611245 2729434489249872512854217)
                    ·
                      refine ⟨2047075866937404384640663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729434489249872512854217 2047075866937404384640663)
                      ·
                        rfl

theorem cell23_3986666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_3986666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986666 prefixEnd_3986666 := by exact prefixLift 3986666
  have htrace : WordTrace (prefixWord ++ tailWord_3986666) baseStart_3986666 baseEnd_3986666 := by
    simpa [prefixWord, tailWord_3986666, baseEnd_3986666] using wordTrace_append hprefix tailTrace_3986666
  have hstable : (prefixWord ++ tailWord_3986666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986666).length < 2 ^ (prefixWord ++ tailWord_3986666).sum := by decide
  have hdescent : baseEnd_3986666 < baseStart_3986666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986682 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_3986682 : Nat := 118140960795 + 3986682 * 2 ^ 59
def prefixEnd_3986682 : Nat := 4983230072969 + 3 ^ 40 * 3986682 * 2
def baseEnd_3986682 : Nat := 2047084082627876322040589

theorem tailTrace_3986682 : CollatzResearch.WordTrace tailWord_3986682 prefixEnd_3986682 2047084082627876322040589 := by
  unfold tailWord_3986682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36351559535734864980948575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96937492095292973282529533 36351559535734864980948575)
  ·
    refine ⟨54527339303602297471422863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36351559535734864980948575 54527339303602297471422863)
    ·
      refine ⟨81791008955403446207134295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54527339303602297471422863 81791008955403446207134295)
      ·
        refine ⟨122686513433105169310701443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81791008955403446207134295 122686513433105169310701443)
        ·
          refine ⟨184029770149657753966052165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122686513433105169310701443 184029770149657753966052165)
          ·
            refine ⟨34505581903060828868634781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184029770149657753966052165 34505581903060828868634781)
            ·
              refine ⟨12939593213647810825738043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34505581903060828868634781 12939593213647810825738043)
              ·
                refine ⟨19409389820471716238607065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939593213647810825738043 19409389820471716238607065)
                ·
                  refine ⟨14557042365353787178955299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19409389820471716238607065 14557042365353787178955299)
                  ·
                    refine ⟨21835563548030680768432949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14557042365353787178955299 21835563548030680768432949)
                    ·
                      refine ⟨2047084082627876322040589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21835563548030680768432949 2047084082627876322040589)
                      ·
                        rfl

theorem cell23_3986682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_3986682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986682 prefixEnd_3986682 := by exact prefixLift 3986682
  have htrace : WordTrace (prefixWord ++ tailWord_3986682) baseStart_3986682 baseEnd_3986682 := by
    simpa [prefixWord, tailWord_3986682, baseEnd_3986682] using wordTrace_append hprefix tailTrace_3986682
  have hstable : (prefixWord ++ tailWord_3986682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986682).length < 2 ^ (prefixWord ++ tailWord_3986682).sum := by decide
  have hdescent : baseEnd_3986682 < baseStart_3986682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986753 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 5]
def baseStart_3986753 : Nat := 118140960795 + 3986753 * 2 ^ 59
def prefixEnd_3986753 : Nat := 4983230072969 + 3 ^ 40 * 3986753 * 2
def baseEnd_3986753 : Nat := 227457837750482838250307

theorem tailTrace_3986753 : CollatzResearch.WordTrace tailWord_3986753 prefixEnd_3986753 227457837750482838250307 := by
  unfold tailWord_3986753
  simp only [CollatzResearch.WordTrace]
  refine ⟨145408827725682239049628913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96939218483788159366419275 145408827725682239049628913)
  ·
    refine ⟨109056620794261679287221685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145408827725682239049628913 109056620794261679287221685)
    ·
      refine ⟨10224058199462032433177033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109056620794261679287221685 10224058199462032433177033)
      ·
        refine ⟨7668043649596524324882775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10224058199462032433177033 7668043649596524324882775)
        ·
          refine ⟨11502065474394786487324163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668043649596524324882775 11502065474394786487324163)
          ·
            refine ⟨17253098211592179730986245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502065474394786487324163 17253098211592179730986245)
            ·
              refine ⟨3234955914673533699559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17253098211592179730986245 3234955914673533699559921)
              ·
                refine ⟨2426216936005150274669941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234955914673533699559921 2426216936005150274669941)
                ·
                  refine ⟨227457837750482838250307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426216936005150274669941 227457837750482838250307)
                  ·
                    rfl

theorem cell23_3986753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 5].length) (baseStart_3986753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986753 prefixEnd_3986753 := by exact prefixLift 3986753
  have htrace : WordTrace (prefixWord ++ tailWord_3986753) baseStart_3986753 baseEnd_3986753 := by
    simpa [prefixWord, tailWord_3986753, baseEnd_3986753] using wordTrace_append hprefix tailTrace_3986753
  have hstable : (prefixWord ++ tailWord_3986753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986753).length < 2 ^ (prefixWord ++ tailWord_3986753).sum := by decide
  have hdescent : baseEnd_3986753 < baseStart_3986753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986786 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3986786 : Nat := 118140960795 + 3986786 * 2 ^ 59
def prefixEnd_3986786 : Nat := 4983230072969 + 3 ^ 40 * 3986786 * 2
def baseEnd_3986786 : Nat := 2047137484615943915140111

theorem tailTrace_3986786 : CollatzResearch.WordTrace tailWord_3986786 prefixEnd_3986786 2047137484615943915140111 := by
  unfold tailWord_3986786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36352507833640671421395053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96940020889708457123720141 36352507833640671421395053)
  ·
    refine ⟨13632190437615251783023145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36352507833640671421395053 13632190437615251783023145)
    ·
      refine ⟨10224142828211438837267359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13632190437615251783023145 10224142828211438837267359)
      ·
        refine ⟨15336214242317158255901039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224142828211438837267359 15336214242317158255901039)
        ·
          refine ⟨23004321363475737383851559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15336214242317158255901039 23004321363475737383851559)
          ·
            refine ⟨34506482045213606075777339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23004321363475737383851559 34506482045213606075777339)
            ·
              refine ⟨51759723067820409113666009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34506482045213606075777339 51759723067820409113666009)
              ·
                refine ⟨38819792300865306835249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51759723067820409113666009 38819792300865306835249507)
                ·
                  refine ⟨58229688451297960252874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38819792300865306835249507 58229688451297960252874261)
                  ·
                    refine ⟨2729516646154591886853481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58229688451297960252874261 2729516646154591886853481)
                    ·
                      refine ⟨2047137484615943915140111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729516646154591886853481 2047137484615943915140111)
                      ·
                        rfl

theorem cell23_3986786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3986786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986786 prefixEnd_3986786 := by exact prefixLift 3986786
  have htrace : WordTrace (prefixWord ++ tailWord_3986786) baseStart_3986786 baseEnd_3986786 := by
    simpa [prefixWord, tailWord_3986786, baseEnd_3986786] using wordTrace_append hprefix tailTrace_3986786
  have hstable : (prefixWord ++ tailWord_3986786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986786).length < 2 ^ (prefixWord ++ tailWord_3986786).sum := by decide
  have hdescent : baseEnd_3986786 < baseStart_3986786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986789 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3986789 : Nat := 118140960795 + 3986789 * 2 ^ 59
def prefixEnd_3986789 : Nat := 4983230072969 + 3 ^ 40 * 3986789 * 2
def baseEnd_3986789 : Nat := 2047139025057907403402597

theorem tailTrace_3986789 : CollatzResearch.WordTrace tailWord_3986789 prefixEnd_3986789 2047139025057907403402597 := by
  unfold tailWord_3986789
  simp only [CollatzResearch.WordTrace]
  refine ⟨145410140753551817197939421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96940093835701211465292947 145410140753551817197939421)
  ·
    refine ⟨54528802782581931449227283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145410140753551817197939421 54528802782581931449227283)
    ·
      refine ⟨81793204173872897173840925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54528802782581931449227283 81793204173872897173840925)
      ·
        refine ⟨30672451565202336440190347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81793204173872897173840925 30672451565202336440190347)
        ·
          refine ⟨46008677347803504660285521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30672451565202336440190347 46008677347803504660285521)
          ·
            refine ⟨34506508010852628495214141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46008677347803504660285521 34506508010852628495214141)
            ·
              refine ⟨12939940504069735685705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34506508010852628495214141 12939940504069735685705303)
              ·
                refine ⟨19409910756104603528557955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12939940504069735685705303 19409910756104603528557955)
                ·
                  refine ⟨29114866134156905292836933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19409910756104603528557955 29114866134156905292836933)
                  ·
                    refine ⟨5459037400154419742406925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29114866134156905292836933 5459037400154419742406925)
                    ·
                      refine ⟨2047139025057907403402597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459037400154419742406925 2047139025057907403402597)
                      ·
                        rfl

theorem cell23_3986789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3986789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986789 prefixEnd_3986789 := by exact prefixLift 3986789
  have htrace : WordTrace (prefixWord ++ tailWord_3986789) baseStart_3986789 baseEnd_3986789 := by
    simpa [prefixWord, tailWord_3986789, baseEnd_3986789] using wordTrace_append hprefix tailTrace_3986789
  have hstable : (prefixWord ++ tailWord_3986789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986789).length < 2 ^ (prefixWord ++ tailWord_3986789).sum := by decide
  have hdescent : baseEnd_3986789 < baseStart_3986789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986809 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 6]
def baseStart_3986809 : Nat := 118140960795 + 3986809 * 2 ^ 59
def prefixEnd_3986809 : Nat := 4983230072969 + 3 ^ 40 * 3986809 * 2
def baseEnd_3986809 : Nat := 227461032741221925016945

theorem tailTrace_3986809 : CollatzResearch.WordTrace tailWord_3986809 prefixEnd_3986809 227461032741221925016945 := by
  unfold tailWord_3986809
  simp only [CollatzResearch.WordTrace]
  refine ⟨145410870213479360613667481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96940580142319573742444987 145410870213479360613667481)
  ·
    refine ⟨109058152660109520460250611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145410870213479360613667481 109058152660109520460250611)
    ·
      refine ⟨163587228990164280690375917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109058152660109520460250611 163587228990164280690375917)
      ·
        refine ⟨61345210871311605258890969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163587228990164280690375917 61345210871311605258890969)
        ·
          refine ⟨46008908153483703944168227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61345210871311605258890969 46008908153483703944168227)
          ·
            refine ⟨69013362230225555916252341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46008908153483703944168227 69013362230225555916252341)
            ·
              refine ⟨6470002709083645867148657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69013362230225555916252341 6470002709083645867148657)
              ·
                refine ⟨4852502031812734400361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470002709083645867148657 4852502031812734400361493)
                ·
                  refine ⟨227461032741221925016945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4852502031812734400361493 227461032741221925016945)
                  ·
                    rfl

theorem cell23_3986809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_3986809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986809 prefixEnd_3986809 := by exact prefixLift 3986809
  have htrace : WordTrace (prefixWord ++ tailWord_3986809) baseStart_3986809 baseEnd_3986809 := by
    simpa [prefixWord, tailWord_3986809, baseEnd_3986809] using wordTrace_append hprefix tailTrace_3986809
  have hstable : (prefixWord ++ tailWord_3986809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986809).length < 2 ^ (prefixWord ++ tailWord_3986809).sum := by decide
  have hdescent : baseEnd_3986809 < baseStart_3986809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986812 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3986812 : Nat := 118140960795 + 3986812 * 2 ^ 59
def prefixEnd_3986812 : Nat := 4983230072969 + 3 ^ 40 * 3986812 * 2
def baseEnd_3986812 : Nat := 2047150835112960813414991

theorem tailTrace_3986812 : CollatzResearch.WordTrace tailWord_3986812 prefixEnd_3986812 2047150835112960813414991 := by
  unfold tailWord_3986812
  simp only [CollatzResearch.WordTrace]
  refine ⟨72705489816234246063013345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96940653088312328084017793 72705489816234246063013345)
  ·
    refine ⟨54529117362175684547260009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72705489816234246063013345 54529117362175684547260009)
    ·
      refine ⟨40896838021631763410445007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54529117362175684547260009 40896838021631763410445007)
      ·
        refine ⟨61345257032447645115667511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40896838021631763410445007 61345257032447645115667511)
        ·
          refine ⟨92017885548671467673501267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61345257032447645115667511 92017885548671467673501267)
          ·
            refine ⟨138026828323007201510251901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92017885548671467673501267 138026828323007201510251901)
            ·
              refine ⟨51760060621127700566344463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138026828323007201510251901 51760060621127700566344463)
              ·
                refine ⟨77640090931691550849516695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51760060621127700566344463 77640090931691550849516695)
                ·
                  refine ⟨116460136397537326274275043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77640090931691550849516695 116460136397537326274275043)
                  ·
                    refine ⟨174690204596305989411412565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116460136397537326274275043 174690204596305989411412565)
                    ·
                      refine ⟨2047150835112960813414991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174690204596305989411412565 2047150835112960813414991)
                      ·
                        rfl

theorem cell23_3986812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3986812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986812 prefixEnd_3986812 := by exact prefixLift 3986812
  have htrace : WordTrace (prefixWord ++ tailWord_3986812) baseStart_3986812 baseEnd_3986812 := by
    simpa [prefixWord, tailWord_3986812, baseEnd_3986812] using wordTrace_append hprefix tailTrace_3986812
  have hstable : (prefixWord ++ tailWord_3986812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986812).length < 2 ^ (prefixWord ++ tailWord_3986812).sum := by decide
  have hdescent : baseEnd_3986812 < baseStart_3986812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 1, 1, 3]
def baseStart_3986853 : Nat := 118140960795 + 3986853 * 2 ^ 59
def prefixEnd_3986853 : Nat := 4983230072969 + 3 ^ 40 * 3986853 * 2
def baseEnd_3986853 : Nat := 2047171887819795153002303

theorem tailTrace_3986853 : CollatzResearch.WordTrace tailWord_3986853 prefixEnd_3986853 2047171887819795153002303 := by
  unfold tailWord_3986853
  simp only [CollatzResearch.WordTrace]
  refine ⟨145412475025319956128269213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96941650016879970752179475 145412475025319956128269213)
  ·
    refine ⟨54529678134494983548100955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145412475025319956128269213 54529678134494983548100955)
    ·
      refine ⟨81794517201742475322151433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54529678134494983548100955 81794517201742475322151433)
      ·
        refine ⟨61345887901306856491613575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81794517201742475322151433 61345887901306856491613575)
        ·
          refine ⟨92018831851960284737420363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61345887901306856491613575 92018831851960284737420363)
          ·
            refine ⟨138028247777940427106130545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92018831851960284737420363 138028247777940427106130545)
            ·
              refine ⟨103521185833455320329597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138028247777940427106130545 103521185833455320329597909)
              ·
                refine ⟨2426277792971609070224951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103521185833455320329597909 2426277792971609070224951)
                ·
                  refine ⟨3639416689457413605337427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426277792971609070224951 3639416689457413605337427)
                  ·
                    refine ⟨5459125034186120408006141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3639416689457413605337427 5459125034186120408006141)
                    ·
                      refine ⟨2047171887819795153002303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459125034186120408006141 2047171887819795153002303)
                      ·
                        rfl

theorem cell23_3986853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_3986853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986853 prefixEnd_3986853 := by exact prefixLift 3986853
  have htrace : WordTrace (prefixWord ++ tailWord_3986853) baseStart_3986853 baseEnd_3986853 := by
    simpa [prefixWord, tailWord_3986853, baseEnd_3986853] using wordTrace_append hprefix tailTrace_3986853
  have hstable : (prefixWord ++ tailWord_3986853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986853).length < 2 ^ (prefixWord ++ tailWord_3986853).sum := by decide
  have hdescent : baseEnd_3986853 < baseStart_3986853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986889 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_3986889 : Nat := 118140960795 + 3986889 * 2 ^ 59
def prefixEnd_3986889 : Nat := 4983230072969 + 3 ^ 40 * 3986889 * 2
def baseEnd_3986889 : Nat := 2047190373123357012152137

theorem tailTrace_3986889 : CollatzResearch.WordTrace tailWord_3986889 prefixEnd_3986889 2047190373123357012152137 := by
  unfold tailWord_3986889
  simp only [CollatzResearch.WordTrace]
  refine ⟨145413788053189534276579721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96942525368793022851053147 145413788053189534276579721)
  ·
    refine ⟨109060341039892150707434791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145413788053189534276579721 109060341039892150707434791)
    ·
      refine ⟨163590511559838226061152187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109060341039892150707434791 163590511559838226061152187)
      ·
        refine ⟨245385767339757339091728281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163590511559838226061152187 245385767339757339091728281)
        ·
          refine ⟨184039325504818004318796211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245385767339757339091728281 184039325504818004318796211)
          ·
            refine ⟨276058988257227006478194317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184039325504818004318796211 276058988257227006478194317)
            ·
              refine ⟨103522120596460127429322869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276058988257227006478194317 103522120596460127429322869)
              ·
                refine ⟨9705198805918136946499019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103522120596460127429322869 9705198805918136946499019)
                ·
                  refine ⟨14557798208877205419748529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705198805918136946499019 14557798208877205419748529)
                  ·
                    refine ⟨10918348656657904064811397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14557798208877205419748529 10918348656657904064811397)
                    ·
                      refine ⟨2047190373123357012152137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10918348656657904064811397 2047190373123357012152137)
                      ·
                        rfl

theorem cell23_3986889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_3986889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986889 prefixEnd_3986889 := by exact prefixLift 3986889
  have htrace : WordTrace (prefixWord ++ tailWord_3986889) baseStart_3986889 baseEnd_3986889 := by
    simpa [prefixWord, tailWord_3986889, baseEnd_3986889] using wordTrace_append hprefix tailTrace_3986889
  have hstable : (prefixWord ++ tailWord_3986889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986889).length < 2 ^ (prefixWord ++ tailWord_3986889).sum := by decide
  have hdescent : baseEnd_3986889 < baseStart_3986889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986906 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_3986906 : Nat := 118140960795 + 3986906 * 2 ^ 59
def prefixEnd_3986906 : Nat := 4983230072969 + 3 ^ 40 * 3986906 * 2
def baseEnd_3986906 : Nat := 2047199102294483445639559

theorem tailTrace_3986906 : CollatzResearch.WordTrace tailWord_3986906 prefixEnd_3986906 2047199102294483445639559 := by
  unfold tailWord_3986906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36353602023531986544987143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96942938729418630786632381 36353602023531986544987143)
  ·
    refine ⟨54530403035297979817480715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36353602023531986544987143 54530403035297979817480715)
    ·
      refine ⟨81795604552946969726221073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54530403035297979817480715 81795604552946969726221073)
      ·
        refine ⟨61346703414710227294665805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81795604552946969726221073 61346703414710227294665805)
        ·
          refine ⟨23005013780516335235499677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61346703414710227294665805 23005013780516335235499677)
          ·
            refine ⟨8626880167693625713312379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23005013780516335235499677 8626880167693625713312379)
            ·
              refine ⟨12940320251540438569968569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626880167693625713312379 12940320251540438569968569)
              ·
                refine ⟨9705240188655328927476427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12940320251540438569968569 9705240188655328927476427)
                ·
                  refine ⟨14557860282982993391214641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705240188655328927476427 14557860282982993391214641)
                  ·
                    refine ⟨10918395212237245043410981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14557860282982993391214641 10918395212237245043410981)
                    ·
                      refine ⟨2047199102294483445639559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10918395212237245043410981 2047199102294483445639559)
                      ·
                        rfl

theorem cell23_3986906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_3986906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986906 prefixEnd_3986906 := by exact prefixLift 3986906
  have htrace : WordTrace (prefixWord ++ tailWord_3986906) baseStart_3986906 baseEnd_3986906 := by
    simpa [prefixWord, tailWord_3986906, baseEnd_3986906] using wordTrace_append hprefix tailTrace_3986906
  have hstable : (prefixWord ++ tailWord_3986906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986906).length < 2 ^ (prefixWord ++ tailWord_3986906).sum := by decide
  have hdescent : baseEnd_3986906 < baseStart_3986906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986926 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3986926 : Nat := 118140960795 + 3986926 * 2 ^ 59
def prefixEnd_3986926 : Nat := 4983230072969 + 3 ^ 40 * 3986926 * 2
def baseEnd_3986926 : Nat := 2047209371907573367389467

theorem tailTrace_3986926 : CollatzResearch.WordTrace tailWord_3986926 prefixEnd_3986926 2047209371907573367389467 := by
  unfold tailWord_3986926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18176892194256936199459579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96943425036036993063784421 18176892194256936199459579)
  ·
    refine ⟨27265338291385404299189369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18176892194256936199459579 27265338291385404299189369)
    ·
      refine ⟨20449003718539053224392027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27265338291385404299189369 20449003718539053224392027)
      ·
        refine ⟨30673505577808579836588041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20449003718539053224392027 30673505577808579836588041)
        ·
          refine ⟨23005129183356434877441031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30673505577808579836588041 23005129183356434877441031)
          ·
            refine ⟨34507693775034652316161547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23005129183356434877441031 34507693775034652316161547)
            ·
              refine ⟨51761540662551978474242321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34507693775034652316161547 51761540662551978474242321)
              ·
                refine ⟨38821155496913983855681741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51761540662551978474242321 38821155496913983855681741)
                ·
                  refine ⟨14557933311342743945880653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38821155496913983855681741 14557933311342743945880653)
                  ·
                    refine ⟨5459224991753528979705245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14557933311342743945880653 5459224991753528979705245)
                    ·
                      refine ⟨2047209371907573367389467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459224991753528979705245 2047209371907573367389467)
                      ·
                        rfl

theorem cell23_3986926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3986926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986926 prefixEnd_3986926 := by exact prefixLift 3986926
  have htrace : WordTrace (prefixWord ++ tailWord_3986926) baseStart_3986926 baseEnd_3986926 := by
    simpa [prefixWord, tailWord_3986926, baseEnd_3986926] using wordTrace_append hprefix tailTrace_3986926
  have hstable : (prefixWord ++ tailWord_3986926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986926).length < 2 ^ (prefixWord ++ tailWord_3986926).sum := by decide
  have hdescent : baseEnd_3986926 < baseStart_3986926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986927 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 1, 2, 2]
def baseStart_3986927 : Nat := 118140960795 + 3986927 * 2 ^ 59
def prefixEnd_3986927 : Nat := 4983230072969 + 3 ^ 40 * 3986927 * 2
def baseEnd_3986927 : Nat := 2047209885388227863476963

theorem tailTrace_3986927 : CollatzResearch.WordTrace tailWord_3986927 prefixEnd_3986927 2047209885388227863476963 := by
  unfold tailWord_3986927
  simp only [CollatzResearch.WordTrace]
  refine ⟨145415174027051866766463035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96943449351367911177642023 145415174027051866766463035)
  ·
    refine ⟨218122761040577800149694553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145415174027051866766463035 218122761040577800149694553)
    ·
      refine ⟨163592070780433350112270915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218122761040577800149694553 163592070780433350112270915)
      ·
        refine ⟨245388106170650025168406373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163592070780433350112270915 245388106170650025168406373)
        ·
          refine ⟨46010269906996879719076195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245388106170650025168406373 46010269906996879719076195)
          ·
            refine ⟨69015404860495319578614293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46010269906996879719076195 69015404860495319578614293)
            ·
              refine ⟨3235097102835718105247545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69015404860495319578614293 3235097102835718105247545)
              ·
                refine ⟨2426322827126788578935659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235097102835718105247545 2426322827126788578935659)
                ·
                  refine ⟨3639484240690182868403489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426322827126788578935659 3639484240690182868403489)
                  ·
                    refine ⟨2729613180517637151302617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639484240690182868403489 2729613180517637151302617)
                    ·
                      refine ⟨2047209885388227863476963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729613180517637151302617 2047209885388227863476963)
                      ·
                        rfl

theorem cell23_3986927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 2, 2].length) (baseStart_3986927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986927 prefixEnd_3986927 := by exact prefixLift 3986927
  have htrace : WordTrace (prefixWord ++ tailWord_3986927) baseStart_3986927 baseEnd_3986927 := by
    simpa [prefixWord, tailWord_3986927, baseEnd_3986927] using wordTrace_append hprefix tailTrace_3986927
  have hstable : (prefixWord ++ tailWord_3986927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986927).length < 2 ^ (prefixWord ++ tailWord_3986927).sum := by decide
  have hdescent : baseEnd_3986927 < baseStart_3986927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986929 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_3986929 : Nat := 118140960795 + 3986929 * 2 ^ 59
def prefixEnd_3986929 : Nat := 4983230072969 + 3 ^ 40 * 3986929 * 2
def baseEnd_3986929 : Nat := 682403637449845618550651

theorem tailTrace_3986929 : CollatzResearch.WordTrace tailWord_3986929 prefixEnd_3986929 682403637449845618550651 := by
  unfold tailWord_3986929
  simp only [CollatzResearch.WordTrace]
  refine ⟨145415246973044621108035841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96943497982029747405357227 145415246973044621108035841)
  ·
    refine ⟨109061435229783465831026881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145415246973044621108035841 109061435229783465831026881)
    ·
      refine ⟨81796076422337599373270161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109061435229783465831026881 81796076422337599373270161)
      ·
        refine ⟨61347057316753199529952621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81796076422337599373270161 61347057316753199529952621)
        ·
          refine ⟨23005146493782449823732233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61347057316753199529952621 23005146493782449823732233)
          ·
            refine ⟨17253859870336837367799175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23005146493782449823732233 17253859870336837367799175)
            ·
              refine ⟨25880789805505256051698763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17253859870336837367799175 25880789805505256051698763)
              ·
                refine ⟨38821184708257884077548145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25880789805505256051698763 38821184708257884077548145)
                ·
                  refine ⟨29115888531193413058161109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38821184708257884077548145 29115888531193413058161109)
                  ·
                    refine ⟨682403637449845618550651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29115888531193413058161109 682403637449845618550651)
                    ·
                      rfl

theorem cell23_3986929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_3986929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986929 prefixEnd_3986929 := by exact prefixLift 3986929
  have htrace : WordTrace (prefixWord ++ tailWord_3986929) baseStart_3986929 baseEnd_3986929 := by
    simpa [prefixWord, tailWord_3986929, baseEnd_3986929] using wordTrace_append hprefix tailTrace_3986929
  have hstable : (prefixWord ++ tailWord_3986929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986929).length < 2 ^ (prefixWord ++ tailWord_3986929).sum := by decide
  have hdescent : baseEnd_3986929 < baseStart_3986929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986933 : List Nat := [1, 3, 5, 1, 1, 3, 1, 8]
def baseStart_3986933 : Nat := 118140960795 + 3986933 * 2 ^ 59
def prefixEnd_3986933 : Nat := 4983230072969 + 3 ^ 40 * 3986933 * 2
def baseEnd_3986933 : Nat := 75822702454524253333405

theorem tailTrace_3986933 : CollatzResearch.WordTrace tailWord_3986933 prefixEnd_3986933 75822702454524253333405 := by
  unfold tailWord_3986933
  simp only [CollatzResearch.WordTrace]
  refine ⟨145415392865030129791181453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96943595243353419860787635 145415392865030129791181453)
  ·
    refine ⟨54530772324386298671693045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145415392865030129791181453 54530772324386298671693045)
    ·
      refine ⟨5112259905411215500471223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54530772324386298671693045 5112259905411215500471223)
      ·
        refine ⟨7668389858116823250706835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112259905411215500471223 7668389858116823250706835)
        ·
          refine ⟨11502584787175234876060253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668389858116823250706835 11502584787175234876060253)
          ·
            refine ⟨4313469295190713078522595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11502584787175234876060253 4313469295190713078522595)
            ·
              refine ⟨6470203942786069617783893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313469295190713078522595 6470203942786069617783893)
              ·
                refine ⟨75822702454524253333405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6470203942786069617783893 75822702454524253333405)
                ·
                  rfl

theorem cell23_3986933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 8].length) (baseStart_3986933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986933 prefixEnd_3986933 := by exact prefixLift 3986933
  have htrace : WordTrace (prefixWord ++ tailWord_3986933) baseStart_3986933 baseEnd_3986933 := by
    simpa [prefixWord, tailWord_3986933, baseEnd_3986933] using wordTrace_append hprefix tailTrace_3986933
  have hstable : (prefixWord ++ tailWord_3986933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986933).length < 2 ^ (prefixWord ++ tailWord_3986933).sum := by decide
  have hdescent : baseEnd_3986933 < baseStart_3986933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986949 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3986949 : Nat := 118140960795 + 3986949 * 2 ^ 59
def prefixEnd_3986949 : Nat := 4983230072969 + 3 ^ 40 * 3986949 * 2
def baseEnd_3986949 : Nat := 2047221181962626777401861

theorem tailTrace_3986949 : CollatzResearch.WordTrace tailWord_3986949 prefixEnd_3986949 2047221181962626777401861 := by
  unfold tailWord_3986949
  simp only [CollatzResearch.WordTrace]
  refine ⟨145415976432972164523763901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96943984288648109682509267 145415976432972164523763901)
  ·
    refine ⟨54530991162364561696411463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145415976432972164523763901 54530991162364561696411463)
    ·
      refine ⟨81796486743546842544617195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54530991162364561696411463 81796486743546842544617195)
      ·
        refine ⟨122694730115320263816925793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81796486743546842544617195 122694730115320263816925793)
        ·
          refine ⟨92021047586490197862694345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122694730115320263816925793 92021047586490197862694345)
          ·
            refine ⟨69015785689867648397020759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92021047586490197862694345 69015785689867648397020759)
            ·
              refine ⟨103523678534801472595531139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69015785689867648397020759 103523678534801472595531139)
              ·
                refine ⟨155285517802202208893296709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103523678534801472595531139 155285517802202208893296709)
                ·
                  refine ⟨29116034587912914167493133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155285517802202208893296709 29116034587912914167493133)
                  ·
                    refine ⟨10918512970467342812809925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29116034587912914167493133 10918512970467342812809925)
                    ·
                      refine ⟨2047221181962626777401861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10918512970467342812809925 2047221181962626777401861)
                      ·
                        rfl

theorem cell23_3986949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3986949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986949 prefixEnd_3986949 := by exact prefixLift 3986949
  have htrace : WordTrace (prefixWord ++ tailWord_3986949) baseStart_3986949 baseEnd_3986949 := by
    simpa [prefixWord, tailWord_3986949, baseEnd_3986949] using wordTrace_append hprefix tailTrace_3986949
  have hstable : (prefixWord ++ tailWord_3986949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986949).length < 2 ^ (prefixWord ++ tailWord_3986949).sum := by decide
  have hdescent : baseEnd_3986949 < baseStart_3986949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986953 : List Nat := [1, 2, 1, 1, 3, 1, 4, 4, 1, 3, 2]
def baseStart_3986953 : Nat := 118140960795 + 3986953 * 2 ^ 59
def prefixEnd_3986953 : Nat := 4983230072969 + 3 ^ 40 * 3986953 * 2
def baseEnd_3986953 : Nat := 2047223235885244761751843

theorem tailTrace_3986953 : CollatzResearch.WordTrace tailWord_3986953 prefixEnd_3986953 2047223235885244761751843 := by
  unfold tailWord_3986953
  simp only [CollatzResearch.WordTrace]
  refine ⟨145416122324957673206909513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96944081549971782137939675 145416122324957673206909513)
  ·
    refine ⟨109062091743718254905182135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145416122324957673206909513 109062091743718254905182135)
    ·
      refine ⟨163593137615577382357773203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109062091743718254905182135 163593137615577382357773203)
      ·
        refine ⟨245389706423366073536659805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163593137615577382357773203 245389706423366073536659805)
        ·
          refine ⟨92021139908762277576247427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245389706423366073536659805 92021139908762277576247427)
          ·
            refine ⟨138031709863143416364371141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92021139908762277576247427 138031709863143416364371141)
            ·
              refine ⟨25880945599339390568319589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138031709863143416364371141 25880945599339390568319589)
              ·
                refine ⟨4852677299876135731559923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25880945599339390568319589 4852677299876135731559923)
                ·
                  refine ⟨7279015949814203597339885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852677299876135731559923 7279015949814203597339885)
                  ·
                    refine ⟨2729630981180326349002457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7279015949814203597339885 2729630981180326349002457)
                    ·
                      refine ⟨2047223235885244761751843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729630981180326349002457 2047223235885244761751843)
                      ·
                        rfl

theorem cell23_3986953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3, 2].length) (baseStart_3986953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986953 prefixEnd_3986953 := by exact prefixLift 3986953
  have htrace : WordTrace (prefixWord ++ tailWord_3986953) baseStart_3986953 baseEnd_3986953 := by
    simpa [prefixWord, tailWord_3986953, baseEnd_3986953] using wordTrace_append hprefix tailTrace_3986953
  have hstable : (prefixWord ++ tailWord_3986953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986953).length < 2 ^ (prefixWord ++ tailWord_3986953).sum := by decide
  have hdescent : baseEnd_3986953 < baseStart_3986953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986964 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3986964 : Nat := 118140960795 + 3986964 * 2 ^ 59
def prefixEnd_3986964 : Nat := 4983230072969 + 3 ^ 40 * 3986964 * 2
def baseEnd_3986964 : Nat := 2047228884172444218714293

theorem tailTrace_3986964 : CollatzResearch.WordTrace tailWord_3986964 prefixEnd_3986964 2047228884172444218714293 := by
  unfold tailWord_3986964
  simp only [CollatzResearch.WordTrace]
  refine ⟨72708261763958911042779973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96944349018611881390373297 72708261763958911042779973)
  ·
    refine ⟨13632799080742295820521245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72708261763958911042779973 13632799080742295820521245)
    ·
      refine ⟨5112299655278360932695467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13632799080742295820521245 5112299655278360932695467)
      ·
        refine ⟨7668449482917541399043201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112299655278360932695467 7668449482917541399043201)
        ·
          refine ⟨5751337112188156049282401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668449482917541399043201 5751337112188156049282401)
          ·
            refine ⟨4313502834141117036961801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751337112188156049282401 4313502834141117036961801)
            ·
              refine ⟨3235127125605837777721351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4313502834141117036961801 3235127125605837777721351)
              ·
                refine ⟨4852690688408756666582027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235127125605837777721351 4852690688408756666582027)
                ·
                  refine ⟨7279036032613134999873041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852690688408756666582027 7279036032613134999873041)
                  ·
                    refine ⟨5459277024459851249904781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7279036032613134999873041 5459277024459851249904781)
                    ·
                      refine ⟨2047228884172444218714293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459277024459851249904781 2047228884172444218714293)
                      ·
                        rfl

theorem cell23_3986964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3986964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986964 prefixEnd_3986964 := by exact prefixLift 3986964
  have htrace : WordTrace (prefixWord ++ tailWord_3986964) baseStart_3986964 baseEnd_3986964 := by
    simpa [prefixWord, tailWord_3986964, baseEnd_3986964] using wordTrace_append hprefix tailTrace_3986964
  have hstable : (prefixWord ++ tailWord_3986964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986964).length < 2 ^ (prefixWord ++ tailWord_3986964).sum := by decide
  have hdescent : baseEnd_3986964 < baseStart_3986964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3986976 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_3986976 : Nat := 118140960795 + 3986976 * 2 ^ 59
def prefixEnd_3986976 : Nat := 4983230072969 + 3 ^ 40 * 3986976 * 2
def baseEnd_3986976 : Nat := 682411681980099390588079

theorem tailTrace_3986976 : CollatzResearch.WordTrace tailWord_3986976 prefixEnd_3986976 682411681980099390588079 := by
  unfold tailWord_3986976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72708480601937174067498391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96944640802582898756664521 72708480601937174067498391)
  ·
    refine ⟨109062720902905761101247587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72708480601937174067498391 109062720902905761101247587)
    ·
      refine ⟨163594081354358641651871381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109062720902905761101247587 163594081354358641651871381)
      ·
        refine ⟨7668472563485561327431471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163594081354358641651871381 7668472563485561327431471)
        ·
          refine ⟨11502708845228341991147207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668472563485561327431471 11502708845228341991147207)
          ·
            refine ⟨17254063267842512986720811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11502708845228341991147207 17254063267842512986720811)
            ·
              refine ⟨25881094901763769480081217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254063267842512986720811 25881094901763769480081217)
              ·
                refine ⟨19410821176322827110060913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25881094901763769480081217 19410821176322827110060913)
                ·
                  refine ⟨14558115882242120332545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19410821176322827110060913 14558115882242120332545685)
                  ·
                    refine ⟨682411681980099390588079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14558115882242120332545685 682411681980099390588079)
                    ·
                      rfl

theorem cell23_3986976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_3986976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3986976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3986976 prefixEnd_3986976 := by exact prefixLift 3986976
  have htrace : WordTrace (prefixWord ++ tailWord_3986976) baseStart_3986976 baseEnd_3986976 := by
    simpa [prefixWord, tailWord_3986976, baseEnd_3986976] using wordTrace_append hprefix tailTrace_3986976
  have hstable : (prefixWord ++ tailWord_3986976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3986976).length < 2 ^ (prefixWord ++ tailWord_3986976).sum := by decide
  have hdescent : baseEnd_3986976 < baseStart_3986976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3986976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987000 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_3987000 : Nat := 118140960795 + 3987000 * 2 ^ 59
def prefixEnd_3987000 : Nat := 4983230072969 + 3 ^ 40 * 3987000 * 2
def baseEnd_3987000 : Nat := 2047247369476006077864127

theorem tailTrace_3987000 : CollatzResearch.WordTrace tailWord_3987000 prefixEnd_3987000 2047247369476006077864127 := by
  unfold tailWord_3987000
  simp only [CollatzResearch.WordTrace]
  refine ⟨72708918277893700116935227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96945224370524933489246969 72708918277893700116935227)
  ·
    refine ⟨109063377416840550175402841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72708918277893700116935227 109063377416840550175402841)
    ·
      refine ⟨81797533062630412631552131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109063377416840550175402841 81797533062630412631552131)
      ·
        refine ⟨122696299593945618947328197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81797533062630412631552131 122696299593945618947328197)
        ·
          refine ⟨23005556173864803552624037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122696299593945618947328197 23005556173864803552624037)
          ·
            refine ⟨4313541782599650666117007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23005556173864803552624037 4313541782599650666117007)
            ·
              refine ⟨6470312673899475999175511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313541782599650666117007 6470312673899475999175511)
              ·
                refine ⟨9705469010849213998763267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6470312673899475999175511 9705469010849213998763267)
                ·
                  refine ⟨14558203516273820998144901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9705469010849213998763267 14558203516273820998144901)
                  ·
                    refine ⟨2729663159301341437152169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14558203516273820998144901 2729663159301341437152169)
                    ·
                      refine ⟨2047247369476006077864127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729663159301341437152169 2047247369476006077864127)
                      ·
                        rfl

theorem cell23_3987000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_3987000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987000 prefixEnd_3987000 := by exact prefixLift 3987000
  have htrace : WordTrace (prefixWord ++ tailWord_3987000) baseStart_3987000 baseEnd_3987000 := by
    simpa [prefixWord, tailWord_3987000, baseEnd_3987000] using wordTrace_append hprefix tailTrace_3987000
  have hstable : (prefixWord ++ tailWord_3987000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987000).length < 2 ^ (prefixWord ++ tailWord_3987000).sum := by decide
  have hdescent : baseEnd_3987000 < baseStart_3987000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3987039 : Nat := 118140960795 + 3987039 * 2 ^ 59
def prefixEnd_3987039 : Nat := 4983230072969 + 3 ^ 40 * 3987039 * 2
def baseEnd_3987039 : Nat := 2047267395221531425276447

theorem tailTrace_3987039 : CollatzResearch.WordTrace tailWord_3987039 prefixEnd_3987039 2047267395221531425276447 := by
  unfold tailWord_3987039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145419259002646109894540171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96946172668430739929693447 145419259002646109894540171)
  ·
    refine ⟨218128888503969164841810257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145419259002646109894540171 218128888503969164841810257)
    ·
      refine ⟨163596666377976873631357693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218128888503969164841810257 163596666377976873631357693)
      ·
        refine ⟨61348749891741327611759135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163596666377976873631357693 61348749891741327611759135)
        ·
          refine ⟨92023124837611991417638703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61348749891741327611759135 92023124837611991417638703)
          ·
            refine ⟨138034687256417987126458055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92023124837611991417638703 138034687256417987126458055)
            ·
              refine ⟨207052030884626980689687083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138034687256417987126458055 207052030884626980689687083)
              ·
                refine ⟨310578046326940471034530625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207052030884626980689687083 310578046326940471034530625)
                ·
                  refine ⟨232933534745205353275897969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310578046326940471034530625 232933534745205353275897969)
                  ·
                    refine ⟨174700151058904014956923477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232933534745205353275897969 174700151058904014956923477)
                    ·
                      refine ⟨2047267395221531425276447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174700151058904014956923477 2047267395221531425276447)
                      ·
                        rfl

theorem cell23_3987039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3987039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987039 prefixEnd_3987039 := by exact prefixLift 3987039
  have htrace : WordTrace (prefixWord ++ tailWord_3987039) baseStart_3987039 baseEnd_3987039 := by
    simpa [prefixWord, tailWord_3987039, baseEnd_3987039] using wordTrace_append hprefix tailTrace_3987039
  have hstable : (prefixWord ++ tailWord_3987039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987039).length < 2 ^ (prefixWord ++ tailWord_3987039).sum := by decide
  have hdescent : baseEnd_3987039 < baseStart_3987039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987059 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_3987059 : Nat := 118140960795 + 3987059 * 2 ^ 59
def prefixEnd_3987059 : Nat := 4983230072969 + 3 ^ 40 * 3987059 * 2
def baseEnd_3987059 : Nat := 2047277664834621347026355

theorem tailTrace_3987059 : CollatzResearch.WordTrace tailWord_3987059 prefixEnd_3987059 2047277664834621347026355 := by
  unfold tailWord_3987059
  simp only [CollatzResearch.WordTrace]
  refine ⟨145419988462573653310268231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96946658975049102206845487 145419988462573653310268231)
  ·
    refine ⟨218129982693860479965402347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145419988462573653310268231 218129982693860479965402347)
    ·
      refine ⟨327194974040790719948103521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218129982693860479965402347 327194974040790719948103521)
      ·
        refine ⟨245396230530593039961077641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327194974040790719948103521 245396230530593039961077641)
        ·
          refine ⟨184047172897944779970808231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245396230530593039961077641 184047172897944779970808231)
          ·
            refine ⟨276070759346917169956212347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184047172897944779970808231 276070759346917169956212347)
            ·
              refine ⟨414106139020375754934318521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276070759346917169956212347 414106139020375754934318521)
              ·
                refine ⟨310579604265281816200738891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414106139020375754934318521 310579604265281816200738891)
                ·
                  refine ⟨465869406397922724301108337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310579604265281816200738891 465869406397922724301108337)
                  ·
                    refine ⟨349402054798442043225831253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465869406397922724301108337 349402054798442043225831253)
                    ·
                      refine ⟨2047277664834621347026355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 349402054798442043225831253 2047277664834621347026355)
                      ·
                        rfl

theorem cell23_3987059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_3987059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987059 prefixEnd_3987059 := by exact prefixLift 3987059
  have htrace : WordTrace (prefixWord ++ tailWord_3987059) baseStart_3987059 baseEnd_3987059 := by
    simpa [prefixWord, tailWord_3987059, baseEnd_3987059] using wordTrace_append hprefix tailTrace_3987059
  have hstable : (prefixWord ++ tailWord_3987059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987059).length < 2 ^ (prefixWord ++ tailWord_3987059).sum := by decide
  have hdescent : baseEnd_3987059 < baseStart_3987059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987073 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3987073 : Nat := 118140960795 + 3987073 * 2 ^ 59
def prefixEnd_3987073 : Nat := 4983230072969 + 3 ^ 40 * 3987073 * 2
def baseEnd_3987073 : Nat := 2047284853563784292251291

theorem tailTrace_3987073 : CollatzResearch.WordTrace tailWord_3987073 prefixEnd_3987073 2047284853563784292251291 := by
  unfold tailWord_3987073
  simp only [CollatzResearch.WordTrace]
  refine ⟨145420499084522933701277873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96946999389681955800851915 145420499084522933701277873)
  ·
    refine ⟨109065374313392200275958405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145420499084522933701277873 109065374313392200275958405)
    ·
      refine ⟨20449757683761037551742201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109065374313392200275958405 20449757683761037551742201)
      ·
        refine ⟨15337318262820778163806651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20449757683761037551742201 15337318262820778163806651)
        ·
          refine ⟨23005977394231167245709977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337318262820778163806651 23005977394231167245709977)
          ·
            refine ⟨17254483045673375434282483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23005977394231167245709977 17254483045673375434282483)
            ·
              refine ⟨25881724568510063151423725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254483045673375434282483 25881724568510063151423725)
              ·
                refine ⟨9705646713191273681783897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25881724568510063151423725 9705646713191273681783897)
                ·
                  refine ⟨7279235034893455261337923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9705646713191273681783897 7279235034893455261337923)
                  ·
                    refine ⟨10918852552340182892006885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279235034893455261337923 10918852552340182892006885)
                    ·
                      refine ⟨2047284853563784292251291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10918852552340182892006885 2047284853563784292251291)
                      ·
                        rfl

theorem cell23_3987073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3987073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987073 prefixEnd_3987073 := by exact prefixLift 3987073
  have htrace : WordTrace (prefixWord ++ tailWord_3987073) baseStart_3987073 baseEnd_3987073 := by
    simpa [prefixWord, tailWord_3987073, baseEnd_3987073] using wordTrace_append hprefix tailTrace_3987073
  have hstable : (prefixWord ++ tailWord_3987073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987073).length < 2 ^ (prefixWord ++ tailWord_3987073).sum := by decide
  have hdescent : baseEnd_3987073 < baseStart_3987073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987140 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3987140 : Nat := 118140960795 + 3987140 * 2 ^ 59
def prefixEnd_3987140 : Nat := 4983230072969 + 3 ^ 40 * 3987140 * 2
def baseEnd_3987140 : Nat := 2047319256767635530113483

theorem tailTrace_3987140 : CollatzResearch.WordTrace tailWord_3987140 prefixEnd_3987140 2047319256767635530113483 := by
  unfold tailWord_3987140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72711471387640102071983437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96948628516853469429311249 72711471387640102071983437)
  ·
    refine ⟨27266801770365038276993789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72711471387640102071983437 27266801770365038276993789)
    ·
      refine ⟨10225050663886889353872671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27266801770365038276993789 10225050663886889353872671)
      ·
        refine ⟨15337575995830334030809007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10225050663886889353872671 15337575995830334030809007)
        ·
          refine ⟨23006363993745501046213511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337575995830334030809007 23006363993745501046213511)
          ·
            refine ⟨34509545990618251569320267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23006363993745501046213511 34509545990618251569320267)
            ·
              refine ⟨51764318985927377353980401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34509545990618251569320267 51764318985927377353980401)
              ·
                refine ⟨38823239239445533015485301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51764318985927377353980401 38823239239445533015485301)
                ·
                  refine ⟨3639678678698018720201747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38823239239445533015485301 3639678678698018720201747)
                  ·
                    refine ⟨5459518018047028080302621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3639678678698018720201747 5459518018047028080302621)
                    ·
                      refine ⟨2047319256767635530113483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459518018047028080302621 2047319256767635530113483)
                      ·
                        rfl

theorem cell23_3987140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3987140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987140 prefixEnd_3987140 := by exact prefixLift 3987140
  have htrace : WordTrace (prefixWord ++ tailWord_3987140) baseStart_3987140 baseEnd_3987140 := by
    simpa [prefixWord, tailWord_3987140, baseEnd_3987140] using wordTrace_append hprefix tailTrace_3987140
  have hstable : (prefixWord ++ tailWord_3987140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987140).length < 2 ^ (prefixWord ++ tailWord_3987140).sum := by decide
  have hdescent : baseEnd_3987140 < baseStart_3987140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987143 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 1, 5]
def baseStart_3987143 : Nat := 118140960795 + 3987143 * 2 ^ 59
def prefixEnd_3987143 : Nat := 4983230072969 + 3 ^ 40 * 3987143 * 2
def baseEnd_3987143 : Nat := 682440265736533006125323

theorem tailTrace_3987143 : CollatzResearch.WordTrace tailWord_3987143 prefixEnd_3987143 682440265736533006125323 := by
  unfold tailWord_3987143
  simp only [CollatzResearch.WordTrace]
  refine ⟨145423052194269335656326083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96948701462846223770884055 145423052194269335656326083)
  ·
    refine ⟨218134578291404003484489125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145423052194269335656326083 218134578291404003484489125)
    ·
      refine ⟨40900233429638250653341711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218134578291404003484489125 40900233429638250653341711)
      ·
        refine ⟨61350350144457375980012567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40900233429638250653341711 61350350144457375980012567)
        ·
          refine ⟨92025525216686063970018851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61350350144457375980012567 92025525216686063970018851)
          ·
            refine ⟨138038287825029095955028277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92025525216686063970018851 138038287825029095955028277)
            ·
              refine ⟨12941089483596477745783901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138038287825029095955028277 12941089483596477745783901)
              ·
                refine ⟨4852908556348679154668963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12941089483596477745783901 4852908556348679154668963)
                ·
                  refine ⟨7279362834523018732003445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4852908556348679154668963 7279362834523018732003445)
                  ·
                    refine ⟨682440265736533006125323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7279362834523018732003445 682440265736533006125323)
                    ·
                      rfl

theorem cell23_3987143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_3987143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987143 prefixEnd_3987143 := by exact prefixLift 3987143
  have htrace : WordTrace (prefixWord ++ tailWord_3987143) baseStart_3987143 baseEnd_3987143 := by
    simpa [prefixWord, tailWord_3987143, baseEnd_3987143] using wordTrace_append hprefix tailTrace_3987143
  have hstable : (prefixWord ++ tailWord_3987143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987143).length < 2 ^ (prefixWord ++ tailWord_3987143).sum := by decide
  have hdescent : baseEnd_3987143 < baseStart_3987143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987150 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_3987150 : Nat := 118140960795 + 3987150 * 2 ^ 59
def prefixEnd_3987150 : Nat := 4983230072969 + 3 ^ 40 * 3987150 * 2
def baseEnd_3987150 : Nat := 2047324391574180490988437

theorem tailTrace_3987150 : CollatzResearch.WordTrace tailWord_3987150 prefixEnd_3987150 2047324391574180490988437 := by
  unfold tailWord_3987150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177913438155496981478863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96948871670162650567887269 18177913438155496981478863)
  ·
    refine ⟨27266870157233245472218295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18177913438155496981478863 27266870157233245472218295)
    ·
      refine ⟨40900305235849868208327443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27266870157233245472218295 40900305235849868208327443)
      ·
        refine ⟨61350457853774802312491165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40900305235849868208327443 61350457853774802312491165)
        ·
          refine ⟨23006421695165550867184187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61350457853774802312491165 23006421695165550867184187)
          ·
            refine ⟨34509632542748326300776281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23006421695165550867184187 34509632542748326300776281)
            ·
              refine ⟨25882224407061244725582211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34509632542748326300776281 25882224407061244725582211)
              ·
                refine ⟨38823336610591867088373317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25882224407061244725582211 38823336610591867088373317)
                ·
                  refine ⟨7279375614485975079069997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38823336610591867088373317 7279375614485975079069997)
                  ·
                    refine ⟨2729765855432240654651249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7279375614485975079069997 2729765855432240654651249)
                    ·
                      refine ⟨2047324391574180490988437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729765855432240654651249 2047324391574180490988437)
                      ·
                        rfl

theorem cell23_3987150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_3987150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987150 prefixEnd_3987150 := by exact prefixLift 3987150
  have htrace : WordTrace (prefixWord ++ tailWord_3987150) baseStart_3987150 baseEnd_3987150 := by
    simpa [prefixWord, tailWord_3987150, baseEnd_3987150] using wordTrace_append hprefix tailTrace_3987150
  have hstable : (prefixWord ++ tailWord_3987150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987150).length < 2 ^ (prefixWord ++ tailWord_3987150).sum := by decide
  have hdescent : baseEnd_3987150 < baseStart_3987150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987190 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3987190 : Nat := 118140960795 + 3987190 * 2 ^ 59
def prefixEnd_3987190 : Nat := 4983230072969 + 3 ^ 40 * 3987190 * 2
def baseEnd_3987190 : Nat := 682448310266786778162751

theorem tailTrace_3987190 : CollatzResearch.WordTrace tailWord_3987190 prefixEnd_3987190 682448310266786778162751 := by
  unfold tailWord_3987190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9089047901568691417705439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96949844283399375122191349 9089047901568691417705439)
  ·
    refine ⟨13633571852353037126558159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9089047901568691417705439 13633571852353037126558159)
    ·
      refine ⟨20450357778529555689837239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633571852353037126558159 20450357778529555689837239)
      ·
        refine ⟨30675536667794333534755859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20450357778529555689837239 30675536667794333534755859)
        ·
          refine ⟨46013305001691500302133789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675536667794333534755859 46013305001691500302133789)
          ·
            refine ⟨17254989375634312613300171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46013305001691500302133789 17254989375634312613300171)
            ·
              refine ⟨25882484063451468919950257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17254989375634312613300171 25882484063451468919950257)
              ·
                refine ⟨19411863047588601689962693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25882484063451468919950257 19411863047588601689962693)
                ·
                  refine ⟨3639724321422862816868005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19411863047588601689962693 3639724321422862816868005)
                  ·
                    refine ⟨682448310266786778162751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639724321422862816868005 682448310266786778162751)
                    ·
                      rfl

theorem cell23_3987190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3987190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987190 prefixEnd_3987190 := by exact prefixLift 3987190
  have htrace : WordTrace (prefixWord ++ tailWord_3987190) baseStart_3987190 baseEnd_3987190 := by
    simpa [prefixWord, tailWord_3987190, baseEnd_3987190] using wordTrace_append hprefix tailTrace_3987190
  have hstable : (prefixWord ++ tailWord_3987190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987190).length < 2 ^ (prefixWord ++ tailWord_3987190).sum := by decide
  have hdescent : baseEnd_3987190 < baseStart_3987190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987214 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3987214 : Nat := 118140960795 + 3987214 * 2 ^ 59
def prefixEnd_3987214 : Nat := 4983230072969 + 3 ^ 40 * 3987214 * 2
def baseEnd_3987214 : Nat := 2047357254336068240588143

theorem tailTrace_3987214 : CollatzResearch.WordTrace tailWord_3987214 prefixEnd_3987214 2047357254336068240588143 := by
  unfold tailWord_3987214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178205222126514347770087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96950427851341409854773797 18178205222126514347770087)
  ·
    refine ⟨27267307833189771521655131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18178205222126514347770087 27267307833189771521655131)
    ·
      refine ⟨40900961749784657282482697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27267307833189771521655131 40900961749784657282482697)
      ·
        refine ⟨30675721312338492961862023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40900961749784657282482697 30675721312338492961862023)
        ·
          refine ⟨46013581968507739442793035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30675721312338492961862023 46013581968507739442793035)
          ·
            refine ⟨69020372952761609164189553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46013581968507739442793035 69020372952761609164189553)
            ·
              refine ⟨51765279714571206873142165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69020372952761609164189553 51765279714571206873142165)
              ·
                refine ⟨2426497486620525322178539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51765279714571206873142165 2426497486620525322178539)
                ·
                  refine ⟨3639746229930787983267809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426497486620525322178539 3639746229930787983267809)
                  ·
                    refine ⟨2729809672448090987450857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639746229930787983267809 2729809672448090987450857)
                    ·
                      refine ⟨2047357254336068240588143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729809672448090987450857 2047357254336068240588143)
                      ·
                        rfl

theorem cell23_3987214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3987214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987214 prefixEnd_3987214 := by exact prefixLift 3987214
  have htrace : WordTrace (prefixWord ++ tailWord_3987214) baseStart_3987214 baseEnd_3987214 := by
    simpa [prefixWord, tailWord_3987214, baseEnd_3987214] using wordTrace_append hprefix tailTrace_3987214
  have hstable : (prefixWord ++ tailWord_3987214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987214).length < 2 ^ (prefixWord ++ tailWord_3987214).sum := by decide
  have hdescent : baseEnd_3987214 < baseStart_3987214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987273 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_3987273 : Nat := 118140960795 + 3987273 * 2 ^ 59
def prefixEnd_3987273 : Nat := 4983230072969 + 3 ^ 40 * 3987273 * 2
def baseEnd_3987273 : Nat := 2047387549694683509750371

theorem tailTrace_3987273 : CollatzResearch.WordTrace tailWord_3987273 prefixEnd_3987273 2047387549694683509750371 := by
  unfold tailWord_3987273
  simp only [CollatzResearch.WordTrace]
  refine ⟨145427793683798367858558473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96951862455865578572372315 145427793683798367858558473)
  ·
    refine ⟨109070845262848775893918855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145427793683798367858558473 109070845262848775893918855)
    ·
      refine ⟨163606267894273163840878283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109070845262848775893918855 163606267894273163840878283)
      ·
        refine ⟨245409401841409745761317425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163606267894273163840878283 245409401841409745761317425)
        ·
          refine ⟨184057051381057309320988069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245409401841409745761317425 184057051381057309320988069)
          ·
            refine ⟨34510697133948245497685263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184057051381057309320988069 34510697133948245497685263)
            ·
              refine ⟨51766045700922368246527895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34510697133948245497685263 51766045700922368246527895)
              ·
                refine ⟨77649068551383552369791843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51766045700922368246527895 77649068551383552369791843)
                ·
                  refine ⟨116473602827075328554687765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77649068551383552369791843 116473602827075328554687765)
                  ·
                    refine ⟨5459700132519156026000989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116473602827075328554687765 5459700132519156026000989)
                    ·
                      refine ⟨2047387549694683509750371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5459700132519156026000989 2047387549694683509750371)
                      ·
                        rfl

theorem cell23_3987273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_3987273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987273 prefixEnd_3987273 := by exact prefixLift 3987273
  have htrace : WordTrace (prefixWord ++ tailWord_3987273) baseStart_3987273 baseEnd_3987273 := by
    simpa [prefixWord, tailWord_3987273, baseEnd_3987273] using wordTrace_append hprefix tailTrace_3987273
  have hstable : (prefixWord ++ tailWord_3987273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987273).length < 2 ^ (prefixWord ++ tailWord_3987273).sum := by decide
  have hdescent : baseEnd_3987273 < baseStart_3987273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987323 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 4, 5]
def baseStart_3987323 : Nat := 118140960795 + 3987323 * 2 ^ 59
def prefixEnd_3987323 : Nat := 4983230072969 + 3 ^ 40 * 3987323 * 2
def baseEnd_3987323 : Nat := 682471074575802771375047

theorem tailTrace_3987323 : CollatzResearch.WordTrace tailWord_3987323 prefixEnd_3987323 682471074575802771375047 := by
  unfold tailWord_3987323
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429617333617226397878623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96953078222411484265252415 145429617333617226397878623)
  ·
    refine ⟨218144426000425839596817935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145429617333617226397878623 218144426000425839596817935)
    ·
      refine ⟨327216639000638759395226903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218144426000425839596817935 327216639000638759395226903)
      ·
        refine ⟨490824958500958139092840355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327216639000638759395226903 490824958500958139092840355)
        ·
          refine ⟨736237437751437208639260533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490824958500958139092840355 736237437751437208639260533)
          ·
            refine ⟨69022259789197238309930675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 736237437751437208639260533 69022259789197238309930675)
            ·
              refine ⟨103533389683795857464896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69022259789197238309930675 103533389683795857464896013)
              ·
                refine ⟨38825021131423446549336005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103533389683795857464896013 38825021131423446549336005)
                ·
                  refine ⟨7279691462141896228000501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38825021131423446549336005 7279691462141896228000501)
                  ·
                    refine ⟨682471074575802771375047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7279691462141896228000501 682471074575802771375047)
                    ·
                      rfl

theorem cell23_3987323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 5].length) (baseStart_3987323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987323 prefixEnd_3987323 := by exact prefixLift 3987323
  have htrace : WordTrace (prefixWord ++ tailWord_3987323) baseStart_3987323 baseEnd_3987323 := by
    simpa [prefixWord, tailWord_3987323, baseEnd_3987323] using wordTrace_append hprefix tailTrace_3987323
  have hstable : (prefixWord ++ tailWord_3987323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987323).length < 2 ^ (prefixWord ++ tailWord_3987323).sum := by decide
  have hdescent : baseEnd_3987323 < baseStart_3987323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987333 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3987333 : Nat := 118140960795 + 3987333 * 2 ^ 59
def prefixEnd_3987333 : Nat := 4983230072969 + 3 ^ 40 * 3987333 * 2
def baseEnd_3987333 : Nat := 2047418358533953275000095

theorem tailTrace_3987333 : CollatzResearch.WordTrace tailWord_3987333 prefixEnd_3987333 2047418358533953275000095 := by
  unfold tailWord_3987333
  simp only [CollatzResearch.WordTrace]
  refine ⟨145429982063580998105742653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96953321375720665403828435 145429982063580998105742653)
  ·
    refine ⟨54536243273842874289653495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145429982063580998105742653 54536243273842874289653495)
    ·
      refine ⟨81804364910764311434480243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54536243273842874289653495 81804364910764311434480243)
      ·
        refine ⟨122706547366146467151720365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81804364910764311434480243 122706547366146467151720365)
        ·
          refine ⟨46014955262304925181895137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122706547366146467151720365 46014955262304925181895137)
          ·
            refine ⟨34511216446728693886421353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46014955262304925181895137 34511216446728693886421353)
            ·
              refine ⟨25883412335046520414816015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34511216446728693886421353 25883412335046520414816015)
              ·
                refine ⟨38825118502569780622224023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25883412335046520414816015 38825118502569780622224023)
                ·
                  refine ⟨58237677753854670933336035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38825118502569780622224023 58237677753854670933336035)
                  ·
                    refine ⟨87356516630782006400004053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58237677753854670933336035 87356516630782006400004053)
                    ·
                      refine ⟨2047418358533953275000095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87356516630782006400004053 2047418358533953275000095)
                      ·
                        rfl

theorem cell23_3987333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3987333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987333 prefixEnd_3987333 := by exact prefixLift 3987333
  have htrace : WordTrace (prefixWord ++ tailWord_3987333) baseStart_3987333 baseEnd_3987333 := by
    simpa [prefixWord, tailWord_3987333, baseEnd_3987333] using wordTrace_append hprefix tailTrace_3987333
  have hstable : (prefixWord ++ tailWord_3987333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987333).length < 2 ^ (prefixWord ++ tailWord_3987333).sum := by decide
  have hdescent : baseEnd_3987333 < baseStart_3987333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987338 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3987338 : Nat := 118140960795 + 3987338 * 2 ^ 59
def prefixEnd_3987338 : Nat := 4983230072969 + 3 ^ 40 * 3987338 * 2
def baseEnd_3987338 : Nat := 2047420925937225755437573

theorem tailTrace_3987338 : CollatzResearch.WordTrace tailWord_3987338 prefixEnd_3987338 2047420925937225755437573 := by
  unfold tailWord_3987338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357541107140720989918667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96953442952375255973116445 36357541107140720989918667)
  ·
    refine ⟨54536311660711081484878001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36357541107140720989918667 54536311660711081484878001)
    ·
      refine ⟨40902233745533311113658501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54536311660711081484878001 40902233745533311113658501)
      ·
        refine ⟨7669168827287495833810969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40902233745533311113658501 7669168827287495833810969)
        ·
          refine ⟨5751876620465621875358227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7669168827287495833810969 5751876620465621875358227)
          ·
            refine ⟨8627814930698432813037341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751876620465621875358227 8627814930698432813037341)
            ·
              refine ⟨3235430599011912304889003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8627814930698432813037341 3235430599011912304889003)
              ·
                refine ⟨4853145898517868457333505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235430599011912304889003 4853145898517868457333505)
                ·
                  refine ⟨3639859423888401343000129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853145898517868457333505 3639859423888401343000129)
                  ·
                    refine ⟨2729894567916301007250097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3639859423888401343000129 2729894567916301007250097)
                    ·
                      refine ⟨2047420925937225755437573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2729894567916301007250097 2047420925937225755437573)
                      ·
                        rfl

theorem cell23_3987338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3987338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987338 prefixEnd_3987338 := by exact prefixLift 3987338
  have htrace : WordTrace (prefixWord ++ tailWord_3987338) baseStart_3987338 baseEnd_3987338 := by
    simpa [prefixWord, tailWord_3987338, baseEnd_3987338] using wordTrace_append hprefix tailTrace_3987338
  have hstable : (prefixWord ++ tailWord_3987338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987338).length < 2 ^ (prefixWord ++ tailWord_3987338).sum := by decide
  have hdescent : baseEnd_3987338 < baseStart_3987338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987360 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3987360 : Nat := 118140960795 + 3987360 * 2 ^ 59
def prefixEnd_3987360 : Nat := 4983230072969 + 3 ^ 40 * 3987360 * 2
def baseEnd_3987360 : Nat := 2047432222511624669362471

theorem tailTrace_3987360 : CollatzResearch.WordTrace tailWord_3987360 prefixEnd_3987360 2047432222511624669362471 := by
  unfold tailWord_3987360
  simp only [CollatzResearch.WordTrace]
  refine ⟨72715483417241590858487767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96953977889655454477983689 72715483417241590858487767)
  ·
    refine ⟨109073225125862386287731651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72715483417241590858487767 109073225125862386287731651)
    ·
      refine ⟨163609837688793579431597477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109073225125862386287731651 163609837688793579431597477)
      ·
        refine ⟨30676844566648796143424527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163609837688793579431597477 30676844566648796143424527)
        ·
          refine ⟨46015266849973194215136791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30676844566648796143424527 46015266849973194215136791)
          ·
            refine ⟨69022900274959791322705187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46015266849973194215136791 69022900274959791322705187)
            ·
              refine ⟨103534350412439686984057781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69022900274959791322705187 103534350412439686984057781)
              ·
                refine ⟨9706345351166220654755417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103534350412439686984057781 9706345351166220654755417)
                ·
                  refine ⟨7279759013374665491066563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706345351166220654755417 7279759013374665491066563)
                  ·
                    refine ⟨10919638520061998236599845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279759013374665491066563 10919638520061998236599845)
                    ·
                      refine ⟨2047432222511624669362471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10919638520061998236599845 2047432222511624669362471)
                      ·
                        rfl

theorem cell23_3987360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3987360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987360 prefixEnd_3987360 := by exact prefixLift 3987360
  have htrace : WordTrace (prefixWord ++ tailWord_3987360) baseStart_3987360 baseEnd_3987360 := by
    simpa [prefixWord, tailWord_3987360, baseEnd_3987360] using wordTrace_append hprefix tailTrace_3987360
  have hstable : (prefixWord ++ tailWord_3987360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987360).length < 2 ^ (prefixWord ++ tailWord_3987360).sum := by decide
  have hdescent : baseEnd_3987360 < baseStart_3987360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987361 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 5]
def baseStart_3987361 : Nat := 118140960795 + 3987361 * 2 ^ 59
def prefixEnd_3987361 : Nat := 4983230072969 + 3 ^ 40 * 3987361 * 2
def baseEnd_3987361 : Nat := 227492526221364351716663

theorem tailTrace_3987361 : CollatzResearch.WordTrace tailWord_3987361 prefixEnd_3987361 227492526221364351716663 := by
  unfold tailWord_3987361
  simp only [CollatzResearch.WordTrace]
  refine ⟨145431003307479558887761937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96954002204986372591841291 145431003307479558887761937)
  ·
    refine ⟨109073252480609669165821453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145431003307479558887761937 109073252480609669165821453)
    ·
      refine ⟨40902469680228625937183045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109073252480609669165821453 40902469680228625937183045)
      ·
        refine ⟨7669213065042867363221821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40902469680228625937183045 7669213065042867363221821)
        ·
          refine ⟨2875954899391075261208183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7669213065042867363221821 2875954899391075261208183)
          ·
            refine ⟨4313932349086612891812275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875954899391075261208183 4313932349086612891812275)
            ·
              refine ⟨6470898523629919337718413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313932349086612891812275 6470898523629919337718413)
              ·
                refine ⟨2426586946361219751644405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6470898523629919337718413 2426586946361219751644405)
                ·
                  refine ⟨227492526221364351716663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426586946361219751644405 227492526221364351716663)
                  ·
                    rfl

theorem cell23_3987361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 5].length) (baseStart_3987361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987361 prefixEnd_3987361 := by exact prefixLift 3987361
  have htrace : WordTrace (prefixWord ++ tailWord_3987361) baseStart_3987361 baseEnd_3987361 := by
    simpa [prefixWord, tailWord_3987361, baseEnd_3987361] using wordTrace_append hprefix tailTrace_3987361
  have hstable : (prefixWord ++ tailWord_3987361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987361).length < 2 ^ (prefixWord ++ tailWord_3987361).sum := by decide
  have hdescent : baseEnd_3987361 < baseStart_3987361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987363 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3987363 : Nat := 118140960795 + 3987363 * 2 ^ 59
def prefixEnd_3987363 : Nat := 4983230072969 + 3 ^ 40 * 3987363 * 2
def baseEnd_3987363 : Nat := 2047433762953588157624957

theorem tailTrace_3987363 : CollatzResearch.WordTrace tailWord_3987363 prefixEnd_3987363 2047433762953588157624957 := by
  unfold tailWord_3987363
  simp only [CollatzResearch.WordTrace]
  refine ⟨145431076253472313229334743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96954050835648208819556495 145431076253472313229334743)
  ·
    refine ⟨218146614380208469844002115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145431076253472313229334743 218146614380208469844002115)
    ·
      refine ⟨327219921570312704766003173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218146614380208469844002115 327219921570312704766003173)
      ·
        refine ⟨61353735294433632143625595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327219921570312704766003173 61353735294433632143625595)
        ·
          refine ⟨92030602941650448215438393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61353735294433632143625595 92030602941650448215438393)
          ·
            refine ⟨69022952206237836161578795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92030602941650448215438393 69022952206237836161578795)
            ·
              refine ⟨103534428309356754242368193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69022952206237836161578795 103534428309356754242368193)
              ·
                refine ⟨77650821232017565681776145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103534428309356754242368193 77650821232017565681776145)
                ·
                  refine ⟨58238115924013174261332109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77650821232017565681776145 58238115924013174261332109)
                  ·
                    refine ⟨21839293471504940347999541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58238115924013174261332109 21839293471504940347999541)
                    ·
                      refine ⟨2047433762953588157624957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21839293471504940347999541 2047433762953588157624957)
                      ·
                        rfl

theorem cell23_3987363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3987363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987363 prefixEnd_3987363 := by exact prefixLift 3987363
  have htrace : WordTrace (prefixWord ++ tailWord_3987363) baseStart_3987363 baseEnd_3987363 := by
    simpa [prefixWord, tailWord_3987363, baseEnd_3987363] using wordTrace_append hprefix tailTrace_3987363
  have hstable : (prefixWord ++ tailWord_3987363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987363).length < 2 ^ (prefixWord ++ tailWord_3987363).sum := by decide
  have hdescent : baseEnd_3987363 < baseStart_3987363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987377 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3987377 : Nat := 118140960795 + 3987377 * 2 ^ 59
def prefixEnd_3987377 : Nat := 4983230072969 + 3 ^ 40 * 3987377 * 2
def baseEnd_3987377 : Nat := 2047440951682751102849893

theorem tailTrace_3987377 : CollatzResearch.WordTrace tailWord_3987377 prefixEnd_3987377 2047440951682751102849893 := by
  unfold tailWord_3987377
  simp only [CollatzResearch.WordTrace]
  refine ⟨145431586875421593620344385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96954391250281062413562923 145431586875421593620344385)
  ·
    refine ⟨109073690156566195215258289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145431586875421593620344385 109073690156566195215258289)
    ·
      refine ⟨81805267617424646411443717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109073690156566195215258289 81805267617424646411443717)
      ·
        refine ⟨15338487678267121202145697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81805267617424646411443717 15338487678267121202145697)
        ·
          refine ⟨11503865758700340901609273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338487678267121202145697 11503865758700340901609273)
          ·
            refine ⟨8627899319025255676206955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11503865758700340901609273 8627899319025255676206955)
            ·
              refine ⟨12941848978537883514310433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8627899319025255676206955 12941848978537883514310433)
              ·
                refine ⟨9706386733903412635732825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12941848978537883514310433 9706386733903412635732825)
                ·
                  refine ⟨7279790050427559476799619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706386733903412635732825 7279790050427559476799619)
                  ·
                    refine ⟨10919685075641339215199429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279790050427559476799619 10919685075641339215199429)
                    ·
                      refine ⟨2047440951682751102849893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10919685075641339215199429 2047440951682751102849893)
                      ·
                        rfl

theorem cell23_3987377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3987377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987377 prefixEnd_3987377 := by exact prefixLift 3987377
  have htrace : WordTrace (prefixWord ++ tailWord_3987377) baseStart_3987377 baseEnd_3987377 := by
    simpa [prefixWord, tailWord_3987377, baseEnd_3987377] using wordTrace_append hprefix tailTrace_3987377
  have hstable : (prefixWord ++ tailWord_3987377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987377).length < 2 ^ (prefixWord ++ tailWord_3987377).sum := by decide
  have hdescent : baseEnd_3987377 < baseStart_3987377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987438 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3987438 : Nat := 118140960795 + 3987438 * 2 ^ 59
def prefixEnd_3987438 : Nat := 4983230072969 + 3 ^ 40 * 3987438 * 2
def baseEnd_3987438 : Nat := 682490758000891788062371

theorem tailTrace_3987438 : CollatzResearch.WordTrace tailWord_3987438 prefixEnd_3987438 682490758000891788062371 := by
  unfold tailWord_3987438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179226466025075129789371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96955874485467067358876645 18179226466025075129789371)
  ·
    refine ⟨27268839699037612694684057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179226466025075129789371 27268839699037612694684057)
    ·
      refine ⟨20451629774278209521013043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27268839699037612694684057 20451629774278209521013043)
      ·
        refine ⟨30677444661417314281519565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451629774278209521013043 30677444661417314281519565)
        ·
          refine ⟨11504041748031492855569837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30677444661417314281519565 11504041748031492855569837)
          ·
            refine ⟨4314015655511809820838689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11504041748031492855569837 4314015655511809820838689)
            ·
              refine ⟨3235511741633857365629017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314015655511809820838689 3235511741633857365629017)
              ·
                refine ⟨2426633806225393024221763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235511741633857365629017 2426633806225393024221763)
                ·
                  refine ⟨3639950709338089536332645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426633806225393024221763 3639950709338089536332645)
                  ·
                    refine ⟨682490758000891788062371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3639950709338089536332645 682490758000891788062371)
                    ·
                      rfl

theorem cell23_3987438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3987438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987438 prefixEnd_3987438 := by exact prefixLift 3987438
  have htrace : WordTrace (prefixWord ++ tailWord_3987438) baseStart_3987438 baseEnd_3987438 := by
    simpa [prefixWord, tailWord_3987438, baseEnd_3987438] using wordTrace_append hprefix tailTrace_3987438
  have hstable : (prefixWord ++ tailWord_3987438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987438).length < 2 ^ (prefixWord ++ tailWord_3987438).sum := by decide
  have hdescent : baseEnd_3987438 < baseStart_3987438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987462 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3987462 : Nat := 118140960795 + 3987462 * 2 ^ 59
def prefixEnd_3987462 : Nat := 4983230072969 + 3 ^ 40 * 3987462 * 2
def baseEnd_3987462 : Nat := 2047484597538383270287003

theorem tailTrace_3987462 : CollatzResearch.WordTrace tailWord_3987462 prefixEnd_3987462 2047484597538383270287003 := by
  unfold tailWord_3987462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544833971253551660537145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96956458053409102091459093 4544833971253551660537145)
  ·
    refine ⟨3408625478440163745402859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4544833971253551660537145 3408625478440163745402859)
    ·
      refine ⟨5112938217660245618104289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408625478440163745402859 5112938217660245618104289)
      ·
        refine ⟨3834703663245184213578217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5112938217660245618104289 3834703663245184213578217)
        ·
          refine ⟨2876027747433888160183663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3834703663245184213578217 2876027747433888160183663)
          ·
            refine ⟨4314041621150832240275495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876027747433888160183663 4314041621150832240275495)
            ·
              refine ⟨6471062431726248360413243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314041621150832240275495 6471062431726248360413243)
              ·
                refine ⟨9706593647589372540619865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471062431726248360413243 9706593647589372540619865)
                ·
                  refine ⟨7279945235692029405464899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9706593647589372540619865 7279945235692029405464899)
                  ·
                    refine ⟨10919917853538044108197349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279945235692029405464899 10919917853538044108197349)
                    ·
                      refine ⟨2047484597538383270287003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10919917853538044108197349 2047484597538383270287003)
                      ·
                        rfl

theorem cell23_3987462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3987462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987462 prefixEnd_3987462 := by exact prefixLift 3987462
  have htrace : WordTrace (prefixWord ++ tailWord_3987462) baseStart_3987462 baseEnd_3987462 := by
    simpa [prefixWord, tailWord_3987462, baseEnd_3987462] using wordTrace_append hprefix tailTrace_3987462
  have hstable : (prefixWord ++ tailWord_3987462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987462).length < 2 ^ (prefixWord ++ tailWord_3987462).sum := by decide
  have hdescent : baseEnd_3987462 < baseStart_3987462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987467 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 4]
def baseStart_3987467 : Nat := 118140960795 + 3987467 * 2 ^ 59
def prefixEnd_3987467 : Nat := 4983230072969 + 3 ^ 40 * 3987467 * 2
def baseEnd_3987467 : Nat := 2047487164941655750724479

theorem tailTrace_3987467 : CollatzResearch.WordTrace tailWord_3987467 prefixEnd_3987467 2047487164941655750724479 := by
  unfold tailWord_3987467
  simp only [CollatzResearch.WordTrace]
  refine ⟨145434869445095538991120655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96956579630063692660747103 145434869445095538991120655)
  ·
    refine ⟨218152304167643308486680983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145434869445095538991120655 218152304167643308486680983)
    ·
      refine ⟨327228456251464962730021475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218152304167643308486680983 327228456251464962730021475)
      ·
        refine ⟨490842684377197444095032213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327228456251464962730021475 490842684377197444095032213)
        ·
          refine ⟨23008250830181130191954635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 490842684377197444095032213 23008250830181130191954635)
          ·
            refine ⟨34512376245271695287931953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23008250830181130191954635 34512376245271695287931953)
            ·
              refine ⟨25884282183953771465948965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34512376245271695287931953 25884282183953771465948965)
              ·
                refine ⟨4853302909491332149865431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25884282183953771465948965 4853302909491332149865431)
                ·
                  refine ⟨7279954364236998224798147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853302909491332149865431 7279954364236998224798147)
                  ·
                    refine ⟨10919931546355497337197221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279954364236998224798147 10919931546355497337197221)
                    ·
                      refine ⟨2047487164941655750724479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10919931546355497337197221 2047487164941655750724479)
                      ·
                        rfl

theorem cell23_3987467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 4].length) (baseStart_3987467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987467 prefixEnd_3987467 := by exact prefixLift 3987467
  have htrace : WordTrace (prefixWord ++ tailWord_3987467) baseStart_3987467 baseEnd_3987467 := by
    simpa [prefixWord, tailWord_3987467, baseEnd_3987467] using wordTrace_append hprefix tailTrace_3987467
  have hstable : (prefixWord ++ tailWord_3987467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987467).length < 2 ^ (prefixWord ++ tailWord_3987467).sum := by decide
  have hdescent : baseEnd_3987467 < baseStart_3987467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987484 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3987484 : Nat := 118140960795 + 3987484 * 2 ^ 59
def prefixEnd_3987484 : Nat := 4983230072969 + 3 ^ 40 * 3987484 * 2
def baseEnd_3987484 : Nat := 2047495894112782184211901

theorem tailTrace_3987484 : CollatzResearch.WordTrace tailWord_3987484 prefixEnd_3987484 2047495894112782184211901 := by
  unfold tailWord_3987484
  simp only [CollatzResearch.WordTrace]
  refine ⟨72717744743016975447244753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96956992990689300596326337 72717744743016975447244753)
  ·
    refine ⟨54538308557262731585433565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72717744743016975447244753 54538308557262731585433565)
    ·
      refine ⟨20451865708973524344537587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54538308557262731585433565 20451865708973524344537587)
      ·
        refine ⟨30677798563460286516806381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451865708973524344537587 30677798563460286516806381)
        ·
          refine ⟨11504174461297607443802393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30677798563460286516806381 11504174461297607443802393)
          ·
            refine ⟨8628130845973205582851795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504174461297607443802393 8628130845973205582851795)
            ·
              refine ⟨12942196268959808374277693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628130845973205582851795 12942196268959808374277693)
              ·
                refine ⟨4853323600859928140354135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12942196268959808374277693 4853323600859928140354135)
                ·
                  refine ⟨7279985401289892210531203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853323600859928140354135 7279985401289892210531203)
                  ·
                    refine ⟨10919978101934838315796805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7279985401289892210531203 10919978101934838315796805)
                    ·
                      refine ⟨2047495894112782184211901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10919978101934838315796805 2047495894112782184211901)
                      ·
                        rfl

theorem cell23_3987484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3987484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987484 prefixEnd_3987484 := by exact prefixLift 3987484
  have htrace : WordTrace (prefixWord ++ tailWord_3987484) baseStart_3987484 baseEnd_3987484 := by
    simpa [prefixWord, tailWord_3987484, baseEnd_3987484] using wordTrace_append hprefix tailTrace_3987484
  have hstable : (prefixWord ++ tailWord_3987484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987484).length < 2 ^ (prefixWord ++ tailWord_3987484).sum := by decide
  have hdescent : baseEnd_3987484 < baseStart_3987484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987490 : List Nat := [3, 3, 1, 1, 1, 2, 12]
def baseStart_3987490 : Nat := 118140960795 + 3987490 * 2 ^ 59
def prefixEnd_3987490 : Nat := 4983230072969 + 3 ^ 40 * 3987490 * 2
def baseEnd_3987490 : Nat := 25277765123416162478233

theorem tailTrace_3987490 : CollatzResearch.WordTrace tailWord_3987490 prefixEnd_3987490 25277765123416162478233 := by
  unfold tailWord_3987490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358927081003053479801981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96957138882674809279471949 36358927081003053479801981)
  ·
    refine ⟨13634597655376145054925743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36358927081003053479801981 13634597655376145054925743)
    ·
      refine ⟨20451896483064217582388615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13634597655376145054925743 20451896483064217582388615)
      ·
        refine ⟨30677844724596326373582923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451896483064217582388615 30677844724596326373582923)
        ·
          refine ⟨46016767086894489560374385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30677844724596326373582923 46016767086894489560374385)
          ·
            refine ⟨34512575315170867170280789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46016767086894489560374385 34512575315170867170280789)
            ·
              refine ⟨25277765123416162478233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34512575315170867170280789 25277765123416162478233)
              ·
                rfl

theorem cell23_3987490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 12].length) (baseStart_3987490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987490 prefixEnd_3987490 := by exact prefixLift 3987490
  have htrace : WordTrace (prefixWord ++ tailWord_3987490) baseStart_3987490 baseEnd_3987490 := by
    simpa [prefixWord, tailWord_3987490, baseEnd_3987490] using wordTrace_append hprefix tailTrace_3987490
  have hstable : (prefixWord ++ tailWord_3987490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987490).length < 2 ^ (prefixWord ++ tailWord_3987490).sum := by decide
  have hdescent : baseEnd_3987490 < baseStart_3987490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987521 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3987521 : Nat := 118140960795 + 3987521 * 2 ^ 59
def prefixEnd_3987521 : Nat := 4983230072969 + 3 ^ 40 * 3987521 * 2
def baseEnd_3987521 : Nat := 2047514892896998539449231

theorem tailTrace_3987521 : CollatzResearch.WordTrace tailWord_3987521 prefixEnd_3987521 2047514892896998539449231 := by
  unfold tailWord_3987521
  simp only [CollatzResearch.WordTrace]
  refine ⟨145436838986899906213586417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96957892657933270809057611 145436838986899906213586417)
  ·
    refine ⟨109077629240174929660189813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145436838986899906213586417 109077629240174929660189813)
    ·
      refine ⟨10226027741266399655642795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109077629240174929660189813 10226027741266399655642795)
      ·
        refine ⟨15339041611899599483464193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226027741266399655642795 15339041611899599483464193)
        ·
          refine ⟨11504281208924699612598145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15339041611899599483464193 11504281208924699612598145)
          ·
            refine ⟨8628210906693524709448609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504281208924699612598145 8628210906693524709448609)
            ·
              refine ⟨6471158180020143532086457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628210906693524709448609 6471158180020143532086457)
              ·
                refine ⟨4853368635015107649064843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471158180020143532086457 4853368635015107649064843)
                ·
                  refine ⟨7280052952522661473597265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4853368635015107649064843 7280052952522661473597265)
                  ·
                    refine ⟨5460039714391996105197949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7280052952522661473597265 5460039714391996105197949)
                    ·
                      refine ⟨2047514892896998539449231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460039714391996105197949 2047514892896998539449231)
                      ·
                        rfl

theorem cell23_3987521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3987521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987521 prefixEnd_3987521 := by exact prefixLift 3987521
  have htrace : WordTrace (prefixWord ++ tailWord_3987521) baseStart_3987521 baseEnd_3987521 := by
    simpa [prefixWord, tailWord_3987521, baseEnd_3987521] using wordTrace_append hprefix tailTrace_3987521
  have hstable : (prefixWord ++ tailWord_3987521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987521).length < 2 ^ (prefixWord ++ tailWord_3987521).sum := by decide
  have hdescent : baseEnd_3987521 < baseStart_3987521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987534 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3987534 : Nat := 118140960795 + 3987534 * 2 ^ 59
def prefixEnd_3987534 : Nat := 4983230072969 + 3 ^ 40 * 3987534 * 2
def baseEnd_3987534 : Nat := 2047521568145506988586671

theorem tailTrace_3987534 : CollatzResearch.WordTrace tailWord_3987534 prefixEnd_3987534 2047521568145506988586671 := by
  unfold tailWord_3987534
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179664141981601179226207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96958208757235206289206437 18179664141981601179226207)
  ·
    refine ⟨27269496212972401768839311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179664141981601179226207 27269496212972401768839311)
    ·
      refine ⟨40904244319458602653258967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27269496212972401768839311 40904244319458602653258967)
      ·
        refine ⟨61356366479187903979888451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40904244319458602653258967 61356366479187903979888451)
        ·
          refine ⟨92034549718781855969832677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61356366479187903979888451 92034549718781855969832677)
          ·
            refine ⟨17256478072271597994343627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92034549718781855969832677 17256478072271597994343627)
            ·
              refine ⟨25884717108407396991515441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17256478072271597994343627 25884717108407396991515441)
              ·
                refine ⟨19413537831305547743636581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25884717108407396991515441 19413537831305547743636581)
                ·
                  refine ⟨3640038343369790201931859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19413537831305547743636581 3640038343369790201931859)
                  ·
                    refine ⟨5460057515054685302897789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640038343369790201931859 5460057515054685302897789)
                    ·
                      refine ⟨2047521568145506988586671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460057515054685302897789 2047521568145506988586671)
                      ·
                        rfl

theorem cell23_3987534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3987534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987534 prefixEnd_3987534 := by exact prefixLift 3987534
  have htrace : WordTrace (prefixWord ++ tailWord_3987534) baseStart_3987534 baseEnd_3987534 := by
    simpa [prefixWord, tailWord_3987534, baseEnd_3987534] using wordTrace_append hprefix tailTrace_3987534
  have hstable : (prefixWord ++ tailWord_3987534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987534).length < 2 ^ (prefixWord ++ tailWord_3987534).sum := by decide
  have hdescent : baseEnd_3987534 < baseStart_3987534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987568 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3]
def baseStart_3987568 : Nat := 118140960795 + 3987568 * 2 ^ 59
def prefixEnd_3987568 : Nat := 4983230072969 + 3 ^ 40 * 3987568 * 2
def baseEnd_3987568 : Nat := 2047539026487759855561515

theorem tailTrace_3987568 : CollatzResearch.WordTrace tailWord_3987568 prefixEnd_3987568 2047539026487759855561515 := by
  unfold tailWord_3987568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72719276608864816620273679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96959035478486422160364905 72719276608864816620273679)
  ·
    refine ⟨109078914913297224930410519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72719276608864816620273679 109078914913297224930410519)
    ·
      refine ⟨163618372369945837395615779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109078914913297224930410519 163618372369945837395615779)
      ·
        refine ⟨245427558554918756093423669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163618372369945837395615779 245427558554918756093423669)
        ·
          refine ⟨23008833614523633383758469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245427558554918756093423669 23008833614523633383758469)
          ·
            refine ⟨4314156302723181259454713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23008833614523633383758469 4314156302723181259454713)
            ·
              refine ⟨3235617227042385944591035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314156302723181259454713 3235617227042385944591035)
              ·
                refine ⟨4853425840563578916886553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235617227042385944591035 4853425840563578916886553)
                ·
                  refine ⟨3640069380422684187664915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853425840563578916886553 3640069380422684187664915)
                  ·
                    refine ⟨5460104070634026281497373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640069380422684187664915 5460104070634026281497373)
                    ·
                      refine ⟨2047539026487759855561515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460104070634026281497373 2047539026487759855561515)
                      ·
                        rfl

theorem cell23_3987568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3].length) (baseStart_3987568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987568 prefixEnd_3987568 := by exact prefixLift 3987568
  have htrace : WordTrace (prefixWord ++ tailWord_3987568) baseStart_3987568 baseEnd_3987568 := by
    simpa [prefixWord, tailWord_3987568, baseEnd_3987568] using wordTrace_append hprefix tailTrace_3987568
  have hstable : (prefixWord ++ tailWord_3987568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987568).length < 2 ^ (prefixWord ++ tailWord_3987568).sum := by decide
  have hdescent : baseEnd_3987568 < baseStart_3987568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987577 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3987577 : Nat := 118140960795 + 3987577 * 2 ^ 59
def prefixEnd_3987577 : Nat := 4983230072969 + 3 ^ 40 * 3987577 * 2
def baseEnd_3987577 : Nat := 2047543647813650320348973

theorem tailTrace_3987577 : CollatzResearch.WordTrace tailWord_3987577 prefixEnd_3987577 2047543647813650320348973 := by
  unfold tailWord_3987577
  simp only [CollatzResearch.WordTrace]
  refine ⟨145438881474697027777624985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96959254316464685185083323 145438881474697027777624985)
  ·
    refine ⟨109079161106022770833218739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145438881474697027777624985 109079161106022770833218739)
    ·
      refine ⟨163618741659034156249828109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109079161106022770833218739 163618741659034156249828109)
      ·
        refine ⟨61357028122137808593685541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163618741659034156249828109 61357028122137808593685541)
        ·
          refine ⟨11504442772900839111316039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61357028122137808593685541 11504442772900839111316039)
          ·
            refine ⟨17256664159351258666974059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11504442772900839111316039 17256664159351258666974059)
            ·
              refine ⟨25884996239026888000461089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17256664159351258666974059 25884996239026888000461089)
              ·
                refine ⟨19413747179270166000345817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25884996239026888000461089 19413747179270166000345817)
                ·
                  refine ⟨14560310384452624500259363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19413747179270166000345817 14560310384452624500259363)
                  ·
                    refine ⟨21840465576678936750389045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14560310384452624500259363 21840465576678936750389045)
                    ·
                      refine ⟨2047543647813650320348973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21840465576678936750389045 2047543647813650320348973)
                      ·
                        rfl

theorem cell23_3987577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3987577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987577 prefixEnd_3987577 := by exact prefixLift 3987577
  have htrace : WordTrace (prefixWord ++ tailWord_3987577) baseStart_3987577 baseEnd_3987577 := by
    simpa [prefixWord, tailWord_3987577, baseEnd_3987577] using wordTrace_append hprefix tailTrace_3987577
  have hstable : (prefixWord ++ tailWord_3987577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987577).length < 2 ^ (prefixWord ++ tailWord_3987577).sum := by decide
  have hdescent : baseEnd_3987577 < baseStart_3987577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987634 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_3987634 : Nat := 118140960795 + 3987634 * 2 ^ 59
def prefixEnd_3987634 : Nat := 4983230072969 + 3 ^ 40 * 3987634 * 2
def baseEnd_3987634 : Nat := 2047572916210956597336211

theorem tailTrace_3987634 : CollatzResearch.WordTrace tailWord_3987634 prefixEnd_3987634 2047572916210956597336211 := by
  unfold tailWord_3987634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36360240108872631628112489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96960640290327017674966637 36360240108872631628112489)
  ·
    refine ⟨27270180081654473721084367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36360240108872631628112489 27270180081654473721084367)
    ·
      refine ⟨40905270122481710581626551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27270180081654473721084367 40905270122481710581626551)
      ·
        refine ⟨61357905183722565872439827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40905270122481710581626551 61357905183722565872439827)
        ·
          refine ⟨92036857775583848808659741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61357905183722565872439827 92036857775583848808659741)
          ·
            refine ⟨34513821665843943303247403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92036857775583848808659741 34513821665843943303247403)
            ·
              refine ⟨51770732498765914954871105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34513821665843943303247403 51770732498765914954871105)
              ·
                refine ⟨38828049374074436216153329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51770732498765914954871105 38828049374074436216153329)
                ·
                  refine ⟨29121037030555827162114997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38828049374074436216153329 29121037030555827162114997)
                  ·
                    refine ⟨2730097221614608796448281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29121037030555827162114997 2730097221614608796448281)
                    ·
                      refine ⟨2047572916210956597336211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730097221614608796448281 2047572916210956597336211)
                      ·
                        rfl

theorem cell23_3987634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_3987634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987634 prefixEnd_3987634 := by exact prefixLift 3987634
  have htrace : WordTrace (prefixWord ++ tailWord_3987634) baseStart_3987634 baseEnd_3987634 := by
    simpa [prefixWord, tailWord_3987634, baseEnd_3987634] using wordTrace_append hprefix tailTrace_3987634
  have hstable : (prefixWord ++ tailWord_3987634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987634).length < 2 ^ (prefixWord ++ tailWord_3987634).sum := by decide
  have hdescent : baseEnd_3987634 < baseStart_3987634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987644 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3987644 : Nat := 118140960795 + 3987644 * 2 ^ 59
def prefixEnd_3987644 : Nat := 4983230072969 + 3 ^ 40 * 3987644 * 2
def baseEnd_3987644 : Nat := 682526017005833852737055

theorem tailTrace_3987644 : CollatzResearch.WordTrace tailWord_3987644 prefixEnd_3987644 682526017005833852737055 := by
  unfold tailWord_3987644
  simp only [CollatzResearch.WordTrace]
  refine ⟨72720662582727149110156993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96960883443636198813542657 72720662582727149110156993)
  ·
    refine ⟨54540496937045361832617745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72720662582727149110156993 54540496937045361832617745)
    ·
      refine ⟨40905372702784021374463309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54540496937045361832617745 40905372702784021374463309)
      ·
        refine ⟨15339514763544008015423741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40905372702784021374463309 15339514763544008015423741)
        ·
          refine ⟨5752318036329003005783903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15339514763544008015423741 5752318036329003005783903)
          ·
            refine ⟨8628477054493504508675855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752318036329003005783903 8628477054493504508675855)
            ·
              refine ⟨12942715581740256763013783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8628477054493504508675855 12942715581740256763013783)
              ·
                refine ⟨19414073372610385144520675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12942715581740256763013783 19414073372610385144520675)
                ·
                  refine ⟨29121110058915577716781013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19414073372610385144520675 29121110058915577716781013)
                  ·
                    refine ⟨682526017005833852737055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29121110058915577716781013 682526017005833852737055)
                    ·
                      rfl

theorem cell23_3987644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3987644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987644 prefixEnd_3987644 := by exact prefixLift 3987644
  have htrace : WordTrace (prefixWord ++ tailWord_3987644) baseStart_3987644 baseEnd_3987644 := by
    simpa [prefixWord, tailWord_3987644, baseEnd_3987644] using wordTrace_append hprefix tailTrace_3987644
  have hstable : (prefixWord ++ tailWord_3987644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987644).length < 2 ^ (prefixWord ++ tailWord_3987644).sum := by decide
  have hdescent : baseEnd_3987644 < baseStart_3987644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987667 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3]
def baseStart_3987667 : Nat := 118140960795 + 3987667 * 2 ^ 59
def prefixEnd_3987667 : Nat := 4983230072969 + 3 ^ 40 * 3987667 * 2
def baseEnd_3987667 : Nat := 2047589861072554968223559

theorem tailTrace_3987667 : CollatzResearch.WordTrace tailWord_3987667 prefixEnd_3987667 2047589861072554968223559 := by
  unfold tailWord_3987667
  simp only [CollatzResearch.WordTrace]
  refine ⟨145442164044370973148401255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96961442696247315432267503 145442164044370973148401255)
  ·
    refine ⟨218163246066556459722601883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145442164044370973148401255 218163246066556459722601883)
    ·
      refine ⟨327244869099834689583902825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218163246066556459722601883 327244869099834689583902825)
      ·
        refine ⟨245433651824876017187927119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327244869099834689583902825 245433651824876017187927119)
        ·
          refine ⟨368150477737314025781890679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245433651824876017187927119 368150477737314025781890679)
          ·
            refine ⟨552225716605971038672836019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368150477737314025781890679 552225716605971038672836019)
            ·
              refine ⟨828338574908956558009254029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552225716605971038672836019 828338574908956558009254029)
              ·
                refine ⟨310626965590858709253470261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828338574908956558009254029 310626965590858709253470261)
                ·
                  refine ⟨29121278024143003992512837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310626965590858709253470261 29121278024143003992512837)
                  ·
                    refine ⟨5460239629526813248596157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29121278024143003992512837 5460239629526813248596157)
                    ·
                      refine ⟨2047589861072554968223559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460239629526813248596157 2047589861072554968223559)
                      ·
                        rfl

theorem cell23_3987667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_3987667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987667 prefixEnd_3987667 := by exact prefixLift 3987667
  have htrace : WordTrace (prefixWord ++ tailWord_3987667) baseStart_3987667 baseEnd_3987667 := by
    simpa [prefixWord, tailWord_3987667, baseEnd_3987667] using wordTrace_append hprefix tailTrace_3987667
  have hstable : (prefixWord ++ tailWord_3987667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987667).length < 2 ^ (prefixWord ++ tailWord_3987667).sum := by decide
  have hdescent : baseEnd_3987667 < baseStart_3987667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987674 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_3987674 : Nat := 118140960795 + 3987674 * 2 ^ 59
def prefixEnd_3987674 : Nat := 4983230072969 + 3 ^ 40 * 3987674 * 2
def baseEnd_3987674 : Nat := 682531151812378813612009

theorem tailTrace_3987674 : CollatzResearch.WordTrace tailWord_3987674 prefixEnd_3987674 682531151812378813612009 := by
  unfold tailWord_3987674
  simp only [CollatzResearch.WordTrace]
  refine ⟨36360604838836403335976519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96961612903563742229270717 36360604838836403335976519)
  ·
    refine ⟨54540907258254605003964779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36360604838836403335976519 54540907258254605003964779)
    ·
      refine ⟨81811360887381907505947169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54540907258254605003964779 81811360887381907505947169)
      ·
        refine ⟨61358520665536430629460377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81811360887381907505947169 61358520665536430629460377)
        ·
          refine ⟨46018890499152322972095283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61358520665536430629460377 46018890499152322972095283)
          ·
            refine ⟨69028335748728484458142925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46018890499152322972095283 69028335748728484458142925)
            ·
              refine ⟨25885625905773181671803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69028335748728484458142925 25885625905773181671803597)
              ·
                refine ⟨9707109714664943126926349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25885625905773181671803597 9707109714664943126926349)
                ·
                  refine ⟨3640166142999353672597381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9707109714664943126926349 3640166142999353672597381)
                  ·
                    refine ⟨682531151812378813612009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640166142999353672597381 682531151812378813612009)
                    ·
                      rfl

theorem cell23_3987674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_3987674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987674 prefixEnd_3987674 := by exact prefixLift 3987674
  have htrace : WordTrace (prefixWord ++ tailWord_3987674) baseStart_3987674 baseEnd_3987674 := by
    simpa [prefixWord, tailWord_3987674, baseEnd_3987674] using wordTrace_append hprefix tailTrace_3987674
  have hstable : (prefixWord ++ tailWord_3987674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987674).length < 2 ^ (prefixWord ++ tailWord_3987674).sum := by decide
  have hdescent : baseEnd_3987674 < baseStart_3987674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987708 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_3987708 : Nat := 118140960795 + 3987708 * 2 ^ 59
def prefixEnd_3987708 : Nat := 4983230072969 + 3 ^ 40 * 3987708 * 2
def baseEnd_3987708 : Nat := 682536971259796435936957

theorem tailTrace_3987708 : CollatzResearch.WordTrace tailWord_3987708 prefixEnd_3987708 682536971259796435936957 := by
  unfold tailWord_3987708
  simp only [CollatzResearch.WordTrace]
  refine ⟨72721829718611218575321889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96962439624814958100429185 72721829718611218575321889)
  ·
    refine ⟨54541372288958413931491417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72721829718611218575321889 54541372288958413931491417)
    ·
      refine ⟨40906029216718810448618563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54541372288958413931491417 40906029216718810448618563)
      ·
        refine ⟨61359043825078215672927845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40906029216718810448618563 61359043825078215672927845)
        ·
          refine ⟨11504820717202165438673971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61359043825078215672927845 11504820717202165438673971)
          ·
            refine ⟨17257231075803248158010957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11504820717202165438673971 17257231075803248158010957)
            ·
              refine ⟨6471461653426218059254109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17257231075803248158010957 6471461653426218059254109)
              ·
                refine ⟨2426798120034831772220291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6471461653426218059254109 2426798120034831772220291)
                ·
                  refine ⟨3640197180052247658330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2426798120034831772220291 3640197180052247658330437)
                  ·
                    refine ⟨682536971259796435936957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640197180052247658330437 682536971259796435936957)
                    ·
                      rfl

theorem cell23_3987708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_3987708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987708 prefixEnd_3987708 := by exact prefixLift 3987708
  have htrace : WordTrace (prefixWord ++ tailWord_3987708) baseStart_3987708 baseEnd_3987708 := by
    simpa [prefixWord, tailWord_3987708, baseEnd_3987708] using wordTrace_append hprefix tailTrace_3987708
  have hstable : (prefixWord ++ tailWord_3987708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987708).length < 2 ^ (prefixWord ++ tailWord_3987708).sum := by decide
  have hdescent : baseEnd_3987708 < baseStart_3987708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987738 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_3987738 : Nat := 118140960795 + 3987738 * 2 ^ 59
def prefixEnd_3987738 : Nat := 4983230072969 + 3 ^ 40 * 3987738 * 2
def baseEnd_3987738 : Nat := 227514035355447132270637

theorem tailTrace_3987738 : CollatzResearch.WordTrace tailWord_3987738 prefixEnd_3987738 227514035355447132270637 := by
  unfold tailWord_3987738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361188406778438068558967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96963169084742501516157245 36361188406778438068558967)
  ·
    refine ⟨54541782610167657102838451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36361188406778438068558967 54541782610167657102838451)
    ·
      refine ⟨81812673915251485654257677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54541782610167657102838451 81812673915251485654257677)
      ·
        refine ⟨30679752718219307120346629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81812673915251485654257677 30679752718219307120346629)
        ·
          refine ⟨5752453634666120085064993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30679752718219307120346629 5752453634666120085064993)
          ·
            refine ⟨4314340225999590063798745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5752453634666120085064993 4314340225999590063798745)
            ·
              refine ⟨3235755169499692547849059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4314340225999590063798745 3235755169499692547849059)
              ·
                refine ⟨4853632754249538821773589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235755169499692547849059 4853632754249538821773589)
                ·
                  refine ⟨227514035355447132270637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4853632754249538821773589 227514035355447132270637)
                  ·
                    rfl

theorem cell23_3987738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_3987738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987738 prefixEnd_3987738 := by exact prefixLift 3987738
  have htrace : WordTrace (prefixWord ++ tailWord_3987738) baseStart_3987738 baseEnd_3987738 := by
    simpa [prefixWord, tailWord_3987738, baseEnd_3987738] using wordTrace_append hprefix tailTrace_3987738
  have hstable : (prefixWord ++ tailWord_3987738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987738).length < 2 ^ (prefixWord ++ tailWord_3987738).sum := by decide
  have hdescent : baseEnd_3987738 < baseStart_3987738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7]
def baseStart_3987787 : Nat := 118140960795 + 3987787 * 2 ^ 59
def prefixEnd_3987787 : Nat := 4983230072969 + 3 ^ 40 * 3987787 * 2
def baseEnd_3987787 : Nat := 2047651478751094498723007

theorem tailTrace_3987787 : CollatzResearch.WordTrace tailWord_3987787 prefixEnd_3987787 2047651478751094498723007 := by
  unfold tailWord_3987787
  simp only [CollatzResearch.WordTrace]
  refine ⟨145446540803936233642769615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96964360535957489095179743 145446540803936233642769615)
  ·
    refine ⟨218169811205904350464154423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145446540803936233642769615 218169811205904350464154423)
    ·
      refine ⟨327254716808856525696231635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218169811205904350464154423 327254716808856525696231635)
      ·
        refine ⟨490882075213284788544347453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327254716808856525696231635 490882075213284788544347453)
        ·
          refine ⟨184080778204981795704130295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490882075213284788544347453 184080778204981795704130295)
          ·
            refine ⟨276121167307472693556195443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184080778204981795704130295 276121167307472693556195443)
            ·
              refine ⟨414181750961209040334293165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276121167307472693556195443 414181750961209040334293165)
              ·
                refine ⟨155318156610453390125359937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414181750961209040334293165 155318156610453390125359937)
                ·
                  refine ⟨116488617457840042594019953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155318156610453390125359937 116488617457840042594019953)
                  ·
                    refine ⟨87366463093380031945514965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116488617457840042594019953 87366463093380031945514965)
                    ·
                      refine ⟨2047651478751094498723007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87366463093380031945514965 2047651478751094498723007)
                      ·
                        rfl

theorem cell23_3987787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_3987787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987787 prefixEnd_3987787 := by exact prefixLift 3987787
  have htrace : WordTrace (prefixWord ++ tailWord_3987787) baseStart_3987787 baseEnd_3987787 := by
    simpa [prefixWord, tailWord_3987787, baseEnd_3987787] using wordTrace_append hprefix tailTrace_3987787
  have hstable : (prefixWord ++ tailWord_3987787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987787).length < 2 ^ (prefixWord ++ tailWord_3987787).sum := by decide
  have hdescent : baseEnd_3987787 < baseStart_3987787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987788 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3987788 : Nat := 118140960795 + 3987788 * 2 ^ 59
def prefixEnd_3987788 : Nat := 4983230072969 + 3 ^ 40 * 3987788 * 2
def baseEnd_3987788 : Nat := 2047651992231748994810503

theorem tailTrace_3987788 : CollatzResearch.WordTrace tailWord_3987788 prefixEnd_3987788 2047651992231748994810503 := by
  unfold tailWord_3987788
  simp only [CollatzResearch.WordTrace]
  refine ⟨72723288638466305406778009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96964384851288407209037345 72723288638466305406778009)
  ·
    refine ⟨54542466478849729055083507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72723288638466305406778009 54542466478849729055083507)
    ·
      refine ⟨81813699718274593582625261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54542466478849729055083507 81813699718274593582625261)
      ·
        refine ⟨30680137394352972593484473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81813699718274593582625261 30680137394352972593484473)
        ·
          refine ⟨23010103045764729445113355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30680137394352972593484473 23010103045764729445113355)
          ·
            refine ⟨34515154568647094167670033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23010103045764729445113355 34515154568647094167670033)
            ·
              refine ⟨25886365926485320625752525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34515154568647094167670033 25886365926485320625752525)
              ·
                refine ⟨9707387222431995234657197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25886365926485320625752525 9707387222431995234657197)
                ·
                  refine ⟨3640270208411998212996449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9707387222431995234657197 3640270208411998212996449)
                  ·
                    refine ⟨2730202656308998659747337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640270208411998212996449 2730202656308998659747337)
                    ·
                      refine ⟨2047651992231748994810503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730202656308998659747337 2047651992231748994810503)
                      ·
                        rfl

theorem cell23_3987788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3987788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987788 prefixEnd_3987788 := by exact prefixLift 3987788
  have htrace : WordTrace (prefixWord ++ tailWord_3987788) baseStart_3987788 baseEnd_3987788 := by
    simpa [prefixWord, tailWord_3987788, baseEnd_3987788] using wordTrace_append hprefix tailTrace_3987788
  have hstable : (prefixWord ++ tailWord_3987788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987788).length < 2 ^ (prefixWord ++ tailWord_3987788).sum := by decide
  have hdescent : baseEnd_3987788 < baseStart_3987788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987794 : List Nat := [3, 2, 2, 1, 1, 1, 5, 8]
def baseStart_3987794 : Nat := 118140960795 + 3987794 * 2 ^ 59
def prefixEnd_3987794 : Nat := 4983230072969 + 3 ^ 40 * 3987794 * 2
def baseEnd_3987794 : Nat := 75839076782062073012425

theorem tailTrace_3987794 : CollatzResearch.WordTrace tailWord_3987794 prefixEnd_3987794 75839076782062073012425 := by
  unfold tailWord_3987794
  simp only [CollatzResearch.WordTrace]
  refine ⟨36361699028727718459568609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96964530743273915892182957 36361699028727718459568609)
  ·
    refine ⟨27271274271545788844676457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36361699028727718459568609 27271274271545788844676457)
    ·
      refine ⟨20453455703659341633507343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27271274271545788844676457 20453455703659341633507343)
      ·
        refine ⟨30680183555489012450261015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453455703659341633507343 30680183555489012450261015)
        ·
          refine ⟨46020275333233518675391523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30680183555489012450261015 46020275333233518675391523)
          ·
            refine ⟨69030412999850278013087285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46020275333233518675391523 69030412999850278013087285)
            ·
              refine ⟨6471601218735963563726933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69030412999850278013087285 6471601218735963563726933)
              ·
                refine ⟨75839076782062073012425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6471601218735963563726933 75839076782062073012425)
                ·
                  rfl

theorem cell23_3987794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_3987794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987794 prefixEnd_3987794 := by exact prefixLift 3987794
  have htrace : WordTrace (prefixWord ++ tailWord_3987794) baseStart_3987794 baseEnd_3987794 := by
    simpa [prefixWord, tailWord_3987794, baseEnd_3987794] using wordTrace_append hprefix tailTrace_3987794
  have hstable : (prefixWord ++ tailWord_3987794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987794).length < 2 ^ (prefixWord ++ tailWord_3987794).sum := by decide
  have hdescent : baseEnd_3987794 < baseStart_3987794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987821 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3987821 : Nat := 118140960795 + 3987821 * 2 ^ 59
def prefixEnd_3987821 : Nat := 4983230072969 + 3 ^ 40 * 3987821 * 2
def baseEnd_3987821 : Nat := 2047668937093347365697851

theorem tailTrace_3987821 : CollatzResearch.WordTrace tailWord_3987821 prefixEnd_3987821 2047668937093347365697851 := by
  unfold tailWord_3987821
  simp only [CollatzResearch.WordTrace]
  refine ⟨145447780885813057449507317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96965187257208704966338211 145447780885813057449507317)
  ·
    refine ⟨13635729458044974135891311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145447780885813057449507317 13635729458044974135891311)
    ·
      refine ⟨20453594187067461203836967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13635729458044974135891311 20453594187067461203836967)
      ·
        refine ⟨30680391280601191805755451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20453594187067461203836967 30680391280601191805755451)
        ·
          refine ⟨46020586920901787708633177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30680391280601191805755451 46020586920901787708633177)
          ·
            refine ⟨34515440190676340781474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46020586920901787708633177 34515440190676340781474883)
            ·
              refine ⟨51773160286014511172212325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34515440190676340781474883 51773160286014511172212325)
              ·
                refine ⟨9707467553627720844789811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51773160286014511172212325 9707467553627720844789811)
                ·
                  refine ⟨14561201330441581267184717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9707467553627720844789811 14561201330441581267184717)
                  ·
                    refine ⟨5460450498915592975194269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14561201330441581267184717 5460450498915592975194269)
                    ·
                      refine ⟨2047668937093347365697851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460450498915592975194269 2047668937093347365697851)
                      ·
                        rfl

theorem cell23_3987821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3987821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987821 prefixEnd_3987821 := by exact prefixLift 3987821
  have htrace : WordTrace (prefixWord ++ tailWord_3987821) baseStart_3987821 baseEnd_3987821 := by
    simpa [prefixWord, tailWord_3987821, baseEnd_3987821] using wordTrace_append hprefix tailTrace_3987821
  have hstable : (prefixWord ++ tailWord_3987821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987821).length < 2 ^ (prefixWord ++ tailWord_3987821).sum := by decide
  have hdescent : baseEnd_3987821 < baseStart_3987821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987831 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_3987831 : Nat := 118140960795 + 3987831 * 2 ^ 59
def prefixEnd_3987831 : Nat := 4983230072969 + 3 ^ 40 * 3987831 * 2
def baseEnd_3987831 : Nat := 2047674071899892326572805

theorem tailTrace_3987831 : CollatzResearch.WordTrace tailWord_3987831 prefixEnd_3987831 2047674071899892326572805 := by
  unfold tailWord_3987831
  simp only [CollatzResearch.WordTrace]
  refine ⟨145448145615776829157371347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96965430410517886104914231 145448145615776829157371347)
  ·
    refine ⟨218172218423665243736057021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145448145615776829157371347 218172218423665243736057021)
    ·
      refine ⟨81814581908874466401021383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218172218423665243736057021 81814581908874466401021383)
      ·
        refine ⟨122721872863311699601532075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81814581908874466401021383 122721872863311699601532075)
        ·
          refine ⟨184082809294967549402298113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122721872863311699601532075 184082809294967549402298113)
          ·
            refine ⟨138062106971225662051723585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184082809294967549402298113 138062106971225662051723585)
            ·
              refine ⟨103546580228419246538792689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138062106971225662051723585 103546580228419246538792689)
              ·
                refine ⟨77659935171314434904094517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103546580228419246538792689 77659935171314434904094517)
                ·
                  refine ⟨7280618922310728272258861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77659935171314434904094517 7280618922310728272258861)
                  ·
                    refine ⟨2730232095866523102097073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7280618922310728272258861 2730232095866523102097073)
                    ·
                      refine ⟨2047674071899892326572805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730232095866523102097073 2047674071899892326572805)
                      ·
                        rfl

theorem cell23_3987831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_3987831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987831 prefixEnd_3987831 := by exact prefixLift 3987831
  have htrace : WordTrace (prefixWord ++ tailWord_3987831) baseStart_3987831 baseEnd_3987831 := by
    simpa [prefixWord, tailWord_3987831, baseEnd_3987831] using wordTrace_append hprefix tailTrace_3987831
  have hstable : (prefixWord ++ tailWord_3987831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987831).length < 2 ^ (prefixWord ++ tailWord_3987831).sum := by decide
  have hdescent : baseEnd_3987831 < baseStart_3987831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987901 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 7]
def baseStart_3987901 : Nat := 118140960795 + 3987901 * 2 ^ 59
def prefixEnd_3987901 : Nat := 4983230072969 + 3 ^ 40 * 3987901 * 2
def baseEnd_3987901 : Nat := 227523335060634116966387

theorem tailTrace_3987901 : CollatzResearch.WordTrace tailWord_3987901 prefixEnd_3987901 227523335060634116966387 := by
  unfold tailWord_3987901
  simp only [CollatzResearch.WordTrace]
  refine ⟨145450698725523231112419557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96967132483682154074946371 145450698725523231112419557)
  ·
    refine ⟨27272006011035605833578667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145450698725523231112419557 27272006011035605833578667)
    ·
      refine ⟨40908009016553408750368001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27272006011035605833578667 40908009016553408750368001)
      ·
        refine ⟨30681006762415056562776001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40908009016553408750368001 30681006762415056562776001)
        ·
          refine ⟨23010755071811292422082001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30681006762415056562776001 23010755071811292422082001)
          ·
            refine ⟨17258066303858469316561501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23010755071811292422082001 17258066303858469316561501)
            ·
              refine ⟨6471774863946925993710563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17258066303858469316561501 6471774863946925993710563)
              ·
                refine ⟨9707662295920388990565845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6471774863946925993710563 9707662295920388990565845)
                ·
                  refine ⟨227523335060634116966387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9707662295920388990565845 227523335060634116966387)
                  ·
                    rfl

theorem cell23_3987901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_3987901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987901 prefixEnd_3987901 := by exact prefixLift 3987901
  have htrace : WordTrace (prefixWord ++ tailWord_3987901) baseStart_3987901 baseEnd_3987901 := by
    simpa [prefixWord, tailWord_3987901, baseEnd_3987901] using wordTrace_append hprefix tailTrace_3987901
  have hstable : (prefixWord ++ tailWord_3987901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987901).length < 2 ^ (prefixWord ++ tailWord_3987901).sum := by decide
  have hdescent : baseEnd_3987901 < baseStart_3987901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987912 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_3987912 : Nat := 118140960795 + 3987912 * 2 ^ 59
def prefixEnd_3987912 : Nat := 4983230072969 + 3 ^ 40 * 3987912 * 2
def baseEnd_3987912 : Nat := 2047715663832906509659933

theorem tailTrace_3987912 : CollatzResearch.WordTrace tailWord_3987912 prefixEnd_3987912 2047715663832906509659933 := by
  unfold tailWord_3987912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72725549964241689995534995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96967399952322253327379993 72725549964241689995534995)
  ·
    refine ⟨109088324946362534993302493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72725549964241689995534995 109088324946362534993302493)
    ·
      refine ⟨40908121854885950622488435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109088324946362534993302493 40908121854885950622488435)
      ·
        refine ⟨61362182782328925933732653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40908121854885950622488435 61362182782328925933732653)
        ·
          refine ⟨23010818543373347225149745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61362182782328925933732653 23010818543373347225149745)
          ·
            refine ⟨17258113907530010418862309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23010818543373347225149745 17258113907530010418862309)
            ·
              refine ⟨3235896357661876953536683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17258113907530010418862309 3235896357661876953536683)
              ·
                refine ⟨4853844536492815430305025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3235896357661876953536683 4853844536492815430305025)
                ·
                  refine ⟨3640383402369611572728769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4853844536492815430305025 3640383402369611572728769)
                  ·
                    refine ⟨2730287551777208679546577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640383402369611572728769 2730287551777208679546577)
                    ·
                      refine ⟨2047715663832906509659933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730287551777208679546577 2047715663832906509659933)
                      ·
                        rfl

theorem cell23_3987912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_3987912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987912 prefixEnd_3987912 := by exact prefixLift 3987912
  have htrace : WordTrace (prefixWord ++ tailWord_3987912) baseStart_3987912 baseEnd_3987912 := by
    simpa [prefixWord, tailWord_3987912, baseEnd_3987912] using wordTrace_append hprefix tailTrace_3987912
  have hstable : (prefixWord ++ tailWord_3987912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987912).length < 2 ^ (prefixWord ++ tailWord_3987912).sum := by decide
  have hdescent : baseEnd_3987912 < baseStart_3987912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987971 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3]
def baseStart_3987971 : Nat := 118140960795 + 3987971 * 2 ^ 59
def prefixEnd_3987971 : Nat := 4983230072969 + 3 ^ 40 * 3987971 * 2
def baseEnd_3987971 : Nat := 2047745959191521778822161

theorem tailTrace_3987971 : CollatzResearch.WordTrace tailWord_3987971 prefixEnd_3987971 2047745959191521778822161 := by
  unfold tailWord_3987971
  simp only [CollatzResearch.WordTrace]
  refine ⟨145453251835269633067467767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96968834556846422044978511 145453251835269633067467767)
  ·
    refine ⟨218179877752904449601201651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145453251835269633067467767 218179877752904449601201651)
    ·
      refine ⟨327269816629356674401802477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218179877752904449601201651 327269816629356674401802477)
      ·
        refine ⟨122726181236008752900675929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327269816629356674401802477 122726181236008752900675929)
        ·
          refine ⟨92044635927006564675506947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122726181236008752900675929 92044635927006564675506947)
          ·
            refine ⟨138066953890509847013260421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92044635927006564675506947 138066953890509847013260421)
            ·
              refine ⟨25887553854470596314986329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138066953890509847013260421 25887553854470596314986329)
              ·
                refine ⟨19415665390852947236239747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25887553854470596314986329 19415665390852947236239747)
                ·
                  refine ⟨29123498086279420854359621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19415665390852947236239747 29123498086279420854359621)
                  ·
                    refine ⟨5460655891177391410192429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29123498086279420854359621 5460655891177391410192429)
                    ·
                      refine ⟨2047745959191521778822161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460655891177391410192429 2047745959191521778822161)
                      ·
                        rfl

theorem cell23_3987971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_3987971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987971 prefixEnd_3987971 := by exact prefixLift 3987971
  have htrace : WordTrace (prefixWord ++ tailWord_3987971) baseStart_3987971 baseEnd_3987971 := by
    simpa [prefixWord, tailWord_3987971, baseEnd_3987971] using wordTrace_append hprefix tailTrace_3987971
  have hstable : (prefixWord ++ tailWord_3987971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987971).length < 2 ^ (prefixWord ++ tailWord_3987971).sum := by decide
  have hdescent : baseEnd_3987971 < baseStart_3987971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3987978 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_3987978 : Nat := 118140960795 + 3987978 * 2 ^ 59
def prefixEnd_3987978 : Nat := 4983230072969 + 3 ^ 40 * 3987978 * 2
def baseEnd_3987978 : Nat := 682583184518701083811543

theorem tailTrace_3987978 : CollatzResearch.WordTrace tailWord_3987978 prefixEnd_3987978 682583184518701083811543 := by
  unfold tailWord_3987978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363376786561068315743147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96969004764162848841981725 36363376786561068315743147)
  ·
    refine ⟨54545065179841602473614721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36363376786561068315743147 54545065179841602473614721)
    ·
      refine ⟨40908798884881201855211041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54545065179841602473614721 40908798884881201855211041)
      ·
        refine ⟨30681599163660901391408281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40908798884881201855211041 30681599163660901391408281)
        ·
          refine ⟨23011199372745676043556211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30681599163660901391408281 23011199372745676043556211)
          ·
            refine ⟨34516799059118514065334317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23011199372745676043556211 34516799059118514065334317)
            ·
              refine ⟨12943799647169442774500369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34516799059118514065334317 12943799647169442774500369)
              ·
                refine ⟨9707849735377082080875277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12943799647169442774500369 9707849735377082080875277)
                ·
                  refine ⟨3640443650766405780328229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9707849735377082080875277 3640443650766405780328229)
                  ·
                    refine ⟨682583184518701083811543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640443650766405780328229 682583184518701083811543)
                    ·
                      rfl

theorem cell23_3987978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_3987978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3987978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3987978 prefixEnd_3987978 := by exact prefixLift 3987978
  have htrace : WordTrace (prefixWord ++ tailWord_3987978) baseStart_3987978 baseEnd_3987978 := by
    simpa [prefixWord, tailWord_3987978, baseEnd_3987978] using wordTrace_append hprefix tailTrace_3987978
  have hstable : (prefixWord ++ tailWord_3987978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3987978).length < 2 ^ (prefixWord ++ tailWord_3987978).sum := by decide
  have hdescent : baseEnd_3987978 < baseStart_3987978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3987978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988008 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 8]
def baseStart_3988008 : Nat := 118140960795 + 3988008 * 2 ^ 59
def prefixEnd_3988008 : Nat := 4983230072969 + 3 ^ 40 * 3988008 * 2
def baseEnd_3988008 : Nat := 227529439775082014895499

theorem tailTrace_3988008 : CollatzResearch.WordTrace tailWord_3988008 prefixEnd_3988008 227529439775082014895499 := by
  unfold tailWord_3988008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72727300668067794193282339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96969734224090392257709785 72727300668067794193282339)
  ·
    refine ⟨109090951002101691289923509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72727300668067794193282339 109090951002101691289923509)
    ·
      refine ⟨10227276656447033558430329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109090951002101691289923509 10227276656447033558430329)
      ·
        refine ⟨7670457492335275168822747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10227276656447033558430329 7670457492335275168822747)
        ·
          refine ⟨11505686238502912753234121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670457492335275168822747 11505686238502912753234121)
          ·
            refine ⟨8629264678877184564925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11505686238502912753234121 8629264678877184564925591)
            ·
              refine ⟨12943897018315776847388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629264678877184564925591 12943897018315776847388387)
              ·
                refine ⟨19415845527473665271082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12943897018315776847388387 19415845527473665271082581)
                ·
                  refine ⟨227529439775082014895499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19415845527473665271082581 227529439775082014895499)
                  ·
                    rfl

theorem cell23_3988008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_3988008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988008 prefixEnd_3988008 := by exact prefixLift 3988008
  have htrace : WordTrace (prefixWord ++ tailWord_3988008) baseStart_3988008 baseEnd_3988008 := by
    simpa [prefixWord, tailWord_3988008, baseEnd_3988008] using wordTrace_append hprefix tailTrace_3988008
  have hstable : (prefixWord ++ tailWord_3988008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988008).length < 2 ^ (prefixWord ++ tailWord_3988008).sum := by decide
  have hdescent : baseEnd_3988008 < baseStart_3988008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988068 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3988068 : Nat := 118140960795 + 3988068 * 2 ^ 59
def prefixEnd_3988068 : Nat := 4983230072969 + 3 ^ 40 * 3988068 * 2
def baseEnd_3988068 : Nat := 682598588938335966436405

theorem tailTrace_3988068 : CollatzResearch.WordTrace tailWord_3988068 prefixEnd_3988068 682598588938335966436405 := by
  unfold tailWord_3988068
  simp only [CollatzResearch.WordTrace]
  refine ⟨72728394857959109316874429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96971193143945479089165905 72728394857959109316874429)
  ·
    refine ⟨27273148071734665993827911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72728394857959109316874429 27273148071734665993827911)
    ·
      refine ⟨40909722107601998990741867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27273148071734665993827911 40909722107601998990741867)
      ·
        refine ⟨61364583161402998486112801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40909722107601998990741867 61364583161402998486112801)
        ·
          refine ⟨46023437371052248864584601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61364583161402998486112801 46023437371052248864584601)
          ·
            refine ⟨34517578028289186648438451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46023437371052248864584601 34517578028289186648438451)
            ·
              refine ⟨51776367042433779972657677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34517578028289186648438451 51776367042433779972657677)
              ·
                refine ⟨19416137640912667489746629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51776367042433779972657677 19416137640912667489746629)
                ·
                  refine ⟨3640525807671125154327493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19416137640912667489746629 3640525807671125154327493)
                  ·
                    refine ⟨682598588938335966436405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640525807671125154327493 682598588938335966436405)
                    ·
                      rfl

theorem cell23_3988068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3988068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988068 prefixEnd_3988068 := by exact prefixLift 3988068
  have htrace : WordTrace (prefixWord ++ tailWord_3988068) baseStart_3988068 baseEnd_3988068 := by
    simpa [prefixWord, tailWord_3988068, baseEnd_3988068] using wordTrace_append hprefix tailTrace_3988068
  have hstable : (prefixWord ++ tailWord_3988068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988068).length < 2 ^ (prefixWord ++ tailWord_3988068).sum := by decide
  have hdescent : baseEnd_3988068 < baseStart_3988068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988069 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 3, 1, 3]
def baseStart_3988069 : Nat := 118140960795 + 3988069 * 2 ^ 59
def prefixEnd_3988069 : Nat := 4983230072969 + 3 ^ 40 * 3988069 * 2
def baseEnd_3988069 : Nat := 2047796280295662395396711

theorem tailTrace_3988069 : CollatzResearch.WordTrace tailWord_3988069 prefixEnd_3988069 2047796280295662395396711 := by
  unfold tailWord_3988069
  simp only [CollatzResearch.WordTrace]
  refine ⟨145456826188914595804535261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96971217459276397203023507 145456826188914595804535261)
  ·
    refine ⟨54546309820842973426700723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145456826188914595804535261 54546309820842973426700723)
    ·
      refine ⟨81819464731264460140051085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54546309820842973426700723 81819464731264460140051085)
      ·
        refine ⟨30682299274224172552519157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81819464731264460140051085 30682299274224172552519157)
        ·
          refine ⟨2876465556958516176798671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30682299274224172552519157 2876465556958516176798671)
          ·
            refine ⟨4314698335437774265198007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876465556958516176798671 4314698335437774265198007)
            ·
              refine ⟨6472047503156661397797011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4314698335437774265198007 6472047503156661397797011)
              ·
                refine ⟨9708071254734992096695517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472047503156661397797011 9708071254734992096695517)
                ·
                  refine ⟨3640526720525622036260819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9708071254734992096695517 3640526720525622036260819)
                  ·
                    refine ⟨5460790080788433054391229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640526720525622036260819 5460790080788433054391229)
                    ·
                      refine ⟨2047796280295662395396711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460790080788433054391229 2047796280295662395396711)
                      ·
                        rfl

theorem cell23_3988069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_3988069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988069 prefixEnd_3988069 := by exact prefixLift 3988069
  have htrace : WordTrace (prefixWord ++ tailWord_3988069) baseStart_3988069 baseEnd_3988069 := by
    simpa [prefixWord, tailWord_3988069, baseEnd_3988069] using wordTrace_append hprefix tailTrace_3988069
  have hstable : (prefixWord ++ tailWord_3988069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988069).length < 2 ^ (prefixWord ++ tailWord_3988069).sum := by decide
  have hdescent : baseEnd_3988069 < baseStart_3988069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988075 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 3, 2, 2]
def baseStart_3988075 : Nat := 118140960795 + 3988075 * 2 ^ 59
def prefixEnd_3988075 : Nat := 4983230072969 + 3 ^ 40 * 3988075 * 2
def baseEnd_3988075 : Nat := 2047799361179589371921683

theorem tailTrace_3988075 : CollatzResearch.WordTrace tailWord_3988075 prefixEnd_3988075 2047799361179589371921683 := by
  unfold tailWord_3988075
  simp only [CollatzResearch.WordTrace]
  refine ⟨145457045026892858829253679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96971363351261905886169119 145457045026892858829253679)
  ·
    refine ⟨218185567540339288243880519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145457045026892858829253679 218185567540339288243880519)
    ·
      refine ⟨327278351310508932365820779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218185567540339288243880519 327278351310508932365820779)
      ·
        refine ⟨490917526965763398548731169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327278351310508932365820779 490917526965763398548731169)
        ·
          refine ⟨368188145224322548911548377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490917526965763398548731169 368188145224322548911548377)
          ·
            refine ⟨276141108918241911683661283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368188145224322548911548377 276141108918241911683661283)
            ·
              refine ⟨414211663377362867525491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276141108918241911683661283 414211663377362867525491925)
              ·
                refine ⟨9708085860406942207628717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414211663377362867525491925 9708085860406942207628717)
                ·
                  refine ⟨3640532197652603327860769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9708085860406942207628717 3640532197652603327860769)
                  ·
                    refine ⟨2730399148239452495895577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640532197652603327860769 2730399148239452495895577)
                    ·
                      refine ⟨2047799361179589371921683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730399148239452495895577 2047799361179589371921683)
                      ·
                        rfl

theorem cell23_3988075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2, 2].length) (baseStart_3988075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988075 prefixEnd_3988075 := by exact prefixLift 3988075
  have htrace : WordTrace (prefixWord ++ tailWord_3988075) baseStart_3988075 baseEnd_3988075 := by
    simpa [prefixWord, tailWord_3988075, baseEnd_3988075] using wordTrace_append hprefix tailTrace_3988075
  have hstable : (prefixWord ++ tailWord_3988075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988075).length < 2 ^ (prefixWord ++ tailWord_3988075).sum := by decide
  have hdescent : baseEnd_3988075 < baseStart_3988075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988125 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3988125 : Nat := 118140960795 + 3988125 * 2 ^ 59
def prefixEnd_3988125 : Nat := 4983230072969 + 3 ^ 40 * 3988125 * 2
def baseEnd_3988125 : Nat := 2047825035212314176296453

theorem tailTrace_3988125 : CollatzResearch.WordTrace tailWord_3988125 prefixEnd_3988125 2047825035212314176296453 := by
  unfold tailWord_3988125
  simp only [CollatzResearch.WordTrace]
  refine ⟨145458868676711717368573829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96972579117807811579049219 145458868676711717368573829)
  ·
    refine ⟨27273537876883447006607593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145458868676711717368573829 27273537876883447006607593)
    ·
      refine ⟨20455153407662585254955695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27273537876883447006607593 20455153407662585254955695)
      ·
        refine ⟨30682730111493877882433543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20455153407662585254955695 30682730111493877882433543)
        ·
          refine ⟨46024095167240816823650315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30682730111493877882433543 46024095167240816823650315)
          ·
            refine ⟨69036142750861225235475473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46024095167240816823650315 69036142750861225235475473)
            ·
              refine ⟨51777107063145918926606605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69036142750861225235475473 51777107063145918926606605)
              ·
                refine ⟨19416415148679719597477477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51777107063145918926606605 19416415148679719597477477)
                ·
                  refine ⟨3640577840377447424527027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19416415148679719597477477 3640577840377447424527027)
                  ·
                    refine ⟨5460866760566171136790541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640577840377447424527027 5460866760566171136790541)
                    ·
                      refine ⟨2047825035212314176296453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460866760566171136790541 2047825035212314176296453)
                      ·
                        rfl

theorem cell23_3988125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3988125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988125 prefixEnd_3988125 := by exact prefixLift 3988125
  have htrace : WordTrace (prefixWord ++ tailWord_3988125) baseStart_3988125 baseEnd_3988125 := by
    simpa [prefixWord, tailWord_3988125, baseEnd_3988125] using wordTrace_append hprefix tailTrace_3988125
  have hstable : (prefixWord ++ tailWord_3988125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988125).length < 2 ^ (prefixWord ++ tailWord_3988125).sum := by decide
  have hdescent : baseEnd_3988125 < baseStart_3988125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988126 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3988126 : Nat := 118140960795 + 3988126 * 2 ^ 59
def prefixEnd_3988126 : Nat := 4983230072969 + 3 ^ 40 * 3988126 * 2
def baseEnd_3988126 : Nat := 2047825548692968672383949

theorem tailTrace_3988126 : CollatzResearch.WordTrace tailWord_3988126 prefixEnd_3988126 2047825548692968672383949 := by
  unfold tailWord_3988126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182363143713511817420029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96972603433138729692906821 18182363143713511817420029)
  ·
    refine ⟨6818386178892566931532511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18182363143713511817420029 6818386178892566931532511)
    ·
      refine ⟨10227579268338850397298767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6818386178892566931532511 10227579268338850397298767)
      ·
        refine ⟨15341368902508275595948151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227579268338850397298767 15341368902508275595948151)
        ·
          refine ⟨23012053353762413393922227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15341368902508275595948151 23012053353762413393922227)
          ·
            refine ⟨34518080030643620090883341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012053353762413393922227 34518080030643620090883341)
            ·
              refine ⟨12944280011491357534081253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34518080030643620090883341 12944280011491357534081253)
              ·
                refine ⟨2427052502154629537640235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12944280011491357534081253 2427052502154629537640235)
                ·
                  refine ⟨3640578753231944306460353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427052502154629537640235 3640578753231944306460353)
                  ·
                    refine ⟨2730434064923958229845265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640578753231944306460353 2730434064923958229845265)
                    ·
                      refine ⟨2047825548692968672383949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730434064923958229845265 2047825548692968672383949)
                      ·
                        rfl

theorem cell23_3988126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3988126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988126 prefixEnd_3988126 := by exact prefixLift 3988126
  have htrace : WordTrace (prefixWord ++ tailWord_3988126) baseStart_3988126 baseEnd_3988126 := by
    simpa [prefixWord, tailWord_3988126, baseEnd_3988126] using wordTrace_append hprefix tailTrace_3988126
  have hstable : (prefixWord ++ tailWord_3988126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988126).length < 2 ^ (prefixWord ++ tailWord_3988126).sum := by decide
  have hdescent : baseEnd_3988126 < baseStart_3988126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988142 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3988142 : Nat := 118140960795 + 3988142 * 2 ^ 59
def prefixEnd_3988142 : Nat := 4983230072969 + 3 ^ 40 * 3988142 * 2
def baseEnd_3988142 : Nat := 2047833764383440609783875

theorem tailTrace_3988142 : CollatzResearch.WordTrace tailWord_3988142 prefixEnd_3988142 2047833764383440609783875 := by
  unfold tailWord_3988142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182436089706266158992835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96972992478433419514628453 18182436089706266158992835)
  ·
    refine ⟨27273654134559399238489253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18182436089706266158992835 27273654134559399238489253)
    ·
      refine ⟨5113810150229887357216735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27273654134559399238489253 5113810150229887357216735)
      ·
        refine ⟨7670715225344831035825103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113810150229887357216735 7670715225344831035825103)
        ·
          refine ⟨11506072838017246553737655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670715225344831035825103 11506072838017246553737655)
          ·
            refine ⟨17259109257025869830606483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506072838017246553737655 17259109257025869830606483)
            ·
              refine ⟨25888663885538804745909725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17259109257025869830606483 25888663885538804745909725)
              ·
                refine ⟨9708248957077051779716147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25888663885538804745909725 9708248957077051779716147)
                ·
                  refine ⟨14562373435615577669574221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9708248957077051779716147 14562373435615577669574221)
                  ·
                    refine ⟨5460890038355841626090333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14562373435615577669574221 5460890038355841626090333)
                    ·
                      refine ⟨2047833764383440609783875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5460890038355841626090333 2047833764383440609783875)
                      ·
                        rfl

theorem cell23_3988142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3988142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988142 prefixEnd_3988142 := by exact prefixLift 3988142
  have htrace : WordTrace (prefixWord ++ tailWord_3988142) baseStart_3988142 baseEnd_3988142 := by
    simpa [prefixWord, tailWord_3988142, baseEnd_3988142] using wordTrace_append hprefix tailTrace_3988142
  have hstable : (prefixWord ++ tailWord_3988142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988142).length < 2 ^ (prefixWord ++ tailWord_3988142).sum := by decide
  have hdescent : baseEnd_3988142 < baseStart_3988142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988158 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3988158 : Nat := 118140960795 + 3988158 * 2 ^ 59
def prefixEnd_3988158 : Nat := 4983230072969 + 3 ^ 40 * 3988158 * 2
def baseEnd_3988158 : Nat := 682613993357970849061267

theorem tailTrace_3988158 : CollatzResearch.WordTrace tailWord_3988158 prefixEnd_3988158 682613993357970849061267 := by
  unfold tailWord_3988158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182509035699020500565641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96973381523728109336350085 18182509035699020500565641)
  ·
    refine ⟨13636881776774265375424231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18182509035699020500565641 13636881776774265375424231)
    ·
      refine ⟨20455322665161398063136347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13636881776774265375424231 20455322665161398063136347)
      ·
        refine ⟨30682983997742097094704521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20455322665161398063136347 30682983997742097094704521)
        ·
          refine ⟨23012237998306572821028391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30682983997742097094704521 23012237998306572821028391)
          ·
            refine ⟨34518356997459859231542587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23012237998306572821028391 34518356997459859231542587)
            ·
              refine ⟨51777535496189788847313881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34518356997459859231542587 51777535496189788847313881)
              ·
                refine ⟨38833151622142341635485411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51777535496189788847313881 38833151622142341635485411)
                ·
                  refine ⟨58249727433213512453228117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38833151622142341635485411 58249727433213512453228117)
                  ·
                    refine ⟨682613993357970849061267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58249727433213512453228117 682613993357970849061267)
                    ·
                      rfl

theorem cell23_3988158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3988158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988158 prefixEnd_3988158 := by exact prefixLift 3988158
  have htrace : WordTrace (prefixWord ++ tailWord_3988158) baseStart_3988158 baseEnd_3988158 := by
    simpa [prefixWord, tailWord_3988158, baseEnd_3988158] using wordTrace_append hprefix tailTrace_3988158
  have hstable : (prefixWord ++ tailWord_3988158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988158).length < 2 ^ (prefixWord ++ tailWord_3988158).sum := by decide
  have hdescent : baseEnd_3988158 < baseStart_3988158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988195 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3988195 : Nat := 118140960795 + 3988195 * 2 ^ 59
def prefixEnd_3988195 : Nat := 4983230072969 + 3 ^ 40 * 3988195 * 2
def baseEnd_3988195 : Nat := 2047860978858128902421131

theorem tailTrace_3988195 : CollatzResearch.WordTrace tailWord_3988195 prefixEnd_3988195 2047860978858128902421131 := by
  unfold tailWord_3988195
  simp only [CollatzResearch.WordTrace]
  refine ⟨145461421786458119323622039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96974281190972079549081359 145461421786458119323622039)
  ·
    refine ⟨218192132679687178985433059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145461421786458119323622039 218192132679687178985433059)
    ·
      refine ⟨327288199019530768478149589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218192132679687178985433059 327288199019530768478149589)
      ·
        refine ⟨7670817164520252386206631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 327288199019530768478149589 7670817164520252386206631)
        ·
          refine ⟨11506225746780378579309947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670817164520252386206631 11506225746780378579309947)
          ·
            refine ⟨17259338620170567868964921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506225746780378579309947 17259338620170567868964921)
            ·
              refine ⟨12944503965127925901723691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17259338620170567868964921 12944503965127925901723691)
              ·
                refine ⟨19416755947691888852585537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944503965127925901723691 19416755947691888852585537)
                ·
                  refine ⟨14562566960768916639439153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19416755947691888852585537 14562566960768916639439153)
                  ·
                    refine ⟨10921925220576687479579365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14562566960768916639439153 10921925220576687479579365)
                    ·
                      refine ⟨2047860978858128902421131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10921925220576687479579365 2047860978858128902421131)
                      ·
                        rfl

theorem cell23_3988195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3988195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988195 prefixEnd_3988195 := by exact prefixLift 3988195
  have htrace : WordTrace (prefixWord ++ tailWord_3988195) baseStart_3988195 baseEnd_3988195 := by
    simpa [prefixWord, tailWord_3988195, baseEnd_3988195] using wordTrace_append hprefix tailTrace_3988195
  have hstable : (prefixWord ++ tailWord_3988195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988195).length < 2 ^ (prefixWord ++ tailWord_3988195).sum := by decide
  have hdescent : baseEnd_3988195 < baseStart_3988195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988218 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_3988218 : Nat := 118140960795 + 3988218 * 2 ^ 59
def prefixEnd_3988218 : Nat := 4983230072969 + 3 ^ 40 * 3988218 * 2
def baseEnd_3988218 : Nat := 682624262971060770811175

theorem tailTrace_3988218 : CollatzResearch.WordTrace tailWord_3988218 prefixEnd_3988218 682624262971060770811175 := by
  unfold tailWord_3988218
  simp only [CollatzResearch.WordTrace]
  refine ⟨36365565166343698562927327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96974840443583196167806205 36365565166343698562927327)
  ·
    refine ⟨54548347749515547844390991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36365565166343698562927327 54548347749515547844390991)
    ·
      refine ⟨81822521624273321766586487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54548347749515547844390991 81822521624273321766586487)
      ·
        refine ⟨122733782436409982649879731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81822521624273321766586487 122733782436409982649879731)
        ·
          refine ⟨184100673654614973974819597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122733782436409982649879731 184100673654614973974819597)
          ·
            refine ⟨69037752620480615240557349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184100673654614973974819597 69037752620480615240557349)
            ·
              refine ⟨12944578616340115357604503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69037752620480615240557349 12944578616340115357604503)
              ·
                refine ⟨19416867924510173036406755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944578616340115357604503 19416867924510173036406755)
                ·
                  refine ⟨29125301886765259554610133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19416867924510173036406755 29125301886765259554610133)
                  ·
                    refine ⟨682624262971060770811175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29125301886765259554610133 682624262971060770811175)
                    ·
                      rfl

theorem cell23_3988218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_3988218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988218 prefixEnd_3988218 := by exact prefixLift 3988218
  have htrace : WordTrace (prefixWord ++ tailWord_3988218) baseStart_3988218 baseEnd_3988218 := by
    simpa [prefixWord, tailWord_3988218, baseEnd_3988218] using wordTrace_append hprefix tailTrace_3988218
  have hstable : (prefixWord ++ tailWord_3988218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988218).length < 2 ^ (prefixWord ++ tailWord_3988218).sum := by decide
  have hdescent : baseEnd_3988218 < baseStart_3988218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988225 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3988225 : Nat := 118140960795 + 3988225 * 2 ^ 59
def prefixEnd_3988225 : Nat := 4983230072969 + 3 ^ 40 * 3988225 * 2
def baseEnd_3988225 : Nat := 2047876383277763785045993

theorem tailTrace_3988225 : CollatzResearch.WordTrace tailWord_3988225 prefixEnd_3988225 2047876383277763785045993 := by
  unfold tailWord_3988225
  simp only [CollatzResearch.WordTrace]
  refine ⟨145462515976349434447214129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96975010650899622964809419 145462515976349434447214129)
  ·
    refine ⟨109096886982262075835410597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145462515976349434447214129 109096886982262075835410597)
    ·
      refine ⟨20455666309174139219139487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109096886982262075835410597 20455666309174139219139487)
      ·
        refine ⟨30683499463761208828709231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20455666309174139219139487 30683499463761208828709231)
        ·
          refine ⟨46025249195641813243063847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30683499463761208828709231 46025249195641813243063847)
          ·
            refine ⟨69037873793462719864595771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46025249195641813243063847 69037873793462719864595771)
            ·
              refine ⟨103556810690194079796893657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69037873793462719864595771 103556810690194079796893657)
              ·
                refine ⟨77667608017645559847670243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103556810690194079796893657 77667608017645559847670243)
                ·
                  refine ⟨116501412026468339771505365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77667608017645559847670243 116501412026468339771505365)
                  ·
                    refine ⟨2730501844370351713394657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116501412026468339771505365 2730501844370351713394657)
                    ·
                      refine ⟨2047876383277763785045993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730501844370351713394657 2047876383277763785045993)
                      ·
                        rfl

theorem cell23_3988225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3988225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988225 prefixEnd_3988225 := by exact prefixLift 3988225
  have htrace : WordTrace (prefixWord ++ tailWord_3988225) baseStart_3988225 baseEnd_3988225 := by
    simpa [prefixWord, tailWord_3988225, baseEnd_3988225] using wordTrace_append hprefix tailTrace_3988225
  have hstable : (prefixWord ++ tailWord_3988225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988225).length < 2 ^ (prefixWord ++ tailWord_3988225).sum := by decide
  have hdescent : baseEnd_3988225 < baseStart_3988225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 9, 2]
def baseStart_3988315 : Nat := 118140960795 + 3988315 * 2 ^ 59
def prefixEnd_3988315 : Nat := 4983230072969 + 3 ^ 40 * 3988315 * 2
def baseEnd_3988315 : Nat := 2047922596536668432920579

theorem tailTrace_3988315 : CollatzResearch.WordTrace tailWord_3988315 prefixEnd_3988315 2047922596536668432920579 := by
  unfold tailWord_3988315
  simp only [CollatzResearch.WordTrace]
  refine ⟨145465798546023379817990399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96977199030682253211993599 145465798546023379817990399)
  ·
    refine ⟨218198697819035069726985599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145465798546023379817990399 218198697819035069726985599)
    ·
      refine ⟨327298046728552604590478399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218198697819035069726985599 327298046728552604590478399)
      ·
        refine ⟨490947070092828906885717599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327298046728552604590478399 490947070092828906885717599)
        ·
          refine ⟨736420605139243360328576399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490947070092828906885717599 736420605139243360328576399)
          ·
            refine ⟨1104630907708865040492864599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736420605139243360328576399 1104630907708865040492864599)
            ·
              refine ⟨1656946361563297560739296899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104630907708865040492864599 1656946361563297560739296899)
              ·
                refine ⟨2485419542344946341108945349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656946361563297560739296899 2485419542344946341108945349)
                ·
                  refine ⟨466016164189677438957927253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2485419542344946341108945349 466016164189677438957927253)
                  ·
                    refine ⟨2730563462048891243894105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 466016164189677438957927253 2730563462048891243894105)
                    ·
                      refine ⟨2047922596536668432920579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730563462048891243894105 2047922596536668432920579)
                      ·
                        rfl

theorem cell23_3988315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9, 2].length) (baseStart_3988315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988315 prefixEnd_3988315 := by exact prefixLift 3988315
  have htrace : WordTrace (prefixWord ++ tailWord_3988315) baseStart_3988315 baseEnd_3988315 := by
    simpa [prefixWord, tailWord_3988315, baseEnd_3988315] using wordTrace_append hprefix tailTrace_3988315
  have hstable : (prefixWord ++ tailWord_3988315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988315).length < 2 ^ (prefixWord ++ tailWord_3988315).sum := by decide
  have hdescent : baseEnd_3988315 < baseStart_3988315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988325 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_3988325 : Nat := 118140960795 + 3988325 * 2 ^ 59
def prefixEnd_3988325 : Nat := 4983230072969 + 3 ^ 40 * 3988325 * 2
def baseEnd_3988325 : Nat := 682642577114404464598511

theorem tailTrace_3988325 : CollatzResearch.WordTrace tailWord_3988325 prefixEnd_3988325 682642577114404464598511 := by
  unfold tailWord_3988325
  simp only [CollatzResearch.WordTrace]
  refine ⟨145466163275987151525854429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96977442183991434350569619 145466163275987151525854429)
  ·
    refine ⟨54549811228495181822195411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145466163275987151525854429 54549811228495181822195411)
    ·
      refine ⟨81824716842742772733293117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54549811228495181822195411 81824716842742772733293117)
      ·
        refine ⟨30684268816028539774984919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81824716842742772733293117 30684268816028539774984919)
        ·
          refine ⟨46026403224042809662477379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30684268816028539774984919 46026403224042809662477379)
          ·
            refine ⟨69039604836064214493716069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46026403224042809662477379 69039604836064214493716069)
            ·
              refine ⟨12944925906762040217571763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69039604836064214493716069 12944925906762040217571763)
              ·
                refine ⟨19417388860143060326357645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944925906762040217571763 19417388860143060326357645)
                ·
                  refine ⟨7281520822553647622384117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19417388860143060326357645 7281520822553647622384117)
                  ·
                    refine ⟨682642577114404464598511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7281520822553647622384117 682642577114404464598511)
                    ·
                      rfl

theorem cell23_3988325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_3988325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988325 prefixEnd_3988325 := by exact prefixLift 3988325
  have htrace : WordTrace (prefixWord ++ tailWord_3988325) baseStart_3988325 baseEnd_3988325 := by
    simpa [prefixWord, tailWord_3988325, baseEnd_3988325] using wordTrace_append hprefix tailTrace_3988325
  have hstable : (prefixWord ++ tailWord_3988325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988325).length < 2 ^ (prefixWord ++ tailWord_3988325).sum := by decide
  have hdescent : baseEnd_3988325 < baseStart_3988325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988332 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_3988332 : Nat := 118140960795 + 3988332 * 2 ^ 59
def prefixEnd_3988332 : Nat := 4983230072969 + 3 ^ 40 * 3988332 * 2
def baseEnd_3988332 : Nat := 2047931325707794866408001

theorem tailTrace_3988332 : CollatzResearch.WordTrace tailWord_3988332 prefixEnd_3988332 2047931325707794866408001 := by
  unfold tailWord_3988332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72733209293480895860679625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96977612391307861147572833 72733209293480895860679625)
  ·
    refine ⟨54549906970110671895509719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72733209293480895860679625 54549906970110671895509719)
    ·
      refine ⟨81824860455166007843264579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54549906970110671895509719 81824860455166007843264579)
      ·
        refine ⟨122737290682749011764896869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81824860455166007843264579 122737290682749011764896869)
        ·
          refine ⟨23013242003015439705918163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122737290682749011764896869 23013242003015439705918163)
          ·
            refine ⟨34519863004523159558877245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23013242003015439705918163 34519863004523159558877245)
            ·
              refine ⟨12944948626696184834578967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34519863004523159558877245 12944948626696184834578967)
              ·
                refine ⟨19417422940044277251868451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12944948626696184834578967 19417422940044277251868451)
                ·
                  refine ⟨29126134410066415877802677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19417422940044277251868451 29126134410066415877802677)
                  ·
                    refine ⟨2730575100943726488544001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29126134410066415877802677 2730575100943726488544001)
                    ·
                      refine ⟨2047931325707794866408001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730575100943726488544001 2047931325707794866408001)
                      ·
                        rfl

theorem cell23_3988332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_3988332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988332 prefixEnd_3988332 := by exact prefixLift 3988332
  have htrace : WordTrace (prefixWord ++ tailWord_3988332) baseStart_3988332 baseEnd_3988332 := by
    simpa [prefixWord, tailWord_3988332, baseEnd_3988332] using wordTrace_append hprefix tailTrace_3988332
  have hstable : (prefixWord ++ tailWord_3988332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988332).length < 2 ^ (prefixWord ++ tailWord_3988332).sum := by decide
  have hdescent : baseEnd_3988332 < baseStart_3988332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988339 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 1, 1, 3]
def baseStart_3988339 : Nat := 118140960795 + 3988339 * 2 ^ 59
def prefixEnd_3988339 : Nat := 4983230072969 + 3 ^ 40 * 3988339 * 2
def baseEnd_3988339 : Nat := 2047934920072376339020469

theorem tailTrace_3988339 : CollatzResearch.WordTrace tailWord_3988339 prefixEnd_3988339 2047934920072376339020469 := by
  unfold tailWord_3988339
  simp only [CollatzResearch.WordTrace]
  refine ⟨145466673897936431916864071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96977782598624287944576047 145466673897936431916864071)
  ·
    refine ⟨218200010846904647875296107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145466673897936431916864071 218200010846904647875296107)
    ·
      refine ⟨327300016270356971812944161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218200010846904647875296107 327300016270356971812944161)
      ·
        refine ⟨245475012202767728859708121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327300016270356971812944161 245475012202767728859708121)
        ·
          refine ⟨184106259152075796644781091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245475012202767728859708121 184106259152075796644781091)
          ·
            refine ⟨276159388728113694967171637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184106259152075796644781091 276159388728113694967171637)
            ·
              refine ⟨25889942693260658903172341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276159388728113694967171637 25889942693260658903172341)
              ·
                refine ⟨2427182127493186772172407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25889942693260658903172341 2427182127493186772172407)
                ·
                  refine ⟨3640773191239780158258611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427182127493186772172407 3640773191239780158258611)
                  ·
                    refine ⟨5461159786859670237387917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3640773191239780158258611 5461159786859670237387917)
                    ·
                      refine ⟨2047934920072376339020469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5461159786859670237387917 2047934920072376339020469)
                      ·
                        rfl

theorem cell23_3988339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 1, 3].length) (baseStart_3988339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988339 prefixEnd_3988339 := by exact prefixLift 3988339
  have htrace : WordTrace (prefixWord ++ tailWord_3988339) baseStart_3988339 baseEnd_3988339 := by
    simpa [prefixWord, tailWord_3988339, baseEnd_3988339] using wordTrace_append hprefix tailTrace_3988339
  have hstable : (prefixWord ++ tailWord_3988339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988339).length < 2 ^ (prefixWord ++ tailWord_3988339).sum := by decide
  have hdescent : baseEnd_3988339 < baseStart_3988339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988375 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3988375 : Nat := 118140960795 + 3988375 * 2 ^ 59
def prefixEnd_3988375 : Nat := 4983230072969 + 3 ^ 40 * 3988375 * 2
def baseEnd_3988375 : Nat := 2047953405375938198170303

theorem tailTrace_3988375 : CollatzResearch.WordTrace tailWord_3988375 prefixEnd_3988375 2047953405375938198170303 := by
  unfold tailWord_3988375
  simp only [CollatzResearch.WordTrace]
  refine ⟨145467986925806010065174579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96978657950537340043449719 145467986925806010065174579)
  ·
    refine ⟨218201980388709015097761869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145467986925806010065174579 218201980388709015097761869)
    ·
      refine ⟨81825742645765880661660701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218201980388709015097761869 81825742645765880661660701)
      ·
        refine ⟨30684653492162205248122763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81825742645765880661660701 30684653492162205248122763)
        ·
          refine ⟨46026980238243307872184145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30684653492162205248122763 46026980238243307872184145)
          ·
            refine ⟨34520235178682480904138109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46026980238243307872184145 34520235178682480904138109)
            ·
              refine ⟨12945088192005930339051791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34520235178682480904138109 12945088192005930339051791)
              ·
                refine ⟨19417632288008895508577687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12945088192005930339051791 19417632288008895508577687)
                ·
                  refine ⟨29126448432013343262866531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19417632288008895508577687 29126448432013343262866531)
                  ·
                    refine ⟨43689672648020014894299797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29126448432013343262866531 43689672648020014894299797)
                    ·
                      refine ⟨2047953405375938198170303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43689672648020014894299797 2047953405375938198170303)
                      ·
                        rfl

theorem cell23_3988375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3988375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988375 prefixEnd_3988375 := by exact prefixLift 3988375
  have htrace : WordTrace (prefixWord ++ tailWord_3988375) baseStart_3988375 baseEnd_3988375 := by
    simpa [prefixWord, tailWord_3988375, baseEnd_3988375] using wordTrace_append hprefix tailTrace_3988375
  have hstable : (prefixWord ++ tailWord_3988375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988375).length < 2 ^ (prefixWord ++ tailWord_3988375).sum := by decide
  have hdescent : baseEnd_3988375 < baseStart_3988375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988413 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3988413 : Nat := 118140960795 + 3988413 * 2 ^ 59
def prefixEnd_3988413 : Nat := 4983230072969 + 3 ^ 40 * 3988413 * 2
def baseEnd_3988413 : Nat := 2047972917640809049495129

theorem tailTrace_3988413 : CollatzResearch.WordTrace tailWord_3988413 prefixEnd_3988413 2047972917640809049495129 := by
  unfold tailWord_3988413
  simp only [CollatzResearch.WordTrace]
  refine ⟨145469372899668342555057893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96979581933112228370038595 145469372899668342555057893)
  ·
    refine ⟨27275507418687814229073355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145469372899668342555057893 27275507418687814229073355)
    ·
      refine ⟨40913261128031721343610033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27275507418687814229073355 40913261128031721343610033)
      ·
        refine ⟨30684945846023791007707525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40913261128031721343610033 30684945846023791007707525)
        ·
          refine ⟨5753427346129460813945161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30684945846023791007707525 5753427346129460813945161)
          ·
            refine ⟨4315070509597095610458871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753427346129460813945161 4315070509597095610458871)
            ·
              refine ⟨6472605764395643415688307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315070509597095610458871 6472605764395643415688307)
              ·
                refine ⟨9708908646593465123532461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472605764395643415688307 9708908646593465123532461)
                ·
                  refine ⟨3640840742472549421324673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9708908646593465123532461 3640840742472549421324673)
                  ·
                    refine ⟨2730630556854412065993505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3640840742472549421324673 2730630556854412065993505)
                    ·
                      refine ⟨2047972917640809049495129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730630556854412065993505 2047972917640809049495129)
                      ·
                        rfl

theorem cell23_3988413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3988413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988413 prefixEnd_3988413 := by exact prefixLift 3988413
  have htrace : WordTrace (prefixWord ++ tailWord_3988413) baseStart_3988413 baseEnd_3988413 := by
    simpa [prefixWord, tailWord_3988413, baseEnd_3988413] using wordTrace_append hprefix tailTrace_3988413
  have hstable : (prefixWord ++ tailWord_3988413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988413).length < 2 ^ (prefixWord ++ tailWord_3988413).sum := by decide
  have hdescent : baseEnd_3988413 < baseStart_3988413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988439 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_3988439 : Nat := 118140960795 + 3988439 * 2 ^ 59
def prefixEnd_3988439 : Nat := 4983230072969 + 3 ^ 40 * 3988439 * 2
def baseEnd_3988439 : Nat := 2047986268137825947770009

theorem tailTrace_3988439 : CollatzResearch.WordTrace tailWord_3988439 prefixEnd_3988439 2047986268137825947770009 := by
  unfold tailWord_3988439
  simp only [CollatzResearch.WordTrace]
  refine ⟨145470321197574148995504371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96980214131716099330336247 145470321197574148995504371)
  ·
    refine ⟨218205481796361223493256557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145470321197574148995504371 218205481796361223493256557)
    ·
      refine ⟨81827055673635458809971209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218205481796361223493256557 81827055673635458809971209)
      ·
        refine ⟨61370291755226594107478407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81827055673635458809971209 61370291755226594107478407)
        ·
          refine ⟨92055437632839891161217611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61370291755226594107478407 92055437632839891161217611)
          ·
            refine ⟨138083156449259836741826417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92055437632839891161217611 138083156449259836741826417)
            ·
              refine ⟨103562367336944877556369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138083156449259836741826417 103562367336944877556369813)
              ·
                refine ⟨4854485968919291135454835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103562367336944877556369813 4854485968919291135454835)
                ·
                  refine ⟨7281728953378936703182253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854485968919291135454835 7281728953378936703182253)
                  ·
                    refine ⟨2730648357517101263693345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7281728953378936703182253 2730648357517101263693345)
                    ·
                      refine ⟨2047986268137825947770009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730648357517101263693345 2047986268137825947770009)
                      ·
                        rfl

theorem cell23_3988439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_3988439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988439 prefixEnd_3988439 := by exact prefixLift 3988439
  have htrace : WordTrace (prefixWord ++ tailWord_3988439) baseStart_3988439 baseEnd_3988439 := by
    simpa [prefixWord, tailWord_3988439, baseEnd_3988439] using wordTrace_append hprefix tailTrace_3988439
  have hstable : (prefixWord ++ tailWord_3988439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988439).length < 2 ^ (prefixWord ++ tailWord_3988439).sum := by decide
  have hdescent : baseEnd_3988439 < baseStart_3988439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988475 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 7]
def baseStart_3988475 : Nat := 118140960795 + 3988475 * 2 ^ 59
def prefixEnd_3988475 : Nat := 4983230072969 + 3 ^ 40 * 3988475 * 2
def baseEnd_3988475 : Nat := 227556083715709756324427

theorem tailTrace_3988475 : CollatzResearch.WordTrace tailWord_3988475 prefixEnd_3988475 227556083715709756324427 := by
  unfold tailWord_3988475
  simp only [CollatzResearch.WordTrace]
  refine ⟨145471634225443727143814879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96981089483629151429209919 145471634225443727143814879)
  ·
    refine ⟨218207451338165590715722319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145471634225443727143814879 218207451338165590715722319)
    ·
      refine ⟨327311177007248386073583479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218207451338165590715722319 327311177007248386073583479)
      ·
        refine ⟨490966765510872579110375219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327311177007248386073583479 490966765510872579110375219)
        ·
          refine ⟨736450148266308868665562829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490966765510872579110375219 736450148266308868665562829)
          ·
            refine ⟨276168805599865825749586061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736450148266308868665562829 276168805599865825749586061)
            ·
              refine ⟨103563302099949684656094773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276168805599865825749586061 103563302099949684656094773)
              ·
                refine ⟨9709059571870282936508885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103563302099949684656094773 9709059571870282936508885)
                ·
                  refine ⟨227556083715709756324427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9709059571870282936508885 227556083715709756324427)
                  ·
                    rfl

theorem cell23_3988475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 7].length) (baseStart_3988475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988475 prefixEnd_3988475 := by exact prefixLift 3988475
  have htrace : WordTrace (prefixWord ++ tailWord_3988475) baseStart_3988475 baseEnd_3988475 := by
    simpa [prefixWord, tailWord_3988475, baseEnd_3988475] using wordTrace_append hprefix tailTrace_3988475
  have hstable : (prefixWord ++ tailWord_3988475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988475).length < 2 ^ (prefixWord ++ tailWord_3988475).sum := by decide
  have hdescent : baseEnd_3988475 < baseStart_3988475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988492 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 7]
def baseStart_3988492 : Nat := 118140960795 + 3988492 * 2 ^ 59
def prefixEnd_3988492 : Nat := 4983230072969 + 3 ^ 40 * 3988492 * 2
def baseEnd_3988492 : Nat := 227557053623612693378585

theorem tailTrace_3988492 : CollatzResearch.WordTrace tailWord_3988492 prefixEnd_3988492 227557053623612693378585 := by
  unfold tailWord_3988492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72736127133191069523591865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96981502844254759364789153 72736127133191069523591865)
  ·
    refine ⟨54552095349893302142693899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72736127133191069523591865 54552095349893302142693899)
    ·
      refine ⟨81828143024839953214040849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54552095349893302142693899 81828143024839953214040849)
      ·
        refine ⟨61371107268629964910530637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81828143024839953214040849 61371107268629964910530637)
        ·
          refine ⟨23014165225736236841448989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61371107268629964910530637 23014165225736236841448989)
          ·
            refine ⟨8630311959651088815543371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23014165225736236841448989 8630311959651088815543371)
            ·
              refine ⟨12945467939476633223315057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8630311959651088815543371 12945467939476633223315057)
              ·
                refine ⟨9709100954607474917486293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945467939476633223315057 9709100954607474917486293)
                ·
                  refine ⟨227557053623612693378585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9709100954607474917486293 227557053623612693378585)
                  ·
                    rfl

theorem cell23_3988492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_3988492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988492 prefixEnd_3988492 := by exact prefixLift 3988492
  have htrace : WordTrace (prefixWord ++ tailWord_3988492) baseStart_3988492 baseEnd_3988492 := by
    simpa [prefixWord, tailWord_3988492, baseEnd_3988492] using wordTrace_append hprefix tailTrace_3988492
  have hstable : (prefixWord ++ tailWord_3988492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988492).length < 2 ^ (prefixWord ++ tailWord_3988492).sum := by decide
  have hdescent : baseEnd_3988492 < baseStart_3988492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988586 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_3988586 : Nat := 118140960795 + 3988586 * 2 ^ 59
def prefixEnd_3988586 : Nat := 4983230072969 + 3 ^ 40 * 3988586 * 2
def baseEnd_3988586 : Nat := 682687249931345624210611

theorem tailTrace_3988586 : CollatzResearch.WordTrace tailWord_3988586 prefixEnd_3988586 682687249931345624210611 := by
  unfold tailWord_3988586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36368920682010398275276403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96983788485361062067403741 36368920682010398275276403)
  ·
    refine ⟨54553381023015597412914605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36368920682010398275276403 54553381023015597412914605)
    ·
      refine ⟨20457517883630849029842977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54553381023015597412914605 20457517883630849029842977)
      ·
        refine ⟨15343138412723136772382233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20457517883630849029842977 15343138412723136772382233)
        ·
          refine ⟨11507353809542352579286675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15343138412723136772382233 11507353809542352579286675)
          ·
            refine ⟨17261030714313528868930013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11507353809542352579286675 17261030714313528868930013)
            ·
              refine ⟨6472886517867573325848755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17261030714313528868930013 6472886517867573325848755)
              ·
                refine ⟨9709329776801359988773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6472886517867573325848755 9709329776801359988773133)
                ·
                  refine ⟨3640998666300509995789925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9709329776801359988773133 3640998666300509995789925)
                  ·
                    refine ⟨682687249931345624210611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3640998666300509995789925 682687249931345624210611)
                    ·
                      rfl

theorem cell23_3988586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_3988586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988586 prefixEnd_3988586 := by exact prefixLift 3988586
  have htrace : WordTrace (prefixWord ++ tailWord_3988586) baseStart_3988586 baseEnd_3988586 := by
    simpa [prefixWord, tailWord_3988586, baseEnd_3988586] using wordTrace_append hprefix tailTrace_3988586
  have hstable : (prefixWord ++ tailWord_3988586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988586).length < 2 ^ (prefixWord ++ tailWord_3988586).sum := by decide
  have hdescent : baseEnd_3988586 < baseStart_3988586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988619 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 5, 2]
def baseStart_3988619 : Nat := 118140960795 + 3988619 * 2 ^ 59
def prefixEnd_3988619 : Nat := 4983230072969 + 3 ^ 40 * 3988619 * 2
def baseEnd_3988619 : Nat := 2048078694655635243519181

theorem tailTrace_3988619 : CollatzResearch.WordTrace tailWord_3988619 prefixEnd_3988619 2048078694655635243519181 := by
  unfold tailWord_3988619
  simp only [CollatzResearch.WordTrace]
  refine ⟨145476886336922039737056911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96984590891281359824704607 145476886336922039737056911)
  ·
    refine ⟨218215329505383059605585367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145476886336922039737056911 218215329505383059605585367)
    ·
      refine ⟨327322994258074589408378051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218215329505383059605585367 327322994258074589408378051)
      ·
        refine ⟨490984491387111884112567077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327322994258074589408378051 490984491387111884112567077)
        ·
          refine ⟨92059592135083478271106327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490984491387111884112567077 92059592135083478271106327)
          ·
            refine ⟨138089388202625217406659491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92059592135083478271106327 138089388202625217406659491)
            ·
              refine ⟨207134082303937826109989237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138089388202625217406659491 207134082303937826109989237)
              ·
                refine ⟨19418820215994171197811491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207134082303937826109989237 19418820215994171197811491)
                ·
                  refine ⟨29128230323991256796717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19418820215994171197811491 29128230323991256796717237)
                  ·
                    refine ⟨2730771592874180324692241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29128230323991256796717237 2730771592874180324692241)
                    ·
                      refine ⟨2048078694655635243519181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730771592874180324692241 2048078694655635243519181)
                      ·
                        rfl

theorem cell23_3988619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5, 2].length) (baseStart_3988619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988619 prefixEnd_3988619 := by exact prefixLift 3988619
  have htrace : WordTrace (prefixWord ++ tailWord_3988619) baseStart_3988619 baseEnd_3988619 := by
    simpa [prefixWord, tailWord_3988619, baseEnd_3988619] using wordTrace_append hprefix tailTrace_3988619
  have hstable : (prefixWord ++ tailWord_3988619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988619).length < 2 ^ (prefixWord ++ tailWord_3988619).sum := by decide
  have hdescent : baseEnd_3988619 < baseStart_3988619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988670 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_3988670 : Nat := 118140960795 + 3988670 * 2 ^ 59
def prefixEnd_3988670 : Nat := 4983230072969 + 3 ^ 40 * 3988670 * 2
def baseEnd_3988670 : Nat := 2048104882169014543981447

theorem tailTrace_3988670 : CollatzResearch.WordTrace tailWord_3988670 prefixEnd_3988670 2048104882169014543981447 := by
  unfold tailWord_3988670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184843307467159430895433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96985830973158183631442309 18184843307467159430895433)
  ·
    refine ⟨13638632480600369573171575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18184843307467159430895433 13638632480600369573171575)
    ·
      refine ⟨20457948720900554359757363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638632480600369573171575 20457948720900554359757363)
      ·
        refine ⟨30686923081350831539636045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20457948720900554359757363 30686923081350831539636045)
        ·
          refine ⟨11507596155506561827363517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30686923081350831539636045 11507596155506561827363517)
          ·
            refine ⟨4315348558314960685261319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11507596155506561827363517 4315348558314960685261319)
            ·
              refine ⟨6473022837472441027891979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315348558314960685261319 6473022837472441027891979)
              ·
                refine ⟨9709534256208661541837969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473022837472441027891979 9709534256208661541837969)
                ·
                  refine ⟨7282150692156496156378477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9709534256208661541837969 7282150692156496156378477)
                  ·
                    refine ⟨2730806509558686058641929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7282150692156496156378477 2730806509558686058641929)
                    ·
                      refine ⟨2048104882169014543981447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730806509558686058641929 2048104882169014543981447)
                      ·
                        rfl

theorem cell23_3988670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_3988670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988670 prefixEnd_3988670 := by exact prefixLift 3988670
  have htrace : WordTrace (prefixWord ++ tailWord_3988670) baseStart_3988670 baseEnd_3988670 := by
    simpa [prefixWord, tailWord_3988670, baseEnd_3988670] using wordTrace_append hprefix tailTrace_3988670
  have hstable : (prefixWord ++ tailWord_3988670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988670).length < 2 ^ (prefixWord ++ tailWord_3988670).sum := by decide
  have hdescent : baseEnd_3988670 < baseStart_3988670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988693 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3988693 : Nat := 118140960795 + 3988693 * 2 ^ 59
def prefixEnd_3988693 : Nat := 4983230072969 + 3 ^ 40 * 3988693 * 2
def baseEnd_3988693 : Nat := 682705564074689317997947

theorem tailTrace_3988693 : CollatzResearch.WordTrace tailWord_3988693 prefixEnd_3988693 682705564074689317997947 := by
  unfold tailWord_3988693
  simp only [CollatzResearch.WordTrace]
  refine ⟨145479585338653950375250733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96986390225769300250167155 145479585338653950375250733)
  ·
    refine ⟨54554844501995231390719025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145479585338653950375250733 54554844501995231390719025)
    ·
      refine ⟨40916133376496423543039269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54554844501995231390719025 40916133376496423543039269)
      ·
        refine ⟨7671775008093079414319863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40916133376496423543039269 7671775008093079414319863)
        ·
          refine ⟨11507662512139619121479795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671775008093079414319863 11507662512139619121479795)
          ·
            refine ⟨17261493768209428682219693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11507662512139619121479795 17261493768209428682219693)
            ·
              refine ⟨6473060163078535755832385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17261493768209428682219693 6473060163078535755832385)
              ·
                refine ⟨4854795122308901816874289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6473060163078535755832385 4854795122308901816874289)
                ·
                  refine ⟨3641096341731676362655717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4854795122308901816874289 3641096341731676362655717)
                  ·
                    refine ⟨682705564074689317997947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641096341731676362655717 682705564074689317997947)
                    ·
                      rfl

theorem cell23_3988693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3988693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988693 prefixEnd_3988693 := by exact prefixLift 3988693
  have htrace : WordTrace (prefixWord ++ tailWord_3988693) baseStart_3988693 baseEnd_3988693 := by
    simpa [prefixWord, tailWord_3988693, baseEnd_3988693] using wordTrace_append hprefix tailTrace_3988693
  have hstable : (prefixWord ++ tailWord_3988693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988693).length < 2 ^ (prefixWord ++ tailWord_3988693).sum := by decide
  have hdescent : baseEnd_3988693 < baseStart_3988693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988716 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_3988716 : Nat := 118140960795 + 3988716 * 2 ^ 59
def prefixEnd_3988716 : Nat := 4983230072969 + 3 ^ 40 * 3988716 * 2
def baseEnd_3988716 : Nat := 2048128502279121364006235

theorem tailTrace_3988716 : CollatzResearch.WordTrace tailWord_3988716 prefixEnd_3988716 2048128502279121364006235 := by
  unfold tailWord_3988716
  simp only [CollatzResearch.WordTrace]
  refine ⟨72740212108785312651669001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96986949478380416868892001 72740212108785312651669001)
  ·
    refine ⟨54555159081588984488751751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72740212108785312651669001 54555159081588984488751751)
    ·
      refine ⟨81832738622383476733127627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54555159081588984488751751 81832738622383476733127627)
      ·
        refine ⟨122749107933575215099691441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81832738622383476733127627 122749107933575215099691441)
        ·
          refine ⟨92061830950181411324768581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122749107933575215099691441 92061830950181411324768581)
          ·
            refine ⟨17261593303159014623394109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92061830950181411324768581 17261593303159014623394109)
            ·
              refine ⟨6473097488684630483772791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17261593303159014623394109 6473097488684630483772791)
              ·
                refine ⟨9709646233026945725659187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473097488684630483772791 9709646233026945725659187)
                ·
                  refine ⟨14564469349540418588488781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9709646233026945725659187 14564469349540418588488781)
                  ·
                    refine ⟨5461676006077656970683293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14564469349540418588488781 5461676006077656970683293)
                    ·
                      refine ⟨2048128502279121364006235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5461676006077656970683293 2048128502279121364006235)
                      ·
                        rfl

theorem cell23_3988716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_3988716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988716 prefixEnd_3988716 := by exact prefixLift 3988716
  have htrace : WordTrace (prefixWord ++ tailWord_3988716) baseStart_3988716 baseEnd_3988716 := by
    simpa [prefixWord, tailWord_3988716, baseEnd_3988716] using wordTrace_append hprefix tailTrace_3988716
  have hstable : (prefixWord ++ tailWord_3988716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988716).length < 2 ^ (prefixWord ++ tailWord_3988716).sum := by decide
  have hdescent : baseEnd_3988716 < baseStart_3988716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988734 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3988734 : Nat := 118140960795 + 3988734 * 2 ^ 59
def prefixEnd_3988734 : Nat := 4983230072969 + 3 ^ 40 * 3988734 * 2
def baseEnd_3988734 : Nat := 2048137744930902293581153

theorem tailTrace_3988734 : CollatzResearch.WordTrace tailWord_3988734 prefixEnd_3988734 2048137744930902293581153 := by
  unfold tailWord_3988734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185135091438176797186657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96987387154336942918328837 18185135091438176797186657)
  ·
    refine ⟨13638851318578632597889993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18185135091438176797186657 13638851318578632597889993)
    ·
      refine ⟨10229138488933974448417495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13638851318578632597889993 10229138488933974448417495)
      ·
        refine ⟨15343707733400961672626243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229138488933974448417495 15343707733400961672626243)
        ·
          refine ⟨23015561600101442508939365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15343707733400961672626243 23015561600101442508939365)
          ·
            refine ⟨4315417800019020470426131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23015561600101442508939365 4315417800019020470426131)
            ·
              refine ⟨6473126700028530705639197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4315417800019020470426131 6473126700028530705639197)
              ·
                refine ⟨2427422512510699014614699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6473126700028530705639197 2427422512510699014614699)
                ·
                  refine ⟨3641133768766048521922049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427422512510699014614699 3641133768766048521922049)
                  ·
                    refine ⟨2730850326574536391441537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641133768766048521922049 2730850326574536391441537)
                    ·
                      refine ⟨2048137744930902293581153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730850326574536391441537 2048137744930902293581153)
                      ·
                        rfl

theorem cell23_3988734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3988734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988734 prefixEnd_3988734 := by exact prefixLift 3988734
  have htrace : WordTrace (prefixWord ++ tailWord_3988734) baseStart_3988734 baseEnd_3988734 := by
    simpa [prefixWord, tailWord_3988734, baseEnd_3988734] using wordTrace_append hprefix tailTrace_3988734
  have hstable : (prefixWord ++ tailWord_3988734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988734).length < 2 ^ (prefixWord ++ tailWord_3988734).sum := by decide
  have hdescent : baseEnd_3988734 < baseStart_3988734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988759 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3988759 : Nat := 118140960795 + 3988759 * 2 ^ 59
def prefixEnd_3988759 : Nat := 4983230072969 + 3 ^ 40 * 3988759 * 2
def baseEnd_3988759 : Nat := 2048150581947264695768537

theorem tailTrace_3988759 : CollatzResearch.WordTrace tailWord_3988759 prefixEnd_3988759 2048150581947264695768537 := by
  unfold tailWord_3988759
  simp only [CollatzResearch.WordTrace]
  refine ⟨145481992556414843647153331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96987995037609895764768887 145481992556414843647153331)
  ·
    refine ⟨218222988834622265470729997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145481992556414843647153331 218222988834622265470729997)
    ·
      refine ⟨81833620812983349551523749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218222988834622265470729997 81833620812983349551523749)
      ·
        refine ⟨15343803902434378040910703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81833620812983349551523749 15343803902434378040910703)
        ·
          refine ⟨23015705853651567061366055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15343803902434378040910703 23015705853651567061366055)
          ·
            refine ⟨34523558780477350592049083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23015705853651567061366055 34523558780477350592049083)
            ·
              refine ⟨51785338170716025888073625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34523558780477350592049083 51785338170716025888073625)
              ·
                refine ⟨38839003628037019416055219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51785338170716025888073625 38839003628037019416055219)
                ·
                  refine ⟨58258505442055529124082829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38839003628037019416055219 58258505442055529124082829)
                  ·
                    refine ⟨21846939540770823421531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58258505442055529124082829 21846939540770823421531061)
                    ·
                      refine ⟨2048150581947264695768537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21846939540770823421531061 2048150581947264695768537)
                      ·
                        rfl

theorem cell23_3988759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3988759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988759 prefixEnd_3988759 := by exact prefixLift 3988759
  have htrace : WordTrace (prefixWord ++ tailWord_3988759) baseStart_3988759 baseEnd_3988759 := by
    simpa [prefixWord, tailWord_3988759, baseEnd_3988759] using wordTrace_append hprefix tailTrace_3988759
  have hstable : (prefixWord ++ tailWord_3988759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988759).length < 2 ^ (prefixWord ++ tailWord_3988759).sum := by decide
  have hdescent : baseEnd_3988759 < baseStart_3988759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988767 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 2, 1, 3]
def baseStart_3988767 : Nat := 118140960795 + 3988767 * 2 ^ 59
def prefixEnd_3988767 : Nat := 4983230072969 + 3 ^ 40 * 3988767 * 2
def baseEnd_3988767 : Nat := 2048154689792500664468501

theorem tailTrace_3988767 : CollatzResearch.WordTrace tailWord_3988767 prefixEnd_3988767 2048154689792500664468501 := by
  unfold tailWord_3988767
  simp only [CollatzResearch.WordTrace]
  refine ⟨145482284340385861013444555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96988189560257240675629703 145482284340385861013444555)
  ·
    refine ⟨218223426510578791520166833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145482284340385861013444555 218223426510578791520166833)
    ·
      refine ⟨163667569882934093640125125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218223426510578791520166833 163667569882934093640125125)
      ·
        refine ⟨30687669353050142557523461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163667569882934093640125125 30687669353050142557523461)
        ·
          refine ⟨5753938003696901729535649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30687669353050142557523461 5753938003696901729535649)
          ·
            refine ⟨4315453502772676297151737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753938003696901729535649 4315453502772676297151737)
            ·
              refine ⟨3236590127079507222863803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315453502772676297151737 3236590127079507222863803)
              ·
                refine ⟨4854885190619260834295705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236590127079507222863803 4854885190619260834295705)
                ·
                  refine ⟨3641163892964445625721779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4854885190619260834295705 3641163892964445625721779)
                  ·
                    refine ⟨5461745839446668438582669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641163892964445625721779 5461745839446668438582669)
                    ·
                      refine ⟨2048154689792500664468501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5461745839446668438582669 2048154689792500664468501)
                      ·
                        rfl

theorem cell23_3988767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_3988767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988767 prefixEnd_3988767 := by exact prefixLift 3988767
  have htrace : WordTrace (prefixWord ++ tailWord_3988767) baseStart_3988767 baseEnd_3988767 := by
    simpa [prefixWord, tailWord_3988767, baseEnd_3988767] using wordTrace_append hprefix tailTrace_3988767
  have hstable : (prefixWord ++ tailWord_3988767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988767).length < 2 ^ (prefixWord ++ tailWord_3988767).sum := by decide
  have hdescent : baseEnd_3988767 < baseStart_3988767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988769 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3988769 : Nat := 118140960795 + 3988769 * 2 ^ 59
def prefixEnd_3988769 : Nat := 4983230072969 + 3 ^ 40 * 3988769 * 2
def baseEnd_3988769 : Nat := 2048155716753809656643491

theorem tailTrace_3988769 : CollatzResearch.WordTrace tailWord_3988769 prefixEnd_3988769 2048155716753809656643491 := by
  unfold tailWord_3988769
  simp only [CollatzResearch.WordTrace]
  refine ⟨145482357286378615355017361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96988238190919076903344907 145482357286378615355017361)
  ·
    refine ⟨109111767964783961516263021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145482357286378615355017361 109111767964783961516263021)
    ·
      refine ⟨40916912986793985568598633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109111767964783961516263021 40916912986793985568598633)
      ·
        refine ⟨30687684740095489176448975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40916912986793985568598633 30687684740095489176448975)
        ·
          refine ⟨46031527110143233764673463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30687684740095489176448975 46031527110143233764673463)
          ·
            refine ⟨69047290665214850647010195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46031527110143233764673463 69047290665214850647010195)
            ·
              refine ⟨103570935997822275970515293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69047290665214850647010195 103570935997822275970515293)
              ·
                refine ⟨38839100999183353488943235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103570935997822275970515293 38839100999183353488943235)
                ·
                  refine ⟨58258651498775030233414853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38839100999183353488943235 58258651498775030233414853)
                  ·
                    refine ⟨10923497156020318168765285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58258651498775030233414853 10923497156020318168765285)
                    ·
                      refine ⟨2048155716753809656643491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10923497156020318168765285 2048155716753809656643491)
                      ·
                        rfl

theorem cell23_3988769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3988769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988769 prefixEnd_3988769 := by exact prefixLift 3988769
  have htrace : WordTrace (prefixWord ++ tailWord_3988769) baseStart_3988769 baseEnd_3988769 := by
    simpa [prefixWord, tailWord_3988769, baseEnd_3988769] using wordTrace_append hprefix tailTrace_3988769
  have hstable : (prefixWord ++ tailWord_3988769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988769).length < 2 ^ (prefixWord ++ tailWord_3988769).sum := by decide
  have hdescent : baseEnd_3988769 < baseStart_3988769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988776 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3988776 : Nat := 118140960795 + 3988776 * 2 ^ 59
def prefixEnd_3988776 : Nat := 4983230072969 + 3 ^ 40 * 3988776 * 2
def baseEnd_3988776 : Nat := 2048159311118391129255959

theorem tailTrace_3988776 : CollatzResearch.WordTrace tailWord_3988776 prefixEnd_3988776 2048159311118391129255959 := by
  unfold tailWord_3988776
  simp only [CollatzResearch.WordTrace]
  refine ⟨72741306298676627775261091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96988408398235503700348121 72741306298676627775261091)
  ·
    refine ⟨109111959448014941662891637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72741306298676627775261091 109111959448014941662891637)
    ·
      refine ⟨10229246198251400780896091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109111959448014941662891637 10229246198251400780896091)
      ·
        refine ⟨15343869297377101171344137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229246198251400780896091 15343869297377101171344137)
        ·
          refine ⟨11507901973032825878508103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15343869297377101171344137 11507901973032825878508103)
          ·
            refine ⟨17261852959549238817762155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11507901973032825878508103 17261852959549238817762155)
            ·
              refine ⟨25892779439323858226643233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17261852959549238817762155 25892779439323858226643233)
              ·
                refine ⟨19419584579492893669982425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25892779439323858226643233 19419584579492893669982425)
                ·
                  refine ⟨14564688434619670252486819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19419584579492893669982425 14564688434619670252486819)
                  ·
                    refine ⟨21847032651929505378730229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14564688434619670252486819 21847032651929505378730229)
                    ·
                      refine ⟨2048159311118391129255959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21847032651929505378730229 2048159311118391129255959)
                      ·
                        rfl

theorem cell23_3988776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3988776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988776 prefixEnd_3988776 := by exact prefixLift 3988776
  have htrace : WordTrace (prefixWord ++ tailWord_3988776) baseStart_3988776 baseEnd_3988776 := by
    simpa [prefixWord, tailWord_3988776, baseEnd_3988776] using wordTrace_append hprefix tailTrace_3988776
  have hstable : (prefixWord ++ tailWord_3988776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988776).length < 2 ^ (prefixWord ++ tailWord_3988776).sum := by decide
  have hdescent : baseEnd_3988776 < baseStart_3988776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988816 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2]
def baseStart_3988816 : Nat := 118140960795 + 3988816 * 2 ^ 59
def prefixEnd_3988816 : Nat := 4983230072969 + 3 ^ 40 * 3988816 * 2
def baseEnd_3988816 : Nat := 2048179850344570972755775

theorem tailTrace_3988816 : CollatzResearch.WordTrace tailWord_3988816 prefixEnd_3988816 2048179850344570972755775 := by
  unfold tailWord_3988816
  simp only [CollatzResearch.WordTrace]
  refine ⟨72742035758604171190989151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96989381011472228254652201 72742035758604171190989151)
  ·
    refine ⟨109113053637906256786483727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72742035758604171190989151 109113053637906256786483727)
    ·
      refine ⟨163669580456859385179725591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109113053637906256786483727 163669580456859385179725591)
      ·
        refine ⟨245504370685289077769588387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163669580456859385179725591 245504370685289077769588387)
        ·
          refine ⟨368256556027933616654382581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245504370685289077769588387 368256556027933616654382581)
          ·
            refine ⟨34524052127618776561348367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368256556027933616654382581 34524052127618776561348367)
            ·
              refine ⟨51786078191428164842022551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34524052127618776561348367 51786078191428164842022551)
              ·
                refine ⟨77679117287142247263033827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51786078191428164842022551 77679117287142247263033827)
                ·
                  refine ⟨116518675930713370894550741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77679117287142247263033827 116518675930713370894550741)
                  ·
                    refine ⟨2730906467126094630341033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 116518675930713370894550741 2730906467126094630341033)
                    ·
                      refine ⟨2048179850344570972755775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2730906467126094630341033 2048179850344570972755775)
                      ·
                        rfl

theorem cell23_3988816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2].length) (baseStart_3988816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988816 prefixEnd_3988816 := by exact prefixLift 3988816
  have htrace : WordTrace (prefixWord ++ tailWord_3988816) baseStart_3988816 baseEnd_3988816 := by
    simpa [prefixWord, tailWord_3988816, baseEnd_3988816] using wordTrace_append hprefix tailTrace_3988816
  have hstable : (prefixWord ++ tailWord_3988816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988816).length < 2 ^ (prefixWord ++ tailWord_3988816).sum := by decide
  have hdescent : baseEnd_3988816 < baseStart_3988816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988819 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_3988819 : Nat := 118140960795 + 3988819 * 2 ^ 59
def prefixEnd_3988819 : Nat := 4983230072969 + 3 ^ 40 * 3988819 * 2
def baseEnd_3988819 : Nat := 2048181390786534461018261

theorem tailTrace_3988819 : CollatzResearch.WordTrace tailWord_3988819 prefixEnd_3988819 2048181390786534461018261 := by
  unfold tailWord_3988819
  simp only [CollatzResearch.WordTrace]
  refine ⟨145484180936197473894337511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96989453957464982596225007 145484180936197473894337511)
  ·
    refine ⟨218226271404296210841506267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145484180936197473894337511 218226271404296210841506267)
    ·
      refine ⟨327339407106444316262259401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218226271404296210841506267 327339407106444316262259401)
      ·
        refine ⟨245504555329833237196694551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327339407106444316262259401 245504555329833237196694551)
        ·
          refine ⟨368256832994749855795041827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245504555329833237196694551 368256832994749855795041827)
          ·
            refine ⟨552385249492124783692562741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368256832994749855795041827 552385249492124783692562741)
            ·
              refine ⟨51786117139886698471177757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 552385249492124783692562741 51786117139886698471177757)
              ·
                refine ⟨19419793927457511926691659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51786117139886698471177757 19419793927457511926691659)
                ·
                  refine ⟨29129690891186267890037489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19419793927457511926691659 29129690891186267890037489)
                  ·
                    refine ⟨21847268168389700917528117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29129690891186267890037489 21847268168389700917528117)
                    ·
                      refine ⟨2048181390786534461018261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21847268168389700917528117 2048181390786534461018261)
                      ·
                        rfl

theorem cell23_3988819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_3988819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988819 prefixEnd_3988819 := by exact prefixLift 3988819
  have htrace : WordTrace (prefixWord ++ tailWord_3988819) baseStart_3988819 baseEnd_3988819 := by
    simpa [prefixWord, tailWord_3988819, baseEnd_3988819] using wordTrace_append hprefix tailTrace_3988819
  have hstable : (prefixWord ++ tailWord_3988819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988819).length < 2 ^ (prefixWord ++ tailWord_3988819).sum := by decide
  have hdescent : baseEnd_3988819 < baseStart_3988819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988859 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_3988859 : Nat := 118140960795 + 3988859 * 2 ^ 59
def prefixEnd_3988859 : Nat := 4983230072969 + 3 ^ 40 * 3988859 * 2
def baseEnd_3988859 : Nat := 2048201930012714304518077

theorem tailTrace_3988859 : CollatzResearch.WordTrace tailWord_3988859 prefixEnd_3988859 2048201930012714304518077 := by
  unfold tailWord_3988859
  simp only [CollatzResearch.WordTrace]
  refine ⟨145485639856052560725793631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96990426570701707150529087 145485639856052560725793631)
  ·
    refine ⟨218228459784078841088690447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145485639856052560725793631 218228459784078841088690447)
    ·
      refine ⟨327342689676118261633035671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218228459784078841088690447 327342689676118261633035671)
      ·
        refine ⟨491014034514177392449553507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327342689676118261633035671 491014034514177392449553507)
        ·
          refine ⟨736521051771266088674330261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491014034514177392449553507 736521051771266088674330261)
          ·
            refine ⟨34524424301778097906609231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 736521051771266088674330261 34524424301778097906609231)
            ·
              refine ⟨51786636452667146859913847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34524424301778097906609231 51786636452667146859913847)
              ·
                refine ⟨77679954679000720289870771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51786636452667146859913847 77679954679000720289870771)
                ·
                  refine ⟨116519932018501080434806157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77679954679000720289870771 116519932018501080434806157)
                  ·
                    refine ⟨43694974506937905163052309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116519932018501080434806157 43694974506937905163052309)
                    ·
                      refine ⟨2048201930012714304518077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43694974506937905163052309 2048201930012714304518077)
                      ·
                        rfl

theorem cell23_3988859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_3988859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988859 prefixEnd_3988859 := by exact prefixLift 3988859
  have htrace : WordTrace (prefixWord ++ tailWord_3988859) baseStart_3988859 baseEnd_3988859 := by
    simpa [prefixWord, tailWord_3988859, baseEnd_3988859] using wordTrace_append hprefix tailTrace_3988859
  have hstable : (prefixWord ++ tailWord_3988859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988859).length < 2 ^ (prefixWord ++ tailWord_3988859).sum := by decide
  have hdescent : baseEnd_3988859 < baseStart_3988859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988896 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3988896 : Nat := 118140960795 + 3988896 * 2 ^ 59
def prefixEnd_3988896 : Nat := 4983230072969 + 3 ^ 40 * 3988896 * 2
def baseEnd_3988896 : Nat := 2048220928796930659755407

theorem tailTrace_3988896 : CollatzResearch.WordTrace tailWord_3988896 prefixEnd_3988896 2048220928796930659755407 := by
  unfold tailWord_3988896
  simp only [CollatzResearch.WordTrace]
  refine ⟨72743494678459258022445271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96991326237945677363260361 72743494678459258022445271)
  ·
    refine ⟨109115242017688887033667907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72743494678459258022445271 109115242017688887033667907)
    ·
      refine ⟨163672863026533330550501861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109115242017688887033667907 163672863026533330550501861)
      ·
        refine ⟨30688661817474999478219099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163672863026533330550501861 30688661817474999478219099)
        ·
          refine ⟨46032992726212499217328649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30688661817474999478219099 46032992726212499217328649)
          ·
            refine ⟨34524744544659374412996487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46032992726212499217328649 34524744544659374412996487)
            ·
              refine ⟨51787116816989061619494731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34524744544659374412996487 51787116816989061619494731)
              ·
                refine ⟨77680675225483592429242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51787116816989061619494731 77680675225483592429242097)
                ·
                  refine ⟨58260506419112694321931573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77680675225483592429242097 58260506419112694321931573)
                  ·
                    refine ⟨5461922476791815092681085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58260506419112694321931573 5461922476791815092681085)
                    ·
                      refine ⟨2048220928796930659755407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5461922476791815092681085 2048220928796930659755407)
                      ·
                        rfl

theorem cell23_3988896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3988896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988896 prefixEnd_3988896 := by exact prefixLift 3988896
  have htrace : WordTrace (prefixWord ++ tailWord_3988896) baseStart_3988896 baseEnd_3988896 := by
    simpa [prefixWord, tailWord_3988896, baseEnd_3988896] using wordTrace_append hprefix tailTrace_3988896
  have hstable : (prefixWord ++ tailWord_3988896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988896).length < 2 ^ (prefixWord ++ tailWord_3988896).sum := by decide
  have hdescent : baseEnd_3988896 < baseStart_3988896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988924 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_3988924 : Nat := 118140960795 + 3988924 * 2 ^ 59
def prefixEnd_3988924 : Nat := 4983230072969 + 3 ^ 40 * 3988924 * 2
def baseEnd_3988924 : Nat := 682745102085085516735093

theorem tailTrace_3988924 : CollatzResearch.WordTrace tailWord_3988924 prefixEnd_3988924 682745102085085516735093 := by
  unfold tailWord_3988924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72744005300408538413454913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96992007067211384551273217 72744005300408538413454913)
  ·
    refine ⟨54558003975306403810091185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72744005300408538413454913 54558003975306403810091185)
    ·
      refine ⟨40918502981479802857568389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54558003975306403810091185 40918502981479802857568389)
      ·
        refine ⟨7672219309027463035794073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40918502981479802857568389 7672219309027463035794073)
        ·
          refine ⟨5754164481770597276845555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672219309027463035794073 5754164481770597276845555)
          ·
            refine ⟨8631246722655895915268333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754164481770597276845555 8631246722655895915268333)
            ·
              refine ⟨3236717520995960968225625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8631246722655895915268333 3236717520995960968225625)
              ·
                refine ⟨2427538140746970726169219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236717520995960968225625 2427538140746970726169219)
                ·
                  refine ⟨3641307211120456089253829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427538140746970726169219 3641307211120456089253829)
                  ·
                    refine ⟨682745102085085516735093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641307211120456089253829 682745102085085516735093)
                    ·
                      rfl

theorem cell23_3988924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_3988924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988924 prefixEnd_3988924 := by exact prefixLift 3988924
  have htrace : WordTrace (prefixWord ++ tailWord_3988924) baseStart_3988924 baseEnd_3988924 := by
    simpa [prefixWord, tailWord_3988924, baseEnd_3988924] using wordTrace_append hprefix tailTrace_3988924
  have hstable : (prefixWord ++ tailWord_3988924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988924).length < 2 ^ (prefixWord ++ tailWord_3988924).sum := by decide
  have hdescent : baseEnd_3988924 < baseStart_3988924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988926 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3988926 : Nat := 118140960795 + 3988926 * 2 ^ 59
def prefixEnd_3988926 : Nat := 4983230072969 + 3 ^ 40 * 3988926 * 2
def baseEnd_3988926 : Nat := 2048236333216565542380269

theorem tailTrace_3988926 : CollatzResearch.WordTrace tailWord_3988926 prefixEnd_3988926 2048236333216565542380269 := by
  unfold tailWord_3988926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18186010443351228896060329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96992055697873220778988421 18186010443351228896060329)
  ·
    refine ⟨13639507832513421672045247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18186010443351228896060329 13639507832513421672045247)
    ·
      refine ⟨20459261748770132508067871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13639507832513421672045247 20459261748770132508067871)
      ·
        refine ⟨30688892623155198762101807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20459261748770132508067871 30688892623155198762101807)
        ·
          refine ⟨46033338934732798143152711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30688892623155198762101807 46033338934732798143152711)
          ·
            refine ⟨69050008402099197214729067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46033338934732798143152711 69050008402099197214729067)
            ·
              refine ⟨103575012603148795822093601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69050008402099197214729067 103575012603148795822093601)
              ·
                refine ⟨77681259452361596866570201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103575012603148795822093601 77681259452361596866570201)
                ·
                  refine ⟨58260944589271197649927651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77681259452361596866570201 58260944589271197649927651)
                  ·
                    refine ⟨87391416883906796474891477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58260944589271197649927651 87391416883906796474891477)
                    ·
                      refine ⟨2048236333216565542380269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87391416883906796474891477 2048236333216565542380269)
                      ·
                        rfl

theorem cell23_3988926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3988926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988926 prefixEnd_3988926 := by exact prefixLift 3988926
  have htrace : WordTrace (prefixWord ++ tailWord_3988926) baseStart_3988926 baseEnd_3988926 := by
    simpa [prefixWord, tailWord_3988926, baseEnd_3988926] using wordTrace_append hprefix tailTrace_3988926
  have hstable : (prefixWord ++ tailWord_3988926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988926).length < 2 ^ (prefixWord ++ tailWord_3988926).sum := by decide
  have hdescent : baseEnd_3988926 < baseStart_3988926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988950 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3988950 : Nat := 118140960795 + 3988950 * 2 ^ 59
def prefixEnd_3988950 : Nat := 4983230072969 + 3 ^ 40 * 3988950 * 2
def baseEnd_3988950 : Nat := 682749552250757816160053

theorem tailTrace_3988950 : CollatzResearch.WordTrace tailWord_3988950 prefixEnd_3988950 682749552250757816160053 := by
  unfold tailWord_3988950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093059931170180204209769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96992639265815255511570869 9093059931170180204209769)
  ·
    refine ⟨6819794948377635153157327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093059931170180204209769 6819794948377635153157327)
    ·
      refine ⟨10229692422566452729735991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819794948377635153157327 10229692422566452729735991)
      ·
        refine ⟨15344538633849679094603987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229692422566452729735991 15344538633849679094603987)
        ·
          refine ⟨23016807950774518641905981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344538633849679094603987 23016807950774518641905981)
          ·
            refine ⟨8631302981540444490714743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016807950774518641905981 8631302981540444490714743)
            ·
              refine ⟨12946954472310666736072115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631302981540444490714743 12946954472310666736072115)
              ·
                refine ⟨19420431708466000104108173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12946954472310666736072115 19420431708466000104108173)
                ·
                  refine ⟨7282661890674750039040565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19420431708466000104108173 7282661890674750039040565)
                  ·
                    refine ⟨682749552250757816160053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7282661890674750039040565 682749552250757816160053)
                    ·
                      rfl

theorem cell23_3988950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3988950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988950 prefixEnd_3988950 := by exact prefixLift 3988950
  have htrace : WordTrace (prefixWord ++ tailWord_3988950) baseStart_3988950 baseEnd_3988950 := by
    simpa [prefixWord, tailWord_3988950, baseEnd_3988950] using wordTrace_append hprefix tailTrace_3988950
  have hstable : (prefixWord ++ tailWord_3988950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988950).length < 2 ^ (prefixWord ++ tailWord_3988950).sum := by decide
  have hdescent : baseEnd_3988950 < baseStart_3988950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988953 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_3988953 : Nat := 118140960795 + 3988953 * 2 ^ 59
def prefixEnd_3988953 : Nat := 4983230072969 + 3 ^ 40 * 3988953 * 2
def baseEnd_3988953 : Nat := 2048250197194236936742645

theorem tailTrace_3988953 : CollatzResearch.WordTrace tailWord_3988953 prefixEnd_3988953 2048250197194236936742645 := by
  unfold tailWord_3988953
  simp only [CollatzResearch.WordTrace]
  refine ⟨145489068317712014779715513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96992712211808009853143675 145489068317712014779715513)
  ·
    refine ⟨109116801238284011084786635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145489068317712014779715513 109116801238284011084786635)
    ·
      refine ⟨163675201857426016627179953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109116801238284011084786635 163675201857426016627179953)
      ·
        refine ⟨122756401393069512470384965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163675201857426016627179953 122756401393069512470384965)
        ·
          refine ⟨23016825261200533588197181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122756401393069512470384965 23016825261200533588197181)
          ·
            refine ⟨8631309472950200095573943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016825261200533588197181 8631309472950200095573943)
            ·
              refine ⟨12946964209425300143360915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631309472950200095573943 12946964209425300143360915)
              ·
                refine ⟨19420446314137950215041373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12946964209425300143360915 19420446314137950215041373)
                ·
                  refine ⟨7282667367801731330640515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19420446314137950215041373 7282667367801731330640515)
                  ·
                    refine ⟨10924001051702596995960773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282667367801731330640515 10924001051702596995960773)
                    ·
                      refine ⟨2048250197194236936742645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10924001051702596995960773 2048250197194236936742645)
                      ·
                        rfl

theorem cell23_3988953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_3988953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988953 prefixEnd_3988953 := by exact prefixLift 3988953
  have htrace : WordTrace (prefixWord ++ tailWord_3988953) baseStart_3988953 baseEnd_3988953 := by
    simpa [prefixWord, tailWord_3988953, baseEnd_3988953] using wordTrace_append hprefix tailTrace_3988953
  have hstable : (prefixWord ++ tailWord_3988953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988953).length < 2 ^ (prefixWord ++ tailWord_3988953).sum := by decide
  have hdescent : baseEnd_3988953 < baseStart_3988953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988957 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3988957 : Nat := 118140960795 + 3988957 * 2 ^ 59
def prefixEnd_3988957 : Nat := 4983230072969 + 3 ^ 40 * 3988957 * 2
def baseEnd_3988957 : Nat := 2048252251116854921092627

theorem tailTrace_3988957 : CollatzResearch.WordTrace tailWord_3988957 prefixEnd_3988957 2048252251116854921092627 := by
  unfold tailWord_3988957
  simp only [CollatzResearch.WordTrace]
  refine ⟨145489214209697523462861125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96992809473131682308574083 145489214209697523462861125)
  ·
    refine ⟨27279227664318285649286461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145489214209697523462861125 27279227664318285649286461)
    ·
      refine ⟨10229710374119357118482423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27279227664318285649286461 10229710374119357118482423)
      ·
        refine ⟨15344565561179035677723635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229710374119357118482423 15344565561179035677723635)
        ·
          refine ⟨23016848341768553516585453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344565561179035677723635 23016848341768553516585453)
          ·
            refine ⟨8631318128163207568719545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23016848341768553516585453 8631318128163207568719545)
            ·
              refine ⟨6473488596122405676539659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631318128163207568719545 6473488596122405676539659)
              ·
                refine ⟨9710232894183608514809489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473488596122405676539659 9710232894183608514809489)
                ·
                  refine ⟨7282674670637706386107117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710232894183608514809489 7282674670637706386107117)
                  ·
                    refine ⟨2731003001489139894790169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7282674670637706386107117 2731003001489139894790169)
                    ·
                      refine ⟨2048252251116854921092627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731003001489139894790169 2048252251116854921092627)
                      ·
                        rfl

theorem cell23_3988957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3988957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988957 prefixEnd_3988957 := by exact prefixLift 3988957
  have htrace : WordTrace (prefixWord ++ tailWord_3988957) baseStart_3988957 baseEnd_3988957 := by
    simpa [prefixWord, tailWord_3988957, baseEnd_3988957] using wordTrace_append hprefix tailTrace_3988957
  have hstable : (prefixWord ++ tailWord_3988957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988957).length < 2 ^ (prefixWord ++ tailWord_3988957).sum := by decide
  have hdescent : baseEnd_3988957 < baseStart_3988957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988963 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 6]
def baseStart_3988963 : Nat := 118140960795 + 3988963 * 2 ^ 59
def prefixEnd_3988963 : Nat := 4983230072969 + 3 ^ 40 * 3988963 * 2
def baseEnd_3988963 : Nat := 682751777333593965872533

theorem tailTrace_3988963 : CollatzResearch.WordTrace tailWord_3988963 prefixEnd_3988963 682751777333593965872533 := by
  unfold tailWord_3988963
  simp only [CollatzResearch.WordTrace]
  refine ⟨145489433047675786487579543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96992955365117190991719695 145489433047675786487579543)
  ·
    refine ⟨218234149571513679731369315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145489433047675786487579543 218234149571513679731369315)
    ·
      refine ⟨327351224357270519597053973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218234149571513679731369315 327351224357270519597053973)
      ·
        refine ⟨15344588641747055606111905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 327351224357270519597053973 15344588641747055606111905)
        ·
          refine ⟨11508441481310291704583929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15344588641747055606111905 11508441481310291704583929)
          ·
            refine ⟨8631331110982718778437947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11508441481310291704583929 8631331110982718778437947)
            ·
              refine ⟨12946996666474078167656921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631331110982718778437947 12946996666474078167656921)
              ·
                refine ⟨9710247499855558625742691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12946996666474078167656921 9710247499855558625742691)
                ·
                  refine ⟨14565371249783337938614037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710247499855558625742691 14565371249783337938614037)
                  ·
                    refine ⟨682751777333593965872533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14565371249783337938614037 682751777333593965872533)
                    ·
                      rfl

theorem cell23_3988963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_3988963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988963 prefixEnd_3988963 := by exact prefixLift 3988963
  have htrace : WordTrace (prefixWord ++ tailWord_3988963) baseStart_3988963 baseEnd_3988963 := by
    simpa [prefixWord, tailWord_3988963, baseEnd_3988963] using wordTrace_append hprefix tailTrace_3988963
  have hstable : (prefixWord ++ tailWord_3988963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988963).length < 2 ^ (prefixWord ++ tailWord_3988963).sum := by decide
  have hdescent : baseEnd_3988963 < baseStart_3988963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988981 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3988981 : Nat := 118140960795 + 3988981 * 2 ^ 59
def prefixEnd_3988981 : Nat := 4983230072969 + 3 ^ 40 * 3988981 * 2
def baseEnd_3988981 : Nat := 2048264574652562827192517

theorem tailTrace_3988981 : CollatzResearch.WordTrace tailWord_3988981 prefixEnd_3988981 2048264574652562827192517 := by
  unfold tailWord_3988981
  simp only [CollatzResearch.WordTrace]
  refine ⟨145490089561610575561734797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96993393041073717041156531 145490089561610575561734797)
  ·
    refine ⟨54558783585603965835650549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145490089561610575561734797 54558783585603965835650549)
    ·
      refine ⟨5114885961150371797092239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54558783585603965835650549 5114885961150371797092239)
      ·
        refine ⟨7672328941725557695638359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114885961150371797092239 7672328941725557695638359)
        ·
          refine ⟨11508493412588336543457539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672328941725557695638359 11508493412588336543457539)
          ·
            refine ⟨17262740118882504815186309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508493412588336543457539 17262740118882504815186309)
            ·
              refine ⟨3236763772290469652847433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17262740118882504815186309 3236763772290469652847433)
              ·
                refine ⟨2427572829217852239635575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236763772290469652847433 2427572829217852239635575)
                ·
                  refine ⟨3641359243826778359453363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427572829217852239635575 3641359243826778359453363)
                  ·
                    refine ⟨5462038865740167539180045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641359243826778359453363 5462038865740167539180045)
                    ·
                      refine ⟨2048264574652562827192517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462038865740167539180045 2048264574652562827192517)
                      ·
                        rfl

theorem cell23_3988981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3988981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988981 prefixEnd_3988981 := by exact prefixLift 3988981
  have htrace : WordTrace (prefixWord ++ tailWord_3988981) baseStart_3988981 baseEnd_3988981 := by
    simpa [prefixWord, tailWord_3988981, baseEnd_3988981] using wordTrace_append hprefix tailTrace_3988981
  have hstable : (prefixWord ++ tailWord_3988981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988981).length < 2 ^ (prefixWord ++ tailWord_3988981).sum := by decide
  have hdescent : baseEnd_3988981 < baseStart_3988981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3988987 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 1, 2, 2]
def baseStart_3988987 : Nat := 118140960795 + 3988987 * 2 ^ 59
def prefixEnd_3988987 : Nat := 4983230072969 + 3 ^ 40 * 3988987 * 2
def baseEnd_3988987 : Nat := 2048267655536489803717489

theorem tailTrace_3988987 : CollatzResearch.WordTrace tailWord_3988987 prefixEnd_3988987 2048267655536489803717489 := by
  unfold tailWord_3988987
  simp only [CollatzResearch.WordTrace]
  refine ⟨145490308399588838586453215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96993538933059225724302143 145490308399588838586453215)
  ·
    refine ⟨218235462599383257879679823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145490308399588838586453215 218235462599383257879679823)
    ·
      refine ⟨327353193899074886819519735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218235462599383257879679823 327353193899074886819519735)
      ·
        refine ⟨491029790848612330229279603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327353193899074886819519735 491029790848612330229279603)
        ·
          refine ⟨736544686272918495343919405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491029790848612330229279603 736544686272918495343919405)
          ·
            refine ⟨276204257352344435753969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736544686272918495343919405 276204257352344435753969777)
            ·
              refine ⟨207153193014258326815477333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276204257352344435753969777 207153193014258326815477333)
              ·
                refine ⟨2427576480635839767368875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 207153193014258326815477333 2427576480635839767368875)
                ·
                  refine ⟨3641364720953759651053313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427576480635839767368875 3641364720953759651053313)
                  ·
                    refine ⟨2731023540715319738289985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641364720953759651053313 2731023540715319738289985)
                    ·
                      refine ⟨2048267655536489803717489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731023540715319738289985 2048267655536489803717489)
                      ·
                        rfl

theorem cell23_3988987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 1, 2, 2].length) (baseStart_3988987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3988987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3988987 prefixEnd_3988987 := by exact prefixLift 3988987
  have htrace : WordTrace (prefixWord ++ tailWord_3988987) baseStart_3988987 baseEnd_3988987 := by
    simpa [prefixWord, tailWord_3988987, baseEnd_3988987] using wordTrace_append hprefix tailTrace_3988987
  have hstable : (prefixWord ++ tailWord_3988987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3988987).length < 2 ^ (prefixWord ++ tailWord_3988987).sum := by decide
  have hdescent : baseEnd_3988987 < baseStart_3988987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3988987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989020 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3989020 : Nat := 118140960795 + 3989020 * 2 ^ 59
def prefixEnd_3989020 : Nat := 4983230072969 + 3 ^ 40 * 3989020 * 2
def baseEnd_3989020 : Nat := 2048284600398088174604837

theorem tailTrace_3989020 : CollatzResearch.WordTrace tailWord_3989020 prefixEnd_3989020 2048284600398088174604837 := by
  unfold tailWord_3989020
  simp only [CollatzResearch.WordTrace]
  refine ⟨72745756004234642611202257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96994341338979523481603009 72745756004234642611202257)
  ·
    refine ⟨54559317003175981958401693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72745756004234642611202257 54559317003175981958401693)
    ·
      refine ⟨20459743876190993234400635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54559317003175981958401693 20459743876190993234400635)
      ·
        refine ⟨30689615814286489851600953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20459743876190993234400635 30689615814286489851600953)
        ·
          refine ⟨23017211860714867388700715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30689615814286489851600953 23017211860714867388700715)
          ·
            refine ⟨34525817791072301083051073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23017211860714867388700715 34525817791072301083051073)
            ·
              refine ⟨25894363343304225812288305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34525817791072301083051073 25894363343304225812288305)
              ·
                refine ⟨19420772507478169359216229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25894363343304225812288305 19420772507478169359216229)
                ·
                  refine ⟨3641394845152156754853043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19420772507478169359216229 3641394845152156754853043)
                  ·
                    refine ⟨5462092267728235132279565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641394845152156754853043 5462092267728235132279565)
                    ·
                      refine ⟨2048284600398088174604837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462092267728235132279565 2048284600398088174604837)
                      ·
                        rfl

theorem cell23_3989020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3989020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989020 prefixEnd_3989020 := by exact prefixLift 3989020
  have htrace : WordTrace (prefixWord ++ tailWord_3989020) baseStart_3989020 baseEnd_3989020 := by
    simpa [prefixWord, tailWord_3989020, baseEnd_3989020] using wordTrace_append hprefix tailTrace_3989020
  have hstable : (prefixWord ++ tailWord_3989020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989020).length < 2 ^ (prefixWord ++ tailWord_3989020).sum := by decide
  have hdescent : baseEnd_3989020 < baseStart_3989020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989024 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3989024 : Nat := 118140960795 + 3989024 * 2 ^ 59
def prefixEnd_3989024 : Nat := 4983230072969 + 3 ^ 40 * 3989024 * 2
def baseEnd_3989024 : Nat := 2048286654320706158954819

theorem tailTrace_3989024 : CollatzResearch.WordTrace tailWord_3989024 prefixEnd_3989024 2048286654320706158954819 := by
  unfold tailWord_3989024
  simp only [CollatzResearch.WordTrace]
  refine ⟨72745828950227396952775063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96994438600303195937033417 72745828950227396952775063)
  ·
    refine ⟨109118743425341095429162595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72745828950227396952775063 109118743425341095429162595)
    ·
      refine ⟨163678115138011643143743893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109118743425341095429162595 163678115138011643143743893)
      ·
        refine ⟨7672411647094295772362995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163678115138011643143743893 7672411647094295772362995)
        ·
          refine ⟨11508617470641443658544493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672411647094295772362995 11508617470641443658544493)
          ·
            refine ⟨4315731551490541371954185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11508617470641443658544493 4315731551490541371954185)
            ·
              refine ⟨3236798663617906028965639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315731551490541371954185 3236798663617906028965639)
              ·
                refine ⟨4855197995426859043448459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236798663617906028965639 4855197995426859043448459)
                ·
                  refine ⟨7282796993140288565172689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855197995426859043448459 7282796993140288565172689)
                  ·
                    refine ⟨5462097744855216423879517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7282796993140288565172689 5462097744855216423879517)
                    ·
                      refine ⟨2048286654320706158954819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462097744855216423879517 2048286654320706158954819)
                      ·
                        rfl

theorem cell23_3989024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3989024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989024 prefixEnd_3989024 := by exact prefixLift 3989024
  have htrace : WordTrace (prefixWord ++ tailWord_3989024) baseStart_3989024 baseEnd_3989024 := by
    simpa [prefixWord, tailWord_3989024, baseEnd_3989024] using wordTrace_append hprefix tailTrace_3989024
  have hstable : (prefixWord ++ tailWord_3989024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989024).length < 2 ^ (prefixWord ++ tailWord_3989024).sum := by decide
  have hdescent : baseEnd_3989024 < baseStart_3989024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989113 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_3989113 : Nat := 118140960795 + 3989113 * 2 ^ 59
def prefixEnd_3989113 : Nat := 4983230072969 + 3 ^ 40 * 3989113 * 2
def baseEnd_3989113 : Nat := 682777451366318770247303

theorem tailTrace_3989113 : CollatzResearch.WordTrace tailWord_3989113 prefixEnd_3989113 682777451366318770247303 := by
  unfold tailWord_3989113
  simp only [CollatzResearch.WordTrace]
  refine ⟨145494903997132362105539993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96996602664754908070359995 145494903997132362105539993)
  ·
    refine ⟨109121177997849271579154995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145494903997132362105539993 109121177997849271579154995)
    ·
      refine ⟨163681766996773907368732493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109121177997849271579154995 163681766996773907368732493)
      ·
        refine ⟨61380662623790215263274685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163681766996773907368732493 61380662623790215263274685)
        ·
          refine ⟨23017748483921330723728007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61380662623790215263274685 23017748483921330723728007)
          ·
            refine ⟨34526622725881996085592011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23017748483921330723728007 34526622725881996085592011)
            ·
              refine ⟨51789934088822994128388017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34526622725881996085592011 51789934088822994128388017)
              ·
                refine ⟨38842450566617245596291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51789934088822994128388017 38842450566617245596291013)
                ·
                  refine ⟨7282959481240733549304565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38842450566617245596291013 7282959481240733549304565)
                  ·
                    refine ⟨682777451366318770247303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7282959481240733549304565 682777451366318770247303)
                    ·
                      rfl

theorem cell23_3989113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_3989113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989113 prefixEnd_3989113 := by exact prefixLift 3989113
  have htrace : WordTrace (prefixWord ++ tailWord_3989113) baseStart_3989113 baseEnd_3989113 := by
    simpa [prefixWord, tailWord_3989113, baseEnd_3989113] using wordTrace_append hprefix tailTrace_3989113
  have hstable : (prefixWord ++ tailWord_3989113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989113).length < 2 ^ (prefixWord ++ tailWord_3989113).sum := by decide
  have hdescent : baseEnd_3989113 < baseStart_3989113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989130 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_3989130 : Nat := 118140960795 + 3989130 * 2 ^ 59
def prefixEnd_3989130 : Nat := 4983230072969 + 3 ^ 40 * 3989130 * 2
def baseEnd_3989130 : Nat := 682780361090027581409777

theorem tailTrace_3989130 : CollatzResearch.WordTrace tailWord_3989130 prefixEnd_3989130 682780361090027581409777 := by
  unfold tailWord_3989130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373881009517693502227211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96997016025380516005939229 36373881009517693502227211)
  ·
    refine ⟨54560821514276540253340817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36373881009517693502227211 54560821514276540253340817)
    ·
      refine ⟨40920616135707405190005613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54560821514276540253340817 40920616135707405190005613)
      ·
        refine ⟨15345231050890276946252105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40920616135707405190005613 15345231050890276946252105)
        ·
          refine ⟨11508923288167707709689079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15345231050890276946252105 11508923288167707709689079)
          ·
            refine ⟨17263384932251561564533619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11508923288167707709689079 17263384932251561564533619)
            ·
              refine ⟨25895077398377342346800429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17263384932251561564533619 25895077398377342346800429)
              ·
                refine ⟨9710654024391503380050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25895077398377342346800429 9710654024391503380050161)
                ·
                  refine ⟨7282990518293627535037621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710654024391503380050161 7282990518293627535037621)
                  ·
                    refine ⟨682780361090027581409777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7282990518293627535037621 682780361090027581409777)
                    ·
                      rfl

theorem cell23_3989130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_3989130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989130 prefixEnd_3989130 := by exact prefixLift 3989130
  have htrace : WordTrace (prefixWord ++ tailWord_3989130) baseStart_3989130 baseEnd_3989130 := by
    simpa [prefixWord, tailWord_3989130, baseEnd_3989130] using wordTrace_append hprefix tailTrace_3989130
  have hstable : (prefixWord ++ tailWord_3989130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989130).length < 2 ^ (prefixWord ++ tailWord_3989130).sum := by decide
  have hdescent : baseEnd_3989130 < baseStart_3989130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989151 : List Nat := [1, 1, 2, 7, 1, 2, 2, 2, 5]
def baseStart_3989151 : Nat := 118140960795 + 3989151 * 2 ^ 59
def prefixEnd_3989151 : Nat := 4983230072969 + 3 ^ 40 * 3989151 * 2
def baseEnd_3989151 : Nat := 227594651818203018007415

theorem tailTrace_3989151 : CollatzResearch.WordTrace tailWord_3989151 prefixEnd_3989151 227594651818203018007415 := by
  unfold tailWord_3989151
  simp only [CollatzResearch.WordTrace]
  refine ⟨145496289970994694595423307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96997526647329796396948871 145496289970994694595423307)
  ·
    refine ⟨218244434956492041893134961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145496289970994694595423307 218244434956492041893134961)
    ·
      refine ⟨163683326217369031419851221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218244434956492041893134961 163683326217369031419851221)
      ·
        refine ⟨3836327958219586673902763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 163683326217369031419851221 3836327958219586673902763)
        ·
          refine ⟨5754491937329380010854145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836327958219586673902763 5754491937329380010854145)
          ·
            refine ⟨4315868952997035008140609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5754491937329380010854145 4315868952997035008140609)
            ·
              refine ⟨3236901714747776256105457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315868952997035008140609 3236901714747776256105457)
              ·
                refine ⟨2427676286060832192079093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236901714747776256105457 2427676286060832192079093)
                ·
                  refine ⟨227594651818203018007415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2427676286060832192079093 227594651818203018007415)
                  ·
                    rfl

theorem cell23_3989151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 5].length) (baseStart_3989151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989151 prefixEnd_3989151 := by exact prefixLift 3989151
  have htrace : WordTrace (prefixWord ++ tailWord_3989151) baseStart_3989151 baseEnd_3989151 := by
    simpa [prefixWord, tailWord_3989151, baseEnd_3989151] using wordTrace_append hprefix tailTrace_3989151
  have hstable : (prefixWord ++ tailWord_3989151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989151).length < 2 ^ (prefixWord ++ tailWord_3989151).sum := by decide
  have hdescent : baseEnd_3989151 < baseStart_3989151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989170 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_3989170 : Nat := 118140960795 + 3989170 * 2 ^ 59
def prefixEnd_3989170 : Nat := 4983230072969 + 3 ^ 40 * 3989170 * 2
def baseEnd_3989170 : Nat := 2048361622496262587729147

theorem tailTrace_3989170 : CollatzResearch.WordTrace tailWord_3989170 prefixEnd_3989170 2048361622496262587729147 := by
  unfold tailWord_3989170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36374245739481465210091241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96997988638617240560243309 36374245739481465210091241)
  ·
    refine ⟨27280684304611098907568431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36374245739481465210091241 27280684304611098907568431)
    ·
      refine ⟨40921026456916648361352647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27280684304611098907568431 40921026456916648361352647)
      ·
        refine ⟨61381539685374972542028971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40921026456916648361352647 61381539685374972542028971)
        ·
          refine ⟨92072309528062458813043457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61381539685374972542028971 92072309528062458813043457)
          ·
            refine ⟨69054232146046844109782593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92072309528062458813043457 69054232146046844109782593)
            ·
              refine ⟨51790674109535133082336945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69054232146046844109782593 51790674109535133082336945)
              ·
                refine ⟨38843005582151349811752709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51790674109535133082336945 38843005582151349811752709)
                ·
                  refine ⟨7283063546653378089703633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38843005582151349811752709 7283063546653378089703633)
                  ·
                    refine ⟨5462297659990033567277725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283063546653378089703633 5462297659990033567277725)
                    ·
                      refine ⟨2048361622496262587729147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462297659990033567277725 2048361622496262587729147)
                      ·
                        rfl

theorem cell23_3989170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_3989170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989170 prefixEnd_3989170 := by exact prefixLift 3989170
  have htrace : WordTrace (prefixWord ++ tailWord_3989170) baseStart_3989170 baseEnd_3989170 := by
    simpa [prefixWord, tailWord_3989170, baseEnd_3989170] using wordTrace_append hprefix tailTrace_3989170
  have hstable : (prefixWord ++ tailWord_3989170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989170).length < 2 ^ (prefixWord ++ tailWord_3989170).sum := by decide
  have hdescent : baseEnd_3989170 < baseStart_3989170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989197 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3989197 : Nat := 118140960795 + 3989197 * 2 ^ 59
def prefixEnd_3989197 : Nat := 4983230072969 + 3 ^ 40 * 3989197 * 2
def baseEnd_3989197 : Nat := 2048375486473933982091523

theorem tailTrace_3989197 : CollatzResearch.WordTrace tailWord_3989197 prefixEnd_3989197 2048375486473933982091523 := by
  unfold tailWord_3989197
  simp only [CollatzResearch.WordTrace]
  refine ⟨145497967728828044451597845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96998645152552029634398563 145497967728828044451597845)
  ·
    refine ⟨6820217237288814583668649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145497967728828044451597845 6820217237288814583668649)
    ·
      refine ⟨5115162927966610937751487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820217237288814583668649 5115162927966610937751487)
      ·
        refine ⟨7672744391949916406627231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115162927966610937751487 7672744391949916406627231)
        ·
          refine ⟨11509116587924874609940847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672744391949916406627231 11509116587924874609940847)
          ·
            refine ⟨17263674881887311914911271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509116587924874609940847 17263674881887311914911271)
            ·
              refine ⟨25895512322830967872366907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17263674881887311914911271 25895512322830967872366907)
              ·
                refine ⟨38843268484246451808550361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25895512322830967872366907 38843268484246451808550361)
                ·
                  refine ⟨29132451363184838856412771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38843268484246451808550361 29132451363184838856412771)
                  ·
                    refine ⟨43698677044777258284619157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29132451363184838856412771 43698677044777258284619157)
                    ·
                      refine ⟨2048375486473933982091523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43698677044777258284619157 2048375486473933982091523)
                      ·
                        rfl

theorem cell23_3989197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3989197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989197 prefixEnd_3989197 := by exact prefixLift 3989197
  have htrace : WordTrace (prefixWord ++ tailWord_3989197) baseStart_3989197 baseEnd_3989197 := by
    simpa [prefixWord, tailWord_3989197, baseEnd_3989197] using wordTrace_append hprefix tailTrace_3989197
  have hstable : (prefixWord ++ tailWord_3989197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989197).length < 2 ^ (prefixWord ++ tailWord_3989197).sum := by decide
  have hdescent : baseEnd_3989197 < baseStart_3989197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989260 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3989260 : Nat := 118140960795 + 3989260 * 2 ^ 59
def prefixEnd_3989260 : Nat := 4983230072969 + 3 ^ 40 * 3989260 * 2
def baseEnd_3989260 : Nat := 2048407835755167235603733

theorem tailTrace_3989260 : CollatzResearch.WordTrace tailWord_3989260 prefixEnd_3989260 2048407835755167235603733 := by
  unfold tailWord_3989260
  simp only [CollatzResearch.WordTrace]
  refine ⟨72750132763799903105570617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97000177018399870807427489 72750132763799903105570617)
  ·
    refine ⟨54562599572849927329177963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72750132763799903105570617 54562599572849927329177963)
    ·
      refine ⟨81843899359274890993766945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54562599572849927329177963 81843899359274890993766945)
      ·
        refine ⟨61382924519456168245325209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81843899359274890993766945 61382924519456168245325209)
        ·
          refine ⟨46037193389592126183993907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61382924519456168245325209 46037193389592126183993907)
          ·
            refine ⟨69055790084388189275990861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46037193389592126183993907 69055790084388189275990861)
            ·
              refine ⟨25895921281645570978496573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69055790084388189275990861 25895921281645570978496573)
              ·
                refine ⟨9710970480617089116936215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25895921281645570978496573 9710970480617089116936215)
                ·
                  refine ⟨14566455720925633675404323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9710970480617089116936215 14566455720925633675404323)
                  ·
                    refine ⟨21849683581388450513106485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14566455720925633675404323 21849683581388450513106485)
                    ·
                      refine ⟨2048407835755167235603733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21849683581388450513106485 2048407835755167235603733)
                      ·
                        rfl

theorem cell23_3989260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3989260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989260 prefixEnd_3989260 := by exact prefixLift 3989260
  have htrace : WordTrace (prefixWord ++ tailWord_3989260) baseStart_3989260 baseEnd_3989260 := by
    simpa [prefixWord, tailWord_3989260, baseEnd_3989260] using wordTrace_append hprefix tailTrace_3989260
  have hstable : (prefixWord ++ tailWord_3989260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989260).length < 2 ^ (prefixWord ++ tailWord_3989260).sum := by decide
  have hdescent : baseEnd_3989260 < baseStart_3989260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989280 : List Nat := [2, 1, 1, 5, 1, 1, 4, 8]
def baseStart_3989280 : Nat := 118140960795 + 3989280 * 2 ^ 59
def prefixEnd_3989280 : Nat := 4983230072969 + 3 ^ 40 * 3989280 * 2
def baseEnd_3989280 : Nat := 75867337235861376198283

theorem tailTrace_3989280 : CollatzResearch.WordTrace tailWord_3989280 prefixEnd_3989280 75867337235861376198283 := by
  unfold tailWord_3989280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72750497493763674813434647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97000663325018233084579529 72750497493763674813434647)
  ·
    refine ⟨109125746240645512220151971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72750497493763674813434647 109125746240645512220151971)
    ·
      refine ⟨163688619360968268330227957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109125746240645512220151971 163688619360968268330227957)
      ·
        refine ⟨15345808065090775155958871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163688619360968268330227957 15345808065090775155958871)
        ·
          refine ⟨23018712097636162733938307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15345808065090775155958871 23018712097636162733938307)
          ·
            refine ⟨34528068146454244100907461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23018712097636162733938307 34528068146454244100907461)
            ·
              refine ⟨6474012777460170768920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34528068146454244100907461 6474012777460170768920149)
              ·
                refine ⟨75867337235861376198283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6474012777460170768920149 75867337235861376198283)
                ·
                  rfl

theorem cell23_3989280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_3989280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989280 prefixEnd_3989280 := by exact prefixLift 3989280
  have htrace : WordTrace (prefixWord ++ tailWord_3989280) baseStart_3989280 baseEnd_3989280 := by
    simpa [prefixWord, tailWord_3989280, baseEnd_3989280] using wordTrace_append hprefix tailTrace_3989280
  have hstable : (prefixWord ++ tailWord_3989280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989280).length < 2 ^ (prefixWord ++ tailWord_3989280).sum := by decide
  have hdescent : baseEnd_3989280 < baseStart_3989280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989284 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3989284 : Nat := 118140960795 + 3989284 * 2 ^ 59
def prefixEnd_3989284 : Nat := 4983230072969 + 3 ^ 40 * 3989284 * 2
def baseEnd_3989284 : Nat := 682806719763625047234541

theorem tailTrace_3989284 : CollatzResearch.WordTrace tailWord_3989284 prefixEnd_3989284 682806719763625047234541 := by
  unfold tailWord_3989284
  simp only [CollatzResearch.WordTrace]
  refine ⟨72750570439756429155007453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97000760586341905540009937 72750570439756429155007453)
  ·
    refine ⟨27281463914908660933127795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72750570439756429155007453 27281463914908660933127795)
    ·
      refine ⟨40922195872362991399691693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27281463914908660933127795 40922195872362991399691693)
      ·
        refine ⟨15345823452136121774884385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40922195872362991399691693 15345823452136121774884385)
        ·
          refine ⟨11509367589102091331163289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15345823452136121774884385 11509367589102091331163289)
          ·
            refine ⟨8632025691826568498372467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11509367589102091331163289 8632025691826568498372467)
            ·
              refine ⟨12948038537739852747558701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632025691826568498372467 12948038537739852747558701)
              ·
                refine ⟨4855514451652444780334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12948038537739852747558701 4855514451652444780334513)
                ·
                  refine ⟨3641635838739333585250885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855514451652444780334513 3641635838739333585250885)
                  ·
                    refine ⟨682806719763625047234541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641635838739333585250885 682806719763625047234541)
                    ·
                      rfl

theorem cell23_3989284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3989284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989284 prefixEnd_3989284 := by exact prefixLift 3989284
  have htrace : WordTrace (prefixWord ++ tailWord_3989284) baseStart_3989284 baseEnd_3989284 := by
    simpa [prefixWord, tailWord_3989284, baseEnd_3989284] using wordTrace_append hprefix tailTrace_3989284
  have hstable : (prefixWord ++ tailWord_3989284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989284).length < 2 ^ (prefixWord ++ tailWord_3989284).sum := by decide
  have hdescent : baseEnd_3989284 < baseStart_3989284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989311 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 1, 2, 3]
def baseStart_3989311 : Nat := 118140960795 + 3989311 * 2 ^ 59
def prefixEnd_3989311 : Nat := 4983230072969 + 3 ^ 40 * 3989311 * 2
def baseEnd_3989311 : Nat := 2048434023268546536065999

theorem tailTrace_3989311 : CollatzResearch.WordTrace tailWord_3989311 prefixEnd_3989311 2048434023268546536065999 := by
  unfold tailWord_3989311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145502125650415041921247787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97001417100276694614165191 145502125650415041921247787)
  ·
    refine ⟨218253188475622562881871681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145502125650415041921247787 218253188475622562881871681)
    ·
      refine ⟨163689891356716922161403761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218253188475622562881871681 163689891356716922161403761)
      ·
        refine ⟨122767418517537691621052821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163689891356716922161403761 122767418517537691621052821)
        ·
          refine ⟨5754722743009579294736851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122767418517537691621052821 5754722743009579294736851)
          ·
            refine ⟨8632084114514368942105277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754722743009579294736851 8632084114514368942105277)
            ·
              refine ⟨3237031542942888353289479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632084114514368942105277 3237031542942888353289479)
              ·
                refine ⟨4855547314414332529934219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237031542942888353289479 4855547314414332529934219)
                ·
                  refine ⟨7283320971621498794901329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855547314414332529934219 7283320971621498794901329)
                  ·
                    refine ⟨5462490728716124096175997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7283320971621498794901329 5462490728716124096175997)
                    ·
                      refine ⟨2048434023268546536065999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462490728716124096175997 2048434023268546536065999)
                      ·
                        rfl

theorem cell23_3989311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_3989311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989311 prefixEnd_3989311 := by exact prefixLift 3989311
  have htrace : WordTrace (prefixWord ++ tailWord_3989311) baseStart_3989311 baseEnd_3989311 := by
    simpa [prefixWord, tailWord_3989311, baseEnd_3989311] using wordTrace_append hprefix tailTrace_3989311
  have hstable : (prefixWord ++ tailWord_3989311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989311).length < 2 ^ (prefixWord ++ tailWord_3989311).sum := by decide
  have hdescent : baseEnd_3989311 < baseStart_3989311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989318 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3989318 : Nat := 118140960795 + 3989318 * 2 ^ 59
def prefixEnd_3989318 : Nat := 4983230072969 + 3 ^ 40 * 3989318 * 2
def baseEnd_3989318 : Nat := 682812539211042669559489

theorem tailTrace_3989318 : CollatzResearch.WordTrace tailWord_3989318 prefixEnd_3989318 682812539211042669559489 := by
  unfold tailWord_3989318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546949405043427566148519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97001587307593121411168405 4546949405043427566148519)
  ·
    refine ⟨6820424107565141349222779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4546949405043427566148519 6820424107565141349222779)
    ·
      refine ⟨10230636161347712023834169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820424107565141349222779 10230636161347712023834169)
      ·
        refine ⟨7672977121010784017875627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230636161347712023834169 7672977121010784017875627)
        ·
          refine ⟨11509465681516176026813441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672977121010784017875627 11509465681516176026813441)
          ·
            refine ⟨8632099261137132020110081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11509465681516176026813441 8632099261137132020110081)
            ·
              refine ⟨6474074445852849015082561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8632099261137132020110081 6474074445852849015082561)
              ·
                refine ⟨4855555834389636761311921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474074445852849015082561 4855555834389636761311921)
                ·
                  refine ⟨3641666875792227570983941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855555834389636761311921 3641666875792227570983941)
                  ·
                    refine ⟨682812539211042669559489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3641666875792227570983941 682812539211042669559489)
                    ·
                      rfl

theorem cell23_3989318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3989318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989318 prefixEnd_3989318 := by exact prefixLift 3989318
  have htrace : WordTrace (prefixWord ++ tailWord_3989318) baseStart_3989318 baseEnd_3989318 := by
    simpa [prefixWord, tailWord_3989318, baseEnd_3989318] using wordTrace_append hprefix tailTrace_3989318
  have hstable : (prefixWord ++ tailWord_3989318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989318).length < 2 ^ (prefixWord ++ tailWord_3989318).sum := by decide
  have hdescent : baseEnd_3989318 < baseStart_3989318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989325 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3989325 : Nat := 118140960795 + 3989325 * 2 ^ 59
def prefixEnd_3989325 : Nat := 4983230072969 + 3 ^ 40 * 3989325 * 2
def baseEnd_3989325 : Nat := 2048441211997709481290935

theorem tailTrace_3989325 : CollatzResearch.WordTrace tailWord_3989325 prefixEnd_3989325 2048441211997709481290935 := by
  unfold tailWord_3989325
  simp only [CollatzResearch.WordTrace]
  refine ⟨145502636272364322312257429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97001757514909548208171619 145502636272364322312257429)
  ·
    refine ⟨6820436075267077608387067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145502636272364322312257429 6820436075267077608387067)
    ·
      refine ⟨10230654112900616412580601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6820436075267077608387067 10230654112900616412580601)
      ·
        refine ⟨7672990584675462309435451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230654112900616412580601 7672990584675462309435451)
        ·
          refine ⟨11509485877013193464153177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7672990584675462309435451 11509485877013193464153177)
          ·
            refine ⟨8632114407759895098114883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11509485877013193464153177 8632114407759895098114883)
            ·
              refine ⟨12948171611639842647172325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632114407759895098114883 12948171611639842647172325)
              ·
                refine ⟨2427782177182470496344811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12948171611639842647172325 2427782177182470496344811)
                ·
                  refine ⟨3641673265773705744517217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427782177182470496344811 3641673265773705744517217)
                  ·
                    refine ⟨2731254949330279308387913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641673265773705744517217 2731254949330279308387913)
                    ·
                      refine ⟨2048441211997709481290935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731254949330279308387913 2048441211997709481290935)
                      ·
                        rfl

theorem cell23_3989325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3989325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989325 prefixEnd_3989325 := by exact prefixLift 3989325
  have htrace : WordTrace (prefixWord ++ tailWord_3989325) baseStart_3989325 baseEnd_3989325 := by
    simpa [prefixWord, tailWord_3989325, baseEnd_3989325] using wordTrace_append hprefix tailTrace_3989325
  have hstable : (prefixWord ++ tailWord_3989325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989325).length < 2 ^ (prefixWord ++ tailWord_3989325).sum := by decide
  have hdescent : baseEnd_3989325 < baseStart_3989325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989360 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_3989360 : Nat := 118140960795 + 3989360 * 2 ^ 59
def prefixEnd_3989360 : Nat := 4983230072969 + 3 ^ 40 * 3989360 * 2
def baseEnd_3989360 : Nat := 2048459183820616844353273

theorem tailTrace_3989360 : CollatzResearch.WordTrace tailWord_3989360 prefixEnd_3989360 2048459183820616844353273 := by
  unfold tailWord_3989360
  simp only [CollatzResearch.WordTrace]
  refine ⟨72751956413618761644890767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97002608551491682193187689 72751956413618761644890767)
  ·
    refine ⟨109127934620428142467336151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72751956413618761644890767 109127934620428142467336151)
    ·
      refine ⟨163691901930642213701004227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109127934620428142467336151 163691901930642213701004227)
      ·
        refine ⟨245537852895963320551506341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163691901930642213701004227 245537852895963320551506341)
        ·
          refine ⟨46038347417993122603407439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245537852895963320551506341 46038347417993122603407439)
          ·
            refine ⟨69057521126989683905111159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46038347417993122603407439 69057521126989683905111159)
            ·
              refine ⟨103586281690484525857666739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69057521126989683905111159 103586281690484525857666739)
              ·
                refine ⟨155379422535726788786500109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103586281690484525857666739 155379422535726788786500109)
                ·
                  refine ⟨58267283450897545794937541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155379422535726788786500109 58267283450897545794937541)
                  ·
                    refine ⟨10925115647043289836550789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58267283450897545794937541 10925115647043289836550789)
                    ·
                      refine ⟨2048459183820616844353273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10925115647043289836550789 2048459183820616844353273)
                      ·
                        rfl

theorem cell23_3989360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_3989360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989360 prefixEnd_3989360 := by exact prefixLift 3989360
  have htrace : WordTrace (prefixWord ++ tailWord_3989360) baseStart_3989360 baseEnd_3989360 := by
    simpa [prefixWord, tailWord_3989360, baseEnd_3989360] using wordTrace_append hprefix tailTrace_3989360
  have hstable : (prefixWord ++ tailWord_3989360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989360).length < 2 ^ (prefixWord ++ tailWord_3989360).sum := by decide
  have hdescent : baseEnd_3989360 < baseStart_3989360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989374 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3989374 : Nat := 118140960795 + 3989374 * 2 ^ 59
def prefixEnd_3989374 : Nat := 4983230072969 + 3 ^ 40 * 3989374 * 2
def baseEnd_3989374 : Nat := 682822124183259929859403

theorem tailTrace_3989374 : CollatzResearch.WordTrace tailWord_3989374 prefixEnd_3989374 682822124183259929859403 := by
  unfold tailWord_3989374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188052931148350460098897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97002948966124535787194117 18188052931148350460098897)
  ·
    refine ⟨13641039698361262845074173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18188052931148350460098897 13641039698361262845074173)
    ·
      refine ⟨5115389886885473566902815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13641039698361262845074173 5115389886885473566902815)
      ·
        refine ⟨7673084830328210350354223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115389886885473566902815 7673084830328210350354223)
        ·
          refine ⟨11509627245492315525531335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673084830328210350354223 11509627245492315525531335)
          ·
            refine ⟨17264440868238473288297003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509627245492315525531335 17264440868238473288297003)
            ·
              refine ⟨25896661302357709932445505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264440868238473288297003 25896661302357709932445505)
              ·
                refine ⟨19422495976768282449334129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25896661302357709932445505 19422495976768282449334129)
                ·
                  refine ⟨14566871982576211837000597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422495976768282449334129 14566871982576211837000597)
                  ·
                    refine ⟨682822124183259929859403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14566871982576211837000597 682822124183259929859403)
                    ·
                      rfl

theorem cell23_3989374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3989374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989374 prefixEnd_3989374 := by exact prefixLift 3989374
  have htrace : WordTrace (prefixWord ++ tailWord_3989374) baseStart_3989374 baseEnd_3989374 := by
    simpa [prefixWord, tailWord_3989374, baseEnd_3989374] using wordTrace_append hprefix tailTrace_3989374
  have hstable : (prefixWord ++ tailWord_3989374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989374).length < 2 ^ (prefixWord ++ tailWord_3989374).sum := by decide
  have hdescent : baseEnd_3989374 < baseStart_3989374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989394 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3989394 : Nat := 118140960795 + 3989394 * 2 ^ 59
def prefixEnd_3989394 : Nat := 4983230072969 + 3 ^ 40 * 3989394 * 2
def baseEnd_3989394 : Nat := 2048476642162869711328117

theorem tailTrace_3989394 : CollatzResearch.WordTrace tailWord_3989394 prefixEnd_3989394 2048476642162869711328117 := by
  unfold tailWord_3989394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36376288227278586774129809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97003435272742898064346157 36376288227278586774129809)
  ·
    refine ⟨27282216170458940080597357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36376288227278586774129809 27282216170458940080597357)
    ·
      refine ⟨10230831063922102530224009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27282216170458940080597357 10230831063922102530224009)
      ·
        refine ⟨7673123297941576897668007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10230831063922102530224009 7673123297941576897668007)
        ·
          refine ⟨11509684946912365346502011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673123297941576897668007 11509684946912365346502011)
          ·
            refine ⟨17264527420368548019753017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11509684946912365346502011 17264527420368548019753017)
            ·
              refine ⟨12948395565276411014814763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17264527420368548019753017 12948395565276411014814763)
              ·
                refine ⟨19422593347914616522222145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12948395565276411014814763 19422593347914616522222145)
                ·
                  refine ⟨14566945010935962391666609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422593347914616522222145 14566945010935962391666609)
                  ·
                    refine ⟨10925208758201971793749957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14566945010935962391666609 10925208758201971793749957)
                    ·
                      refine ⟨2048476642162869711328117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10925208758201971793749957 2048476642162869711328117)
                      ·
                        rfl

theorem cell23_3989394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3989394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989394 prefixEnd_3989394 := by exact prefixLift 3989394
  have htrace : WordTrace (prefixWord ++ tailWord_3989394) baseStart_3989394 baseEnd_3989394 := by
    simpa [prefixWord, tailWord_3989394, baseEnd_3989394] using wordTrace_append hprefix tailTrace_3989394
  have hstable : (prefixWord ++ tailWord_3989394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989394).length < 2 ^ (prefixWord ++ tailWord_3989394).sum := by decide
  have hdescent : baseEnd_3989394 < baseStart_3989394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989397 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3989397 : Nat := 118140960795 + 3989397 * 2 ^ 59
def prefixEnd_3989397 : Nat := 4983230072969 + 3 ^ 40 * 3989397 * 2
def baseEnd_3989397 : Nat := 2048478182604833199590603

theorem tailTrace_3989397 : CollatzResearch.WordTrace tailWord_3989397 prefixEnd_3989397 2048478182604833199590603 := by
  unfold tailWord_3989397
  simp only [CollatzResearch.WordTrace]
  refine ⟨145505262328103478608878445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97003508218735652405918963 145505262328103478608878445)
  ·
    refine ⟨54564473373038804478329417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145505262328103478608878445 54564473373038804478329417)
    ·
      refine ⟨40923355029779103358747063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54564473373038804478329417 40923355029779103358747063)
      ·
        refine ⟨61385032544668655038120595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40923355029779103358747063 61385032544668655038120595)
        ·
          refine ⟨92077548817002982557180893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61385032544668655038120595 92077548817002982557180893)
          ·
            refine ⟨34529080806376118458942835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92077548817002982557180893 34529080806376118458942835)
            ·
              refine ⟨51793621209564177688414253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34529080806376118458942835 51793621209564177688414253)
              ·
                refine ⟨19422607953586566633155345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51793621209564177688414253 19422607953586566633155345)
                ·
                  refine ⟨14566955965189924974866509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19422607953586566633155345 14566955965189924974866509)
                  ·
                    refine ⟨5462608486946221865574941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14566955965189924974866509 5462608486946221865574941)
                    ·
                      refine ⟨2048478182604833199590603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462608486946221865574941 2048478182604833199590603)
                      ·
                        rfl

theorem cell23_3989397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3989397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989397 prefixEnd_3989397 := by exact prefixLift 3989397
  have htrace : WordTrace (prefixWord ++ tailWord_3989397) baseStart_3989397 baseEnd_3989397 := by
    simpa [prefixWord, tailWord_3989397, baseEnd_3989397] using wordTrace_append hprefix tailTrace_3989397
  have hstable : (prefixWord ++ tailWord_3989397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989397).length < 2 ^ (prefixWord ++ tailWord_3989397).sum := by decide
  have hdescent : baseEnd_3989397 < baseStart_3989397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989454 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_3989454 : Nat := 118140960795 + 3989454 * 2 ^ 59
def prefixEnd_3989454 : Nat := 4983230072969 + 3 ^ 40 * 3989454 * 2
def baseEnd_3989454 : Nat := 2048507451002139476577841

theorem tailTrace_3989454 : CollatzResearch.WordTrace tailWord_3989454 prefixEnd_3989454 2048507451002139476577841 := by
  unfold tailWord_3989454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188417661112122167962927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97004894192597984895802277 18188417661112122167962927)
  ·
    refine ⟨27282626491668183251944391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18188417661112122167962927 27282626491668183251944391)
    ·
      refine ⟨40923939737502274877916587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27282626491668183251944391 40923939737502274877916587)
      ·
        refine ⟨61385909606253412316874881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40923939737502274877916587 61385909606253412316874881)
        ·
          refine ⟨46039432204690059237656161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61385909606253412316874881 46039432204690059237656161)
          ·
            refine ⟨34529574153517544428242121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46039432204690059237656161 34529574153517544428242121)
            ·
              refine ⟨25897180615138158321181591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34529574153517544428242121 25897180615138158321181591)
              ·
                refine ⟨38845770922707237481772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897180615138158321181591 38845770922707237481772387)
                ·
                  refine ⟨58268656384060856222658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38845770922707237481772387 58268656384060856222658581)
                  ·
                    refine ⟨2731343268002852635437121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58268656384060856222658581 2731343268002852635437121)
                    ·
                      refine ⟨2048507451002139476577841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731343268002852635437121 2048507451002139476577841)
                      ·
                        rfl

theorem cell23_3989454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_3989454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989454 prefixEnd_3989454 := by exact prefixLift 3989454
  have htrace : WordTrace (prefixWord ++ tailWord_3989454) baseStart_3989454 baseEnd_3989454 := by
    simpa [prefixWord, tailWord_3989454, baseEnd_3989454] using wordTrace_append hprefix tailTrace_3989454
  have hstable : (prefixWord ++ tailWord_3989454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989454).length < 2 ^ (prefixWord ++ tailWord_3989454).sum := by decide
  have hdescent : baseEnd_3989454 < baseStart_3989454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989457 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_3989457 : Nat := 118140960795 + 3989457 * 2 ^ 59
def prefixEnd_3989457 : Nat := 4983230072969 + 3 ^ 40 * 3989457 * 2
def baseEnd_3989457 : Nat := 2048508991444102964840327

theorem tailTrace_3989457 : CollatzResearch.WordTrace tailWord_3989457 prefixEnd_3989457 2048508991444102964840327 := by
  unfold tailWord_3989457
  simp only [CollatzResearch.WordTrace]
  refine ⟨145507450707886108856062625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97004967138590739237375083 145507450707886108856062625)
  ·
    refine ⟨109130588030914581642046969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145507450707886108856062625 109130588030914581642046969)
    ·
      refine ⟨81847941023185936231535227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109130588030914581642046969 81847941023185936231535227)
      ·
        refine ⟨122771911534778904347302841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81847941023185936231535227 122771911534778904347302841)
        ·
          refine ⟨92078933651084178260477131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122771911534778904347302841 92078933651084178260477131)
          ·
            refine ⟨138118400476626267390715697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92078933651084178260477131 138118400476626267390715697)
            ·
              refine ⟨103588800357469700543036773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138118400476626267390715697 103588800357469700543036773)
              ·
                refine ⟨19422900067025568851819395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103588800357469700543036773 19422900067025568851819395)
                ·
                  refine ⟨29134350100538353277729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19422900067025568851819395 29134350100538353277729093)
                  ·
                    refine ⟨5462690643850941239574205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29134350100538353277729093 5462690643850941239574205)
                    ·
                      refine ⟨2048508991444102964840327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462690643850941239574205 2048508991444102964840327)
                      ·
                        rfl

theorem cell23_3989457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_3989457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989457 prefixEnd_3989457 := by exact prefixLift 3989457
  have htrace : WordTrace (prefixWord ++ tailWord_3989457) baseStart_3989457 baseEnd_3989457 := by
    simpa [prefixWord, tailWord_3989457, baseEnd_3989457] using wordTrace_append hprefix tailTrace_3989457
  have hstable : (prefixWord ++ tailWord_3989457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989457).length < 2 ^ (prefixWord ++ tailWord_3989457).sum := by decide
  have hdescent : baseEnd_3989457 < baseStart_3989457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989541 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_3989541 : Nat := 118140960795 + 3989541 * 2 ^ 59
def prefixEnd_3989541 : Nat := 4983230072969 + 3 ^ 40 * 3989541 * 2
def baseEnd_3989541 : Nat := 682850707939693545396647

theorem tailTrace_3989541 : CollatzResearch.WordTrace tailWord_3989541 prefixEnd_3989541 682850707939693545396647 := by
  unfold tailWord_3989541
  simp only [CollatzResearch.WordTrace]
  refine ⟨145510514439581791202120477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97007009626387860801413651 145510514439581791202120477)
  ·
    refine ⟨54566442914843171700795179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145510514439581791202120477 54566442914843171700795179)
    ·
      refine ⟨81849664372264757551192769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54566442914843171700795179 81849664372264757551192769)
      ·
        refine ⟨61387248279198568163394577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81849664372264757551192769 61387248279198568163394577)
        ·
          refine ⟨46040436209398926122545933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61387248279198568163394577 46040436209398926122545933)
          ·
            refine ⟨17265163578524597295954725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46040436209398926122545933 17265163578524597295954725)
            ·
              refine ⟨3237218170973361992991511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17265163578524597295954725 3237218170973361992991511)
              ·
                refine ⟨4855827256460042989487267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237218170973361992991511 4855827256460042989487267)
                ·
                  refine ⟨7283740884690064484230901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4855827256460042989487267 7283740884690064484230901)
                  ·
                    refine ⟨682850707939693545396647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7283740884690064484230901 682850707939693545396647)
                    ·
                      rfl

theorem cell23_3989541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_3989541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989541 prefixEnd_3989541 := by exact prefixLift 3989541
  have htrace : WordTrace (prefixWord ++ tailWord_3989541) baseStart_3989541 baseEnd_3989541 := by
    simpa [prefixWord, tailWord_3989541, baseEnd_3989541] using wordTrace_append hprefix tailTrace_3989541
  have hstable : (prefixWord ++ tailWord_3989541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989541).length < 2 ^ (prefixWord ++ tailWord_3989541).sum := by decide
  have hdescent : baseEnd_3989541 < baseStart_3989541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989564 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3989564 : Nat := 118140960795 + 3989564 * 2 ^ 59
def prefixEnd_3989564 : Nat := 4983230072969 + 3 ^ 40 * 3989564 * 2
def baseEnd_3989564 : Nat := 2048563933874134046202335

theorem tailTrace_3989564 : CollatzResearch.WordTrace tailWord_3989564 prefixEnd_3989564 2048563933874134046202335 := by
  unfold tailWord_3989564
  simp only [CollatzResearch.WordTrace]
  refine ⟨72755676659249233065103873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97007568878998977420138497 72755676659249233065103873)
  ·
    refine ⟨54566757494436924798827905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72755676659249233065103873 54566757494436924798827905)
    ·
      refine ⟨40925068120827693599120929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54566757494436924798827905 40925068120827693599120929)
      ·
        refine ⟨30693801090620770199340697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40925068120827693599120929 30693801090620770199340697)
        ·
          refine ⟨23020350817965577649505523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30693801090620770199340697 23020350817965577649505523)
          ·
            refine ⟨34530526226948366474258285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23020350817965577649505523 34530526226948366474258285)
            ·
              refine ⟨12948947335105637427846857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34530526226948366474258285 12948947335105637427846857)
              ·
                refine ⟨9711710501329228070885143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12948947335105637427846857 9711710501329228070885143)
                ·
                  refine ⟨14567565751993842106327715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9711710501329228070885143 14567565751993842106327715)
                  ·
                    refine ⟨21851348627990763159491573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14567565751993842106327715 21851348627990763159491573)
                    ·
                      refine ⟨2048563933874134046202335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21851348627990763159491573 2048563933874134046202335)
                      ·
                        rfl

theorem cell23_3989564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3989564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989564 prefixEnd_3989564 := by exact prefixLift 3989564
  have htrace : WordTrace (prefixWord ++ tailWord_3989564) baseStart_3989564 baseEnd_3989564 := by
    simpa [prefixWord, tailWord_3989564, baseEnd_3989564] using wordTrace_append hprefix tailTrace_3989564
  have hstable : (prefixWord ++ tailWord_3989564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989564).length < 2 ^ (prefixWord ++ tailWord_3989564).sum := by decide
  have hdescent : baseEnd_3989564 < baseStart_3989564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989594 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_3989594 : Nat := 118140960795 + 3989594 * 2 ^ 59
def prefixEnd_3989594 : Nat := 4983230072969 + 3 ^ 40 * 3989594 * 2
def baseEnd_3989594 : Nat := 2048579338293768928827197

theorem tailTrace_3989594 : CollatzResearch.WordTrace tailWord_3989594 prefixEnd_3989594 2048579338293768928827197 := by
  unfold tailWord_3989594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378111877097445313449959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97008298338926520835866557 36378111877097445313449959)
  ·
    refine ⟨54567167815646167970174939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36378111877097445313449959 54567167815646167970174939)
    ·
      refine ⟨81850751723469251955262409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54567167815646167970174939 81850751723469251955262409)
      ·
        refine ⟨61388063792601938966446807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81850751723469251955262409 61388063792601938966446807)
        ·
          refine ⟨92082095688902908449670211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61388063792601938966446807 92082095688902908449670211)
          ·
            refine ⟨138123143533354362674505317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92082095688902908449670211 138123143533354362674505317)
            ·
              refine ⟨25898089412503943001469747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138123143533354362674505317 25898089412503943001469747)
              ·
                refine ⟨38847134118755914502204621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25898089412503943001469747 38847134118755914502204621)
                ·
                  refine ⟨14567675294533467938326733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38847134118755914502204621 14567675294533467938326733)
                  ·
                    refine ⟨5462878235450050476872525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14567675294533467938326733 5462878235450050476872525)
                    ·
                      refine ⟨2048579338293768928827197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462878235450050476872525 2048579338293768928827197)
                      ·
                        rfl

theorem cell23_3989594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_3989594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989594 prefixEnd_3989594 := by exact prefixLift 3989594
  have htrace : WordTrace (prefixWord ++ tailWord_3989594) baseStart_3989594 baseEnd_3989594 := by
    simpa [prefixWord, tailWord_3989594, baseEnd_3989594] using wordTrace_append hprefix tailTrace_3989594
  have hstable : (prefixWord ++ tailWord_3989594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989594).length < 2 ^ (prefixWord ++ tailWord_3989594).sum := by decide
  have hdescent : baseEnd_3989594 < baseStart_3989594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989612 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_3989612 : Nat := 118140960795 + 3989612 * 2 ^ 59
def prefixEnd_3989612 : Nat := 4983230072969 + 3 ^ 40 * 3989612 * 2
def baseEnd_3989612 : Nat := 2048588580945549858402115

theorem tailTrace_3989612 : CollatzResearch.WordTrace tailWord_3989612 prefixEnd_3989612 2048588580945549858402115 := by
  unfold tailWord_3989612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756552011162285163977545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97008736014883046885303393 72756552011162285163977545)
  ·
    refine ⟨54567414008371713872983159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72756552011162285163977545 54567414008371713872983159)
    ·
      refine ⟨81851121012557570809474739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54567414008371713872983159 81851121012557570809474739)
      ·
        refine ⟨122776681518836356214212109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81851121012557570809474739 122776681518836356214212109)
        ·
          refine ⟨46041255569563633580329541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122776681518836356214212109 46041255569563633580329541)
          ·
            refine ⟨8632735419293181296311789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46041255569563633580329541 8632735419293181296311789)
            ·
              refine ⟨3237275782234942986116921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632735419293181296311789 3237275782234942986116921)
              ·
                refine ⟨2427956836676207239587691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3237275782234942986116921 2427956836676207239587691)
                ·
                  refine ⟨3641935255014310859381537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2427956836676207239587691 3641935255014310859381537)
                  ·
                    refine ⟨2731451441260733144536153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3641935255014310859381537 2731451441260733144536153)
                    ·
                      refine ⟨2048588580945549858402115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731451441260733144536153 2048588580945549858402115)
                      ·
                        rfl

theorem cell23_3989612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_3989612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989612 prefixEnd_3989612 := by exact prefixLift 3989612
  have htrace : WordTrace (prefixWord ++ tailWord_3989612) baseStart_3989612 baseEnd_3989612 := by
    simpa [prefixWord, tailWord_3989612, baseEnd_3989612] using wordTrace_append hprefix tailTrace_3989612
  have hstable : (prefixWord ++ tailWord_3989612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989612).length < 2 ^ (prefixWord ++ tailWord_3989612).sum := by decide
  have hdescent : baseEnd_3989612 < baseStart_3989612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989614 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3989614 : Nat := 118140960795 + 3989614 * 2 ^ 59
def prefixEnd_3989614 : Nat := 4983230072969 + 3 ^ 40 * 3989614 * 2
def baseEnd_3989614 : Nat := 682863202635619616859035

theorem tailTrace_3989614 : CollatzResearch.WordTrace tailWord_3989614 prefixEnd_3989614 682863202635619616859035 := by
  unfold tailWord_3989614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18189147121039665583690987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97008784645544883113018597 18189147121039665583690987)
  ·
    refine ⟨27283720681559498375536481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18189147121039665583690987 27283720681559498375536481)
    ·
      refine ⟨20462790511169623781652361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27283720681559498375536481 20462790511169623781652361)
      ·
        refine ⟨15347092883377217836239271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20462790511169623781652361 15347092883377217836239271)
        ·
          refine ⟨23020639325065826754358907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347092883377217836239271 23020639325065826754358907)
          ·
            refine ⟨34530958987598740131538361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23020639325065826754358907 34530958987598740131538361)
            ·
              refine ⟨25898219240699055098653771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34530958987598740131538361 25898219240699055098653771)
              ·
                refine ⟨38847328861048582647980657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25898219240699055098653771 38847328861048582647980657)
                ·
                  refine ⟨29135496645786436985985493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38847328861048582647980657 29135496645786436985985493)
                  ·
                    refine ⟨682863202635619616859035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29135496645786436985985493 682863202635619616859035)
                    ·
                      rfl

theorem cell23_3989614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3989614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989614 prefixEnd_3989614 := by exact prefixLift 3989614
  have htrace : WordTrace (prefixWord ++ tailWord_3989614) baseStart_3989614 baseEnd_3989614 := by
    simpa [prefixWord, tailWord_3989614, baseEnd_3989614] using wordTrace_append hprefix tailTrace_3989614
  have hstable : (prefixWord ++ tailWord_3989614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989614).length < 2 ^ (prefixWord ++ tailWord_3989614).sum := by decide
  have hdescent : baseEnd_3989614 < baseStart_3989614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989628 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_3989628 : Nat := 118140960795 + 3989628 * 2 ^ 59
def prefixEnd_3989628 : Nat := 4983230072969 + 3 ^ 40 * 3989628 * 2
def baseEnd_3989628 : Nat := 2048596796636021795802041

theorem tailTrace_3989628 : CollatzResearch.WordTrace tailWord_3989628 prefixEnd_3989628 2048596796636021795802041 := by
  unfold tailWord_3989628
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756843795133302530268769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97009125060177736707025025 72756843795133302530268769)
  ·
    refine ⟨54567632846349976897701577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72756843795133302530268769 54567632846349976897701577)
    ·
      refine ⟨40925724634762482673276183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54567632846349976897701577 40925724634762482673276183)
      ·
        refine ⟨61388586952143724009914275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40925724634762482673276183 61388586952143724009914275)
        ·
          refine ⟨92082880428215586014871413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61388586952143724009914275 92082880428215586014871413)
          ·
            refine ⟨8632770040145211188894195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92082880428215586014871413 8632770040145211188894195)
            ·
              refine ⟨12949155060217816783341293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8632770040145211188894195 12949155060217816783341293)
              ·
                refine ⟨4855933147581681293752985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949155060217816783341293 4855933147581681293752985)
                ·
                  refine ⟨3641949860686260970314739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855933147581681293752985 3641949860686260970314739)
                  ·
                    refine ⟨5462924791029391455472109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641949860686260970314739 5462924791029391455472109)
                    ·
                      refine ⟨2048596796636021795802041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462924791029391455472109 2048596796636021795802041)
                      ·
                        rfl

theorem cell23_3989628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_3989628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989628 prefixEnd_3989628 := by exact prefixLift 3989628
  have htrace : WordTrace (prefixWord ++ tailWord_3989628) baseStart_3989628 baseEnd_3989628 := by
    simpa [prefixWord, tailWord_3989628, baseEnd_3989628] using wordTrace_append hprefix tailTrace_3989628
  have hstable : (prefixWord ++ tailWord_3989628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989628).length < 2 ^ (prefixWord ++ tailWord_3989628).sum := by decide
  have hdescent : baseEnd_3989628 < baseStart_3989628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989647 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_3989647 : Nat := 118140960795 + 3989647 * 2 ^ 59
def prefixEnd_3989647 : Nat := 4983230072969 + 3 ^ 40 * 3989647 * 2
def baseEnd_3989647 : Nat := 2048606552768457221464453

theorem tailTrace_3989647 : CollatzResearch.WordTrace tailWord_3989647 prefixEnd_3989647 2048606552768457221464453 := by
  unfold tailWord_3989647
  simp only [CollatzResearch.WordTrace]
  refine ⟨145514380577197771305479195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97009587051465180870319463 145514380577197771305479195)
  ·
    refine ⟨218271570865796656958218793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145514380577197771305479195 218271570865796656958218793)
    ·
      refine ⟨163703678149347492718664095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218271570865796656958218793 163703678149347492718664095)
      ·
        refine ⟨245555517224021239077996143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163703678149347492718664095 245555517224021239077996143)
        ·
          refine ⟨368333275836031858616994215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245555517224021239077996143 368333275836031858616994215)
          ·
            refine ⟨552499913754047787925491323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368333275836031858616994215 552499913754047787925491323)
            ·
              refine ⟨828749870631071681888236985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552499913754047787925491323 828749870631071681888236985)
              ·
                refine ⟨621562402973303761416177739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828749870631071681888236985 621562402973303761416177739)
                ·
                  refine ⟨932343604459955642124266609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621562402973303761416177739 932343604459955642124266609)
                  ·
                    refine ⟨699257703344966731593199957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932343604459955642124266609 699257703344966731593199957)
                    ·
                      refine ⟨2048606552768457221464453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 699257703344966731593199957 2048606552768457221464453)
                      ·
                        rfl

theorem cell23_3989647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_3989647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989647 prefixEnd_3989647 := by exact prefixLift 3989647
  have htrace : WordTrace (prefixWord ++ tailWord_3989647) baseStart_3989647 baseEnd_3989647 := by
    simpa [prefixWord, tailWord_3989647, baseEnd_3989647] using wordTrace_append hprefix tailTrace_3989647
  have hstable : (prefixWord ++ tailWord_3989647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989647).length < 2 ^ (prefixWord ++ tailWord_3989647).sum := by decide
  have hdescent : baseEnd_3989647 < baseStart_3989647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989662 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3989662 : Nat := 118140960795 + 3989662 * 2 ^ 59
def prefixEnd_3989662 : Nat := 4983230072969 + 3 ^ 40 * 3989662 * 2
def baseEnd_3989662 : Nat := 2048614254978274662776885

theorem tailTrace_3989662 : CollatzResearch.WordTrace tailWord_3989662 prefixEnd_3989662 2048614254978274662776885 := by
  unfold tailWord_3989662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18189365959017928608409405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97009951781428952578183493 18189365959017928608409405)
  ·
    refine ⟨6821012234631723228153527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18189365959017928608409405 6821012234631723228153527)
    ·
      refine ⟨10231518351947584842230291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821012234631723228153527 10231518351947584842230291)
      ·
        refine ⟨15347277527921377263345437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231518351947584842230291 15347277527921377263345437)
        ·
          refine ⟨5755229072970516473754539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15347277527921377263345437 5755229072970516473754539)
          ·
            refine ⟨8632843609455774710631809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755229072970516473754539 8632843609455774710631809)
            ·
              refine ⟨6474632707091831032973857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8632843609455774710631809 6474632707091831032973857)
              ·
                refine ⟨4855974530318873274730393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474632707091831032973857 4855974530318873274730393)
                ·
                  refine ⟨3641980897739154956047795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4855974530318873274730393 3641980897739154956047795)
                  ·
                    refine ⟨5462971346608732434071693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3641980897739154956047795 5462971346608732434071693)
                    ·
                      refine ⟨2048614254978274662776885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5462971346608732434071693 2048614254978274662776885)
                      ·
                        rfl

theorem cell23_3989662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3989662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989662 prefixEnd_3989662 := by exact prefixLift 3989662
  have htrace : WordTrace (prefixWord ++ tailWord_3989662) baseStart_3989662 baseEnd_3989662 := by
    simpa [prefixWord, tailWord_3989662, baseEnd_3989662] using wordTrace_append hprefix tailTrace_3989662
  have hstable : (prefixWord ++ tailWord_3989662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989662).length < 2 ^ (prefixWord ++ tailWord_3989662).sum := by decide
  have hdescent : baseEnd_3989662 < baseStart_3989662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989758 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3989758 : Nat := 118140960795 + 3989758 * 2 ^ 59
def prefixEnd_3989758 : Nat := 4983230072969 + 3 ^ 40 * 3989758 * 2
def baseEnd_3989758 : Nat := 2048663549121106287176443

theorem tailTrace_3989758 : CollatzResearch.WordTrace tailWord_3989758 prefixEnd_3989758 2048663549121106287176443 := by
  unfold tailWord_3989758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18189803634974454657846241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97012286053197091508513285 18189803634974454657846241)
  ·
    refine ⟨13642352726230840993384681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18189803634974454657846241 13642352726230840993384681)
    ·
      refine ⟨10231764544673130745038511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13642352726230840993384681 10231764544673130745038511)
      ·
        refine ⟨15347646817009696117557767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10231764544673130745038511 15347646817009696117557767)
        ·
          refine ⟨23021470225514544176336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15347646817009696117557767 23021470225514544176336651)
          ·
            refine ⟨34532205338271816264504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23021470225514544176336651 34532205338271816264504977)
            ·
              refine ⟨25899154003703862198378733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34532205338271816264504977 25899154003703862198378733)
              ·
                refine ⟨9712182751388948324392025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25899154003703862198378733 9712182751388948324392025)
                ·
                  refine ⟨7284137063541711243294019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712182751388948324392025 7284137063541711243294019)
                  ·
                    refine ⟨10926205595312566864941029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7284137063541711243294019 10926205595312566864941029)
                    ·
                      refine ⟨2048663549121106287176443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10926205595312566864941029 2048663549121106287176443)
                      ·
                        rfl

theorem cell23_3989758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3989758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989758 prefixEnd_3989758 := by exact prefixLift 3989758
  have htrace : WordTrace (prefixWord ++ tailWord_3989758) baseStart_3989758 baseEnd_3989758 := by
    simpa [prefixWord, tailWord_3989758, baseEnd_3989758] using wordTrace_append hprefix tailTrace_3989758
  have hstable : (prefixWord ++ tailWord_3989758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989758).length < 2 ^ (prefixWord ++ tailWord_3989758).sum := by decide
  have hdescent : baseEnd_3989758 < baseStart_3989758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989761 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3989761 : Nat := 118140960795 + 3989761 * 2 ^ 59
def prefixEnd_3989761 : Nat := 4983230072969 + 3 ^ 40 * 3989761 * 2
def baseEnd_3989761 : Nat := 2048665089563069775438929

theorem tailTrace_3989761 : CollatzResearch.WordTrace tailWord_3989761 prefixEnd_3989761 2048665089563069775438929 := by
  unfold tailWord_3989761
  simp only [CollatzResearch.WordTrace]
  refine ⟨145518538498784768775129137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97012358999189845850086091 145518538498784768775129137)
  ·
    refine ⟨109138903874088576581346853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145518538498784768775129137 109138903874088576581346853)
    ·
      refine ⟨20463544476391608109002535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109138903874088576581346853 20463544476391608109002535)
      ·
        refine ⟨30695316714587412163503803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463544476391608109002535 30695316714587412163503803)
        ·
          refine ⟨46042975071881118245255705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30695316714587412163503803 46042975071881118245255705)
          ·
            refine ⟨34532231303910838683941779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46042975071881118245255705 34532231303910838683941779)
            ·
              refine ⟨51798346955866258025912669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34532231303910838683941779 51798346955866258025912669)
              ·
                refine ⟨19424380108449846759717251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51798346955866258025912669 19424380108449846759717251)
                ·
                  refine ⟨29136570162674770139575877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19424380108449846759717251 29136570162674770139575877)
                  ·
                    refine ⟨5463106905501519401170477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29136570162674770139575877 5463106905501519401170477)
                    ·
                      refine ⟨2048665089563069775438929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463106905501519401170477 2048665089563069775438929)
                      ·
                        rfl

theorem cell23_3989761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3989761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989761 prefixEnd_3989761 := by exact prefixLift 3989761
  have htrace : WordTrace (prefixWord ++ tailWord_3989761) baseStart_3989761 baseEnd_3989761 := by
    simpa [prefixWord, tailWord_3989761, baseEnd_3989761] using wordTrace_append hprefix tailTrace_3989761
  have hstable : (prefixWord ++ tailWord_3989761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989761).length < 2 ^ (prefixWord ++ tailWord_3989761).sum := by decide
  have hdescent : baseEnd_3989761 < baseStart_3989761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989811 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 3, 5]
def baseStart_3989811 : Nat := 118140960795 + 3989811 * 2 ^ 59
def prefixEnd_3989811 : Nat := 4983230072969 + 3 ^ 40 * 3989811 * 2
def baseEnd_3989811 : Nat := 682896921198598193271233

theorem tailTrace_3989811 : CollatzResearch.WordTrace tailWord_3989811 prefixEnd_3989811 682896921198598193271233 := by
  unfold tailWord_3989811
  simp only [CollatzResearch.WordTrace]
  refine ⟨145520362148603627314449287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97013574765735751542966191 145520362148603627314449287)
  ·
    refine ⟨218280543222905440971673931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145520362148603627314449287 218280543222905440971673931)
    ·
      refine ⟨327420814834358161457510897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218280543222905440971673931 327420814834358161457510897)
      ·
        refine ⟨245565611125768621093133173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327420814834358161457510897 245565611125768621093133173)
        ·
          refine ⟨23021776043040808227481235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245565611125768621093133173 23021776043040808227481235)
          ·
            refine ⟨34532664064561212341221853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23021776043040808227481235 34532664064561212341221853)
            ·
              refine ⟨12949749024210454627958195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34532664064561212341221853 12949749024210454627958195)
              ·
                refine ⟨19424623536315681941937293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12949749024210454627958195 19424623536315681941937293)
                ·
                  refine ⟨7284233826118380728226485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19424623536315681941937293 7284233826118380728226485)
                  ·
                    refine ⟨682896921198598193271233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7284233826118380728226485 682896921198598193271233)
                    ·
                      rfl

theorem cell23_3989811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].length) (baseStart_3989811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989811 prefixEnd_3989811 := by exact prefixLift 3989811
  have htrace : WordTrace (prefixWord ++ tailWord_3989811) baseStart_3989811 baseEnd_3989811 := by
    simpa [prefixWord, tailWord_3989811, baseEnd_3989811] using wordTrace_append hprefix tailTrace_3989811
  have hstable : (prefixWord ++ tailWord_3989811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989811).length < 2 ^ (prefixWord ++ tailWord_3989811).sum := by decide
  have hdescent : baseEnd_3989811 < baseStart_3989811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989858 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3989858 : Nat := 118140960795 + 3989858 * 2 ^ 59
def prefixEnd_3989858 : Nat := 4983230072969 + 3 ^ 40 * 3989858 * 2
def baseEnd_3989858 : Nat := 682904965728851965308661

theorem tailTrace_3989858 : CollatzResearch.WordTrace tailWord_3989858 prefixEnd_3989858 682904965728851965308661 := by
  unfold tailWord_3989858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36380519094858338585352557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97014717586288902894273485 36380519094858338585352557)
  ·
    refine ⟨13642694660571876969507209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36380519094858338585352557 13642694660571876969507209)
    ·
      refine ⟨10232020995428907727130407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13642694660571876969507209 10232020995428907727130407)
      ·
        refine ⟨15348031493143361590695611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232020995428907727130407 15348031493143361590695611)
        ·
          refine ⟨23022047239715042386043417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348031493143361590695611 23022047239715042386043417)
          ·
            refine ⟨17266535429786281789532563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23022047239715042386043417 17266535429786281789532563)
            ·
              refine ⟨25899803144679422684298845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266535429786281789532563 25899803144679422684298845)
              ·
                refine ⟨9712426179254783506612067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25899803144679422684298845 9712426179254783506612067)
                ·
                  refine ⟨14568639268882175259918101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9712426179254783506612067 14568639268882175259918101)
                  ·
                    refine ⟨682904965728851965308661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14568639268882175259918101 682904965728851965308661)
                    ·
                      rfl

theorem cell23_3989858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3989858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989858 prefixEnd_3989858 := by exact prefixLift 3989858
  have htrace : WordTrace (prefixWord ++ tailWord_3989858) baseStart_3989858 baseEnd_3989858 := by
    simpa [prefixWord, tailWord_3989858, baseEnd_3989858] using wordTrace_append hprefix tailTrace_3989858
  have hstable : (prefixWord ++ tailWord_3989858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989858).length < 2 ^ (prefixWord ++ tailWord_3989858).sum := by decide
  have hdescent : baseEnd_3989858 < baseStart_3989858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989865 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 3, 2, 2]
def baseStart_3989865 : Nat := 118140960795 + 3989865 * 2 ^ 59
def prefixEnd_3989865 : Nat := 4983230072969 + 3 ^ 40 * 3989865 * 2
def baseEnd_3989865 : Nat := 2048718491551137368538451

theorem tailTrace_3989865 : CollatzResearch.WordTrace tailWord_3989865 prefixEnd_3989865 2048718491551137368538451 := by
  unfold tailWord_3989865
  simp only [CollatzResearch.WordTrace]
  refine ⟨145522331690407994536915049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97014887793605329691276699 145522331690407994536915049)
  ·
    refine ⟨109141748767805995902686287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145522331690407994536915049 109141748767805995902686287)
    ·
      refine ⟨163712623151708993854029431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109141748767805995902686287 163712623151708993854029431)
      ·
        refine ⟨245568934727563490781044147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163712623151708993854029431 245568934727563490781044147)
        ·
          refine ⟨368353402091345236171566221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245568934727563490781044147 368353402091345236171566221)
          ·
            refine ⟨138132525784254463564337333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368353402091345236171566221 138132525784254463564337333)
            ·
              refine ⟨12949924292273855959156625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138132525784254463564337333 12949924292273855959156625)
              ·
                refine ⟨9712443219205391969367469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12949924292273855959156625 9712443219205391969367469)
                ·
                  refine ⟨3642166207202021988512801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9712443219205391969367469 3642166207202021988512801)
                  ·
                    refine ⟨2731624655401516491384601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3642166207202021988512801 2731624655401516491384601)
                    ·
                      refine ⟨2048718491551137368538451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731624655401516491384601 2048718491551137368538451)
                      ·
                        rfl

theorem cell23_3989865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2, 2].length) (baseStart_3989865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989865 prefixEnd_3989865 := by exact prefixLift 3989865
  have htrace : WordTrace (prefixWord ++ tailWord_3989865) baseStart_3989865 baseEnd_3989865 := by
    simpa [prefixWord, tailWord_3989865, baseEnd_3989865] using wordTrace_append hprefix tailTrace_3989865
  have hstable : (prefixWord ++ tailWord_3989865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989865).length < 2 ^ (prefixWord ++ tailWord_3989865).sum := by decide
  have hdescent : baseEnd_3989865 < baseStart_3989865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989885 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_3989885 : Nat := 118140960795 + 3989885 * 2 ^ 59
def prefixEnd_3989885 : Nat := 4983230072969 + 3 ^ 40 * 3989885 * 2
def baseEnd_3989885 : Nat := 2048728761164227290288359

theorem tailTrace_3989885 : CollatzResearch.WordTrace tailWord_3989885 prefixEnd_3989885 2048728761164227290288359 := by
  unfold tailWord_3989885
  simp only [CollatzResearch.WordTrace]
  refine ⟨145523061150335537952643109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97015374100223691968428739 145523061150335537952643109)
  ·
    refine ⟨27285573965687913366120583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145523061150335537952643109 27285573965687913366120583)
    ·
      refine ⟨40928360948531870049180875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27285573965687913366120583 40928360948531870049180875)
      ·
        refine ⟨61392541422797805073771313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40928360948531870049180875 61392541422797805073771313)
        ·
          refine ⟨46044406067098353805328485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61392541422797805073771313 46044406067098353805328485)
          ·
            refine ⟨8633326137580941338499091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46044406067098353805328485 8633326137580941338499091)
            ·
              refine ⟨12949989206371412007748637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633326137580941338499091 12949989206371412007748637)
              ·
                refine ⟨4856245952389279502905739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12949989206371412007748637 4856245952389279502905739)
                ·
                  refine ⟨7284368928583919254358609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856245952389279502905739 7284368928583919254358609)
                  ·
                    refine ⟨5463276696437939440768957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7284368928583919254358609 5463276696437939440768957)
                    ·
                      refine ⟨2048728761164227290288359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463276696437939440768957 2048728761164227290288359)
                      ·
                        rfl

theorem cell23_3989885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_3989885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989885 prefixEnd_3989885 := by exact prefixLift 3989885
  have htrace : WordTrace (prefixWord ++ tailWord_3989885) baseStart_3989885 baseEnd_3989885 := by
    simpa [prefixWord, tailWord_3989885, baseEnd_3989885] using wordTrace_append hprefix tailTrace_3989885
  have hstable : (prefixWord ++ tailWord_3989885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989885).length < 2 ^ (prefixWord ++ tailWord_3989885).sum := by decide
  have hdescent : baseEnd_3989885 < baseStart_3989885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989933 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3989933 : Nat := 118140960795 + 3989933 * 2 ^ 59
def prefixEnd_3989933 : Nat := 4983230072969 + 3 ^ 40 * 3989933 * 2
def baseEnd_3989933 : Nat := 2048753408235643102488139

theorem tailTrace_3989933 : CollatzResearch.WordTrace tailWord_3989933 prefixEnd_3989933 2048753408235643102488139 := by
  unfold tailWord_3989933
  simp only [CollatzResearch.WordTrace]
  refine ⟨145524811854161642150390453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97016541236107761433593635 145524811854161642150390453)
  ·
    refine ⟨13642951111327653951599105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145524811854161642150390453 13642951111327653951599105)
    ·
      refine ⟨10232213333495740463699329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13642951111327653951599105 10232213333495740463699329)
      ·
        refine ⟨7674160000121805347774497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10232213333495740463699329 7674160000121805347774497)
        ·
          refine ⟨5755620000091354010830873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7674160000121805347774497 5755620000091354010830873)
          ·
            refine ⟨4316715000068515508123155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5755620000091354010830873 4316715000068515508123155)
            ·
              refine ⟨6475072500102773262184733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316715000068515508123155 6475072500102773262184733)
              ·
                refine ⟨2428152187538539973319275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6475072500102773262184733 2428152187538539973319275)
                ·
                  refine ⟨3642228281307809959978913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428152187538539973319275 3642228281307809959978913)
                  ·
                    refine ⟨2731671210980857469984185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3642228281307809959978913 2731671210980857469984185)
                    ·
                      refine ⟨2048753408235643102488139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2731671210980857469984185 2048753408235643102488139)
                      ·
                        rfl

theorem cell23_3989933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3989933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989933 prefixEnd_3989933 := by exact prefixLift 3989933
  have htrace : WordTrace (prefixWord ++ tailWord_3989933) baseStart_3989933 baseEnd_3989933 := by
    simpa [prefixWord, tailWord_3989933, baseEnd_3989933] using wordTrace_append hprefix tailTrace_3989933
  have hstable : (prefixWord ++ tailWord_3989933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989933).length < 2 ^ (prefixWord ++ tailWord_3989933).sum := by decide
  have hdescent : baseEnd_3989933 < baseStart_3989933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3989988 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3989988 : Nat := 118140960795 + 3989988 * 2 ^ 59
def prefixEnd_3989988 : Nat := 4983230072969 + 3 ^ 40 * 3989988 * 2
def baseEnd_3989988 : Nat := 2048781649671640387300385

theorem tailTrace_3989988 : CollatzResearch.WordTrace tailWord_3989988 prefixEnd_3989988 2048781649671640387300385 := by
  unfold tailWord_3989988
  simp only [CollatzResearch.WordTrace]
  refine ⟨72763408934481193271821309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97017878579308257695761745 72763408934481193271821309)
  ·
    refine ⟨27286278350430447476932991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72763408934481193271821309 27286278350430447476932991)
    ·
      refine ⟨40929417525645671215399487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27286278350430447476932991 40929417525645671215399487)
      ·
        refine ⟨61394126288468506823099231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40929417525645671215399487 61394126288468506823099231)
        ·
          refine ⟨92091189432702760234648847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61394126288468506823099231 92091189432702760234648847)
          ·
            refine ⟨138136784149054140351973271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92091189432702760234648847 138136784149054140351973271)
            ·
              refine ⟨207205176223581210527959907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138136784149054140351973271 207205176223581210527959907)
              ·
                refine ⟨310807764335371815791939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207205176223581210527959907 310807764335371815791939861)
                ·
                  refine ⟨14569113953220553865247181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 310807764335371815791939861 14569113953220553865247181)
                  ·
                    refine ⟨5463417732457707699467693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569113953220553865247181 5463417732457707699467693)
                    ·
                      refine ⟨2048781649671640387300385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463417732457707699467693 2048781649671640387300385)
                      ·
                        rfl

theorem cell23_3989988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3989988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3989988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3989988 prefixEnd_3989988 := by exact prefixLift 3989988
  have htrace : WordTrace (prefixWord ++ tailWord_3989988) baseStart_3989988 baseEnd_3989988 := by
    simpa [prefixWord, tailWord_3989988, baseEnd_3989988] using wordTrace_append hprefix tailTrace_3989988
  have hstable : (prefixWord ++ tailWord_3989988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3989988).length < 2 ^ (prefixWord ++ tailWord_3989988).sum := by decide
  have hdescent : baseEnd_3989988 < baseStart_3989988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3989988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990008 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_3990008 : Nat := 118140960795 + 3990008 * 2 ^ 59
def prefixEnd_3990008 : Nat := 4983230072969 + 3 ^ 40 * 3990008 * 2
def baseEnd_3990008 : Nat := 682930639761576769683431

theorem tailTrace_3990008 : CollatzResearch.WordTrace tailWord_3990008 prefixEnd_3990008 682930639761576769683431 := by
  unfold tailWord_3990008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72763773664444964979685339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97018364885926619972913785 72763773664444964979685339)
  ·
    refine ⟨109145660496667447469528009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72763773664444964979685339 109145660496667447469528009)
    ·
      refine ⟨81859245372500585602146007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109145660496667447469528009 81859245372500585602146007)
      ·
        refine ⟨122788868058750878403219011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81859245372500585602146007 122788868058750878403219011)
        ·
          refine ⟨184183302088126317604828517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122788868058750878403219011 184183302088126317604828517)
          ·
            refine ⟨34534369141523684550905347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184183302088126317604828517 34534369141523684550905347)
            ·
              refine ⟨51801553712285526826358021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34534369141523684550905347 51801553712285526826358021)
              ·
                refine ⟨9712791321053536279942129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51801553712285526826358021 9712791321053536279942129)
                ·
                  refine ⟨7284593490790152209956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712791321053536279942129 7284593490790152209956597)
                  ·
                    refine ⟨682930639761576769683431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7284593490790152209956597 682930639761576769683431)
                    ·
                      rfl

theorem cell23_3990008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_3990008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990008 prefixEnd_3990008 := by exact prefixLift 3990008
  have htrace : WordTrace (prefixWord ++ tailWord_3990008) baseStart_3990008 baseEnd_3990008 := by
    simpa [prefixWord, tailWord_3990008, baseEnd_3990008] using wordTrace_append hprefix tailTrace_3990008
  have hstable : (prefixWord ++ tailWord_3990008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990008).length < 2 ^ (prefixWord ++ tailWord_3990008).sum := by decide
  have hdescent : baseEnd_3990008 < baseStart_3990008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_3990011 : Nat := 118140960795 + 3990011 * 2 ^ 59
def prefixEnd_3990011 : Nat := 4983230072969 + 3 ^ 40 * 3990011 * 2
def baseEnd_3990011 : Nat := 2048793459726693797312779

theorem tailTrace_3990011 : CollatzResearch.WordTrace tailWord_3990011 prefixEnd_3990011 2048793459726693797312779 := by
  unfold tailWord_3990011
  simp only [CollatzResearch.WordTrace]
  refine ⟨145527656747879061471729887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97018437831919374314486591 145527656747879061471729887)
  ·
    refine ⟨218291485121818592207594831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145527656747879061471729887 218291485121818592207594831)
    ·
      refine ⟨327437227682727888311392247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218291485121818592207594831 327437227682727888311392247)
      ·
        refine ⟨491155841524091832467088371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327437227682727888311392247 491155841524091832467088371)
        ·
          refine ⟨736733762286137748700632557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491155841524091832467088371 736733762286137748700632557)
          ·
            refine ⟨276275160857301655762737209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 736733762286137748700632557 276275160857301655762737209)
            ·
              refine ⟨207206370642976241822052907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276275160857301655762737209 207206370642976241822052907)
              ·
                refine ⟨310809555964464362733079361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207206370642976241822052907 310809555964464362733079361)
                ·
                  refine ⟨233107166973348272049809521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310809555964464362733079361 233107166973348272049809521)
                  ·
                    refine ⟨174830375230011204037357141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233107166973348272049809521 174830375230011204037357141)
                    ·
                      refine ⟨2048793459726693797312779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 174830375230011204037357141 2048793459726693797312779)
                      ·
                        rfl

theorem cell23_3990011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_3990011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990011 prefixEnd_3990011 := by exact prefixLift 3990011
  have htrace : WordTrace (prefixWord ++ tailWord_3990011) baseStart_3990011 baseEnd_3990011 := by
    simpa [prefixWord, tailWord_3990011, baseEnd_3990011] using wordTrace_append hprefix tailTrace_3990011
  have hstable : (prefixWord ++ tailWord_3990011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990011).length < 2 ^ (prefixWord ++ tailWord_3990011).sum := by decide
  have hdescent : baseEnd_3990011 < baseStart_3990011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990045 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3990045 : Nat := 118140960795 + 3990045 * 2 ^ 59
def prefixEnd_3990045 : Nat := 4983230072969 + 3 ^ 40 * 3990045 * 2
def baseEnd_3990045 : Nat := 2048810918068946664287623

theorem tailTrace_3990045 : CollatzResearch.WordTrace tailWord_3990045 prefixEnd_3990045 2048810918068946664287623 := by
  unfold tailWord_3990045
  simp only [CollatzResearch.WordTrace]
  refine ⟨145528896829755885278467589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97019264553170590185645059 145528896829755885278467589)
  ·
    refine ⟨27286668155579228489712673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145528896829755885278467589 27286668155579228489712673)
    ·
      refine ⟨20465001116684421367284505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27286668155579228489712673 20465001116684421367284505)
      ·
        refine ⟨15348750837513316025463379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20465001116684421367284505 15348750837513316025463379)
        ·
          refine ⟨23023126256269974038195069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348750837513316025463379 23023126256269974038195069)
          ·
            refine ⟨8633672346101240264323151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23023126256269974038195069 8633672346101240264323151)
            ·
              refine ⟨12950508519151860396484727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633672346101240264323151 12950508519151860396484727)
              ·
                refine ⟨19425762778727790594727091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12950508519151860396484727 19425762778727790594727091)
                ·
                  refine ⟨29138644168091685892090637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19425762778727790594727091 29138644168091685892090637)
                  ·
                    refine ⟨10926991563034382209533989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29138644168091685892090637 10926991563034382209533989)
                    ·
                      refine ⟨2048810918068946664287623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10926991563034382209533989 2048810918068946664287623)
                      ·
                        rfl

theorem cell23_3990045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3990045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990045 prefixEnd_3990045 := by exact prefixLift 3990045
  have htrace : WordTrace (prefixWord ++ tailWord_3990045) baseStart_3990045 baseEnd_3990045 := by
    simpa [prefixWord, tailWord_3990045, baseEnd_3990045] using wordTrace_append hprefix tailTrace_3990045
  have hstable : (prefixWord ++ tailWord_3990045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990045).length < 2 ^ (prefixWord ++ tailWord_3990045).sum := by decide
  have hdescent : baseEnd_3990045 < baseStart_3990045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990065 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3990065 : Nat := 118140960795 + 3990065 * 2 ^ 59
def prefixEnd_3990065 : Nat := 4983230072969 + 3 ^ 40 * 3990065 * 2
def baseEnd_3990065 : Nat := 2048821187682036586037531

theorem tailTrace_3990065 : CollatzResearch.WordTrace tailWord_3990065 prefixEnd_3990065 2048821187682036586037531 := by
  unfold tailWord_3990065
  simp only [CollatzResearch.WordTrace]
  refine ⟨145529626289683428694195649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97019750859788952462797099 145529626289683428694195649)
  ·
    refine ⟨109147219717262571520646737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145529626289683428694195649 109147219717262571520646737)
    ·
      refine ⟨81860414787946928640485053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109147219717262571520646737 81860414787946928640485053)
      ·
        refine ⟨30697655545480098240181895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81860414787946928640485053 30697655545480098240181895)
        ·
          refine ⟨46046483318220147360272843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30697655545480098240181895 46046483318220147360272843)
          ·
            refine ⟨69069724977330221040409265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46046483318220147360272843 69069724977330221040409265)
            ·
              refine ⟨51802293732997665780306949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69069724977330221040409265 51802293732997665780306949)
              ·
                refine ⟨9712930074937062333807553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51802293732997665780306949 9712930074937062333807553)
                ·
                  refine ⟨7284697556202796750355665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9712930074937062333807553 7284697556202796750355665)
                  ·
                    refine ⟨5463523167152097562766749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7284697556202796750355665 5463523167152097562766749)
                    ·
                      refine ⟨2048821187682036586037531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463523167152097562766749 2048821187682036586037531)
                      ·
                        rfl

theorem cell23_3990065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3990065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990065 prefixEnd_3990065 := by exact prefixLift 3990065
  have htrace : WordTrace (prefixWord ++ tailWord_3990065) baseStart_3990065 baseEnd_3990065 := by
    simpa [prefixWord, tailWord_3990065, baseEnd_3990065] using wordTrace_append hprefix tailTrace_3990065
  have hstable : (prefixWord ++ tailWord_3990065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990065).length < 2 ^ (prefixWord ++ tailWord_3990065).sum := by decide
  have hdescent : baseEnd_3990065 < baseStart_3990065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990072 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 1, 4]
def baseStart_3990072 : Nat := 118140960795 + 3990072 * 2 ^ 59
def prefixEnd_3990072 : Nat := 4983230072969 + 3 ^ 40 * 3990072 * 2
def baseEnd_3990072 : Nat := 682941594015539352883333

theorem tailTrace_3990072 : CollatzResearch.WordTrace tailWord_3990072 prefixEnd_3990072 682941594015539352883333 := by
  unfold tailWord_3990072
  simp only [CollatzResearch.WordTrace]
  refine ⟨72764940800329034444850235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97019921067105379259800313 72764940800329034444850235)
  ·
    refine ⟨109147411200493551667275353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72764940800329034444850235 109147411200493551667275353)
    ·
      refine ⟨81860558400370163750456515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109147411200493551667275353 81860558400370163750456515)
      ·
        refine ⟨122790837600555245625684773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81860558400370163750456515 122790837600555245625684773)
        ·
          refine ⟨23023282050104108554815895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122790837600555245625684773 23023282050104108554815895)
          ·
            refine ⟨34534923075156162832223843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23023282050104108554815895 34534923075156162832223843)
            ·
              refine ⟨51802384612734244248335765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34534923075156162832223843 51802384612734244248335765)
              ·
                refine ⟨2428236778721917699140739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51802384612734244248335765 2428236778721917699140739)
                ·
                  refine ⟨3642355168082876548711109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428236778721917699140739 3642355168082876548711109)
                  ·
                    refine ⟨682941594015539352883333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3642355168082876548711109 682941594015539352883333)
                    ·
                      rfl

theorem cell23_3990072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_3990072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990072 prefixEnd_3990072 := by exact prefixLift 3990072
  have htrace : WordTrace (prefixWord ++ tailWord_3990072) baseStart_3990072 baseEnd_3990072 := by
    simpa [prefixWord, tailWord_3990072, baseEnd_3990072] using wordTrace_append hprefix tailTrace_3990072
  have hstable : (prefixWord ++ tailWord_3990072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990072).length < 2 ^ (prefixWord ++ tailWord_3990072).sum := by decide
  have hdescent : baseEnd_3990072 < baseStart_3990072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990115 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 1, 5]
def baseStart_3990115 : Nat := 118140960795 + 3990115 * 2 ^ 59
def prefixEnd_3990115 : Nat := 4983230072969 + 3 ^ 40 * 3990115 * 2
def baseEnd_3990115 : Nat := 682948953904920463470767

theorem tailTrace_3990115 : CollatzResearch.WordTrace tailWord_3990115 prefixEnd_3990115 682948953904920463470767 := by
  unfold tailWord_3990115
  simp only [CollatzResearch.WordTrace]
  refine ⟨145531449939502287233515799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97020966626334858155677199 145531449939502287233515799)
  ·
    refine ⟨218297174909253430850273699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145531449939502287233515799 218297174909253430850273699)
    ·
      refine ⟨327445762363880146275410549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218297174909253430850273699 327445762363880146275410549)
      ·
        refine ⟨30698040221613763713319739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327445762363880146275410549 30698040221613763713319739)
        ·
          refine ⟨46047060332420645569979609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30698040221613763713319739 46047060332420645569979609)
          ·
            refine ⟨34535295249315484177484707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46047060332420645569979609 34535295249315484177484707)
            ·
              refine ⟨51802942873973226266227061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34535295249315484177484707 51802942873973226266227061)
              ·
                refine ⟨4856525894434989962458787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51802942873973226266227061 4856525894434989962458787)
                ·
                  refine ⟨7284788841652484943688181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856525894434989962458787 7284788841652484943688181)
                  ·
                    refine ⟨682948953904920463470767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7284788841652484943688181 682948953904920463470767)
                    ·
                      rfl

theorem cell23_3990115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 5].length) (baseStart_3990115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990115 prefixEnd_3990115 := by exact prefixLift 3990115
  have htrace : WordTrace (prefixWord ++ tailWord_3990115) baseStart_3990115 baseEnd_3990115 := by
    simpa [prefixWord, tailWord_3990115, baseEnd_3990115] using wordTrace_append hprefix tailTrace_3990115
  have hstable : (prefixWord ++ tailWord_3990115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990115).length < 2 ^ (prefixWord ++ tailWord_3990115).sum := by decide
  have hdescent : baseEnd_3990115 < baseStart_3990115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990138 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_3990138 : Nat := 118140960795 + 3990138 * 2 ^ 59
def prefixEnd_3990138 : Nat := 4983230072969 + 3 ^ 40 * 3990138 * 2
def baseEnd_3990138 : Nat := 2048858671769814800424695

theorem tailTrace_3990138 : CollatzResearch.WordTrace tailWord_3990138 prefixEnd_3990138 2048858671769814800424695 := by
  unfold tailWord_3990138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383072204604740540400767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97021525878945974774402045 36383072204604740540400767)
  ·
    refine ⟨54574608306907110810601151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36383072204604740540400767 54574608306907110810601151)
    ·
      refine ⟨81861912460360666215901727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54574608306907110810601151 81861912460360666215901727)
      ·
        refine ⟨122792868690540999323852591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81861912460360666215901727 122792868690540999323852591)
        ·
          refine ⟨184189303035811498985778887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122792868690540999323852591 184189303035811498985778887)
          ·
            refine ⟨276283954553717248478668331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184189303035811498985778887 276283954553717248478668331)
            ·
              refine ⟨414425931830575872718002497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276283954553717248478668331 414425931830575872718002497)
              ·
                refine ⟨310819448872931904538501873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414425931830575872718002497 310819448872931904538501873)
                ·
                  refine ⟨233114586654698928403876405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310819448872931904538501873 233114586654698928403876405)
                  ·
                    refine ⟨21854492498878024537863413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233114586654698928403876405 21854492498878024537863413)
                    ·
                      refine ⟨2048858671769814800424695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21854492498878024537863413 2048858671769814800424695)
                      ·
                        rfl

theorem cell23_3990138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_3990138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990138 prefixEnd_3990138 := by exact prefixLift 3990138
  have htrace : WordTrace (prefixWord ++ tailWord_3990138) baseStart_3990138 baseEnd_3990138 := by
    simpa [prefixWord, tailWord_3990138, baseEnd_3990138] using wordTrace_append hprefix tailTrace_3990138
  have hstable : (prefixWord ++ tailWord_3990138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990138).length < 2 ^ (prefixWord ++ tailWord_3990138).sum := by decide
  have hdescent : baseEnd_3990138 < baseStart_3990138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990145 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3990145 : Nat := 118140960795 + 3990145 * 2 ^ 59
def prefixEnd_3990145 : Nat := 4983230072969 + 3 ^ 40 * 3990145 * 2
def baseEnd_3990145 : Nat := 682954088711465424345721

theorem tailTrace_3990145 : CollatzResearch.WordTrace tailWord_3990145 prefixEnd_3990145 682954088711465424345721 := by
  unfold tailWord_3990145
  simp only [CollatzResearch.WordTrace]
  refine ⟨145532544129393602357107889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97021696086262401571405259 145532544129393602357107889)
  ·
    refine ⟨109149408097045201767830917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145532544129393602357107889 109149408097045201767830917)
    ·
      refine ⟨20465514018195975331468297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109149408097045201767830917 20465514018195975331468297)
      ·
        refine ⟨15349135513646981498601223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20465514018195975331468297 15349135513646981498601223)
        ·
          refine ⟨23023703270470472247901835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15349135513646981498601223 23023703270470472247901835)
          ·
            refine ⟨34535554905705708371852753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23023703270470472247901835 34535554905705708371852753)
            ·
              refine ⟨25901666179279281278889565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34535554905705708371852753 25901666179279281278889565)
              ·
                refine ⟨9713124817229730479583587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25901666179279281278889565 9713124817229730479583587)
                ·
                  refine ⟨14569687225844595719375381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713124817229730479583587 14569687225844595719375381)
                  ·
                    refine ⟨682954088711465424345721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14569687225844595719375381 682954088711465424345721)
                    ·
                      rfl

theorem cell23_3990145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3990145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990145 prefixEnd_3990145 := by exact prefixLift 3990145
  have htrace : WordTrace (prefixWord ++ tailWord_3990145) baseStart_3990145 baseEnd_3990145 := by
    simpa [prefixWord, tailWord_3990145, baseEnd_3990145] using wordTrace_append hprefix tailTrace_3990145
  have hstable : (prefixWord ++ tailWord_3990145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990145).length < 2 ^ (prefixWord ++ tailWord_3990145).sum := by decide
  have hdescent : baseEnd_3990145 < baseStart_3990145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990162 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3990162 : Nat := 118140960795 + 3990162 * 2 ^ 59
def prefixEnd_3990162 : Nat := 4983230072969 + 3 ^ 40 * 3990162 * 2
def baseEnd_3990162 : Nat := 682956998435174235508195

theorem tailTrace_3990162 : CollatzResearch.WordTrace tailWord_3990162 prefixEnd_3990162 682956998435174235508195 := by
  unfold tailWord_3990162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383291042583003565119185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97022109446888009506984493 36383291042583003565119185)
  ·
    refine ⟨27287468281937252673839389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36383291042583003565119185 27287468281937252673839389)
    ·
      refine ⟨10232800605726469752689771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27287468281937252673839389 10232800605726469752689771)
      ·
        refine ⟨15349200908589704629034657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232800605726469752689771 15349200908589704629034657)
        ·
          refine ⟨11511900681442278471775993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15349200908589704629034657 11511900681442278471775993)
          ·
            refine ⟨8633925511081708853831995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11511900681442278471775993 8633925511081708853831995)
            ·
              refine ⟨12950888266622563280747993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8633925511081708853831995 12950888266622563280747993)
              ·
                refine ⟨9713166199966922460560995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12950888266622563280747993 9713166199966922460560995)
                ·
                  refine ⟨14569749299950383690841493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713166199966922460560995 14569749299950383690841493)
                  ·
                    refine ⟨682956998435174235508195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14569749299950383690841493 682956998435174235508195)
                    ·
                      rfl

theorem cell23_3990162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3990162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990162 prefixEnd_3990162 := by exact prefixLift 3990162
  have htrace : WordTrace (prefixWord ++ tailWord_3990162) baseStart_3990162 baseEnd_3990162 := by
    simpa [prefixWord, tailWord_3990162, baseEnd_3990162] using wordTrace_append hprefix tailTrace_3990162
  have hstable : (prefixWord ++ tailWord_3990162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990162).length < 2 ^ (prefixWord ++ tailWord_3990162).sum := by decide
  have hdescent : baseEnd_3990162 < baseStart_3990162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990172 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3990172 : Nat := 118140960795 + 3990172 * 2 ^ 59
def prefixEnd_3990172 : Nat := 4983230072969 + 3 ^ 40 * 3990172 * 2
def baseEnd_3990172 : Nat := 2048876130112067667399539

theorem tailTrace_3990172 : CollatzResearch.WordTrace tailWord_3990172 prefixEnd_3990172 2048876130112067667399539 := by
  unfold tailWord_3990172
  simp only [CollatzResearch.WordTrace]
  refine ⟨72766764450147892984170385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97022352600197190645560513 72766764450147892984170385)
  ·
    refine ⟨54575073337610919738127789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72766764450147892984170385 54575073337610919738127789)
    ·
      refine ⟨20465652501604094901797921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54575073337610919738127789 20465652501604094901797921)
      ·
        refine ⟨15349239376203071176348441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20465652501604094901797921 15349239376203071176348441)
        ·
          refine ⟨11511929532152303382261331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15349239376203071176348441 11511929532152303382261331)
          ·
            refine ⟨17267894298228455073391997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511929532152303382261331 17267894298228455073391997)
            ·
              refine ⟨6475460361835670652521999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17267894298228455073391997 6475460361835670652521999)
              ·
                refine ⟨9713190542753505978782999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475460361835670652521999 9713190542753505978782999)
                ·
                  refine ⟨14569785814130258968174499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713190542753505978782999 14569785814130258968174499)
                  ·
                    refine ⟨21854678721195388452261749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14569785814130258968174499 21854678721195388452261749)
                    ·
                      refine ⟨2048876130112067667399539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21854678721195388452261749 2048876130112067667399539)
                      ·
                        rfl

theorem cell23_3990172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3990172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990172 prefixEnd_3990172 := by exact prefixLift 3990172
  have htrace : WordTrace (prefixWord ++ tailWord_3990172) baseStart_3990172 baseEnd_3990172 := by
    simpa [prefixWord, tailWord_3990172, baseEnd_3990172] using wordTrace_append hprefix tailTrace_3990172
  have hstable : (prefixWord ++ tailWord_3990172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990172).length < 2 ^ (prefixWord ++ tailWord_3990172).sum := by decide
  have hdescent : baseEnd_3990172 < baseStart_3990172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990202 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_3990202 : Nat := 118140960795 + 3990202 * 2 ^ 59
def prefixEnd_3990202 : Nat := 4983230072969 + 3 ^ 40 * 3990202 * 2
def baseEnd_3990202 : Nat := 2048891534531702550024401

theorem tailTrace_3990202 : CollatzResearch.WordTrace tailWord_3990202 prefixEnd_3990202 2048891534531702550024401 := by
  unfold tailWord_3990202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36383655772546775272983215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97023082060124734061288573 36383655772546775272983215)
  ·
    refine ⟨54575483658820162909474823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36383655772546775272983215 54575483658820162909474823)
    ·
      refine ⟨81863225488230244364212235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54575483658820162909474823 81863225488230244364212235)
      ·
        refine ⟨122794838232345366546318353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81863225488230244364212235 122794838232345366546318353)
        ·
          refine ⟨92096128674259024909738765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122794838232345366546318353 92096128674259024909738765)
          ·
            refine ⟨34536048252847134341152037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92096128674259024909738765 34536048252847134341152037)
            ·
              refine ⟨6475509047408837688966007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34536048252847134341152037 6475509047408837688966007)
              ·
                refine ⟨9713263571113256533449011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6475509047408837688966007 9713263571113256533449011)
                ·
                  refine ⟨14569895356669884800173517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9713263571113256533449011 14569895356669884800173517)
                  ·
                    refine ⟨5463710758751206800065069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14569895356669884800173517 5463710758751206800065069)
                    ·
                      refine ⟨2048891534531702550024401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463710758751206800065069 2048891534531702550024401)
                      ·
                        rfl

theorem cell23_3990202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_3990202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990202 prefixEnd_3990202 := by exact prefixLift 3990202
  have htrace : WordTrace (prefixWord ++ tailWord_3990202) baseStart_3990202 baseEnd_3990202 := by
    simpa [prefixWord, tailWord_3990202, baseEnd_3990202] using wordTrace_append hprefix tailTrace_3990202
  have hstable : (prefixWord ++ tailWord_3990202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990202).length < 2 ^ (prefixWord ++ tailWord_3990202).sum := by decide
  have hdescent : baseEnd_3990202 < baseStart_3990202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990236 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3990236 : Nat := 118140960795 + 3990236 * 2 ^ 59
def prefixEnd_3990236 : Nat := 4983230072969 + 3 ^ 40 * 3990236 * 2
def baseEnd_3990236 : Nat := 2048908992873955416999245

theorem tailTrace_3990236 : CollatzResearch.WordTrace tailWord_3990236 prefixEnd_3990236 2048908992873955416999245 := by
  unfold tailWord_3990236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72767931586031962449335281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97023908781375949932447041 72767931586031962449335281)
  ·
    refine ⟨54575948689523971837001461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72767931586031962449335281 54575948689523971837001461)
    ·
      refine ⟨5116495189642872359718887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54575948689523971837001461 5116495189642872359718887)
      ·
        refine ⟨7674742784464308539578331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116495189642872359718887 7674742784464308539578331)
        ·
          refine ⟨11512114176696462809367497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674742784464308539578331 11512114176696462809367497)
          ·
            refine ⟨8634085632522347107025623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512114176696462809367497 8634085632522347107025623)
            ·
              refine ⟨12951128448783520660538435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634085632522347107025623 12951128448783520660538435)
              ·
                refine ⟨19426692673175280990807653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951128448783520660538435 19426692673175280990807653)
                ·
                  refine ⟨3642504876220365185776435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19426692673175280990807653 3642504876220365185776435)
                  ·
                    refine ⟨5463757314330547778664653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3642504876220365185776435 5463757314330547778664653)
                    ·
                      refine ⟨2048908992873955416999245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5463757314330547778664653 2048908992873955416999245)
                      ·
                        rfl

theorem cell23_3990236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3990236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990236 prefixEnd_3990236 := by exact prefixLift 3990236
  have htrace : WordTrace (prefixWord ++ tailWord_3990236) baseStart_3990236 baseEnd_3990236 := by
    simpa [prefixWord, tailWord_3990236, baseEnd_3990236] using wordTrace_append hprefix tailTrace_3990236
  have hstable : (prefixWord ++ tailWord_3990236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990236).length < 2 ^ (prefixWord ++ tailWord_3990236).sum := by decide
  have hdescent : baseEnd_3990236 < baseStart_3990236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990262 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3990262 : Nat := 118140960795 + 3990262 * 2 ^ 59
def prefixEnd_3990262 : Nat := 4983230072969 + 3 ^ 40 * 3990262 * 2
def baseEnd_3990262 : Nat := 2048922343370972315274125

theorem tailTrace_3990262 : CollatzResearch.WordTrace tailWord_3990262 prefixEnd_3990262 2048922343370972315274125 := by
  unfold tailWord_3990262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096050716873108208694815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97024540979979820892744693 9096050716873108208694815)
  ·
    refine ⟨13644076075309662313042223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096050716873108208694815 13644076075309662313042223)
    ·
      refine ⟨20466114112964493469563335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644076075309662313042223 20466114112964493469563335)
      ·
        refine ⟨30699171169446740204345003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466114112964493469563335 30699171169446740204345003)
        ·
          refine ⟨46048756754170110306517505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30699171169446740204345003 46048756754170110306517505)
          ·
            refine ⟨34536567565627582729888129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46048756754170110306517505 34536567565627582729888129)
            ·
              refine ⟨25902425674220687047416097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34536567565627582729888129 25902425674220687047416097)
              ·
                refine ⟨19426819255665515285562073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25902425674220687047416097 19426819255665515285562073)
                ·
                  refine ⟨14570114441749136464171555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19426819255665515285562073 14570114441749136464171555)
                  ·
                    refine ⟨21855171662623704696257333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14570114441749136464171555 21855171662623704696257333)
                    ·
                      refine ⟨2048922343370972315274125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21855171662623704696257333 2048922343370972315274125)
                      ·
                        rfl

theorem cell23_3990262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3990262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990262 prefixEnd_3990262 := by exact prefixLift 3990262
  have htrace : WordTrace (prefixWord ++ tailWord_3990262) baseStart_3990262 baseEnd_3990262 := by
    simpa [prefixWord, tailWord_3990262, baseEnd_3990262] using wordTrace_append hprefix tailTrace_3990262
  have hstable : (prefixWord ++ tailWord_3990262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990262).length < 2 ^ (prefixWord ++ tailWord_3990262).sum := by decide
  have hdescent : baseEnd_3990262 < baseStart_3990262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990312 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3990312 : Nat := 118140960795 + 3990312 * 2 ^ 59
def prefixEnd_3990312 : Nat := 4983230072969 + 3 ^ 40 * 3990312 * 2
def baseEnd_3990312 : Nat := 682982672467899039882965

theorem tailTrace_3990312 : CollatzResearch.WordTrace tailWord_3990312 prefixEnd_3990312 682982672467899039882965 := by
  unfold tailWord_3990312
  simp only [CollatzResearch.WordTrace]
  refine ⟨72769317559894294939218595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97025756746525726585624793 72769317559894294939218595)
  ·
    refine ⟨109153976339841442408827893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72769317559894294939218595 109153976339841442408827893)
    ·
      refine ⟨10233185281860135225827615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109153976339841442408827893 10233185281860135225827615)
      ·
        refine ⟨15349777922790202838741423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10233185281860135225827615 15349777922790202838741423)
        ·
          refine ⟨23024666884185304258112135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15349777922790202838741423 23024666884185304258112135)
          ·
            refine ⟨34537000326277956387168203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23024666884185304258112135 34537000326277956387168203)
            ·
              refine ⟨51805500489416934580752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34537000326277956387168203 51805500489416934580752305)
              ·
                refine ⟨38854125367062700935564229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51805500489416934580752305 38854125367062700935564229)
                ·
                  refine ⟨7285148506324256425418293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38854125367062700935564229 7285148506324256425418293)
                  ·
                    refine ⟨682982672467899039882965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7285148506324256425418293 682982672467899039882965)
                    ·
                      rfl

theorem cell23_3990312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3990312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990312 prefixEnd_3990312 := by exact prefixLift 3990312
  have htrace : WordTrace (prefixWord ++ tailWord_3990312) baseStart_3990312 baseEnd_3990312 := by
    simpa [prefixWord, tailWord_3990312, baseEnd_3990312] using wordTrace_append hprefix tailTrace_3990312
  have hstable : (prefixWord ++ tailWord_3990312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990312).length < 2 ^ (prefixWord ++ tailWord_3990312).sum := by decide
  have hdescent : baseEnd_3990312 < baseStart_3990312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990355 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 8]
def baseStart_3990355 : Nat := 118140960795 + 3990355 * 2 ^ 59
def prefixEnd_3990355 : Nat := 4983230072969 + 3 ^ 40 * 3990355 * 2
def baseEnd_3990355 : Nat := 227663344119093383490133

theorem tailTrace_3990355 : CollatzResearch.WordTrace tailWord_3990355 prefixEnd_3990355 227663344119093383490133 := by
  unfold tailWord_3990355
  simp only [CollatzResearch.WordTrace]
  refine ⟨145540203458632808222252519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97026802305755205481501679 145540203458632808222252519)
  ·
    refine ⟨218310305187949212333378779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145540203458632808222252519 218310305187949212333378779)
    ·
      refine ⟨327465457781923818500068169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218310305187949212333378779 327465457781923818500068169)
      ·
        refine ⟨245599093336442863875051127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327465457781923818500068169 245599093336442863875051127)
        ·
          refine ⟨368398640004664295812576691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245599093336442863875051127 368398640004664295812576691)
          ·
            refine ⟨552597960006996443718865037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368398640004664295812576691 552597960006996443718865037)
            ·
              refine ⟨207224235002623666394574389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 552597960006996443718865037 207224235002623666394574389)
              ·
                refine ⟨19427272031495968724491349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207224235002623666394574389 19427272031495968724491349)
                ·
                  refine ⟨227663344119093383490133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19427272031495968724491349 227663344119093383490133)
                  ·
                    rfl

theorem cell23_3990355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 8].length) (baseStart_3990355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990355 prefixEnd_3990355 := by exact prefixLift 3990355
  have htrace : WordTrace (prefixWord ++ tailWord_3990355) baseStart_3990355 baseEnd_3990355 := by
    simpa [prefixWord, tailWord_3990355, baseEnd_3990355] using wordTrace_append hprefix tailTrace_3990355
  have hstable : (prefixWord ++ tailWord_3990355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990355).length < 2 ^ (prefixWord ++ tailWord_3990355).sum := by decide
  have hdescent : baseEnd_3990355 < baseStart_3990355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990486 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3990486 : Nat := 118140960795 + 3990486 * 2 ^ 59
def prefixEnd_3990486 : Nat := 4983230072969 + 3 ^ 40 * 3990486 * 2
def baseEnd_3990486 : Nat := 2049037363037579438873095

theorem tailTrace_3990486 : CollatzResearch.WordTrace tailWord_3990486 prefixEnd_3990486 2049037363037579438873095 := by
  unfold tailWord_3990486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096561338822388599704457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97029987614105478396847541 9096561338822388599704457)
  ·
    refine ⟨6822421004116791449778343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9096561338822388599704457 6822421004116791449778343)
    ·
      refine ⟨10233631506175187174667515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6822421004116791449778343 10233631506175187174667515)
      ·
        refine ⟨15350447259262780762001273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10233631506175187174667515 15350447259262780762001273)
        ·
          refine ⟨11512835444447085571500955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15350447259262780762001273 11512835444447085571500955)
          ·
            refine ⟨17269253166670628357251433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512835444447085571500955 17269253166670628357251433)
            ·
              refine ⟨12951939875002971267938575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17269253166670628357251433 12951939875002971267938575)
              ·
                refine ⟨19427909812504456901907863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12951939875002971267938575 19427909812504456901907863)
                ·
                  refine ⟨29141864718756685352861795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19427909812504456901907863 29141864718756685352861795)
                  ·
                    refine ⟨43712797078135028029292693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29141864718756685352861795 43712797078135028029292693)
                    ·
                      refine ⟨2049037363037579438873095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43712797078135028029292693 2049037363037579438873095)
                      ·
                        rfl

theorem cell23_3990486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3990486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990486 prefixEnd_3990486 := by exact prefixLift 3990486
  have htrace : WordTrace (prefixWord ++ tailWord_3990486) baseStart_3990486 baseEnd_3990486 := by
    simpa [prefixWord, tailWord_3990486, baseEnd_3990486] using wordTrace_append hprefix tailTrace_3990486
  have hstable : (prefixWord ++ tailWord_3990486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990486).length < 2 ^ (prefixWord ++ tailWord_3990486).sum := by decide
  have hdescent : baseEnd_3990486 < baseStart_3990486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990493 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3990493 : Nat := 118140960795 + 3990493 * 2 ^ 59
def prefixEnd_3990493 : Nat := 4983230072969 + 3 ^ 40 * 3990493 * 2
def baseEnd_3990493 : Nat := 2049040957402160911485563

theorem tailTrace_3990493 : CollatzResearch.WordTrace tailWord_3990493 prefixEnd_3990493 2049040957402160911485563 := by
  unfold tailWord_3990493
  simp only [CollatzResearch.WordTrace]
  refine ⟨145545236732132857790776133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97030157821421905193850755 145545236732132857790776133)
  ·
    refine ⟨27289731887274910835770525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145545236732132857790776133 27289731887274910835770525)
    ·
      refine ⟨10233649457728091563413947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27289731887274910835770525 10233649457728091563413947)
      ·
        refine ⟨15350474186592137345120921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10233649457728091563413947 15350474186592137345120921)
        ·
          refine ⟨11512855639944103008840691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15350474186592137345120921 11512855639944103008840691)
          ·
            refine ⟨17269283459916154513261037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512855639944103008840691 17269283459916154513261037)
            ·
              refine ⟨6475981297468557942472889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17269283459916154513261037 6475981297468557942472889)
              ·
                refine ⟨4856985973101418456854667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475981297468557942472889 4856985973101418456854667)
                ·
                  refine ⟨7285478959652127685282001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4856985973101418456854667 7285478959652127685282001)
                  ·
                    refine ⟨5464109219739095763961501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7285478959652127685282001 5464109219739095763961501)
                    ·
                      refine ⟨2049040957402160911485563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464109219739095763961501 2049040957402160911485563)
                      ·
                        rfl

theorem cell23_3990493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3990493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990493 prefixEnd_3990493 := by exact prefixLift 3990493
  have htrace : WordTrace (prefixWord ++ tailWord_3990493) baseStart_3990493 baseEnd_3990493 := by
    simpa [prefixWord, tailWord_3990493, baseEnd_3990493] using wordTrace_append hprefix tailTrace_3990493
  have hstable : (prefixWord ++ tailWord_3990493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990493).length < 2 ^ (prefixWord ++ tailWord_3990493).sum := by decide
  have hdescent : baseEnd_3990493 < baseStart_3990493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990506 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_3990506 : Nat := 118140960795 + 3990506 * 2 ^ 59
def prefixEnd_3990506 : Nat := 4983230072969 + 3 ^ 40 * 3990506 * 2
def baseEnd_3990506 : Nat := 2049047632650669360623003

theorem tailTrace_3990506 : CollatzResearch.WordTrace tailWord_3990506 prefixEnd_3990506 2049047632650669360623003 := by
  unfold tailWord_3990506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386427720271440252749843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97030473920723840673999581 36386427720271440252749843)
  ·
    refine ⟨54579641580407160379124765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386427720271440252749843 54579641580407160379124765)
    ·
      refine ⟨20467365592652685142171787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54579641580407160379124765 20467365592652685142171787)
      ·
        refine ⟨30701048388979027713257681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20467365592652685142171787 30701048388979027713257681)
        ·
          refine ⟨23025786291734270784943261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30701048388979027713257681 23025786291734270784943261)
          ·
            refine ⟨8634669859400351544353723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23025786291734270784943261 8634669859400351544353723)
            ·
              refine ⟨12952004789100527316530585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634669859400351544353723 12952004789100527316530585)
              ·
                refine ⟨9714003591825395487397939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952004789100527316530585 9714003591825395487397939)
                ·
                  refine ⟨14571005387738093231096909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714003591825395487397939 14571005387738093231096909)
                  ·
                    refine ⟨5464127020401784961661341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14571005387738093231096909 5464127020401784961661341)
                    ·
                      refine ⟨2049047632650669360623003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464127020401784961661341 2049047632650669360623003)
                      ·
                        rfl

theorem cell23_3990506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_3990506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990506 prefixEnd_3990506 := by exact prefixLift 3990506
  have htrace : WordTrace (prefixWord ++ tailWord_3990506) baseStart_3990506 baseEnd_3990506 := by
    simpa [prefixWord, tailWord_3990506, baseEnd_3990506] using wordTrace_append hprefix tailTrace_3990506
  have hstable : (prefixWord ++ tailWord_3990506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990506).length < 2 ^ (prefixWord ++ tailWord_3990506).sum := by decide
  have hdescent : baseEnd_3990506 < baseStart_3990506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990510 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_3990510 : Nat := 118140960795 + 3990510 * 2 ^ 59
def prefixEnd_3990510 : Nat := 4983230072969 + 3 ^ 40 * 3990510 * 2
def baseEnd_3990510 : Nat := 2049049686573287344972985

theorem tailTrace_3990510 : CollatzResearch.WordTrace tailWord_3990510 prefixEnd_3990510 2049049686573287344972985 := by
  unfold tailWord_3990510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193232096633908711768123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97030571182047513129429989 18193232096633908711768123)
  ·
    refine ⟨27289848144950863067652185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18193232096633908711768123 27289848144950863067652185)
    ·
      refine ⟨20467386108713147300739139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27289848144950863067652185 20467386108713147300739139)
      ·
        refine ⟨30701079163069720951108709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20467386108713147300739139 30701079163069720951108709)
        ·
          refine ⟨5756452343075572678332883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30701079163069720951108709 5756452343075572678332883)
          ·
            refine ⟨8634678514613359017499325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756452343075572678332883 8634678514613359017499325)
            ·
              refine ⟨3238004442980009631562247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8634678514613359017499325 3238004442980009631562247)
              ·
                refine ⟨4857006664470014447343371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238004442980009631562247 4857006664470014447343371)
                ·
                  refine ⟨7285509996705021671015057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857006664470014447343371 7285509996705021671015057)
                  ·
                    refine ⟨5464132497528766253261293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7285509996705021671015057 5464132497528766253261293)
                    ·
                      refine ⟨2049049686573287344972985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464132497528766253261293 2049049686573287344972985)
                      ·
                        rfl

theorem cell23_3990510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_3990510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990510 prefixEnd_3990510 := by exact prefixLift 3990510
  have htrace : WordTrace (prefixWord ++ tailWord_3990510) baseStart_3990510 baseEnd_3990510 := by
    simpa [prefixWord, tailWord_3990510, baseEnd_3990510] using wordTrace_append hprefix tailTrace_3990510
  have hstable : (prefixWord ++ tailWord_3990510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990510).length < 2 ^ (prefixWord ++ tailWord_3990510).sum := by decide
  have hdescent : baseEnd_3990510 < baseStart_3990510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990522 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_3990522 : Nat := 118140960795 + 3990522 * 2 ^ 59
def prefixEnd_3990522 : Nat := 4983230072969 + 3 ^ 40 * 3990522 * 2
def baseEnd_3990522 : Nat := 683018616113713766007643

theorem tailTrace_3990522 : CollatzResearch.WordTrace tailWord_3990522 prefixEnd_3990522 683018616113713766007643 := by
  unfold tailWord_3990522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386573612256948935895455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97030862966018530495721213 36386573612256948935895455)
  ·
    refine ⟨54579860418385423403843183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36386573612256948935895455 54579860418385423403843183)
    ·
      refine ⟨81869790627578135105764775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54579860418385423403843183 81869790627578135105764775)
      ·
        refine ⟨122804685941367202658647163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81869790627578135105764775 122804685941367202658647163)
        ·
          refine ⟨184207028912050803987970745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122804685941367202658647163 184207028912050803987970745)
          ·
            refine ⟨138155271684038102990978059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184207028912050803987970745 138155271684038102990978059)
            ·
              refine ⟨207232907526057154486467089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138155271684038102990978059 207232907526057154486467089)
              ·
                refine ⟨155424680644542865864850317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207232907526057154486467089 155424680644542865864850317)
                ·
                  refine ⟨58284255241703574699318869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155424680644542865864850317 58284255241703574699318869)
                  ·
                    refine ⟨683018616113713766007643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58284255241703574699318869 683018616113713766007643)
                    ·
                      rfl

theorem cell23_3990522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_3990522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990522 prefixEnd_3990522 := by exact prefixLift 3990522
  have htrace : WordTrace (prefixWord ++ tailWord_3990522) baseStart_3990522 baseEnd_3990522 := by
    simpa [prefixWord, tailWord_3990522, baseEnd_3990522] using wordTrace_append hprefix tailTrace_3990522
  have hstable : (prefixWord ++ tailWord_3990522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990522).length < 2 ^ (prefixWord ++ tailWord_3990522).sum := by decide
  have hdescent : baseEnd_3990522 < baseStart_3990522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990529 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3990529 : Nat := 118140960795 + 3990529 * 2 ^ 59
def prefixEnd_3990529 : Nat := 4983230072969 + 3 ^ 40 * 3990529 * 2
def baseEnd_3990529 : Nat := 2049059442705722770635397

theorem tailTrace_3990529 : CollatzResearch.WordTrace tailWord_3990529 prefixEnd_3990529 2049059442705722770635397 := by
  unfold tailWord_3990529
  simp only [CollatzResearch.WordTrace]
  refine ⟨145546549760002435939086641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97031033173334957292724427 145546549760002435939086641)
  ·
    refine ⟨109159912320001826954314981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145546549760002435939086641 109159912320001826954314981)
    ·
      refine ⟨20467483560000342553934059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109159912320001826954314981 20467483560000342553934059)
      ·
        refine ⟨30701225340000513830901089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20467483560000342553934059 30701225340000513830901089)
        ·
          refine ⟨23025919005000385373175817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30701225340000513830901089 23025919005000385373175817)
          ·
            refine ⟨17269439253750289029881863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23025919005000385373175817 17269439253750289029881863)
            ·
              refine ⟨25904158880625433544822795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17269439253750289029881863 25904158880625433544822795)
              ·
                refine ⟨38856238320938150317234193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25904158880625433544822795 38856238320938150317234193)
                ·
                  refine ⟨29142178740703612737925645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38856238320938150317234193 29142178740703612737925645)
                  ·
                    refine ⟨10928317027763854776722117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29142178740703612737925645 10928317027763854776722117)
                    ·
                      refine ⟨2049059442705722770635397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10928317027763854776722117 2049059442705722770635397)
                      ·
                        rfl

theorem cell23_3990529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3990529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990529 prefixEnd_3990529 := by exact prefixLift 3990529
  have htrace : WordTrace (prefixWord ++ tailWord_3990529) baseStart_3990529 baseEnd_3990529 := by
    simpa [prefixWord, tailWord_3990529, baseEnd_3990529] using wordTrace_append hprefix tailTrace_3990529
  have hstable : (prefixWord ++ tailWord_3990529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990529).length < 2 ^ (prefixWord ++ tailWord_3990529).sum := by decide
  have hdescent : baseEnd_3990529 < baseStart_3990529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990530 : List Nat := [3, 4, 1, 3, 2, 1, 1, 8]
def baseStart_3990530 : Nat := 118140960795 + 3990530 * 2 ^ 59
def prefixEnd_3990530 : Nat := 4983230072969 + 3 ^ 40 * 3990530 * 2
def baseEnd_3990530 : Nat := 75891109488384343211959

theorem tailTrace_3990530 : CollatzResearch.WordTrace tailWord_3990530 prefixEnd_3990530 75891109488384343211959 := by
  unfold tailWord_3990530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36386646558249703277468261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97031057488665875406582029 36386646558249703277468261)
  ·
    refine ⟨6822496229671819364525299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36386646558249703277468261 6822496229671819364525299)
    ·
      refine ⟨10233744344507729046787949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6822496229671819364525299 10233744344507729046787949)
      ·
        refine ⟨3837654129190398392545481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10233744344507729046787949 3837654129190398392545481)
        ·
          refine ⟨2878240596892798794409111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837654129190398392545481 2878240596892798794409111)
          ·
            refine ⟨4317360895339198191613667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878240596892798794409111 4317360895339198191613667)
            ·
              refine ⟨6476041343008797287420501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317360895339198191613667 6476041343008797287420501)
              ·
                refine ⟨75891109488384343211959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6476041343008797287420501 75891109488384343211959)
                ·
                  rfl

theorem cell23_3990530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_3990530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990530 prefixEnd_3990530 := by exact prefixLift 3990530
  have htrace : WordTrace (prefixWord ++ tailWord_3990530) baseStart_3990530 baseEnd_3990530 := by
    simpa [prefixWord, tailWord_3990530, baseEnd_3990530] using wordTrace_append hprefix tailTrace_3990530
  have hstable : (prefixWord ++ tailWord_3990530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990530).length < 2 ^ (prefixWord ++ tailWord_3990530).sum := by decide
  have hdescent : baseEnd_3990530 < baseStart_3990530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990539 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 6]
def baseStart_3990539 : Nat := 118140960795 + 3990539 * 2 ^ 59
def prefixEnd_3990539 : Nat := 4983230072969 + 3 ^ 40 * 3990539 * 2
def baseEnd_3990539 : Nat := 683021525837422577170117

theorem tailTrace_3990539 : CollatzResearch.WordTrace tailWord_3990539 prefixEnd_3990539 683021525837422577170117 := by
  unfold tailWord_3990539
  simp only [CollatzResearch.WordTrace]
  refine ⟨145546914489966207646950671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97031276326644138431300447 145546914489966207646950671)
  ·
    refine ⟨218320371734949311470426007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145546914489966207646950671 218320371734949311470426007)
    ·
      refine ⟨327480557602423967205639011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218320371734949311470426007 327480557602423967205639011)
      ·
        refine ⟨491220836403635950808458517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327480557602423967205639011 491220836403635950808458517)
        ·
          refine ⟨23025976706420435194146493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 491220836403635950808458517 23025976706420435194146493)
          ·
            refine ⟨8634741264907663197804935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23025976706420435194146493 8634741264907663197804935)
            ·
              refine ⟨12952111897361494796707403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8634741264907663197804935 12952111897361494796707403)
              ·
                refine ⟨19428167846042242195061105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952111897361494796707403 19428167846042242195061105)
                ·
                  refine ⟨14571125884531681646295829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19428167846042242195061105 14571125884531681646295829)
                  ·
                    refine ⟨683021525837422577170117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14571125884531681646295829 683021525837422577170117)
                    ·
                      rfl

theorem cell23_3990539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_3990539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990539 prefixEnd_3990539 := by exact prefixLift 3990539
  have htrace : WordTrace (prefixWord ++ tailWord_3990539) baseStart_3990539 baseEnd_3990539 := by
    simpa [prefixWord, tailWord_3990539, baseEnd_3990539] using wordTrace_append hprefix tailTrace_3990539
  have hstable : (prefixWord ++ tailWord_3990539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990539).length < 2 ^ (prefixWord ++ tailWord_3990539).sum := by decide
  have hdescent : baseEnd_3990539 < baseStart_3990539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990567 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3990567 : Nat := 118140960795 + 3990567 * 2 ^ 59
def prefixEnd_3990567 : Nat := 4983230072969 + 3 ^ 40 * 3990567 * 2
def baseEnd_3990567 : Nat := 2049078954970593621960223

theorem tailTrace_3990567 : CollatzResearch.WordTrace tailWord_3990567 prefixEnd_3990567 2049078954970593621960223 := by
  unfold tailWord_3990567
  simp only [CollatzResearch.WordTrace]
  refine ⟨145547935733864768428969955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97031957155909845619313303 145547935733864768428969955)
  ·
    refine ⟨218321903600797152643454933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145547935733864768428969955 218321903600797152643454933)
    ·
      refine ⟨5116919615643683265080975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218321903600797152643454933 5116919615643683265080975)
      ·
        refine ⟨7675379423465524897621463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116919615643683265080975 7675379423465524897621463)
        ·
          refine ⟨11513069135198287346432195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7675379423465524897621463 11513069135198287346432195)
          ·
            refine ⟨17269603702797431019648293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513069135198287346432195 17269603702797431019648293)
            ·
              refine ⟨3238050694274518316184055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17269603702797431019648293 3238050694274518316184055)
              ·
                refine ⟨4857076041411777474276083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238050694274518316184055 4857076041411777474276083)
                ·
                  refine ⟨7285614062117666211414125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857076041411777474276083 7285614062117666211414125)
                  ·
                    refine ⟨2732105273294124829280297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7285614062117666211414125 2732105273294124829280297)
                    ·
                      refine ⟨2049078954970593621960223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732105273294124829280297 2049078954970593621960223)
                      ·
                        rfl

theorem cell23_3990567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3990567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990567 prefixEnd_3990567 := by exact prefixLift 3990567
  have htrace : WordTrace (prefixWord ++ tailWord_3990567) baseStart_3990567 baseEnd_3990567 := by
    simpa [prefixWord, tailWord_3990567, baseEnd_3990567] using wordTrace_append hprefix tailTrace_3990567
  have hstable : (prefixWord ++ tailWord_3990567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990567).length < 2 ^ (prefixWord ++ tailWord_3990567).sum := by decide
  have hdescent : baseEnd_3990567 < baseStart_3990567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990586 : List Nat := [3, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_3990586 : Nat := 118140960795 + 3990586 * 2 ^ 59
def prefixEnd_3990586 : Nat := 4983230072969 + 3 ^ 40 * 3990586 * 2
def baseEnd_3990586 : Nat := 227676523455892116402515

theorem tailTrace_3990586 : CollatzResearch.WordTrace tailWord_3990586 prefixEnd_3990586 227676523455892116402515 := by
  unfold tailWord_3990586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36387157180198983668477903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97032419147197289782607741 36387157180198983668477903)
  ·
    refine ⟨54580735770298475502716855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36387157180198983668477903 54580735770298475502716855)
    ·
      refine ⟨81871103655447713254075283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54580735770298475502716855 81871103655447713254075283)
      ·
        refine ⟨122806655483171569881112925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81871103655447713254075283 122806655483171569881112925)
        ·
          refine ⟨46052495806189338705417347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122806655483171569881112925 46052495806189338705417347)
          ·
            refine ⟨69078743709284008058126021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46052495806189338705417347 69078743709284008058126021)
            ·
              refine ⟨12952264445490751510898629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69078743709284008058126021 12952264445490751510898629)
              ·
                refine ⟨2428549583529515908293493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12952264445490751510898629 2428549583529515908293493)
                ·
                  refine ⟨227676523455892116402515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2428549583529515908293493 227676523455892116402515)
                  ·
                    rfl

theorem cell23_3990586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_3990586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990586 prefixEnd_3990586 := by exact prefixLift 3990586
  have htrace : WordTrace (prefixWord ++ tailWord_3990586) baseStart_3990586 baseEnd_3990586 := by
    simpa [prefixWord, tailWord_3990586, baseEnd_3990586] using wordTrace_append hprefix tailTrace_3990586
  have hstable : (prefixWord ++ tailWord_3990586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990586).length < 2 ^ (prefixWord ++ tailWord_3990586).sum := by decide
  have hdescent : baseEnd_3990586 < baseStart_3990586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990599 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 7]
def baseStart_3990599 : Nat := 118140960795 + 3990599 * 2 ^ 59
def prefixEnd_3990599 : Nat := 4983230072969 + 3 ^ 40 * 3990599 * 2
def baseEnd_3990599 : Nat := 683031795450512498920025

theorem tailTrace_3990599 : CollatzResearch.WordTrace tailWord_3990599 prefixEnd_3990599 683031795450512498920025 := by
  unfold tailWord_3990599
  simp only [CollatzResearch.WordTrace]
  refine ⟨145549102869748837894134851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97032735246499225262756567 145549102869748837894134851)
  ·
    refine ⟨218323654304623256841202277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145549102869748837894134851 218323654304623256841202277)
    ·
      refine ⟨40935685182116860657725427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218323654304623256841202277 40935685182116860657725427)
      ·
        refine ⟨61403527773175290986588141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40935685182116860657725427 61403527773175290986588141)
        ·
          refine ⟨23026322914940734119970553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61403527773175290986588141 23026322914940734119970553)
          ·
            refine ⟨17269742186205550589977915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23026322914940734119970553 17269742186205550589977915)
            ·
              refine ⟨25904613279308325884966873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17269742186205550589977915 25904613279308325884966873)
              ·
                refine ⟨19428459959481244413725155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25904613279308325884966873 19428459959481244413725155)
                ·
                  refine ⟨29142689939221866620587733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19428459959481244413725155 29142689939221866620587733)
                  ·
                    refine ⟨683031795450512498920025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29142689939221866620587733 683031795450512498920025)
                    ·
                      rfl

theorem cell23_3990599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_3990599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990599 prefixEnd_3990599 := by exact prefixLift 3990599
  have htrace : WordTrace (prefixWord ++ tailWord_3990599) baseStart_3990599 baseEnd_3990599 := by
    simpa [prefixWord, tailWord_3990599, baseEnd_3990599] using wordTrace_append hprefix tailTrace_3990599
  have hstable : (prefixWord ++ tailWord_3990599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990599).length < 2 ^ (prefixWord ++ tailWord_3990599).sum := by decide
  have hdescent : baseEnd_3990599 < baseStart_3990599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990636 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_3990636 : Nat := 118140960795 + 3990636 * 2 ^ 59
def prefixEnd_3990636 : Nat := 4983230072969 + 3 ^ 40 * 3990636 * 2
def baseEnd_3990636 : Nat := 2049114385135753851997405

theorem tailTrace_3990636 : CollatzResearch.WordTrace tailWord_3990636 prefixEnd_3990636 2049114385135753851997405 := by
  unfold tailWord_3990636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72775226185307396606615881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97033634913743195475487841 72775226185307396606615881)
  ·
    refine ⟨54581419638980547454961911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72775226185307396606615881 54581419638980547454961911)
    ·
      refine ⟨81872129458470821182442867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54581419638980547454961911 81872129458470821182442867)
      ·
        refine ⟨122808194187706231773664301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81872129458470821182442867 122808194187706231773664301)
        ·
          refine ⟨46053072820389836915124113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122808194187706231773664301 46053072820389836915124113)
          ·
            refine ⟨34539804615292377686343085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46053072820389836915124113 34539804615292377686343085)
            ·
              refine ⟨12952426730734641632378657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34539804615292377686343085 12952426730734641632378657)
              ·
                refine ⟨9714320048050981224283993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952426730734641632378657 9714320048050981224283993)
                ·
                  refine ⟨7285740036038235918212995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714320048050981224283993 7285740036038235918212995)
                  ·
                    refine ⟨10928610054057353877319493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7285740036038235918212995 10928610054057353877319493)
                    ·
                      refine ⟨2049114385135753851997405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10928610054057353877319493 2049114385135753851997405)
                      ·
                        rfl

theorem cell23_3990636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_3990636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990636 prefixEnd_3990636 := by exact prefixLift 3990636
  have htrace : WordTrace (prefixWord ++ tailWord_3990636) baseStart_3990636 baseEnd_3990636 := by
    simpa [prefixWord, tailWord_3990636, baseEnd_3990636] using wordTrace_append hprefix tailTrace_3990636
  have hstable : (prefixWord ++ tailWord_3990636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990636).length < 2 ^ (prefixWord ++ tailWord_3990636).sum := by decide
  have hdescent : baseEnd_3990636 < baseStart_3990636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990706 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3990706 : Nat := 118140960795 + 3990706 * 2 ^ 59
def prefixEnd_3990706 : Nat := 4983230072969 + 3 ^ 40 * 3990706 * 2
def baseEnd_3990706 : Nat := 683050109593856192707361

theorem tailTrace_3990706 : CollatzResearch.WordTrace tailWord_3990706 prefixEnd_3990706 683050109593856192707361 := by
  unfold tailWord_3990706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388251370090298792069993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97035336986907463445519981 36388251370090298792069993)
  ·
    refine ⟨27291188527567724094052495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36388251370090298792069993 27291188527567724094052495)
    ·
      refine ⟨40936782791351586141078743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27291188527567724094052495 40936782791351586141078743)
      ·
        refine ⟨61405174187027379211618115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40936782791351586141078743 61405174187027379211618115)
        ·
          refine ⟨92107761280541068817427173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61405174187027379211618115 92107761280541068817427173)
          ·
            refine ⟨17270205240101450403267595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92107761280541068817427173 17270205240101450403267595)
            ·
              refine ⟨25905307860152175604901393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17270205240101450403267595 25905307860152175604901393)
              ·
                refine ⟨19428980895114131703676045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25905307860152175604901393 19428980895114131703676045)
                ·
                  refine ⟨7285867835667799388878517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19428980895114131703676045 7285867835667799388878517)
                  ·
                    refine ⟨683050109593856192707361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7285867835667799388878517 683050109593856192707361)
                    ·
                      rfl

theorem cell23_3990706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3990706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990706 prefixEnd_3990706 := by exact prefixLift 3990706
  have htrace : WordTrace (prefixWord ++ tailWord_3990706) baseStart_3990706 baseEnd_3990706 := by
    simpa [prefixWord, tailWord_3990706, baseEnd_3990706] using wordTrace_append hprefix tailTrace_3990706
  have hstable : (prefixWord ++ tailWord_3990706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990706).length < 2 ^ (prefixWord ++ tailWord_3990706).sum := by decide
  have hdescent : baseEnd_3990706 < baseStart_3990706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990720 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_3990720 : Nat := 118140960795 + 3990720 * 2 ^ 59
def prefixEnd_3990720 : Nat := 4983230072969 + 3 ^ 40 * 3990720 * 2
def baseEnd_3990720 : Nat := 2049157517510731523347019

theorem tailTrace_3990720 : CollatzResearch.WordTrace tailWord_3990720 prefixEnd_3990720 2049157517510731523347019 := by
  unfold tailWord_3990720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72776758051155237779644807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97035677401540317039526409 72776758051155237779644807)
  ·
    refine ⟨109165137076732856669467211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72776758051155237779644807 109165137076732856669467211)
    ·
      refine ⟨163747705615099285004200817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109165137076732856669467211 163747705615099285004200817)
      ·
        refine ⟨122810779211324463753150613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163747705615099285004200817 122810779211324463753150613)
        ·
          refine ⟨5756755275530834238428935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122810779211324463753150613 5756755275530834238428935)
          ·
            refine ⟨8635132913296251357643403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756755275530834238428935 8635132913296251357643403)
            ·
              refine ⟨12952699369944377036465105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635132913296251357643403 12952699369944377036465105)
              ·
                refine ⟨9714524527458282777348829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12952699369944377036465105 9714524527458282777348829)
                ·
                  refine ⟨3642946697796856041505811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9714524527458282777348829 3642946697796856041505811)
                  ·
                    refine ⟨5464420046695284062258717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3642946697796856041505811 5464420046695284062258717)
                    ·
                      refine ⟨2049157517510731523347019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464420046695284062258717 2049157517510731523347019)
                      ·
                        rfl

theorem cell23_3990720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_3990720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990720 prefixEnd_3990720 := by exact prefixLift 3990720
  have htrace : WordTrace (prefixWord ++ tailWord_3990720) baseStart_3990720 baseEnd_3990720 := by
    simpa [prefixWord, tailWord_3990720, baseEnd_3990720] using wordTrace_append hprefix tailTrace_3990720
  have hstable : (prefixWord ++ tailWord_3990720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990720).length < 2 ^ (prefixWord ++ tailWord_3990720).sum := by decide
  have hdescent : baseEnd_3990720 < baseStart_3990720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990730 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_3990730 : Nat := 118140960795 + 3990730 * 2 ^ 59
def prefixEnd_3990730 : Nat := 4983230072969 + 3 ^ 40 * 3990730 * 2
def baseEnd_3990730 : Nat := 2049162652317276484221973

theorem tailTrace_3990730 : CollatzResearch.WordTrace tailWord_3990730 prefixEnd_3990730 2049162652317276484221973 := by
  unfold tailWord_3990730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388470208068561816788411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97035920554849498178102429 36388470208068561816788411)
  ·
    refine ⟨54582705312102842725182617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36388470208068561816788411 54582705312102842725182617)
    ·
      refine ⟨40937028984077132043886963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54582705312102842725182617 40937028984077132043886963)
      ·
        refine ⟨61405543476115698065830445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40937028984077132043886963 61405543476115698065830445)
        ·
          refine ⟨23027078803543386774686417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61405543476115698065830445 23027078803543386774686417)
          ·
            refine ⟨17270309102657540081014813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23027078803543386774686417 17270309102657540081014813)
            ·
              refine ⟨6476365913496577530380555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17270309102657540081014813 6476365913496577530380555)
              ·
                refine ⟨9714548870244866295570833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476365913496577530380555 9714548870244866295570833)
                ·
                  refine ⟨7285911652683649721678125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9714548870244866295570833 7285911652683649721678125)
                  ·
                    refine ⟨2732216869756368645629297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7285911652683649721678125 2732216869756368645629297)
                    ·
                      refine ⟨2049162652317276484221973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732216869756368645629297 2049162652317276484221973)
                      ·
                        rfl

theorem cell23_3990730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_3990730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990730 prefixEnd_3990730 := by exact prefixLift 3990730
  have htrace : WordTrace (prefixWord ++ tailWord_3990730) baseStart_3990730 baseEnd_3990730 := by
    simpa [prefixWord, tailWord_3990730, baseEnd_3990730] using wordTrace_append hprefix tailTrace_3990730
  have hstable : (prefixWord ++ tailWord_3990730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990730).length < 2 ^ (prefixWord ++ tailWord_3990730).sum := by decide
  have hdescent : baseEnd_3990730 < baseStart_3990730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990746 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_3990746 : Nat := 118140960795 + 3990746 * 2 ^ 59
def prefixEnd_3990746 : Nat := 4983230072969 + 3 ^ 40 * 3990746 * 2
def baseEnd_3990746 : Nat := 2049170868007748421621899

theorem tailTrace_3990746 : CollatzResearch.WordTrace tailWord_3990746 prefixEnd_3990746 2049170868007748421621899 := by
  unfold tailWord_3990746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388616100054070499934023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97036309600144187999824061 36388616100054070499934023)
  ·
    refine ⟨54582924150081105749901035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36388616100054070499934023 54582924150081105749901035)
    ·
      refine ⟨81874386225121658624851553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54582924150081105749901035 81874386225121658624851553)
      ·
        refine ⟨61405789668841243968638665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81874386225121658624851553 61405789668841243968638665)
        ·
          refine ⟨46054342251630932976478999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61405789668841243968638665 46054342251630932976478999)
          ·
            refine ⟨69081513377446399464718499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46054342251630932976478999 69081513377446399464718499)
            ·
              refine ⟨103622270066169599197077749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69081513377446399464718499 103622270066169599197077749)
              ·
                refine ⟨9714587818703399924726039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103622270066169599197077749 9714587818703399924726039)
                ·
                  refine ⟨14571881728055099887089059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714587818703399924726039 14571881728055099887089059)
                  ·
                    refine ⟨21857822592082649830633589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14571881728055099887089059 21857822592082649830633589)
                    ·
                      refine ⟨2049170868007748421621899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21857822592082649830633589 2049170868007748421621899)
                      ·
                        rfl

theorem cell23_3990746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3990746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990746 prefixEnd_3990746 := by exact prefixLift 3990746
  have htrace : WordTrace (prefixWord ++ tailWord_3990746) baseStart_3990746 baseEnd_3990746 := by
    simpa [prefixWord, tailWord_3990746, baseEnd_3990746] using wordTrace_append hprefix tailTrace_3990746
  have hstable : (prefixWord ++ tailWord_3990746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990746).length < 2 ^ (prefixWord ++ tailWord_3990746).sum := by decide
  have hdescent : baseEnd_3990746 < baseStart_3990746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990753 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3990753 : Nat := 118140960795 + 3990753 * 2 ^ 59
def prefixEnd_3990753 : Nat := 4983230072969 + 3 ^ 40 * 3990753 * 2
def baseEnd_3990753 : Nat := 683058154124109964744789

theorem tailTrace_3990753 : CollatzResearch.WordTrace tailWord_3990753 prefixEnd_3990753 683058154124109964744789 := by
  unfold tailWord_3990753
  simp only [CollatzResearch.WordTrace]
  refine ⟨145554719711190922195240913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97036479807460614796827275 145554719711190922195240913)
  ·
    refine ⟨109166039783393191646430685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145554719711190922195240913 109166039783393191646430685)
    ·
      refine ⟨40937264918772446867411507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109166039783393191646430685 40937264918772446867411507)
      ·
        refine ⟨61405897378158670301117261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40937264918772446867411507 61405897378158670301117261)
        ·
          refine ⟨23027211516809501362918973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61405897378158670301117261 23027211516809501362918973)
          ·
            refine ⟨8635204318803563011094615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23027211516809501362918973 8635204318803563011094615)
            ·
              refine ⟨12952806478205344516641923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635204318803563011094615 12952806478205344516641923)
              ·
                refine ⟨19429209717308016774962885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952806478205344516641923 19429209717308016774962885)
                ·
                  refine ⟨3642976821995253145305541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19429209717308016774962885 3642976821995253145305541)
                  ·
                    refine ⟨683058154124109964744789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3642976821995253145305541 683058154124109964744789)
                    ·
                      rfl

theorem cell23_3990753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3990753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990753 prefixEnd_3990753 := by exact prefixLift 3990753
  have htrace : WordTrace (prefixWord ++ tailWord_3990753) baseStart_3990753 baseEnd_3990753 := by
    simpa [prefixWord, tailWord_3990753, baseEnd_3990753] using wordTrace_append hprefix tailTrace_3990753
  have hstable : (prefixWord ++ tailWord_3990753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990753).length < 2 ^ (prefixWord ++ tailWord_3990753).sum := by decide
  have hdescent : baseEnd_3990753 < baseStart_3990753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990756 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3990756 : Nat := 118140960795 + 3990756 * 2 ^ 59
def prefixEnd_3990756 : Nat := 4983230072969 + 3 ^ 40 * 3990756 * 2
def baseEnd_3990756 : Nat := 2049176002814293382496853

theorem tailTrace_3990756 : CollatzResearch.WordTrace tailWord_3990756 prefixEnd_3990756 2049176002814293382496853 := by
  unfold tailWord_3990756
  simp only [CollatzResearch.WordTrace]
  refine ⟨72777414565090026853800061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97036552753453369138400081 72777414565090026853800061)
  ·
    refine ⟨27291530461908760070175023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72777414565090026853800061 27291530461908760070175023)
    ·
      refine ⟨40937295692863140105262535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27291530461908760070175023 40937295692863140105262535)
      ·
        refine ⟨61405943539294710157893803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40937295692863140105262535 61405943539294710157893803)
        ·
          refine ⟨92108915308942065236840705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61405943539294710157893803 92108915308942065236840705)
          ·
            refine ⟨69081686481706548927630529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92108915308942065236840705 69081686481706548927630529)
            ·
              refine ⟨51811264861279911695722897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69081686481706548927630529 51811264861279911695722897)
              ·
                refine ⟨38858448645959933771792173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51811264861279911695722897 38858448645959933771792173)
                ·
                  refine ⟨14571918242234975164422065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38858448645959933771792173 14571918242234975164422065)
                  ·
                    refine ⟨10928938681676231373316549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14571918242234975164422065 10928938681676231373316549)
                    ·
                      refine ⟨2049176002814293382496853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10928938681676231373316549 2049176002814293382496853)
                      ·
                        rfl

theorem cell23_3990756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3990756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990756 prefixEnd_3990756 := by exact prefixLift 3990756
  have htrace : WordTrace (prefixWord ++ tailWord_3990756) baseStart_3990756 baseEnd_3990756 := by
    simpa [prefixWord, tailWord_3990756, baseEnd_3990756] using wordTrace_append hprefix tailTrace_3990756
  have hstable : (prefixWord ++ tailWord_3990756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990756).length < 2 ^ (prefixWord ++ tailWord_3990756).sum := by decide
  have hdescent : baseEnd_3990756 < baseStart_3990756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990770 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3990770 : Nat := 118140960795 + 3990770 * 2 ^ 59
def prefixEnd_3990770 : Nat := 4983230072969 + 3 ^ 40 * 3990770 * 2
def baseEnd_3990770 : Nat := 683061063847818775907263

theorem tailTrace_3990770 : CollatzResearch.WordTrace tailWord_3990770 prefixEnd_3990770 683061063847818775907263 := by
  unfold tailWord_3990770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36388834938032333524652441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97036893168086222732406509 36388834938032333524652441)
  ·
    refine ⟨27291626203524250143489331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36388834938032333524652441 27291626203524250143489331)
    ·
      refine ⟨40937439305286375215233997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27291626203524250143489331 40937439305286375215233997)
      ·
        refine ⟨15351539739482390705712749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40937439305286375215233997 15351539739482390705712749)
        ·
          refine ⟨5756827402305896514642281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15351539739482390705712749 5756827402305896514642281)
          ·
            refine ⟨4317620551729422385981711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756827402305896514642281 4317620551729422385981711)
            ·
              refine ⟨6476430827594133578972567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317620551729422385981711 6476430827594133578972567)
              ·
                refine ⟨9714646241391200368458851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476430827594133578972567 9714646241391200368458851)
                ·
                  refine ⟨14571969362086800552688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9714646241391200368458851 14571969362086800552688277)
                  ·
                    refine ⟨683061063847818775907263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14571969362086800552688277 683061063847818775907263)
                    ·
                      rfl

theorem cell23_3990770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3990770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990770 prefixEnd_3990770 := by exact prefixLift 3990770
  have htrace : WordTrace (prefixWord ++ tailWord_3990770) baseStart_3990770 baseEnd_3990770 := by
    simpa [prefixWord, tailWord_3990770, baseEnd_3990770] using wordTrace_append hprefix tailTrace_3990770
  have hstable : (prefixWord ++ tailWord_3990770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990770).length < 2 ^ (prefixWord ++ tailWord_3990770).sum := by decide
  have hdescent : baseEnd_3990770 < baseStart_3990770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990783 : List Nat := [1, 1, 2, 2, 1, 7, 2, 7]
def baseStart_3990783 : Nat := 118140960795 + 3990783 * 2 ^ 59
def prefixEnd_3990783 : Nat := 4983230072969 + 3 ^ 40 * 3990783 * 2
def baseEnd_3990783 : Nat := 75895920992294991735527

theorem tailTrace_3990783 : CollatzResearch.WordTrace tailWord_3990783 prefixEnd_3990783 75895920992294991735527 := by
  unfold tailWord_3990783
  simp only [CollatzResearch.WordTrace]
  refine ⟨145555813901082237318833003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97037209267388158212555335 145555813901082237318833003)
  ·
    refine ⟨218333720851623355978249505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145555813901082237318833003 218333720851623355978249505)
    ·
      refine ⟨163750290638717516983687129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218333720851623355978249505 163750290638717516983687129)
      ·
        refine ⟨122812717979038137737765347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163750290638717516983687129 122812717979038137737765347)
        ·
          refine ⟨184219076968557206606648021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122812717979038137737765347 184219076968557206606648021)
          ·
            refine ⟨4317634616450559529843313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 184219076968557206606648021 4317634616450559529843313)
            ·
              refine ⟨3238225962337919647382485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317634616450559529843313 3238225962337919647382485)
              ·
                refine ⟨75895920992294991735527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3238225962337919647382485 75895920992294991735527)
                ·
                  rfl

theorem cell23_3990783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 7].length) (baseStart_3990783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990783 prefixEnd_3990783 := by exact prefixLift 3990783
  have htrace : WordTrace (prefixWord ++ tailWord_3990783) baseStart_3990783 baseEnd_3990783 := by
    simpa [prefixWord, tailWord_3990783, baseEnd_3990783] using wordTrace_append hprefix tailTrace_3990783
  have hstable : (prefixWord ++ tailWord_3990783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990783).length < 2 ^ (prefixWord ++ tailWord_3990783).sum := by decide
  have hdescent : baseEnd_3990783 < baseStart_3990783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990793 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_3990793 : Nat := 118140960795 + 3990793 * 2 ^ 59
def prefixEnd_3990793 : Nat := 4983230072969 + 3 ^ 40 * 3990793 * 2
def baseEnd_3990793 : Nat := 2049195001598509737734183

theorem tailTrace_3990793 : CollatzResearch.WordTrace tailWord_3990793 prefixEnd_3990793 2049195001598509737734183 := by
  unfold tailWord_3990793
  simp only [CollatzResearch.WordTrace]
  refine ⟨145556178631046009026697033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97037452420697339351131355 145556178631046009026697033)
  ·
    refine ⟨109167133973284506770022775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145556178631046009026697033 109167133973284506770022775)
    ·
      refine ⟨163750700959926760155034163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109167133973284506770022775 163750700959926760155034163)
      ·
        refine ⟨245626051439890140232551245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163750700959926760155034163 245626051439890140232551245)
        ·
          refine ⟨92109769289958802587206717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245626051439890140232551245 92109769289958802587206717)
          ·
            refine ⟨34541163483734550970202519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92109769289958802587206717 34541163483734550970202519)
            ·
              refine ⟨51811745225601826455303779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34541163483734550970202519 51811745225601826455303779)
              ·
                refine ⟨77717617838402739682955669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51811745225601826455303779 77717617838402739682955669)
                ·
                  refine ⟨3643013336175128422638547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77717617838402739682955669 3643013336175128422638547)
                  ·
                    refine ⟨5464520004262692633957821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643013336175128422638547 5464520004262692633957821)
                    ·
                      refine ⟨2049195001598509737734183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464520004262692633957821 2049195001598509737734183)
                      ·
                        rfl

theorem cell23_3990793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_3990793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990793 prefixEnd_3990793 := by exact prefixLift 3990793
  have htrace : WordTrace (prefixWord ++ tailWord_3990793) baseStart_3990793 baseEnd_3990793 := by
    simpa [prefixWord, tailWord_3990793, baseEnd_3990793] using wordTrace_append hprefix tailTrace_3990793
  have hstable : (prefixWord ++ tailWord_3990793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990793).length < 2 ^ (prefixWord ++ tailWord_3990793).sum := by decide
  have hdescent : baseEnd_3990793 < baseStart_3990793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990803 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 7, 3, 2]
def baseStart_3990803 : Nat := 118140960795 + 3990803 * 2 ^ 59
def prefixEnd_3990803 : Nat := 4983230072969 + 3 ^ 40 * 3990803 * 2
def baseEnd_3990803 : Nat := 2049200136405054698609137

theorem tailTrace_3990803 : CollatzResearch.WordTrace tailWord_3990803 prefixEnd_3990803 2049200136405054698609137 := by
  unfold tailWord_3990803
  simp only [CollatzResearch.WordTrace]
  refine ⟨145556543361009780734561063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97037695574006520489707375 145556543361009780734561063)
  ·
    refine ⟨218334815041514671101841595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145556543361009780734561063 218334815041514671101841595)
    ·
      refine ⟨327502222562272006652762393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218334815041514671101841595 327502222562272006652762393)
      ·
        refine ⟨245626666921704004989571795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327502222562272006652762393 245626666921704004989571795)
        ·
          refine ⟨368440000382556007484357693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245626666921704004989571795 368440000382556007484357693)
          ·
            refine ⟨138165000143458502806634135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368440000382556007484357693 138165000143458502806634135)
            ·
              refine ⟨207247500215187754209951203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138165000143458502806634135 207247500215187754209951203)
              ·
                refine ⟨310871250322781631314926805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207247500215187754209951203 310871250322781631314926805)
                ·
                  refine ⟨7286044929440194483943597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310871250322781631314926805 7286044929440194483943597)
                  ·
                    refine ⟨2732266848540072931478849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7286044929440194483943597 2732266848540072931478849)
                    ·
                      refine ⟨2049200136405054698609137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732266848540072931478849 2049200136405054698609137)
                      ·
                        rfl

theorem cell23_3990803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3, 2].length) (baseStart_3990803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990803 prefixEnd_3990803 := by exact prefixLift 3990803
  have htrace : WordTrace (prefixWord ++ tailWord_3990803) baseStart_3990803 baseEnd_3990803 := by
    simpa [prefixWord, tailWord_3990803, baseEnd_3990803] using wordTrace_append hprefix tailTrace_3990803
  have hstable : (prefixWord ++ tailWord_3990803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990803).length < 2 ^ (prefixWord ++ tailWord_3990803).sum := by decide
  have hdescent : baseEnd_3990803 < baseStart_3990803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990810 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_3990810 : Nat := 118140960795 + 3990810 * 2 ^ 59
def prefixEnd_3990810 : Nat := 4983230072969 + 3 ^ 40 * 3990810 * 2
def baseEnd_3990810 : Nat := 2049203730769636171221605

theorem tailTrace_3990810 : CollatzResearch.WordTrace tailWord_3990810 prefixEnd_3990810 2049203730769636171221605 := by
  unfold tailWord_3990810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36389199667996105232516471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97037865781322947286710589 36389199667996105232516471)
  ·
    refine ⟨54583799501994157848774707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36389199667996105232516471 54583799501994157848774707)
    ·
      refine ⟨81875699252991236773162061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54583799501994157848774707 81875699252991236773162061)
      ·
        refine ⟨30703387219871713789935773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81875699252991236773162061 30703387219871713789935773)
        ·
          refine ⟨11513770207451892671225915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30703387219871713789935773 11513770207451892671225915)
          ·
            refine ⟨17270655311177839006838873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11513770207451892671225915 17270655311177839006838873)
            ·
              refine ⟨12952991483383379255129155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17270655311177839006838873 12952991483383379255129155)
              ·
                refine ⟨19429487225075068882693733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12952991483383379255129155 19429487225075068882693733)
                ·
                  refine ⟨3643028854701575415505075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19429487225075068882693733 3643028854701575415505075)
                  ·
                    refine ⟨5464543282052363123257613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643028854701575415505075 5464543282052363123257613)
                    ·
                      refine ⟨2049203730769636171221605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464543282052363123257613 2049203730769636171221605)
                      ·
                        rfl

theorem cell23_3990810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_3990810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990810 prefixEnd_3990810 := by exact prefixLift 3990810
  have htrace : WordTrace (prefixWord ++ tailWord_3990810) baseStart_3990810 baseEnd_3990810 := by
    simpa [prefixWord, tailWord_3990810, baseEnd_3990810] using wordTrace_append hprefix tailTrace_3990810
  have hstable : (prefixWord ++ tailWord_3990810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990810).length < 2 ^ (prefixWord ++ tailWord_3990810).sum := by decide
  have hdescent : baseEnd_3990810 < baseStart_3990810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990820 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3990820 : Nat := 118140960795 + 3990820 * 2 ^ 59
def prefixEnd_3990820 : Nat := 4983230072969 + 3 ^ 40 * 3990820 * 2
def baseEnd_3990820 : Nat := 2049208865576181132096559

theorem tailTrace_3990820 : CollatzResearch.WordTrace tailWord_3990820 prefixEnd_3990820 2049208865576181132096559 := by
  unfold tailWord_3990820
  simp only [CollatzResearch.WordTrace]
  refine ⟨72778581700974096318964957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97038108934632128425286609 72778581700974096318964957)
  ·
    refine ⟨27291968137865286119611859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72778581700974096318964957 27291968137865286119611859)
    ·
      refine ⟨40937952206797929179417789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27291968137865286119611859 40937952206797929179417789)
      ·
        refine ⟨15351732077549223442281671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40937952206797929179417789 15351732077549223442281671)
        ·
          refine ⟨23027598116323835163422507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15351732077549223442281671 23027598116323835163422507)
          ·
            refine ⟨34541397174485752745133761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23027598116323835163422507 34541397174485752745133761)
            ·
              refine ⟨25906047880864314558850321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34541397174485752745133761 25906047880864314558850321)
              ·
                refine ⟨19429535910648235919137741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25906047880864314558850321 19429535910648235919137741)
                ·
                  refine ⟨7286075966493088469676653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19429535910648235919137741 7286075966493088469676653)
                  ·
                    refine ⟨2732278487434908176128745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7286075966493088469676653 2732278487434908176128745)
                    ·
                      refine ⟨2049208865576181132096559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732278487434908176128745 2049208865576181132096559)
                      ·
                        rfl

theorem cell23_3990820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3990820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990820 prefixEnd_3990820 := by exact prefixLift 3990820
  have htrace : WordTrace (prefixWord ++ tailWord_3990820) baseStart_3990820 baseEnd_3990820 := by
    simpa [prefixWord, tailWord_3990820, baseEnd_3990820] using wordTrace_append hprefix tailTrace_3990820
  have hstable : (prefixWord ++ tailWord_3990820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990820).length < 2 ^ (prefixWord ++ tailWord_3990820).sum := by decide
  have hdescent : baseEnd_3990820 < baseStart_3990820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990837 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_3990837 : Nat := 118140960795 + 3990837 * 2 ^ 59
def prefixEnd_3990837 : Nat := 4983230072969 + 3 ^ 40 * 3990837 * 2
def baseEnd_3990837 : Nat := 2049217594747307565583981

theorem tailTrace_3990837 : CollatzResearch.WordTrace tailWord_3990837 prefixEnd_3990837 2049217594747307565583981 := by
  unfold tailWord_3990837
  simp only [CollatzResearch.WordTrace]
  refine ⟨145557783442886604541298765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97038522295257736360865843 145557783442886604541298765)
  ·
    refine ⟨54584168791082476702987037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145557783442886604541298765 54584168791082476702987037)
    ·
      refine ⟨20469063296655928763620139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54584168791082476702987037 20469063296655928763620139)
      ·
        refine ⟨30703594944983893145430209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20469063296655928763620139 30703594944983893145430209)
        ·
          refine ⟨23027696208737919859072657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30703594944983893145430209 23027696208737919859072657)
          ·
            refine ⟨17270772156553439894304493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23027696208737919859072657 17270772156553439894304493)
            ·
              refine ⟨6476539558707539960364185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17270772156553439894304493 6476539558707539960364185)
              ·
                refine ⟨4857404669030654970273139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476539558707539960364185 4857404669030654970273139)
                ·
                  refine ⟨7286107003545982455409709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857404669030654970273139 7286107003545982455409709)
                  ·
                    refine ⟨2732290126329743420778641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7286107003545982455409709 2732290126329743420778641)
                    ·
                      refine ⟨2049217594747307565583981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732290126329743420778641 2049217594747307565583981)
                      ·
                        rfl

theorem cell23_3990837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_3990837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990837 prefixEnd_3990837 := by exact prefixLift 3990837
  have htrace : WordTrace (prefixWord ++ tailWord_3990837) baseStart_3990837 baseEnd_3990837 := by
    simpa [prefixWord, tailWord_3990837, baseEnd_3990837] using wordTrace_append hprefix tailTrace_3990837
  have hstable : (prefixWord ++ tailWord_3990837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990837).length < 2 ^ (prefixWord ++ tailWord_3990837).sum := by decide
  have hdescent : baseEnd_3990837 < baseStart_3990837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990861 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3990861 : Nat := 118140960795 + 3990861 * 2 ^ 59
def prefixEnd_3990861 : Nat := 4983230072969 + 3 ^ 40 * 3990861 * 2
def baseEnd_3990861 : Nat := 2049229918283015471683871

theorem tailTrace_3990861 : CollatzResearch.WordTrace tailWord_3990861 prefixEnd_3990861 2049229918283015471683871 := by
  unfold tailWord_3990861
  simp only [CollatzResearch.WordTrace]
  refine ⟨145558658794799656640172437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97039105863199771093448291 145558658794799656640172437)
  ·
    refine ⟨6823062131006233905008083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145558658794799656640172437 6823062131006233905008083)
    ·
      refine ⟨10234593196509350857512125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823062131006233905008083 10234593196509350857512125)
      ·
        refine ⟨3837972448691006571567047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10234593196509350857512125 3837972448691006571567047)
        ·
          refine ⟨5756958673036509857350571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837972448691006571567047 5756958673036509857350571)
          ·
            refine ⟨8635438009554764786025857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5756958673036509857350571 8635438009554764786025857)
            ·
              refine ⟨6476578507166073589519393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635438009554764786025857 6476578507166073589519393)
              ·
                refine ⟨4857433880374555192139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476578507166073589519393 4857433880374555192139545)
                ·
                  refine ⟨3643075410280916394104659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4857433880374555192139545 3643075410280916394104659)
                  ·
                    refine ⟨5464613115421374591156989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643075410280916394104659 5464613115421374591156989)
                    ·
                      refine ⟨2049229918283015471683871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464613115421374591156989 2049229918283015471683871)
                      ·
                        rfl

theorem cell23_3990861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3990861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990861 prefixEnd_3990861 := by exact prefixLift 3990861
  have htrace : WordTrace (prefixWord ++ tailWord_3990861) baseStart_3990861 baseEnd_3990861 := by
    simpa [prefixWord, tailWord_3990861, baseEnd_3990861] using wordTrace_append hprefix tailTrace_3990861
  have hstable : (prefixWord ++ tailWord_3990861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990861).length < 2 ^ (prefixWord ++ tailWord_3990861).sum := by decide
  have hdescent : baseEnd_3990861 < baseStart_3990861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990867 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 2, 2, 2]
def baseStart_3990867 : Nat := 118140960795 + 3990867 * 2 ^ 59
def prefixEnd_3990867 : Nat := 4983230072969 + 3 ^ 40 * 3990867 * 2
def baseEnd_3990867 : Nat := 2049232999166942448208843

theorem tailTrace_3990867 : CollatzResearch.WordTrace tailWord_3990867 prefixEnd_3990867 2049232999166942448208843 := by
  unfold tailWord_3990867
  simp only [CollatzResearch.WordTrace]
  refine ⟨145558877632777919664890855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97039251755185279776593903 145558877632777919664890855)
  ·
    refine ⟨218338316449166879497336283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145558877632777919664890855 218338316449166879497336283)
    ·
      refine ⟨327507474673750319246004425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218338316449166879497336283 327507474673750319246004425)
      ·
        refine ⟨245630606005312739434503319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327507474673750319246004425 245630606005312739434503319)
        ·
          refine ⟨368445909007969109151754979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245630606005312739434503319 368445909007969109151754979)
          ·
            refine ⟨552668863511953663727632469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368445909007969109151754979 552668863511953663727632469)
            ·
              refine ⟨6476588244280706996808193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 552668863511953663727632469 6476588244280706996808193)
              ·
                refine ⟨4857441183210530247606145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476588244280706996808193 4857441183210530247606145)
                ·
                  refine ⟨3643080887407897685704609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4857441183210530247606145 3643080887407897685704609)
                  ·
                    refine ⟨2732310665555923264278457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3643080887407897685704609 2732310665555923264278457)
                    ·
                      refine ⟨2049232999166942448208843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732310665555923264278457 2049232999166942448208843)
                      ·
                        rfl

theorem cell23_3990867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2, 2].length) (baseStart_3990867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990867 prefixEnd_3990867 := by exact prefixLift 3990867
  have htrace : WordTrace (prefixWord ++ tailWord_3990867) baseStart_3990867 baseEnd_3990867 := by
    simpa [prefixWord, tailWord_3990867, baseEnd_3990867] using wordTrace_append hprefix tailTrace_3990867
  have hstable : (prefixWord ++ tailWord_3990867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990867).length < 2 ^ (prefixWord ++ tailWord_3990867).sum := by decide
  have hdescent : baseEnd_3990867 < baseStart_3990867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990883 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3990883 : Nat := 118140960795 + 3990883 * 2 ^ 59
def prefixEnd_3990883 : Nat := 4983230072969 + 3 ^ 40 * 3990883 * 2
def baseEnd_3990883 : Nat := 2049241214857414385608769

theorem tailTrace_3990883 : CollatzResearch.WordTrace tailWord_3990883 prefixEnd_3990883 2049241214857414385608769 := by
  unfold tailWord_3990883
  simp only [CollatzResearch.WordTrace]
  refine ⟨145559461200719954397473303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97039640800479969598315535 145559461200719954397473303)
  ·
    refine ⟨218339191801079931596209955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145559461200719954397473303 218339191801079931596209955)
    ·
      refine ⟨327508787701619897394314933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218339191801079931596209955 327508787701619897394314933)
      ·
        refine ⟨30703948847026865380717025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327508787701619897394314933 30703948847026865380717025)
        ·
          refine ⟨23027961635270149035537769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30703948847026865380717025 23027961635270149035537769)
          ·
            refine ⟨17270971226452611776653327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23027961635270149035537769 17270971226452611776653327)
            ·
              refine ⟨25906456839678917664979991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17270971226452611776653327 25906456839678917664979991)
              ·
                refine ⟨38859685259518376497469987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25906456839678917664979991 38859685259518376497469987)
                ·
                  refine ⟨58289527889277564746204981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38859685259518376497469987 58289527889277564746204981)
                  ·
                    refine ⟨5464643239619771694956717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58289527889277564746204981 5464643239619771694956717)
                    ·
                      refine ⟨2049241214857414385608769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464643239619771694956717 2049241214857414385608769)
                      ·
                        rfl

theorem cell23_3990883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3990883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990883 prefixEnd_3990883 := by exact prefixLift 3990883
  have htrace : WordTrace (prefixWord ++ tailWord_3990883) baseStart_3990883 baseEnd_3990883 := by
    simpa [prefixWord, tailWord_3990883, baseEnd_3990883] using wordTrace_append hprefix tailTrace_3990883
  have hstable : (prefixWord ++ tailWord_3990883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990883).length < 2 ^ (prefixWord ++ tailWord_3990883).sum := by decide
  have hdescent : baseEnd_3990883 < baseStart_3990883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990890 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_3990890 : Nat := 118140960795 + 3990890 * 2 ^ 59
def prefixEnd_3990890 : Nat := 4983230072969 + 3 ^ 40 * 3990890 * 2
def baseEnd_3990890 : Nat := 227693867691332873135693

theorem tailTrace_3990890 : CollatzResearch.WordTrace tailWord_3990890 prefixEnd_3990890 227693867691332873135693 := by
  unfold tailWord_3990890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36389929127923648648244531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97039811007796396395318749 36389929127923648648244531)
  ·
    refine ⟨54584893691885472972366797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36389929127923648648244531 54584893691885472972366797)
    ·
      refine ⟨20469335134457052364637549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54584893691885472972366797 20469335134457052364637549)
      ·
        refine ⟨7676000675421394636739081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20469335134457052364637549 7676000675421394636739081)
        ·
          refine ⟨5757000506566045977554311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7676000675421394636739081 5757000506566045977554311)
          ·
            refine ⟨8635500759849068966331467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757000506566045977554311 8635500759849068966331467)
            ·
              refine ⟨12953251139773603449497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635500759849068966331467 12953251139773603449497201)
              ·
                refine ⟨9714938354830202587122901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12953251139773603449497201 9714938354830202587122901)
                ·
                  refine ⟨227693867691332873135693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9714938354830202587122901 227693867691332873135693)
                  ·
                    rfl

theorem cell23_3990890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_3990890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990890 prefixEnd_3990890 := by exact prefixLift 3990890
  have htrace : WordTrace (prefixWord ++ tailWord_3990890) baseStart_3990890 baseEnd_3990890 := by
    simpa [prefixWord, tailWord_3990890, baseEnd_3990890] using wordTrace_append hprefix tailTrace_3990890
  have hstable : (prefixWord ++ tailWord_3990890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990890).length < 2 ^ (prefixWord ++ tailWord_3990890).sum := by decide
  have hdescent : baseEnd_3990890 < baseStart_3990890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990923 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4]
def baseStart_3990923 : Nat := 118140960795 + 3990923 * 2 ^ 59
def prefixEnd_3990923 : Nat := 4983230072969 + 3 ^ 40 * 3990923 * 2
def baseEnd_3990923 : Nat := 2049261754083594229108585

theorem tailTrace_3990923 : CollatzResearch.WordTrace tailWord_3990923 prefixEnd_3990923 2049261754083594229108585 := by
  unfold tailWord_3990923
  simp only [CollatzResearch.WordTrace]
  refine ⟨145560920120575041228929423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97040613413716694152619615 145560920120575041228929423)
  ·
    refine ⟨218341380180862561843394135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145560920120575041228929423 218341380180862561843394135)
    ·
      refine ⟨327512070271293842765091203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218341380180862561843394135 327512070271293842765091203)
      ·
        refine ⟨491268105406940764147636805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327512070271293842765091203 491268105406940764147636805)
        ·
          refine ⟨92112769763801393277681901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491268105406940764147636805 92112769763801393277681901)
          ·
            refine ⟨34542288661425522479130713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92112769763801393277681901 34542288661425522479130713)
            ·
              refine ⟨25906716496069141859348035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34542288661425522479130713 25906716496069141859348035)
              ·
                refine ⟨38860074744103712789022053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25906716496069141859348035 38860074744103712789022053)
                ·
                  refine ⟨7286264014519446147941635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38860074744103712789022053 7286264014519446147941635)
                  ·
                    refine ⟨10929396021779169221912453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7286264014519446147941635 10929396021779169221912453)
                    ·
                      refine ⟨2049261754083594229108585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10929396021779169221912453 2049261754083594229108585)
                      ·
                        rfl

theorem cell23_3990923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_3990923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990923 prefixEnd_3990923 := by exact prefixLift 3990923
  have htrace : WordTrace (prefixWord ++ tailWord_3990923) baseStart_3990923 baseEnd_3990923 := by
    simpa [prefixWord, tailWord_3990923, baseEnd_3990923] using wordTrace_append hprefix tailTrace_3990923
  have hstable : (prefixWord ++ tailWord_3990923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990923).length < 2 ^ (prefixWord ++ tailWord_3990923).sum := by decide
  have hdescent : baseEnd_3990923 < baseStart_3990923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990980 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 8]
def baseStart_3990980 : Nat := 118140960795 + 3990980 * 2 ^ 59
def prefixEnd_3990980 : Nat := 4983230072969 + 3 ^ 40 * 3990980 * 2
def baseEnd_3990980 : Nat := 227699002497877834010647

theorem tailTrace_3990980 : CollatzResearch.WordTrace tailWord_3990980 prefixEnd_3990980 227699002497877834010647 := by
  unfold tailWord_3990980
  simp only [CollatzResearch.WordTrace]
  refine ⟨72781499540684269981877197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97041999387579026642502929 72781499540684269981877197)
  ·
    refine ⟨27293062327756601243203949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72781499540684269981877197 27293062327756601243203949)
    ·
      refine ⟨10234898372908725466201481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27293062327756601243203949 10234898372908725466201481)
      ·
        refine ⟨7676173779681544099651111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10234898372908725466201481 7676173779681544099651111)
        ·
          refine ⟨11514260669522316149476667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676173779681544099651111 11514260669522316149476667)
          ·
            refine ⟨17271391004283474224215001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11514260669522316149476667 17271391004283474224215001)
            ·
              refine ⟨12953543253212605668161251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17271391004283474224215001 12953543253212605668161251)
              ·
                refine ⟨19430314879818908502241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12953543253212605668161251 19430314879818908502241877)
                ·
                  refine ⟨227699002497877834010647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19430314879818908502241877 227699002497877834010647)
                  ·
                    rfl

theorem cell23_3990980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_3990980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990980 prefixEnd_3990980 := by exact prefixLift 3990980
  have htrace : WordTrace (prefixWord ++ tailWord_3990980) baseStart_3990980 baseEnd_3990980 := by
    simpa [prefixWord, tailWord_3990980, baseEnd_3990980] using wordTrace_append hprefix tailTrace_3990980
  have hstable : (prefixWord ++ tailWord_3990980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990980).length < 2 ^ (prefixWord ++ tailWord_3990980).sum := by decide
  have hdescent : baseEnd_3990980 < baseStart_3990980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3990984 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 1, 4]
def baseStart_3990984 : Nat := 118140960795 + 3990984 * 2 ^ 59
def prefixEnd_3990984 : Nat := 4983230072969 + 3 ^ 40 * 3990984 * 2
def baseEnd_3990984 : Nat := 683097692134506163481935

theorem tailTrace_3990984 : CollatzResearch.WordTrace tailWord_3990984 prefixEnd_3990984 683097692134506163481935 := by
  unfold tailWord_3990984
  simp only [CollatzResearch.WordTrace]
  refine ⟨72781572486677024323450003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97042096648902699097933337 72781572486677024323450003)
  ·
    refine ⟨109172358730015536485175005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72781572486677024323450003 109172358730015536485175005)
    ·
      refine ⟨40939634523755826181940627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109172358730015536485175005 40939634523755826181940627)
      ·
        refine ⟨61409451785633739272910941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40939634523755826181940627 61409451785633739272910941)
        ·
          refine ⟨23028544419612652227341603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61409451785633739272910941 23028544419612652227341603)
          ·
            refine ⟨34542816629418978341012405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23028544419612652227341603 34542816629418978341012405)
            ·
              refine ⟨3238389059008029219469913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34542816629418978341012405 3238389059008029219469913)
              ·
                refine ⟨2428791794256021914602435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238389059008029219469913 2428791794256021914602435)
                ·
                  refine ⟨3643187691384032871903653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428791794256021914602435 3643187691384032871903653)
                  ·
                    refine ⟨683097692134506163481935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3643187691384032871903653 683097692134506163481935)
                    ·
                      rfl

theorem cell23_3990984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_3990984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3990984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3990984 prefixEnd_3990984 := by exact prefixLift 3990984
  have htrace : WordTrace (prefixWord ++ tailWord_3990984) baseStart_3990984 baseEnd_3990984 := by
    simpa [prefixWord, tailWord_3990984, baseEnd_3990984] using wordTrace_append hprefix tailTrace_3990984
  have hstable : (prefixWord ++ tailWord_3990984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3990984).length < 2 ^ (prefixWord ++ tailWord_3990984).sum := by decide
  have hdescent : baseEnd_3990984 < baseStart_3990984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3990984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
