import V185TrunkScan20Chunk110

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_674148 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_674148 : Nat := 118140960795 + 674148 * 2 ^ 59
def prefixEnd_674148 : Nat := 4983230072969 + 3 ^ 40 * 674148 * 2
def baseEnd_674148 : Nat := 307699516682074334710805

theorem tailTrace_674148 : CollatzResearch.WordTrace tailWord_674148 prefixEnd_674148 307699516682074334710805 := by
  unfold tailWord_674148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12294098780842203078559549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16392131707789604104746065 12294098780842203078559549)
  ·
    refine ⟨4610287042815826154459831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12294098780842203078559549 4610287042815826154459831)
    ·
      refine ⟨6915430564223739231689747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610287042815826154459831 6915430564223739231689747)
      ·
        refine ⟨10373145846335608847534621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915430564223739231689747 10373145846335608847534621)
        ·
          refine ⟨3889929692375853317825483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10373145846335608847534621 3889929692375853317825483)
          ·
            refine ⟨5834894538563779976738225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889929692375853317825483 5834894538563779976738225)
            ·
              refine ⟨4376170903922834982553669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834894538563779976738225 4376170903922834982553669)
              ·
                refine ⟨820532044485531559228813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4376170903922834982553669 820532044485531559228813)
                ·
                  refine ⟨307699516682074334710805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820532044485531559228813 307699516682074334710805)
                  ·
                    rfl

theorem cell20_674148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_674148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674148 prefixEnd_674148 := by exact prefixLift 674148
  have htrace : WordTrace (prefixWord ++ tailWord_674148) baseStart_674148 baseEnd_674148 := by
    simpa [prefixWord, tailWord_674148, baseEnd_674148] using wordTrace_append hprefix tailTrace_674148
  have hstable : (prefixWord ++ tailWord_674148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674148).length < 2 ^ (prefixWord ++ tailWord_674148).sum := by decide
  have hdescent : baseEnd_674148 < baseStart_674148 := by decide
  rcases family_descends (prefixWord ++ tailWord_674148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674162 : List Nat := [3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_674162 : Nat := 118140960795 + 674162 * 2 ^ 59
def prefixEnd_674162 : Nat := 4983230072969 + 3 ^ 40 * 674162 * 2
def baseEnd_674162 : Nat := 102568635554517502748027

theorem tailTrace_674162 : CollatzResearch.WordTrace tailWord_674162 prefixEnd_674162 102568635554517502748027 := by
  unfold tailWord_674162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147177045908421637032185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16392472122422457698752493 6147177045908421637032185)
  ·
    refine ⟨4610382784431316227774139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6147177045908421637032185 4610382784431316227774139)
    ·
      refine ⟨6915574176646974341661209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610382784431316227774139 6915574176646974341661209)
      ·
        refine ⟨5186680632485230756245907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6915574176646974341661209 5186680632485230756245907)
        ·
          refine ⟨7780020948727846134368861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186680632485230756245907 7780020948727846134368861)
          ·
            refine ⟨2917507855772942300388323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7780020948727846134368861 2917507855772942300388323)
            ·
              refine ⟨4376261783659413450582485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917507855772942300388323 4376261783659413450582485)
              ·
                refine ⟨102568635554517502748027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4376261783659413450582485 102568635554517502748027)
                ·
                  rfl

theorem cell20_674162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_674162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674162 prefixEnd_674162 := by exact prefixLift 674162
  have htrace : WordTrace (prefixWord ++ tailWord_674162) baseStart_674162 baseEnd_674162 := by
    simpa [prefixWord, tailWord_674162, baseEnd_674162] using wordTrace_append hprefix tailTrace_674162
  have hstable : (prefixWord ++ tailWord_674162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674162).length < 2 ^ (prefixWord ++ tailWord_674162).sum := by decide
  have hdescent : baseEnd_674162 < baseStart_674162 := by decide
  rcases family_descends (prefixWord ++ tailWord_674162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674165 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_674165 : Nat := 118140960795 + 674165 * 2 ^ 59
def prefixEnd_674165 : Nat := 4983230072969 + 3 ^ 40 * 674165 * 2
def baseEnd_674165 : Nat := 307707275945297831144069

theorem tailTrace_674165 : CollatzResearch.WordTrace tailWord_674165 prefixEnd_674165 307707275945297831144069 := by
  unfold tailWord_674165
  simp only [CollatzResearch.WordTrace]
  refine ⟨24588817602622818060487949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16392545068415212040325299 24588817602622818060487949)
  ·
    refine ⟨9220806600983556772682981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24588817602622818060487949 9220806600983556772682981)
    ·
      refine ⟨1728901237684416894878059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9220806600983556772682981 1728901237684416894878059)
      ·
        refine ⟨2593351856526625342317089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728901237684416894878059 2593351856526625342317089)
        ·
          refine ⟨1945013892394969006737817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2593351856526625342317089 1945013892394969006737817)
          ·
            refine ⟨1458760419296226755053363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945013892394969006737817 1458760419296226755053363)
            ·
              refine ⟨2188140628944340132580045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458760419296226755053363 2188140628944340132580045)
              ·
                refine ⟨820552735854127549717517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2188140628944340132580045 820552735854127549717517)
                ·
                  refine ⟨307707275945297831144069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820552735854127549717517 307707275945297831144069)
                  ·
                    rfl

theorem cell20_674165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_674165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674165 prefixEnd_674165 := by exact prefixLift 674165
  have htrace : WordTrace (prefixWord ++ tailWord_674165) baseStart_674165 baseEnd_674165 := by
    simpa [prefixWord, tailWord_674165, baseEnd_674165] using wordTrace_append hprefix tailTrace_674165
  have hstable : (prefixWord ++ tailWord_674165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674165).length < 2 ^ (prefixWord ++ tailWord_674165).sum := by decide
  have hdescent : baseEnd_674165 < baseStart_674165 := by decide
  rcases family_descends (prefixWord ++ tailWord_674165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674198 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_674198 : Nat := 118140960795 + 674198 * 2 ^ 59
def prefixEnd_674198 : Nat := 4983230072969 + 3 ^ 40 * 674198 * 2
def baseEnd_674198 : Nat := 307722338044496383043935

theorem tailTrace_674198 : CollatzResearch.WordTrace tailWord_674198 prefixEnd_674198 307722338044496383043935 := by
  unfold tailWord_674198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536876325718954043527453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16393347474335509797626165 1536876325718954043527453)
  ·
    refine ⟨576328622144607766322795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1536876325718954043527453 576328622144607766322795)
    ·
      refine ⟨864492933216911649484193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576328622144607766322795 864492933216911649484193)
      ·
        refine ⟨648369699912683737113145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864492933216911649484193 648369699912683737113145)
        ·
          refine ⟨486277274934512802834859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648369699912683737113145 486277274934512802834859)
          ·
            refine ⟨729415912401769204252289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486277274934512802834859 729415912401769204252289)
            ·
              refine ⟨547061934301326903189217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729415912401769204252289 547061934301326903189217)
              ·
                refine ⟨410296450725995177391913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547061934301326903189217 410296450725995177391913)
                ·
                  refine ⟨307722338044496383043935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410296450725995177391913 307722338044496383043935)
                  ·
                    rfl

theorem cell20_674198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_674198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674198 prefixEnd_674198 := by exact prefixLift 674198
  have htrace : WordTrace (prefixWord ++ tailWord_674198) baseStart_674198 baseEnd_674198 := by
    simpa [prefixWord, tailWord_674198, baseEnd_674198] using wordTrace_append hprefix tailTrace_674198
  have hstable : (prefixWord ++ tailWord_674198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674198).length < 2 ^ (prefixWord ++ tailWord_674198).sum := by decide
  have hdescent : baseEnd_674198 < baseStart_674198 := by decide
  rcases family_descends (prefixWord ++ tailWord_674198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674200 : List Nat := [2, 1, 2, 5, 1, 9]
def baseStart_674200 : Nat := 118140960795 + 674200 * 2 ^ 59
def prefixEnd_674200 : Nat := 4983230072969 + 3 ^ 40 * 674200 * 2
def baseEnd_674200 : Nat := 11397157440703454258417

theorem tailTrace_674200 : CollatzResearch.WordTrace tailWord_674200 prefixEnd_674200 11397157440703454258417 := by
  unfold tailWord_674200
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295047078748009519006027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16393396104997346025341369 12295047078748009519006027)
  ·
    refine ⟨18442570618122014278509041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12295047078748009519006027 18442570618122014278509041)
    ·
      refine ⟨13831927963591510708881781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18442570618122014278509041 13831927963591510708881781)
      ·
        refine ⟨1296743246586704128957667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13831927963591510708881781 1296743246586704128957667)
        ·
          refine ⟨1945114869880056193436501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296743246586704128957667 1945114869880056193436501)
          ·
            refine ⟨11397157440703454258417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1945114869880056193436501 11397157440703454258417)
            ·
              rfl

theorem cell20_674200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 9].length) (baseStart_674200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674200 prefixEnd_674200 := by exact prefixLift 674200
  have htrace : WordTrace (prefixWord ++ tailWord_674200) baseStart_674200 baseEnd_674200 := by
    simpa [prefixWord, tailWord_674200, baseEnd_674200] using wordTrace_append hprefix tailTrace_674200
  have hstable : (prefixWord ++ tailWord_674200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674200).length < 2 ^ (prefixWord ++ tailWord_674200).sum := by decide
  have hdescent : baseEnd_674200 < baseStart_674200 := by decide
  rcases family_descends (prefixWord ++ tailWord_674200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674206 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_674206 : Nat := 118140960795 + 674206 * 2 ^ 59
def prefixEnd_674206 : Nat := 4983230072969 + 3 ^ 40 * 674206 * 2
def baseEnd_674206 : Nat := 307725989462483910777235

theorem tailTrace_674206 : CollatzResearch.WordTrace tailWord_674206 prefixEnd_674206 307725989462483910777235 := by
  unfold tailWord_674206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073789124434285257841309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16393541996982854708486981 3073789124434285257841309)
  ·
    refine ⟨1152670921662856971690491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3073789124434285257841309 1152670921662856971690491)
    ·
      refine ⟨1729006382494285457535737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152670921662856971690491 1729006382494285457535737)
      ·
        refine ⟨1296754786870714093151803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729006382494285457535737 1296754786870714093151803)
        ·
          refine ⟨1945132180306071139727705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296754786870714093151803 1945132180306071139727705)
          ·
            refine ⟨1458849135229553354795779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945132180306071139727705 1458849135229553354795779)
            ·
              refine ⟨2188273702844330032193669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458849135229553354795779 2188273702844330032193669)
              ·
                refine ⟨410301319283311881036313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2188273702844330032193669 410301319283311881036313)
                ·
                  refine ⟨307725989462483910777235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410301319283311881036313 307725989462483910777235)
                  ·
                    rfl

theorem cell20_674206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_674206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674206 prefixEnd_674206 := by exact prefixLift 674206
  have htrace : WordTrace (prefixWord ++ tailWord_674206) baseStart_674206 baseEnd_674206 := by
    simpa [prefixWord, tailWord_674206, baseEnd_674206] using wordTrace_append hprefix tailTrace_674206
  have hstable : (prefixWord ++ tailWord_674206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674206).length < 2 ^ (prefixWord ++ tailWord_674206).sum := by decide
  have hdescent : baseEnd_674206 < baseStart_674206 := by decide
  rcases family_descends (prefixWord ++ tailWord_674206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674231 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_674231 : Nat := 118140960795 + 674231 * 2 ^ 59
def prefixEnd_674231 : Nat := 4983230072969 + 3 ^ 40 * 674231 * 2
def baseEnd_674231 : Nat := 307737400143694934943799

theorem tailTrace_674231 : CollatzResearch.WordTrace tailWord_674231 prefixEnd_674231 307737400143694934943799 := by
  unfold tailWord_674231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591224820383711332390547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16394149880255807554927031 24591224820383711332390547)
  ·
    refine ⟨36886837230575566998585821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24591224820383711332390547 36886837230575566998585821)
    ·
      refine ⟨13832563961465837624469683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36886837230575566998585821 13832563961465837624469683)
      ·
        refine ⟨20748845942198756436704525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13832563961465837624469683 20748845942198756436704525)
        ·
          refine ⟨7780817228324533663764197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20748845942198756436704525 7780817228324533663764197)
          ·
            refine ⟨1458903230310850061955787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7780817228324533663764197 1458903230310850061955787)
            ·
              refine ⟨2188354845466275092933681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458903230310850061955787 2188354845466275092933681)
              ·
                refine ⟨1641266134099706319700261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188354845466275092933681 1641266134099706319700261)
                ·
                  refine ⟨307737400143694934943799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641266134099706319700261 307737400143694934943799)
                  ·
                    rfl

theorem cell20_674231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_674231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674231 prefixEnd_674231 := by exact prefixLift 674231
  have htrace : WordTrace (prefixWord ++ tailWord_674231) baseStart_674231 baseEnd_674231 := by
    simpa [prefixWord, tailWord_674231, baseEnd_674231] using wordTrace_append hprefix tailTrace_674231
  have hstable : (prefixWord ++ tailWord_674231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674231).length < 2 ^ (prefixWord ++ tailWord_674231).sum := by decide
  have hdescent : baseEnd_674231 < baseStart_674231 := by decide
  rcases family_descends (prefixWord ++ tailWord_674231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674238 : List Nat := [4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_674238 : Nat := 118140960795 + 674238 * 2 ^ 59
def prefixEnd_674238 : Nat := 4983230072969 + 3 ^ 40 * 674238 * 2
def baseEnd_674238 : Nat := 102580198378144673903479

theorem tailTrace_674238 : CollatzResearch.WordTrace tailWord_674238 prefixEnd_674238 102580198378144673903479 := by
  unfold tailWord_674238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073935016419793940986921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16394320087572234351930245 3073935016419793940986921)
  ·
    refine ⟨2305451262314845455740191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3073935016419793940986921 2305451262314845455740191)
    ·
      refine ⟨3458176893472268183610287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305451262314845455740191 3458176893472268183610287)
      ·
        refine ⟨5187265340208402275415431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458176893472268183610287 5187265340208402275415431)
        ·
          refine ⟨7780898010312603413123147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187265340208402275415431 7780898010312603413123147)
          ·
            refine ⟨11671347015468905119684721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780898010312603413123147 11671347015468905119684721)
            ·
              refine ⟨8753510261601678839763541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11671347015468905119684721 8753510261601678839763541)
              ·
                refine ⟨102580198378144673903479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8753510261601678839763541 102580198378144673903479)
                ·
                  rfl

theorem cell20_674238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_674238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674238 prefixEnd_674238 := by exact prefixLift 674238
  have htrace : WordTrace (prefixWord ++ tailWord_674238) baseStart_674238 baseEnd_674238 := by
    simpa [prefixWord, tailWord_674238, baseEnd_674238] using wordTrace_append hprefix tailTrace_674238
  have hstable : (prefixWord ++ tailWord_674238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674238).length < 2 ^ (prefixWord ++ tailWord_674238).sum := by decide
  have hdescent : baseEnd_674238 < baseStart_674238 := by decide
  rcases family_descends (prefixWord ++ tailWord_674238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674244 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_674244 : Nat := 118140960795 + 674244 * 2 ^ 59
def prefixEnd_674244 : Nat := 4983230072969 + 3 ^ 40 * 674244 * 2
def baseEnd_674244 : Nat := 307743333697924667510413

theorem tailTrace_674244 : CollatzResearch.WordTrace tailWord_674244 prefixEnd_674244 307743333697924667510413 := by
  unfold tailWord_674244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295849484668307276306893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16394465979557743035075857 12295849484668307276306893)
  ·
    refine ⟨4610943556750615228615085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12295849484668307276306893 4610943556750615228615085)
    ·
      refine ⟨1729103833781480710730657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4610943556750615228615085 1729103833781480710730657)
      ·
        refine ⟨1296827875336110533047993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729103833781480710730657 1296827875336110533047993)
        ·
          refine ⟨972620906502082899785995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296827875336110533047993 972620906502082899785995)
          ·
            refine ⟨1458931359753124349678993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972620906502082899785995 1458931359753124349678993)
            ·
              refine ⟨1094198519814843262259245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458931359753124349678993 1094198519814843262259245)
              ·
                refine ⟨410324444930566223347217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094198519814843262259245 410324444930566223347217)
                ·
                  refine ⟨307743333697924667510413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410324444930566223347217 307743333697924667510413)
                  ·
                    rfl

theorem cell20_674244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_674244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674244 prefixEnd_674244 := by exact prefixLift 674244
  have htrace : WordTrace (prefixWord ++ tailWord_674244) baseStart_674244 baseEnd_674244 := by
    simpa [prefixWord, tailWord_674244, baseEnd_674244] using wordTrace_append hprefix tailTrace_674244
  have hstable : (prefixWord ++ tailWord_674244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674244).length < 2 ^ (prefixWord ++ tailWord_674244).sum := by decide
  have hdescent : baseEnd_674244 < baseStart_674244 := by decide
  rcases family_descends (prefixWord ++ tailWord_674244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674248 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 2]
def baseStart_674248 : Nat := 118140960795 + 674248 * 2 ^ 59
def prefixEnd_674248 : Nat := 4983230072969 + 3 ^ 40 * 674248 * 2
def baseEnd_674248 : Nat := 307745159406918431377063

theorem tailTrace_674248 : CollatzResearch.WordTrace tailWord_674248 prefixEnd_674248 307745159406918431377063 := by
  unfold tailWord_674248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295922430661061617879699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16394563240881415490506265 12295922430661061617879699)
  ·
    refine ⟨18443883645991592426819549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12295922430661061617879699 18443883645991592426819549)
    ·
      refine ⟨6916456367246847160057331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18443883645991592426819549 6916456367246847160057331)
      ·
        refine ⟨10374684550870270740085997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916456367246847160057331 10374684550870270740085997)
        ·
          refine ⟨3890506706576351527532249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10374684550870270740085997 3890506706576351527532249)
          ·
            refine ⟨2917880029932263645649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890506706576351527532249 2917880029932263645649187)
            ·
              refine ⟨4376820044898395468473781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917880029932263645649187 4376820044898395468473781)
              ·
                refine ⟨410326879209224575169417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4376820044898395468473781 410326879209224575169417)
                ·
                  refine ⟨307745159406918431377063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410326879209224575169417 307745159406918431377063)
                  ·
                    rfl

theorem cell20_674248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_674248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674248 prefixEnd_674248 := by exact prefixLift 674248
  have htrace : WordTrace (prefixWord ++ tailWord_674248) baseStart_674248 baseEnd_674248 := by
    simpa [prefixWord, tailWord_674248, baseEnd_674248] using wordTrace_append hprefix tailTrace_674248
  have hstable : (prefixWord ++ tailWord_674248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674248).length < 2 ^ (prefixWord ++ tailWord_674248).sum := by decide
  have hdescent : baseEnd_674248 < baseStart_674248 := by decide
  rcases family_descends (prefixWord ++ tailWord_674248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674279 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_674279 : Nat := 118140960795 + 674279 * 2 ^ 59
def prefixEnd_674279 : Nat := 4983230072969 + 3 ^ 40 * 674279 * 2
def baseEnd_674279 : Nat := 307759308651620101343603

theorem tailTrace_674279 : CollatzResearch.WordTrace tailWord_674279 prefixEnd_674279 307759308651620101343603 := by
  unfold tailWord_674279
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592975524209815530137891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16395317016139877020091927 24592975524209815530137891)
  ·
    refine ⟨36889463286314723295206837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24592975524209815530137891 36889463286314723295206837)
    ·
      refine ⟨3458387183092005308925641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36889463286314723295206837 3458387183092005308925641)
      ·
        refine ⟨2593790387319003981694231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3458387183092005308925641 2593790387319003981694231)
        ·
          refine ⟨3890685580978505972541347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593790387319003981694231 3890685580978505972541347)
          ·
            refine ⟨5836028371467758958812021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890685580978505972541347 5836028371467758958812021)
            ·
              refine ⟨547127659825102402388627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5836028371467758958812021 547127659825102402388627)
              ·
                refine ⟨820691489737653603582941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547127659825102402388627 820691489737653603582941)
                ·
                  refine ⟨307759308651620101343603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820691489737653603582941 307759308651620101343603)
                  ·
                    rfl

theorem cell20_674279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_674279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674279 prefixEnd_674279 := by exact prefixLift 674279
  have htrace : WordTrace (prefixWord ++ tailWord_674279) baseStart_674279 baseEnd_674279 := by
    simpa [prefixWord, tailWord_674279, baseEnd_674279] using wordTrace_append hprefix tailTrace_674279
  have hstable : (prefixWord ++ tailWord_674279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674279).length < 2 ^ (prefixWord ++ tailWord_674279).sum := by decide
  have hdescent : baseEnd_674279 < baseStart_674279 := by decide
  rcases family_descends (prefixWord ++ tailWord_674279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674373 : List Nat := [1, 3, 1, 1, 1, 13]
def baseStart_674373 : Nat := 118140960795 + 674373 * 2 ^ 59
def prefixEnd_674373 : Nat := 4983230072969 + 3 ^ 40 * 674373 * 2
def baseEnd_674373 : Nat := 11400081956036057489255

theorem tailTrace_674373 : CollatzResearch.WordTrace tailWord_674373 prefixEnd_674373 11400081956036057489255 := by
  unfold tailWord_674373
  simp only [CollatzResearch.WordTrace]
  refine ⟨24596403985869269584059773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16397602657246179722706515 24596403985869269584059773)
  ·
    refine ⟨9223651494700976094022415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24596403985869269584059773 9223651494700976094022415)
    ·
      refine ⟨13835477242051464141033623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9223651494700976094022415 13835477242051464141033623)
      ·
        refine ⟨20753215863077196211550435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13835477242051464141033623 20753215863077196211550435)
        ·
          refine ⟨31129823794615794317325653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20753215863077196211550435 31129823794615794317325653)
          ·
            refine ⟨11400081956036057489255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31129823794615794317325653 11400081956036057489255)
            ·
              rfl

theorem cell20_674373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_674373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674373 prefixEnd_674373 := by exact prefixLift 674373
  have htrace : WordTrace (prefixWord ++ tailWord_674373) baseStart_674373 baseEnd_674373 := by
    simpa [prefixWord, tailWord_674373, baseEnd_674373] using wordTrace_append hprefix tailTrace_674373
  have hstable : (prefixWord ++ tailWord_674373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674373).length < 2 ^ (prefixWord ++ tailWord_674373).sum := by decide
  have hdescent : baseEnd_674373 < baseStart_674373 := by decide
  rcases family_descends (prefixWord ++ tailWord_674373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674493 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 2]
def baseStart_674493 : Nat := 118140960795 + 674493 * 2 ^ 59
def prefixEnd_674493 : Nat := 4983230072969 + 3 ^ 40 * 674493 * 2
def baseEnd_674493 : Nat := 307856984082786468209395

theorem tailTrace_674493 : CollatzResearch.WordTrace tailWord_674493 prefixEnd_674493 307856984082786468209395 := by
  unfold tailWord_674493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600780745434530078428133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16400520496956353385618755 24600780745434530078428133)
  ·
    refine ⟨4612646389768974389705275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24600780745434530078428133 4612646389768974389705275)
    ·
      refine ⟨6918969584653461584557913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612646389768974389705275 6918969584653461584557913)
      ·
        refine ⟨5189227188490096188418435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6918969584653461584557913 5189227188490096188418435)
        ·
          refine ⟨7783840782735144282627653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189227188490096188418435 7783840782735144282627653)
          ·
            refine ⟨1459470146762839552992685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7783840782735144282627653 1459470146762839552992685)
            ·
              refine ⟨547301305036064832372257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1459470146762839552992685 547301305036064832372257)
              ·
                refine ⟨410475978777048624279193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547301305036064832372257 410475978777048624279193)
                ·
                  refine ⟨307856984082786468209395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410475978777048624279193 307856984082786468209395)
                  ·
                    rfl

theorem cell20_674493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_674493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674493 prefixEnd_674493 := by exact prefixLift 674493
  have htrace : WordTrace (prefixWord ++ tailWord_674493) baseStart_674493 baseEnd_674493 := by
    simpa [prefixWord, tailWord_674493, baseEnd_674493] using wordTrace_append hprefix tailTrace_674493
  have hstable : (prefixWord ++ tailWord_674493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674493).length < 2 ^ (prefixWord ++ tailWord_674493).sum := by decide
  have hdescent : baseEnd_674493 < baseStart_674493 := by decide
  rcases family_descends (prefixWord ++ tailWord_674493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674504 : List Nat := [2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_674504 : Nat := 118140960795 + 674504 * 2 ^ 59
def prefixEnd_674504 : Nat := 4983230072969 + 3 ^ 40 * 674504 * 2
def baseEnd_674504 : Nat := 102620668260839772947561

theorem tailTrace_674504 : CollatzResearch.WordTrace tailWord_674504 prefixEnd_674504 102620668260839772947561 := by
  unfold tailWord_674504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300590974197339478539283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16400787965596452638052377 12300590974197339478539283)
  ·
    refine ⟨18450886461296009217808925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12300590974197339478539283 18450886461296009217808925)
    ·
      refine ⟨6919082422986003456678347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18450886461296009217808925 6919082422986003456678347)
      ·
        refine ⟨10378623634479005185017521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919082422986003456678347 10378623634479005185017521)
        ·
          refine ⟨7783967725859253888763141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10378623634479005185017521 7783967725859253888763141)
          ·
            refine ⟨1459493948598610104143089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7783967725859253888763141 1459493948598610104143089)
            ·
              refine ⟨1094620461448957578107317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459493948598610104143089 1094620461448957578107317)
              ·
                refine ⟨102620668260839772947561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094620461448957578107317 102620668260839772947561)
                ·
                  rfl

theorem cell20_674504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_674504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674504 prefixEnd_674504 := by exact prefixLift 674504
  have htrace : WordTrace (prefixWord ++ tailWord_674504) baseStart_674504 baseEnd_674504 := by
    simpa [prefixWord, tailWord_674504, baseEnd_674504] using wordTrace_append hprefix tailTrace_674504
  have hstable : (prefixWord ++ tailWord_674504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674504).length < 2 ^ (prefixWord ++ tailWord_674504).sum := by decide
  have hdescent : baseEnd_674504 < baseStart_674504 := by decide
  rcases family_descends (prefixWord ++ tailWord_674504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674611 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_674611 : Nat := 118140960795 + 674611 * 2 ^ 59
def prefixEnd_674611 : Nat := 4983230072969 + 3 ^ 40 * 674611 * 2
def baseEnd_674611 : Nat := 307910842498102502275579

theorem tailTrace_674611 : CollatzResearch.WordTrace tailWord_674611 prefixEnd_674611 307910842498102502275579 := by
  unfold tailWord_674611
  simp only [CollatzResearch.WordTrace]
  refine ⟨24605084559007036231223687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16403389706004690820815791 24605084559007036231223687)
  ·
    refine ⟨36907626838510554346835531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24605084559007036231223687 36907626838510554346835531)
    ·
      refine ⟨55361440257765831520253297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36907626838510554346835531 55361440257765831520253297)
      ·
        refine ⟨41521080193324373640189973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55361440257765831520253297 41521080193324373640189973)
        ·
          refine ⟨1946300634062080014383905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41521080193324373640189973 1946300634062080014383905)
          ·
            refine ⟨1459725475546560010787929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946300634062080014383905 1459725475546560010787929)
            ·
              refine ⟨1094794106659920008090947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459725475546560010787929 1094794106659920008090947)
              ·
                refine ⟨1642191159989880012136421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094794106659920008090947 1642191159989880012136421)
                ·
                  refine ⟨307910842498102502275579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642191159989880012136421 307910842498102502275579)
                  ·
                    rfl

theorem cell20_674611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_674611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674611 prefixEnd_674611 := by exact prefixLift 674611
  have htrace : WordTrace (prefixWord ++ tailWord_674611) baseStart_674611 baseEnd_674611 := by
    simpa [prefixWord, tailWord_674611, baseEnd_674611] using wordTrace_append hprefix tailTrace_674611
  have hstable : (prefixWord ++ tailWord_674611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674611).length < 2 ^ (prefixWord ++ tailWord_674611).sum := by decide
  have hdescent : baseEnd_674611 < baseStart_674611 := by decide
  rcases family_descends (prefixWord ++ tailWord_674611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674632 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_674632 : Nat := 118140960795 + 674632 * 2 ^ 59
def prefixEnd_674632 : Nat := 4983230072969 + 3 ^ 40 * 674632 * 2
def baseEnd_674632 : Nat := 307920427470319762575493

theorem tailTrace_674632 : CollatzResearch.WordTrace tailWord_674632 prefixEnd_674632 307920427470319762575493 := by
  unfold tailWord_674632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302925245965478408869075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16403900327953971211825433 12302925245965478408869075)
  ·
    refine ⟨18454387868948217613303613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12302925245965478408869075 18454387868948217613303613)
    ·
      refine ⟨6920395450855581604988855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18454387868948217613303613 6920395450855581604988855)
      ·
        refine ⟨10380593176283372407483283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920395450855581604988855 10380593176283372407483283)
        ·
          refine ⟨15570889764425058611224925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10380593176283372407483283 15570889764425058611224925)
          ·
            refine ⟨5839083661659396979209347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15570889764425058611224925 5839083661659396979209347)
            ·
              refine ⟨8758625492489095468814021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839083661659396979209347 8758625492489095468814021)
              ·
                refine ⟨1642242279841705400402629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8758625492489095468814021 1642242279841705400402629)
                ·
                  refine ⟨307920427470319762575493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642242279841705400402629 307920427470319762575493)
                  ·
                    rfl

theorem cell20_674632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_674632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674632 prefixEnd_674632 := by exact prefixLift 674632
  have htrace : WordTrace (prefixWord ++ tailWord_674632) baseStart_674632 baseEnd_674632 := by
    simpa [prefixWord, tailWord_674632, baseEnd_674632] using wordTrace_append hprefix tailTrace_674632
  have hstable : (prefixWord ++ tailWord_674632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674632).length < 2 ^ (prefixWord ++ tailWord_674632).sum := by decide
  have hdescent : baseEnd_674632 < baseStart_674632 := by decide
  rcases family_descends (prefixWord ++ tailWord_674632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674663 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_674663 : Nat := 118140960795 + 674663 * 2 ^ 59
def prefixEnd_674663 : Nat := 4983230072969 + 3 ^ 40 * 674663 * 2
def baseEnd_674663 : Nat := 307934576715021432542033

theorem tailTrace_674663 : CollatzResearch.WordTrace tailWord_674663 prefixEnd_674663 307934576715021432542033 := by
  unfold tailWord_674663
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606981154818649112116643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16404654103212432741411095 24606981154818649112116643)
  ·
    refine ⟨36910471732227973668174965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24606981154818649112116643 36910471732227973668174965)
    ·
      refine ⟨3460356724896372531391403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36910471732227973668174965 3460356724896372531391403)
      ·
        refine ⟨5190535087344558797087105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460356724896372531391403 5190535087344558797087105)
        ·
          refine ⟨3892901315508419097815329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190535087344558797087105 3892901315508419097815329)
          ·
            refine ⟨2919675986631314323361497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892901315508419097815329 2919675986631314323361497)
            ·
              refine ⟨2189756989973485742521123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919675986631314323361497 2189756989973485742521123)
              ·
                refine ⟨3284635484960228613781685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189756989973485742521123 3284635484960228613781685)
                ·
                  refine ⟨307934576715021432542033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284635484960228613781685 307934576715021432542033)
                  ·
                    rfl

theorem cell20_674663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_674663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674663 prefixEnd_674663 := by exact prefixLift 674663
  have htrace : WordTrace (prefixWord ++ tailWord_674663) baseStart_674663 baseEnd_674663 := by
    simpa [prefixWord, tailWord_674663, baseEnd_674663] using wordTrace_append hprefix tailTrace_674663
  have hstable : (prefixWord ++ tailWord_674663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674663).length < 2 ^ (prefixWord ++ tailWord_674663).sum := by decide
  have hdescent : baseEnd_674663 < baseStart_674663 := by decide
  rcases family_descends (prefixWord ++ tailWord_674663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674721 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 2]
def baseStart_674721 : Nat := 118140960795 + 674721 * 2 ^ 59
def prefixEnd_674721 : Nat := 4983230072969 + 3 ^ 40 * 674721 * 2
def baseEnd_674721 : Nat := 307961049495431008608463

theorem tailTrace_674721 : CollatzResearch.WordTrace tailWord_674721 prefixEnd_674721 307961049495431008608463 := by
  unfold tailWord_674721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609096588608525017728017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16406064392405683345152011 24609096588608525017728017)
  ·
    refine ⟨18456822441456393763296013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24609096588608525017728017 18456822441456393763296013)
    ·
      refine ⟨6921308415546147661236005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18456822441456393763296013 6921308415546147661236005)
      ·
        refine ⟨1297745327914902686481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6921308415546147661236005 1297745327914902686481751)
        ·
          refine ⟨1946617991872354029722627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297745327914902686481751 1946617991872354029722627)
          ·
            refine ⟨2919926987808531044583941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946617991872354029722627 2919926987808531044583941)
            ·
              refine ⟨547486310214099570859489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2919926987808531044583941 547486310214099570859489)
              ·
                refine ⟨410614732660574678144617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547486310214099570859489 410614732660574678144617)
                ·
                  refine ⟨307961049495431008608463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410614732660574678144617 307961049495431008608463)
                  ·
                    rfl

theorem cell20_674721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_674721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674721 prefixEnd_674721 := by exact prefixLift 674721
  have htrace : WordTrace (prefixWord ++ tailWord_674721) baseStart_674721 baseEnd_674721 := by
    simpa [prefixWord, tailWord_674721, baseEnd_674721] using wordTrace_append hprefix tailTrace_674721
  have hstable : (prefixWord ++ tailWord_674721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674721).length < 2 ^ (prefixWord ++ tailWord_674721).sum := by decide
  have hdescent : baseEnd_674721 < baseStart_674721 := by decide
  rcases family_descends (prefixWord ++ tailWord_674721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674746 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_674746 : Nat := 118140960795 + 674746 * 2 ^ 59
def prefixEnd_674746 : Nat := 4983230072969 + 3 ^ 40 * 674746 * 2
def baseEnd_674746 : Nat := 307972460176642032775027

theorem tailTrace_674746 : CollatzResearch.WordTrace tailWord_674746 prefixEnd_674746 307972460176642032775027 := by
  unfold tailWord_674746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152502103379488571847023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16406672275678636191592061 6152502103379488571847023)
  ·
    refine ⟨9228753155069232857770535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6152502103379488571847023 9228753155069232857770535)
    ·
      refine ⟨13843129732603849286655803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9228753155069232857770535 13843129732603849286655803)
      ·
        refine ⟨20764694598905773929983705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13843129732603849286655803 20764694598905773929983705)
        ·
          refine ⟨15573520949179330447487779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20764694598905773929983705 15573520949179330447487779)
          ·
            refine ⟨23360281423768995671231669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15573520949179330447487779 23360281423768995671231669)
            ·
              refine ⟨2190026383478343344177969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23360281423768995671231669 2190026383478343344177969)
              ·
                refine ⟨1642519787608757508133477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190026383478343344177969 1642519787608757508133477)
                ·
                  refine ⟨307972460176642032775027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642519787608757508133477 307972460176642032775027)
                  ·
                    rfl

theorem cell20_674746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_674746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674746 prefixEnd_674746 := by exact prefixLift 674746
  have htrace : WordTrace (prefixWord ++ tailWord_674746) baseStart_674746 baseEnd_674746 := by
    simpa [prefixWord, tailWord_674746, baseEnd_674746] using wordTrace_append hprefix tailTrace_674746
  have hstable : (prefixWord ++ tailWord_674746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674746).length < 2 ^ (prefixWord ++ tailWord_674746).sum := by decide
  have hdescent : baseEnd_674746 < baseStart_674746 := by decide
  rcases family_descends (prefixWord ++ tailWord_674746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674749 : List Nat := [1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_674749 : Nat := 118140960795 + 674749 * 2 ^ 59
def prefixEnd_674749 : Nat := 4983230072969 + 3 ^ 40 * 674749 * 2
def baseEnd_674749 : Nat := 102657943152795785225005

theorem tailTrace_674749 : CollatzResearch.WordTrace tailWord_674749 prefixEnd_674749 102657943152795785225005 := by
  unfold tailWord_674749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610117832507085799747301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16406745221671390533164867 24610117832507085799747301)
  ·
    refine ⟨4614397093595078587452619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24610117832507085799747301 4614397093595078587452619)
    ·
      refine ⟨6921595640392617881178929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614397093595078587452619 6921595640392617881178929)
      ·
        refine ⟨5191196730294463410884197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921595640392617881178929 5191196730294463410884197)
        ·
          refine ⟨973349386930211889540787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5191196730294463410884197 973349386930211889540787)
          ·
            refine ⟨1460024080395317834311181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973349386930211889540787 1460024080395317834311181)
            ·
              refine ⟨547509030148244187866693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1460024080395317834311181 547509030148244187866693)
              ·
                refine ⟨102657943152795785225005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547509030148244187866693 102657943152795785225005)
                ·
                  rfl

theorem cell20_674749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_674749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674749 prefixEnd_674749 := by exact prefixLift 674749
  have htrace : WordTrace (prefixWord ++ tailWord_674749) baseStart_674749 baseEnd_674749 := by
    simpa [prefixWord, tailWord_674749, baseEnd_674749] using wordTrace_append hprefix tailTrace_674749
  have hstable : (prefixWord ++ tailWord_674749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674749).length < 2 ^ (prefixWord ++ tailWord_674749).sum := by decide
  have hdescent : baseEnd_674749 < baseStart_674749 := by decide
  rcases family_descends (prefixWord ++ tailWord_674749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674763 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 2]
def baseStart_674763 : Nat := 118140960795 + 674763 * 2 ^ 59
def prefixEnd_674763 : Nat := 4983230072969 + 3 ^ 40 * 674763 * 2
def baseEnd_674763 : Nat := 307980219439865529208291

theorem tailTrace_674763 : CollatzResearch.WordTrace tailWord_674763 prefixEnd_674763 307980219439865529208291 := by
  unfold tailWord_674763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610628454456366190756943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16407085636304244127171295 24610628454456366190756943)
  ·
    refine ⟨36915942681684549286135415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24610628454456366190756943 36915942681684549286135415)
    ·
      refine ⟨55373914022526823929203123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36915942681684549286135415 55373914022526823929203123)
      ·
        refine ⟨83060871033790235893804685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55373914022526823929203123 83060871033790235893804685)
        ·
          refine ⟨31147826637671338460176757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83060871033790235893804685 31147826637671338460176757)
          ·
            refine ⟨2920108747281687980641571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31147826637671338460176757 2920108747281687980641571)
            ·
              refine ⟨4380163120922531970962357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920108747281687980641571 4380163120922531970962357)
              ·
                refine ⟨410640292586487372277721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4380163120922531970962357 410640292586487372277721)
                ·
                  refine ⟨307980219439865529208291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410640292586487372277721 307980219439865529208291)
                  ·
                    rfl

theorem cell20_674763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2].length) (baseStart_674763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674763 prefixEnd_674763 := by exact prefixLift 674763
  have htrace : WordTrace (prefixWord ++ tailWord_674763) baseStart_674763 baseEnd_674763 := by
    simpa [prefixWord, tailWord_674763, baseEnd_674763] using wordTrace_append hprefix tailTrace_674763
  have hstable : (prefixWord ++ tailWord_674763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674763).length < 2 ^ (prefixWord ++ tailWord_674763).sum := by decide
  have hdescent : baseEnd_674763 < baseStart_674763 := by decide
  rcases family_descends (prefixWord ++ tailWord_674763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674770 : List Nat := [3, 2, 2, 3, 1, 2, 7]
def baseStart_674770 : Nat := 118140960795 + 674770 * 2 ^ 59
def prefixEnd_674770 : Nat := 4983230072969 + 3 ^ 40 * 674770 * 2
def baseEnd_674770 : Nat := 34220379381178290663881

theorem tailTrace_674770 : CollatzResearch.WordTrace tailWord_674770 prefixEnd_674770 34220379381178290663881 := by
  unfold tailWord_674770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152720941357751596565441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16407255843620670924174509 6152720941357751596565441)
  ·
    refine ⟨4614540706018313697424081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6152720941357751596565441 4614540706018313697424081)
    ·
      refine ⟨3460905529513735273068061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614540706018313697424081 3460905529513735273068061)
      ·
        refine ⟨1297839573567650727400523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3460905529513735273068061 1297839573567650727400523)
        ·
          refine ⟨1946759360351476091100785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297839573567650727400523 1946759360351476091100785)
          ·
            refine ⟨1460069520263607068325589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946759360351476091100785 1460069520263607068325589)
            ·
              refine ⟨34220379381178290663881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1460069520263607068325589 34220379381178290663881)
              ·
                rfl

theorem cell20_674770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_674770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674770 prefixEnd_674770 := by exact prefixLift 674770
  have htrace : WordTrace (prefixWord ++ tailWord_674770) baseStart_674770 baseEnd_674770 := by
    simpa [prefixWord, tailWord_674770, baseEnd_674770] using wordTrace_append hprefix tailTrace_674770
  have hstable : (prefixWord ++ tailWord_674770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674770).length < 2 ^ (prefixWord ++ tailWord_674770).sum := by decide
  have hdescent : baseEnd_674770 < baseStart_674770 := by decide
  rcases family_descends (prefixWord ++ tailWord_674770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674773 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_674773 : Nat := 118140960795 + 674773 * 2 ^ 59
def prefixEnd_674773 : Nat := 4983230072969 + 3 ^ 40 * 674773 * 2
def baseEnd_674773 : Nat := 307984783712349938874917

theorem tailTrace_674773 : CollatzResearch.WordTrace tailWord_674773 prefixEnd_674773 307984783712349938874917 := by
  unfold tailWord_674773
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610993184420137898620973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16407328789613425265747315 24610993184420137898620973)
  ·
    refine ⟨9229122444157551711982865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24610993184420137898620973 9229122444157551711982865)
    ·
      refine ⟨6921841833118163783987149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9229122444157551711982865 6921841833118163783987149)
      ·
        refine ⟨2595690687419311418995181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6921841833118163783987149 2595690687419311418995181)
        ·
          refine ⟨973384007782241782123193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2595690687419311418995181 973384007782241782123193)
          ·
            refine ⟨730038005836681336592395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973384007782241782123193 730038005836681336592395)
            ·
              refine ⟨1095057008755022004888593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730038005836681336592395 1095057008755022004888593)
              ·
                refine ⟨821292756566266503666445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095057008755022004888593 821292756566266503666445)
                ·
                  refine ⟨307984783712349938874917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821292756566266503666445 307984783712349938874917)
                  ·
                    rfl

theorem cell20_674773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_674773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674773 prefixEnd_674773 := by exact prefixLift 674773
  have htrace : WordTrace (prefixWord ++ tailWord_674773) baseStart_674773 baseEnd_674773 := by
    simpa [prefixWord, tailWord_674773, baseEnd_674773] using wordTrace_append hprefix tailTrace_674773
  have hstable : (prefixWord ++ tailWord_674773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674773).length < 2 ^ (prefixWord ++ tailWord_674773).sum := by decide
  have hdescent : baseEnd_674773 < baseStart_674773 := by decide
  rcases family_descends (prefixWord ++ tailWord_674773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674777 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_674777 : Nat := 118140960795 + 674777 * 2 ^ 59
def prefixEnd_674777 : Nat := 4983230072969 + 3 ^ 40 * 674777 * 2
def baseEnd_674777 : Nat := 307986609421343702741567

theorem tailTrace_674777 : CollatzResearch.WordTrace tailWord_674777 prefixEnd_674777 307986609421343702741567 := by
  unfold tailWord_674777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611139076405646581766585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16407426050937097721177723 24611139076405646581766585)
  ·
    refine ⟨18458354307304234936324939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24611139076405646581766585 18458354307304234936324939)
    ·
      refine ⟨27687531460956352404487409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458354307304234936324939 27687531460956352404487409)
      ·
        refine ⟨20765648595717264303365557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27687531460956352404487409 20765648595717264303365557)
        ·
          refine ⟨1946779555848493528440521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20765648595717264303365557 1946779555848493528440521)
          ·
            refine ⟨1460084666886370146330391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946779555848493528440521 1460084666886370146330391)
            ·
              refine ⟨2190127000329555219495587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460084666886370146330391 2190127000329555219495587)
              ·
                refine ⟨3285190500494332829243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190127000329555219495587 3285190500494332829243381)
                ·
                  refine ⟨307986609421343702741567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285190500494332829243381 307986609421343702741567)
                  ·
                    rfl

theorem cell20_674777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_674777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674777 prefixEnd_674777 := by exact prefixLift 674777
  have htrace : WordTrace (prefixWord ++ tailWord_674777) baseStart_674777 baseEnd_674777 := by
    simpa [prefixWord, tailWord_674777, baseEnd_674777] using wordTrace_append hprefix tailTrace_674777
  have hstable : (prefixWord ++ tailWord_674777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674777).length < 2 ^ (prefixWord ++ tailWord_674777).sum := by decide
  have hdescent : baseEnd_674777 < baseStart_674777 := by decide
  rcases family_descends (prefixWord ++ tailWord_674777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674814 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_674814 : Nat := 118140960795 + 674814 * 2 ^ 59
def prefixEnd_674814 : Nat := 4983230072969 + 3 ^ 40 * 674814 * 2
def baseEnd_674814 : Nat := 308003497229536018508083

theorem tailTrace_674814 : CollatzResearch.WordTrace tailWord_674814 prefixEnd_674814 308003497229536018508083 := by
  unfold tailWord_674814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076561072158950237607937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16408325718181067933908997 3076561072158950237607937)
  ·
    refine ⟨2307420804119212678205953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3076561072158950237607937 2307420804119212678205953)
    ·
      refine ⟨1730565603089409508654465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2307420804119212678205953 1730565603089409508654465)
      ·
        refine ⟨1297924202317057131490849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1730565603089409508654465 1297924202317057131490849)
        ·
          refine ⟨973443151737792848618137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297924202317057131490849 973443151737792848618137)
          ·
            refine ⟨730082363803344636463603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973443151737792848618137 730082363803344636463603)
            ·
              refine ⟨1095123545705016954695405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730082363803344636463603 1095123545705016954695405)
              ·
                refine ⟨410671329639381358010777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095123545705016954695405 410671329639381358010777)
                ·
                  refine ⟨308003497229536018508083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410671329639381358010777 308003497229536018508083)
                  ·
                    rfl

theorem cell20_674814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_674814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674814 prefixEnd_674814 := by exact prefixLift 674814
  have htrace : WordTrace (prefixWord ++ tailWord_674814) baseStart_674814 baseEnd_674814 := by
    simpa [prefixWord, tailWord_674814, baseEnd_674814] using wordTrace_append hprefix tailTrace_674814
  have hstable : (prefixWord ++ tailWord_674814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674814).length < 2 ^ (prefixWord ++ tailWord_674814).sum := by decide
  have hdescent : baseEnd_674814 < baseStart_674814 := by decide
  rcases family_descends (prefixWord ++ tailWord_674814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674839 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_674839 : Nat := 118140960795 + 674839 * 2 ^ 59
def prefixEnd_674839 : Nat := 4983230072969 + 3 ^ 40 * 674839 * 2
def baseEnd_674839 : Nat := 308014907910747042674647

theorem tailTrace_674839 : CollatzResearch.WordTrace tailWord_674839 prefixEnd_674839 308014907910747042674647 := by
  unfold tailWord_674839
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613400402181031170523571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16408933601454020780349047 24613400402181031170523571)
  ·
    refine ⟨36920100603271546755785357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24613400402181031170523571 36920100603271546755785357)
    ·
      refine ⟨13845037726226830033419509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36920100603271546755785357 13845037726226830033419509)
      ·
        refine ⟨1297972286833765315633079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13845037726226830033419509 1297972286833765315633079)
        ·
          refine ⟨1946958430250647973449619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297972286833765315633079 1946958430250647973449619)
          ·
            refine ⟨2920437645375971960174429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946958430250647973449619 2920437645375971960174429)
            ·
              refine ⟨1095164117015989485065411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2920437645375971960174429 1095164117015989485065411)
              ·
                refine ⟨1642746175523984227598117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095164117015989485065411 1642746175523984227598117)
                ·
                  refine ⟨308014907910747042674647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642746175523984227598117 308014907910747042674647)
                  ·
                    rfl

theorem cell20_674839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_674839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674839 prefixEnd_674839 := by exact prefixLift 674839
  have htrace : WordTrace (prefixWord ++ tailWord_674839) baseStart_674839 baseEnd_674839 := by
    simpa [prefixWord, tailWord_674839, baseEnd_674839] using wordTrace_append hprefix tailTrace_674839
  have hstable : (prefixWord ++ tailWord_674839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674839).length < 2 ^ (prefixWord ++ tailWord_674839).sum := by decide
  have hdescent : baseEnd_674839 < baseStart_674839 := by decide
  rcases family_descends (prefixWord ++ tailWord_674839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674849 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_674849 : Nat := 118140960795 + 674849 * 2 ^ 59
def prefixEnd_674849 : Nat := 4983230072969 + 3 ^ 40 * 674849 * 2
def baseEnd_674849 : Nat := 308019472183231452341273

theorem tailTrace_674849 : CollatzResearch.WordTrace tailWord_674849 prefixEnd_674849 308019472183231452341273 := by
  unfold tailWord_674849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613765132144802878387601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16409176754763201918925067 24613765132144802878387601)
  ·
    refine ⟨18460323849108602158790701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24613765132144802878387601 18460323849108602158790701)
    ·
      refine ⟨6922621443415725809546513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18460323849108602158790701 6922621443415725809546513)
      ·
        refine ⟨5191966082561794357159885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6922621443415725809546513 5191966082561794357159885)
        ·
          refine ⟨1946987280960672883934957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5191966082561794357159885 1946987280960672883934957)
          ·
            refine ⟨730120230360252331475609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1946987280960672883934957 730120230360252331475609)
            ·
              refine ⟨547590172770189248606707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730120230360252331475609 547590172770189248606707)
              ·
                refine ⟨821385259155283872910061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547590172770189248606707 821385259155283872910061)
                ·
                  refine ⟨308019472183231452341273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821385259155283872910061 308019472183231452341273)
                  ·
                    rfl

theorem cell20_674849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_674849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674849 prefixEnd_674849 := by exact prefixLift 674849
  have htrace : WordTrace (prefixWord ++ tailWord_674849) baseStart_674849 baseEnd_674849 := by
    simpa [prefixWord, tailWord_674849, baseEnd_674849] using wordTrace_append hprefix tailTrace_674849
  have hstable : (prefixWord ++ tailWord_674849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674849).length < 2 ^ (prefixWord ++ tailWord_674849).sum := by decide
  have hdescent : baseEnd_674849 < baseStart_674849 := by decide
  rcases family_descends (prefixWord ++ tailWord_674849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674853 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_674853 : Nat := 118140960795 + 674853 * 2 ^ 59
def prefixEnd_674853 : Nat := 4983230072969 + 3 ^ 40 * 674853 * 2
def baseEnd_674853 : Nat := 308021297892225216207923

theorem tailTrace_674853 : CollatzResearch.WordTrace tailWord_674853 prefixEnd_674853 308021297892225216207923 := by
  unfold tailWord_674853
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613911024130311561533213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16409274016086874374355475 24613911024130311561533213)
  ·
    refine ⟨9230216634048866835574955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24613911024130311561533213 9230216634048866835574955)
    ·
      refine ⟨13845324951073300253362433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230216634048866835574955 13845324951073300253362433)
      ·
        refine ⟨10383993713304975190021825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845324951073300253362433 10383993713304975190021825)
        ·
          refine ⟨7787995284978731392516369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10383993713304975190021825 7787995284978731392516369)
          ·
            refine ⟨5840996463734048544387277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787995284978731392516369 5840996463734048544387277)
            ·
              refine ⟨2190373673900268204145229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5840996463734048544387277 2190373673900268204145229)
              ·
                refine ⟨821390127712600576554461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190373673900268204145229 821390127712600576554461)
                ·
                  refine ⟨308021297892225216207923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821390127712600576554461 308021297892225216207923)
                  ·
                    rfl

theorem cell20_674853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_674853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674853 prefixEnd_674853 := by exact prefixLift 674853
  have htrace : WordTrace (prefixWord ++ tailWord_674853) baseStart_674853 baseEnd_674853 := by
    simpa [prefixWord, tailWord_674853, baseEnd_674853] using wordTrace_append hprefix tailTrace_674853
  have hstable : (prefixWord ++ tailWord_674853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674853).length < 2 ^ (prefixWord ++ tailWord_674853).sum := by decide
  have hdescent : baseEnd_674853 < baseStart_674853 := by decide
  rcases family_descends (prefixWord ++ tailWord_674853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674874 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_674874 : Nat := 118140960795 + 674874 * 2 ^ 59
def prefixEnd_674874 : Nat := 4983230072969 + 3 ^ 40 * 674874 * 2
def baseEnd_674874 : Nat := 308030882864442476507837

theorem tailTrace_674874 : CollatzResearch.WordTrace tailWord_674874 prefixEnd_674874 308030882864442476507837 := by
  unfold tailWord_674874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153669239263558037011919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16409784638036154765365117 6153669239263558037011919)
  ·
    refine ⟨9230503858895337055517879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6153669239263558037011919 9230503858895337055517879)
    ·
      refine ⟨13845755788343005583276819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230503858895337055517879 13845755788343005583276819)
      ·
        refine ⟨20768633682514508374915229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13845755788343005583276819 20768633682514508374915229)
        ·
          refine ⟨7788237630942940640593211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20768633682514508374915229 7788237630942940640593211)
          ·
            refine ⟨11682356446414410960889817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788237630942940640593211 11682356446414410960889817)
            ·
              refine ⟨8761767334810808220667363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11682356446414410960889817 8761767334810808220667363)
              ·
                refine ⟨13142651002216212331001045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8761767334810808220667363 13142651002216212331001045)
                ·
                  refine ⟨308030882864442476507837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13142651002216212331001045 308030882864442476507837)
                  ·
                    rfl

theorem cell20_674874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_674874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674874 prefixEnd_674874 := by exact prefixLift 674874
  have htrace : WordTrace (prefixWord ++ tailWord_674874) baseStart_674874 baseEnd_674874 := by
    simpa [prefixWord, tailWord_674874, baseEnd_674874] using wordTrace_append hprefix tailTrace_674874
  have hstable : (prefixWord ++ tailWord_674874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674874).length < 2 ^ (prefixWord ++ tailWord_674874).sum := by decide
  have hdescent : baseEnd_674874 < baseStart_674874 := by decide
  rcases family_descends (prefixWord ++ tailWord_674874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674942 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_674942 : Nat := 118140960795 + 674942 * 2 ^ 59
def prefixEnd_674942 : Nat := 4983230072969 + 3 ^ 40 * 674942 * 2
def baseEnd_674942 : Nat := 308061919917336462240893

theorem tailTrace_674942 : CollatzResearch.WordTrace tailWord_674942 prefixEnd_674942 308061919917336462240893 := by
  unfold tailWord_674942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077144640100984970190385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16411438080538586507682053 3077144640100984970190385)
  ·
    refine ⟨2307858480075738727642789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3077144640100984970190385 2307858480075738727642789)
    ·
      refine ⟨432723465014201011433023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2307858480075738727642789 432723465014201011433023)
      ·
        refine ⟨649085197521301517149535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432723465014201011433023 649085197521301517149535)
        ·
          refine ⟨973627796281952275724303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649085197521301517149535 973627796281952275724303)
          ·
            refine ⟨1460441694422928413586455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973627796281952275724303 1460441694422928413586455)
            ·
              refine ⟨2190662541634392620379683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460441694422928413586455 2190662541634392620379683)
              ·
                refine ⟨3285993812451588930569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190662541634392620379683 3285993812451588930569525)
                ·
                  refine ⟨308061919917336462240893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285993812451588930569525 308061919917336462240893)
                  ·
                    rfl

theorem cell20_674942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_674942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674942 prefixEnd_674942 := by exact prefixLift 674942
  have htrace : WordTrace (prefixWord ++ tailWord_674942) baseStart_674942 baseEnd_674942 := by
    simpa [prefixWord, tailWord_674942, baseEnd_674942] using wordTrace_append hprefix tailTrace_674942
  have hstable : (prefixWord ++ tailWord_674942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674942).length < 2 ^ (prefixWord ++ tailWord_674942).sum := by decide
  have hdescent : baseEnd_674942 < baseStart_674942 := by decide
  rcases family_descends (prefixWord ++ tailWord_674942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674953 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 2]
def baseStart_674953 : Nat := 118140960795 + 674953 * 2 ^ 59
def prefixEnd_674953 : Nat := 4983230072969 + 3 ^ 40 * 674953 * 2
def baseEnd_674953 : Nat := 308066940617069312874181

theorem tailTrace_674953 : CollatzResearch.WordTrace tailWord_674953 prefixEnd_674953 308066940617069312874181 := by
  unfold tailWord_674953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617558323768028640173513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16411705549178685760115675 24617558323768028640173513)
  ·
    refine ⟨18463168742826021480130135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24617558323768028640173513 18463168742826021480130135)
    ·
      refine ⟨27694753114239032220195203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18463168742826021480130135 27694753114239032220195203)
      ·
        refine ⟨41542129671358548330292805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27694753114239032220195203 41542129671358548330292805)
        ·
          refine ⟨7789149313379727811929901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41542129671358548330292805 7789149313379727811929901)
          ·
            refine ⟨2920930992517397929473713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7789149313379727811929901 2920930992517397929473713)
            ·
              refine ⟨2190698244388048447105285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920930992517397929473713 2190698244388048447105285)
              ·
                refine ⟨410755920822759083832241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2190698244388048447105285 410755920822759083832241)
                ·
                  refine ⟨308066940617069312874181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410755920822759083832241 308066940617069312874181)
                  ·
                    rfl

theorem cell20_674953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_674953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674953 prefixEnd_674953 := by exact prefixLift 674953
  have htrace : WordTrace (prefixWord ++ tailWord_674953) baseStart_674953 baseEnd_674953 := by
    simpa [prefixWord, tailWord_674953, baseEnd_674953] using wordTrace_append hprefix tailTrace_674953
  have hstable : (prefixWord ++ tailWord_674953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674953).length < 2 ^ (prefixWord ++ tailWord_674953).sum := by decide
  have hdescent : baseEnd_674953 < baseStart_674953 := by decide
  rcases family_descends (prefixWord ++ tailWord_674953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674981 : List Nat := [1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_674981 : Nat := 118140960795 + 674981 * 2 ^ 59
def prefixEnd_674981 : Nat := 4983230072969 + 3 ^ 40 * 674981 * 2
def baseEnd_674981 : Nat := 102693240193341886646911

theorem tailTrace_674981 : CollatzResearch.WordTrace tailWord_674981 prefixEnd_674981 102693240193341886646911 := by
  unfold tailWord_674981
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618579567666589422192797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16412386378444392948128531 24618579567666589422192797)
  ·
    refine ⟨9231967337874971033322299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24618579567666589422192797 9231967337874971033322299)
    ·
      refine ⟨13847951006812456549983449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9231967337874971033322299 13847951006812456549983449)
      ·
        refine ⟨10385963255109342412487587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13847951006812456549983449 10385963255109342412487587)
        ·
          refine ⟨15578944882664013618731381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385963255109342412487587 15578944882664013618731381)
          ·
            refine ⟨1460526082749751276756067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15578944882664013618731381 1460526082749751276756067)
            ·
              refine ⟨2190789124124626915134101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460526082749751276756067 2190789124124626915134101)
              ·
                refine ⟨102693240193341886646911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2190789124124626915134101 102693240193341886646911)
                ·
                  rfl

theorem cell20_674981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_674981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674981 prefixEnd_674981 := by exact prefixLift 674981
  have htrace : WordTrace (prefixWord ++ tailWord_674981) baseStart_674981 baseEnd_674981 := by
    simpa [prefixWord, tailWord_674981, baseEnd_674981] using wordTrace_append hprefix tailTrace_674981
  have hstable : (prefixWord ++ tailWord_674981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674981).length < 2 ^ (prefixWord ++ tailWord_674981).sum := by decide
  have hdescent : baseEnd_674981 < baseStart_674981 := by decide
  rcases family_descends (prefixWord ++ tailWord_674981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674991 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 2]
def baseStart_674991 : Nat := 118140960795 + 674991 * 2 ^ 59
def prefixEnd_674991 : Nat := 4983230072969 + 3 ^ 40 * 674991 * 2
def baseEnd_674991 : Nat := 308084284852510069607359

theorem tailTrace_674991 : CollatzResearch.WordTrace tailWord_674991 prefixEnd_674991 308084284852510069607359 := by
  unfold tailWord_674991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618944297630361130056827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16412629531753574086704551 24618944297630361130056827)
  ·
    refine ⟨36928416446445541695085241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618944297630361130056827 36928416446445541695085241)
    ·
      refine ⟨27696312334834156271313931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36928416446445541695085241 27696312334834156271313931)
      ·
        refine ⟨41544468502251234406970897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27696312334834156271313931 41544468502251234406970897)
        ·
          refine ⟨31158351376688425805228173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41544468502251234406970897 31158351376688425805228173)
          ·
            refine ⟨11684381766258159676960565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31158351376688425805228173 11684381766258159676960565)
            ·
              refine ⟨1095410790586702469715053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11684381766258159676960565 1095410790586702469715053)
              ·
                refine ⟨410779046470013426143145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095410790586702469715053 410779046470013426143145)
                ·
                  refine ⟨308084284852510069607359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410779046470013426143145 308084284852510069607359)
                  ·
                    rfl

theorem cell20_674991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 2].length) (baseStart_674991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674991 prefixEnd_674991 := by exact prefixLift 674991
  have htrace : WordTrace (prefixWord ++ tailWord_674991) baseStart_674991 baseEnd_674991 := by
    simpa [prefixWord, tailWord_674991, baseEnd_674991] using wordTrace_append hprefix tailTrace_674991
  have hstable : (prefixWord ++ tailWord_674991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674991).length < 2 ^ (prefixWord ++ tailWord_674991).sum := by decide
  have hdescent : baseEnd_674991 < baseStart_674991 := by decide
  rcases family_descends (prefixWord ++ tailWord_674991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674995 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_674995 : Nat := 118140960795 + 674995 * 2 ^ 59
def prefixEnd_674995 : Nat := 4983230072969 + 3 ^ 40 * 674995 * 2
def baseEnd_674995 : Nat := 308086110561503833474009

theorem tailTrace_674995 : CollatzResearch.WordTrace tailWord_674995 prefixEnd_674995 308086110561503833474009 := by
  unfold tailWord_674995
  simp only [CollatzResearch.WordTrace]
  refine ⟨24619090189615869813202439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16412726793077246542134959 24619090189615869813202439)
  ·
    refine ⟨36928635284423804719803659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24619090189615869813202439 36928635284423804719803659)
    ·
      refine ⟨55392952926635707079705489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36928635284423804719803659 55392952926635707079705489)
      ·
        refine ⟨41544714694976780309779117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55392952926635707079705489 41544714694976780309779117)
        ·
          refine ⟨15579268010616292616167169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41544714694976780309779117 15579268010616292616167169)
          ·
            refine ⟨11684451007962219462125377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579268010616292616167169 11684451007962219462125377)
            ·
              refine ⟨8763338255971664596594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11684451007962219462125377 8763338255971664596594033)
              ·
                refine ⟨6572503691978748447445525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8763338255971664596594033 6572503691978748447445525)
                ·
                  refine ⟨308086110561503833474009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6572503691978748447445525 308086110561503833474009)
                  ·
                    rfl

theorem cell20_674995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_674995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_674995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_674995 prefixEnd_674995 := by exact prefixLift 674995
  have htrace : WordTrace (prefixWord ++ tailWord_674995) baseStart_674995 baseEnd_674995 := by
    simpa [prefixWord, tailWord_674995, baseEnd_674995] using wordTrace_append hprefix tailTrace_674995
  have hstable : (prefixWord ++ tailWord_674995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674995).length < 2 ^ (prefixWord ++ tailWord_674995).sum := by decide
  have hdescent : baseEnd_674995 < baseStart_674995 := by decide
  rcases family_descends (prefixWord ++ tailWord_674995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675008 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_675008 : Nat := 118140960795 + 675008 * 2 ^ 59
def prefixEnd_675008 : Nat := 4983230072969 + 3 ^ 40 * 675008 * 2
def baseEnd_675008 : Nat := 308092044115733566040623

theorem tailTrace_675008 : CollatzResearch.WordTrace tailWord_675008 prefixEnd_675008 308092044115733566040623 := by
  unfold tailWord_675008
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309782169284386516712839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16413042892379182022283785 12309782169284386516712839)
  ·
    refine ⟨18464673253926579775069259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12309782169284386516712839 18464673253926579775069259)
    ·
      refine ⟨27697009880889869662603889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18464673253926579775069259 27697009880889869662603889)
      ·
        refine ⟨20772757410667402246952917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27697009880889869662603889 20772757410667402246952917)
        ·
          refine ⟨486861501812517240162959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20772757410667402246952917 486861501812517240162959)
          ·
            refine ⟨730292252718775860244439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486861501812517240162959 730292252718775860244439)
            ·
              refine ⟨1095438379078163790366659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730292252718775860244439 1095438379078163790366659)
              ·
                refine ⟨1643157568617245685549989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095438379078163790366659 1643157568617245685549989)
                ·
                  refine ⟨308092044115733566040623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643157568617245685549989 308092044115733566040623)
                  ·
                    rfl

theorem cell20_675008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_675008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675008 prefixEnd_675008 := by exact prefixLift 675008
  have htrace : WordTrace (prefixWord ++ tailWord_675008) baseStart_675008 baseEnd_675008 := by
    simpa [prefixWord, tailWord_675008, baseEnd_675008] using wordTrace_append hprefix tailTrace_675008
  have hstable : (prefixWord ++ tailWord_675008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675008).length < 2 ^ (prefixWord ++ tailWord_675008).sum := by decide
  have hdescent : baseEnd_675008 < baseStart_675008 := by decide
  rcases family_descends (prefixWord ++ tailWord_675008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675014 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_675014 : Nat := 118140960795 + 675014 * 2 ^ 59
def prefixEnd_675014 : Nat := 4983230072969 + 3 ^ 40 * 675014 * 2
def baseEnd_675014 : Nat := 308094782679224211840599

theorem tailTrace_675014 : CollatzResearch.WordTrace tailWord_675014 prefixEnd_675014 308094782679224211840599 := by
  unfold tailWord_675014
  simp only [CollatzResearch.WordTrace]
  refine ⟨769368224267094876817003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16413188784364690705429397 769368224267094876817003)
  ·
    refine ⟨1154052336400642315225505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 769368224267094876817003 1154052336400642315225505)
    ·
      refine ⟨865539252300481736419129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154052336400642315225505 865539252300481736419129)
      ·
        refine ⟨649154439225361302314347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 865539252300481736419129 649154439225361302314347)
        ·
          refine ⟨973731658838041953471521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649154439225361302314347 973731658838041953471521)
          ·
            refine ⟨730298744128531465103641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973731658838041953471521 730298744128531465103641)
            ·
              refine ⟨547724058096398598827731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730298744128531465103641 547724058096398598827731)
              ·
                refine ⟨821586087144597898241597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547724058096398598827731 821586087144597898241597)
                ·
                  refine ⟨308094782679224211840599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821586087144597898241597 308094782679224211840599)
                  ·
                    rfl

theorem cell20_675014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_675014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675014 prefixEnd_675014 := by exact prefixLift 675014
  have htrace : WordTrace (prefixWord ++ tailWord_675014) baseStart_675014 baseEnd_675014 := by
    simpa [prefixWord, tailWord_675014, baseEnd_675014] using wordTrace_append hprefix tailTrace_675014
  have hstable : (prefixWord ++ tailWord_675014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675014).length < 2 ^ (prefixWord ++ tailWord_675014).sum := by decide
  have hdescent : baseEnd_675014 < baseStart_675014 := by decide
  rcases family_descends (prefixWord ++ tailWord_675014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675022 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_675022 : Nat := 118140960795 + 675022 * 2 ^ 59
def prefixEnd_675022 : Nat := 4983230072969 + 3 ^ 40 * 675022 * 2
def baseEnd_675022 : Nat := 308098434097211739573899

theorem tailTrace_675022 : CollatzResearch.WordTrace tailWord_675022 prefixEnd_675022 308098434097211739573899 := by
  unfold tailWord_675022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077509370064756678054415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16413383307012035616290213 3077509370064756678054415)
  ·
    refine ⟨4616264055097135017081623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3077509370064756678054415 4616264055097135017081623)
    ·
      refine ⟨6924396082645702525622435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616264055097135017081623 6924396082645702525622435)
      ·
        refine ⟨10386594123968553788433653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6924396082645702525622435 10386594123968553788433653)
        ·
          refine ⟨973743199122051917665655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10386594123968553788433653 973743199122051917665655)
          ·
            refine ⟨1460614798683077876498483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973743199122051917665655 1460614798683077876498483)
            ·
              refine ⟨2190922198024616814747725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460614798683077876498483 2190922198024616814747725)
              ·
                refine ⟨821595824259231305530397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190922198024616814747725 821595824259231305530397)
                ·
                  refine ⟨308098434097211739573899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821595824259231305530397 308098434097211739573899)
                  ·
                    rfl

theorem cell20_675022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_675022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675022 prefixEnd_675022 := by exact prefixLift 675022
  have htrace : WordTrace (prefixWord ++ tailWord_675022) baseStart_675022 baseEnd_675022 := by
    simpa [prefixWord, tailWord_675022, baseEnd_675022] using wordTrace_append hprefix tailTrace_675022
  have hstable : (prefixWord ++ tailWord_675022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675022).length < 2 ^ (prefixWord ++ tailWord_675022).sum := by decide
  have hdescent : baseEnd_675022 < baseStart_675022 := by decide
  rcases family_descends (prefixWord ++ tailWord_675022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675033 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_675033 : Nat := 118140960795 + 675033 * 2 ^ 59
def prefixEnd_675033 : Nat := 4983230072969 + 3 ^ 40 * 675033 * 2
def baseEnd_675033 : Nat := 308103454796944590207187

theorem tailTrace_675033 : CollatzResearch.WordTrace tailWord_675033 prefixEnd_675033 308103454796944590207187 := by
  unfold tailWord_675033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24620476163478202303085753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16413650775652134868723835 24620476163478202303085753)
  ·
    refine ⟨18465357122608651727314315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24620476163478202303085753 18465357122608651727314315)
    ·
      refine ⟨27698035683912977590971473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18465357122608651727314315 27698035683912977590971473)
      ·
        refine ⟨20773526762934733193228605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27698035683912977590971473 20773526762934733193228605)
        ·
          refine ⟨7790072536100524947460727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20773526762934733193228605 7790072536100524947460727)
          ·
            refine ⟨11685108804150787421191091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7790072536100524947460727 11685108804150787421191091)
            ·
              refine ⟨17527663206226181131786637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685108804150787421191091 17527663206226181131786637)
              ·
                refine ⟨6572873702334817924419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17527663206226181131786637 6572873702334817924419989)
                ·
                  refine ⟨308103454796944590207187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6572873702334817924419989 308103454796944590207187)
                  ·
                    rfl

theorem cell20_675033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_675033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675033 prefixEnd_675033 := by exact prefixLift 675033
  have htrace : WordTrace (prefixWord ++ tailWord_675033) baseStart_675033 baseEnd_675033 := by
    simpa [prefixWord, tailWord_675033, baseEnd_675033] using wordTrace_append hprefix tailTrace_675033
  have hstable : (prefixWord ++ tailWord_675033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675033).length < 2 ^ (prefixWord ++ tailWord_675033).sum := by decide
  have hdescent : baseEnd_675033 < baseStart_675033 := by decide
  rcases family_descends (prefixWord ++ tailWord_675033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675142 : List Nat := [6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_675142 : Nat := 118140960795 + 675142 * 2 ^ 59
def prefixEnd_675142 : Nat := 4983230072969 + 3 ^ 40 * 675142 * 2
def baseEnd_675142 : Nat := 102717735122341551857803

theorem tailTrace_675142 : CollatzResearch.WordTrace tailWord_675142 prefixEnd_675142 102717735122341551857803 := by
  unfold tailWord_675142
  simp only [CollatzResearch.WordTrace]
  refine ⟨769514116252603559962615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16416301146722209279202453 769514116252603559962615)
  ·
    refine ⟨1154271174378905339943923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 769514116252603559962615 1154271174378905339943923)
    ·
      refine ⟨1731406761568358009915885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154271174378905339943923 1731406761568358009915885)
      ·
        refine ⟨649277535588134253718457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1731406761568358009915885 649277535588134253718457)
        ·
          refine ⟨486958151691100690288843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649277535588134253718457 486958151691100690288843)
          ·
            refine ⟨730437227536651035433265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486958151691100690288843 730437227536651035433265)
            ·
              refine ⟨547827920652488276574949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730437227536651035433265 547827920652488276574949)
              ·
                refine ⟨102717735122341551857803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 547827920652488276574949 102717735122341551857803)
                ·
                  rfl

theorem cell20_675142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_675142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675142 prefixEnd_675142 := by exact prefixLift 675142
  have htrace : WordTrace (prefixWord ++ tailWord_675142) baseStart_675142 baseEnd_675142 := by
    simpa [prefixWord, tailWord_675142, baseEnd_675142] using wordTrace_append hprefix tailTrace_675142
  have hstable : (prefixWord ++ tailWord_675142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675142).length < 2 ^ (prefixWord ++ tailWord_675142).sum := by decide
  have hdescent : baseEnd_675142 < baseStart_675142 := by decide
  rcases family_descends (prefixWord ++ tailWord_675142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675171 : List Nat := [1, 1, 1, 5, 2, 4, 6]
def baseStart_675171 : Nat := 118140960795 + 675171 * 2 ^ 59
def prefixEnd_675171 : Nat := 4983230072969 + 3 ^ 40 * 675171 * 2
def baseEnd_675171 : Nat := 34240715750803271511847

theorem tailTrace_675171 : CollatzResearch.WordTrace tailWord_675171 prefixEnd_675171 34240715750803271511847 := by
  unfold tailWord_675171
  simp only [CollatzResearch.WordTrace]
  refine ⟨24625509436978251871609367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16417006291318834581072911 24625509436978251871609367)
  ·
    refine ⟨36938264155467377807414051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24625509436978251871609367 36938264155467377807414051)
    ·
      refine ⟨55407396233201066711121077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36938264155467377807414051 55407396233201066711121077)
      ·
        refine ⟨5194443396862600004167601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55407396233201066711121077 5194443396862600004167601)
        ·
          refine ⟨3895832547646950003125701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5194443396862600004167601 3895832547646950003125701)
          ·
            refine ⟨730468602683803125586069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3895832547646950003125701 730468602683803125586069)
            ·
              refine ⟨34240715750803271511847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 730468602683803125586069 34240715750803271511847)
              ·
                rfl

theorem cell20_675171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_675171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675171 prefixEnd_675171 := by exact prefixLift 675171
  have htrace : WordTrace (prefixWord ++ tailWord_675171) baseStart_675171 baseEnd_675171 := by
    simpa [prefixWord, tailWord_675171, baseEnd_675171] using wordTrace_append hprefix tailTrace_675171
  have hstable : (prefixWord ++ tailWord_675171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675171).length < 2 ^ (prefixWord ++ tailWord_675171).sum := by decide
  have hdescent : baseEnd_675171 < baseStart_675171 := by decide
  rcases family_descends (prefixWord ++ tailWord_675171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675181 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_675181 : Nat := 118140960795 + 675181 * 2 ^ 59
def prefixEnd_675181 : Nat := 4983230072969 + 3 ^ 40 * 675181 * 2
def baseEnd_675181 : Nat := 308171006029713853273249

theorem tailTrace_675181 : CollatzResearch.WordTrace tailWord_675181 prefixEnd_675181 308171006029713853273249 := by
  unfold tailWord_675181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24625874166942023579473397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16417249444628015719648931 24625874166942023579473397)
  ·
    refine ⟨2308675703150814710575631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24625874166942023579473397 2308675703150814710575631)
    ·
      refine ⟨3463013554726222065863447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308675703150814710575631 3463013554726222065863447)
      ·
        refine ⟨5194520332089333098795171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463013554726222065863447 5194520332089333098795171)
        ·
          refine ⟨7791780498133999648192757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194520332089333098795171 7791780498133999648192757)
          ·
            refine ⟨730479421700062467018071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7791780498133999648192757 730479421700062467018071)
            ·
              refine ⟨1095719132550093700527107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730479421700062467018071 1095719132550093700527107)
              ·
                refine ⟨1643578698825140550790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095719132550093700527107 1643578698825140550790661)
                ·
                  refine ⟨308171006029713853273249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643578698825140550790661 308171006029713853273249)
                  ·
                    rfl

theorem cell20_675181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_675181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675181 prefixEnd_675181 := by exact prefixLift 675181
  have htrace : WordTrace (prefixWord ++ tailWord_675181) baseStart_675181 baseEnd_675181 := by
    simpa [prefixWord, tailWord_675181, baseEnd_675181] using wordTrace_append hprefix tailTrace_675181
  have hstable : (prefixWord ++ tailWord_675181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675181).length < 2 ^ (prefixWord ++ tailWord_675181).sum := by decide
  have hdescent : baseEnd_675181 < baseStart_675181 := by decide
  rcases family_descends (prefixWord ++ tailWord_675181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675329 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 2]
def baseStart_675329 : Nat := 118140960795 + 675329 * 2 ^ 59
def prefixEnd_675329 : Nat := 4983230072969 + 3 ^ 40 * 675329 * 2
def baseEnd_675329 : Nat := 308238557262483116339311

theorem tailTrace_675329 : CollatzResearch.WordTrace tailWord_675329 prefixEnd_675329 308238557262483116339311 := by
  unfold tailWord_675329
  simp only [CollatzResearch.WordTrace]
  refine ⟨24631272170405844855861041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16420848113603896570574027 24631272170405844855861041)
  ·
    refine ⟨18473454127804383641895781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24631272170405844855861041 18473454127804383641895781)
    ·
      refine ⟨3463772648963321932855459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18473454127804383641895781 3463772648963321932855459)
      ·
        refine ⟨5195658973444982899283189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463772648963321932855459 5195658973444982899283189)
        ·
          refine ⟨487093028760467146807799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5195658973444982899283189 487093028760467146807799)
          ·
            refine ⟨730639543140700720211699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487093028760467146807799 730639543140700720211699)
            ·
              refine ⟨1095959314711051080317549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730639543140700720211699 1095959314711051080317549)
              ·
                refine ⟨410984743016644155119081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1095959314711051080317549 410984743016644155119081)
                ·
                  refine ⟨308238557262483116339311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410984743016644155119081 308238557262483116339311)
                  ·
                    rfl

theorem cell20_675329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_675329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675329 prefixEnd_675329 := by exact prefixLift 675329
  have htrace : WordTrace (prefixWord ++ tailWord_675329) baseStart_675329 baseEnd_675329 := by
    simpa [prefixWord, tailWord_675329, baseEnd_675329] using wordTrace_append hprefix tailTrace_675329
  have hstable : (prefixWord ++ tailWord_675329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675329).length < 2 ^ (prefixWord ++ tailWord_675329).sum := by decide
  have hdescent : baseEnd_675329 < baseStart_675329 := by decide
  rcases family_descends (prefixWord ++ tailWord_675329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675340 : List Nat := [2, 2, 1, 2, 6, 1, 6]
def baseStart_675340 : Nat := 118140960795 + 675340 * 2 ^ 59
def prefixEnd_675340 : Nat := 4983230072969 + 3 ^ 40 * 675340 * 2
def baseEnd_675340 : Nat := 34249286440246218552511

theorem tailTrace_675340 : CollatzResearch.WordTrace tailWord_675340 prefixEnd_675340 34249286440246218552511 := by
  unfold tailWord_675340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315836686682996867255737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16421115582243995823007649 12315836686682996867255737)
  ·
    refine ⟨9236877515012247650441803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12315836686682996867255737 9236877515012247650441803)
    ·
      refine ⟨13855316272518371475662705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236877515012247650441803 13855316272518371475662705)
      ·
        refine ⟨10391487204388778606747029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13855316272518371475662705 10391487204388778606747029)
        ·
          refine ⟨487100962705723997191267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10391487204388778606747029 487100962705723997191267)
          ·
            refine ⟨730651444058585995786901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487100962705723997191267 730651444058585995786901)
            ·
              refine ⟨34249286440246218552511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 730651444058585995786901 34249286440246218552511)
              ·
                rfl

theorem cell20_675340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_675340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675340 prefixEnd_675340 := by exact prefixLift 675340
  have htrace : WordTrace (prefixWord ++ tailWord_675340) baseStart_675340 baseEnd_675340 := by
    simpa [prefixWord, tailWord_675340, baseEnd_675340] using wordTrace_append hprefix tailTrace_675340
  have hstable : (prefixWord ++ tailWord_675340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675340).length < 2 ^ (prefixWord ++ tailWord_675340).sum := by decide
  have hdescent : baseEnd_675340 < baseStart_675340 := by decide
  rcases family_descends (prefixWord ++ tailWord_675340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675361 : List Nat := [1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_675361 : Nat := 118140960795 + 675361 * 2 ^ 59
def prefixEnd_675361 : Nat := 4983230072969 + 3 ^ 40 * 675361 * 2
def baseEnd_675361 : Nat := 102751054311477742424171

theorem tailTrace_675361 : CollatzResearch.WordTrace tailWord_675361 prefixEnd_675361 102751054311477742424171 := by
  unfold tailWord_675361
  simp only [CollatzResearch.WordTrace]
  refine ⟨24632439306289914321025937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16421626204193276214017291 24632439306289914321025937)
  ·
    refine ⟨18474329479717435740769453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24632439306289914321025937 18474329479717435740769453)
    ·
      refine ⟨6927873554894038402788545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18474329479717435740769453 6927873554894038402788545)
      ·
        refine ⟨5195905166170528802091409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6927873554894038402788545 5195905166170528802091409)
        ·
          refine ⟨3896928874627896601568557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195905166170528802091409 3896928874627896601568557)
          ·
            refine ⟨1461348327985461225588209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3896928874627896601568557 1461348327985461225588209)
            ·
              refine ⟨1096011245989095919191157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461348327985461225588209 1096011245989095919191157)
              ·
                refine ⟨102751054311477742424171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1096011245989095919191157 102751054311477742424171)
                ·
                  rfl

theorem cell20_675361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_675361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675361 prefixEnd_675361 := by exact prefixLift 675361
  have htrace : WordTrace (prefixWord ++ tailWord_675361) baseStart_675361 baseEnd_675361 := by
    simpa [prefixWord, tailWord_675361, baseEnd_675361] using wordTrace_append hprefix tailTrace_675361
  have hstable : (prefixWord ++ tailWord_675361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675361).length < 2 ^ (prefixWord ++ tailWord_675361).sum := by decide
  have hdescent : baseEnd_675361 < baseStart_675361 := by decide
  rcases family_descends (prefixWord ++ tailWord_675361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675392 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_675392 : Nat := 118140960795 + 675392 * 2 ^ 59
def prefixEnd_675392 : Nat := 4983230072969 + 3 ^ 40 * 675392 * 2
def baseEnd_675392 : Nat := 308267312179134897239053

theorem tailTrace_675392 : CollatzResearch.WordTrace tailWord_675392 prefixEnd_675392 308267312179134897239053 := by
  unfold tailWord_675392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316784984588803307702215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16422379979451737743602953 12316784984588803307702215)
  ·
    refine ⟨18475177476883204961553323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316784984588803307702215 18475177476883204961553323)
    ·
      refine ⟨27712766215324807442329985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18475177476883204961553323 27712766215324807442329985)
      ·
        refine ⟨20784574661493605581747489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27712766215324807442329985 20784574661493605581747489)
        ·
          refine ⟨15588430996120204186310617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20784574661493605581747489 15588430996120204186310617)
          ·
            refine ⟨11691323247090153139732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15588430996120204186310617 11691323247090153139732963)
            ·
              refine ⟨17536984870635229709599445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691323247090153139732963 17536984870635229709599445)
              ·
                refine ⟨411023082905513196318737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17536984870635229709599445 411023082905513196318737)
                ·
                  refine ⟨308267312179134897239053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411023082905513196318737 308267312179134897239053)
                  ·
                    rfl

theorem cell20_675392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_675392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675392 prefixEnd_675392 := by exact prefixLift 675392
  have htrace : WordTrace (prefixWord ++ tailWord_675392) baseStart_675392 baseEnd_675392 := by
    simpa [prefixWord, tailWord_675392, baseEnd_675392] using wordTrace_append hprefix tailTrace_675392
  have hstable : (prefixWord ++ tailWord_675392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675392).length < 2 ^ (prefixWord ++ tailWord_675392).sum := by decide
  have hdescent : baseEnd_675392 < baseStart_675392 := by decide
  rcases family_descends (prefixWord ++ tailWord_675392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675399 : List Nat := [1, 1, 4, 1, 6, 7]
def baseStart_675399 : Nat := 118140960795 + 675399 * 2 ^ 59
def prefixEnd_675399 : Nat := 4983230072969 + 3 ^ 40 * 675399 * 2
def baseEnd_675399 : Nat := 11417426191476814222433

theorem tailTrace_675399 : CollatzResearch.WordTrace tailWord_675399 prefixEnd_675399 11417426191476814222433 := by
  unfold tailWord_675399
  simp only [CollatzResearch.WordTrace]
  refine ⟨24633825280152246810909251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16422550186768164540606167 24633825280152246810909251)
  ·
    refine ⟨36950737920228370216363877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24633825280152246810909251 36950737920228370216363877)
    ·
      refine ⟨6928263360042819415568227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36950737920228370216363877 6928263360042819415568227)
      ·
        refine ⟨10392395040064229123352341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928263360042819415568227 10392395040064229123352341)
        ·
          refine ⟨487143517503010740157141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10392395040064229123352341 487143517503010740157141)
          ·
            refine ⟨11417426191476814222433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 487143517503010740157141 11417426191476814222433)
            ·
              rfl

theorem cell20_675399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 7].length) (baseStart_675399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675399 prefixEnd_675399 := by exact prefixLift 675399
  have htrace : WordTrace (prefixWord ++ tailWord_675399) baseStart_675399 baseEnd_675399 := by
    simpa [prefixWord, tailWord_675399, baseEnd_675399] using wordTrace_append hprefix tailTrace_675399
  have hstable : (prefixWord ++ tailWord_675399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675399).length < 2 ^ (prefixWord ++ tailWord_675399).sum := by decide
  have hdescent : baseEnd_675399 < baseStart_675399 := by decide
  rcases family_descends (prefixWord ++ tailWord_675399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675413 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_675413 : Nat := 118140960795 + 675413 * 2 ^ 59
def prefixEnd_675413 : Nat := 4983230072969 + 3 ^ 40 * 675413 * 2
def baseEnd_675413 : Nat := 308276897151352157538967

theorem tailTrace_675413 : CollatzResearch.WordTrace tailWord_675413 prefixEnd_675413 308276897151352157538967 := by
  unfold tailWord_675413
  simp only [CollatzResearch.WordTrace]
  refine ⟨24634335902101527201918893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16422890601401018134612595 24634335902101527201918893)
  ·
    refine ⟨9237875963288072700719585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24634335902101527201918893 9237875963288072700719585)
    ·
      refine ⟨6928406972466054525539689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9237875963288072700719585 6928406972466054525539689)
      ·
        refine ⟨5196305229349540894154767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6928406972466054525539689 5196305229349540894154767)
        ·
          refine ⟨7794457844024311341232151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196305229349540894154767 7794457844024311341232151)
          ·
            refine ⟨11691686766036467011848227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794457844024311341232151 11691686766036467011848227)
            ·
              refine ⟨17537530149054700517772341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11691686766036467011848227 17537530149054700517772341)
              ·
                refine ⟨1644143451473878173541157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17537530149054700517772341 1644143451473878173541157)
                ·
                  refine ⟨308276897151352157538967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644143451473878173541157 308276897151352157538967)
                  ·
                    rfl

theorem cell20_675413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_675413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675413 prefixEnd_675413 := by exact prefixLift 675413
  have htrace : WordTrace (prefixWord ++ tailWord_675413) baseStart_675413 baseEnd_675413 := by
    simpa [prefixWord, tailWord_675413, baseEnd_675413] using wordTrace_append hprefix tailTrace_675413
  have hstable : (prefixWord ++ tailWord_675413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675413).length < 2 ^ (prefixWord ++ tailWord_675413).sum := by decide
  have hdescent : baseEnd_675413 < baseStart_675413 := by decide
  rcases family_descends (prefixWord ++ tailWord_675413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675468 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_675468 : Nat := 118140960795 + 675468 * 2 ^ 59
def prefixEnd_675468 : Nat := 4983230072969 + 3 ^ 40 * 675468 * 2
def baseEnd_675468 : Nat := 308302000650016410705409

theorem tailTrace_675468 : CollatzResearch.WordTrace tailWord_675468 prefixEnd_675468 308302000650016410705409 := by
  unfold tailWord_675468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318170958451135797585529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16424227944601514396780705 12318170958451135797585529)
  ·
    refine ⟨9238628218838351848189147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12318170958451135797585529 9238628218838351848189147)
    ·
      refine ⟨13857942328257527772283721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9238628218838351848189147 13857942328257527772283721)
      ·
        refine ⟨10393456746193145829212791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13857942328257527772283721 10393456746193145829212791)
        ·
          refine ⟨15590185119289718743819187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393456746193145829212791 15590185119289718743819187)
          ·
            refine ⟨23385277678934578115728781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590185119289718743819187 23385277678934578115728781)
            ·
              refine ⟨8769479129600466793398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23385277678934578115728781 8769479129600466793398293)
              ·
                refine ⟨411069334200021880940545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8769479129600466793398293 411069334200021880940545)
                ·
                  refine ⟨308302000650016410705409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411069334200021880940545 308302000650016410705409)
                  ·
                    rfl

theorem cell20_675468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_675468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675468 prefixEnd_675468 := by exact prefixLift 675468
  have htrace : WordTrace (prefixWord ++ tailWord_675468) baseStart_675468 baseEnd_675468 := by
    simpa [prefixWord, tailWord_675468, baseEnd_675468] using wordTrace_append hprefix tailTrace_675468
  have hstable : (prefixWord ++ tailWord_675468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675468).length < 2 ^ (prefixWord ++ tailWord_675468).sum := by decide
  have hdescent : baseEnd_675468 < baseStart_675468 := by decide
  rcases family_descends (prefixWord ++ tailWord_675468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675492 : List Nat := [2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_675492 : Nat := 118140960795 + 675492 * 2 ^ 59
def prefixEnd_675492 : Nat := 4983230072969 + 3 ^ 40 * 675492 * 2
def baseEnd_675492 : Nat := 102770984967992997968437

theorem tailTrace_675492 : CollatzResearch.WordTrace tailWord_675492 prefixEnd_675492 102770984967992997968437 := by
  unfold tailWord_675492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318608634407661847022365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16424811512543549129363153 12318608634407661847022365)
  ·
    refine ⟨4619478237902873192633387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12318608634407661847022365 4619478237902873192633387)
    ·
      refine ⟨6929217356854309788950081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619478237902873192633387 6929217356854309788950081)
      ·
        refine ⟨5196913017640732341712561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6929217356854309788950081 5196913017640732341712561)
        ·
          refine ⟨3897684763230549256284421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5196913017640732341712561 3897684763230549256284421)
          ·
            refine ⟨730815893105727985553329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3897684763230549256284421 730815893105727985553329)
            ·
              refine ⟨548111919829295989164997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730815893105727985553329 548111919829295989164997)
              ·
                refine ⟨102770984967992997968437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548111919829295989164997 102770984967992997968437)
                ·
                  rfl

theorem cell20_675492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_675492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675492 prefixEnd_675492 := by exact prefixLift 675492
  have htrace : WordTrace (prefixWord ++ tailWord_675492) baseStart_675492 baseEnd_675492 := by
    simpa [prefixWord, tailWord_675492, baseEnd_675492] using wordTrace_append hprefix tailTrace_675492
  have hstable : (prefixWord ++ tailWord_675492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675492).length < 2 ^ (prefixWord ++ tailWord_675492).sum := by decide
  have hdescent : baseEnd_675492 < baseStart_675492 := by decide
  rcases family_descends (prefixWord ++ tailWord_675492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675503 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_675503 : Nat := 118140960795 + 675503 * 2 ^ 59
def prefixEnd_675503 : Nat := 4983230072969 + 3 ^ 40 * 675503 * 2
def baseEnd_675503 : Nat := 308317975603711844538599

theorem tailTrace_675503 : CollatzResearch.WordTrace tailWord_675503 prefixEnd_675503 308317975603711844538599 := by
  unfold tailWord_675503
  simp only [CollatzResearch.WordTrace]
  refine ⟨24637618471775472572695163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16425078981183648381796775 24637618471775472572695163)
  ·
    refine ⟨36956427707663208859042745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24637618471775472572695163 36956427707663208859042745)
    ·
      refine ⟨27717320780747406644282059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36956427707663208859042745 27717320780747406644282059)
      ·
        refine ⟨41575981171121109966423089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27717320780747406644282059 41575981171121109966423089)
        ·
          refine ⟨31181985878340832474817317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41575981171121109966423089 31181985878340832474817317)
          ·
            refine ⟨5846622352188906089028247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31181985878340832474817317 5846622352188906089028247)
            ·
              refine ⟨8769933528283359133542371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846622352188906089028247 8769933528283359133542371)
              ·
                refine ⟨13154900292425038700313557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769933528283359133542371 13154900292425038700313557)
                ·
                  refine ⟨308317975603711844538599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13154900292425038700313557 308317975603711844538599)
                  ·
                    rfl

theorem cell20_675503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_675503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675503 prefixEnd_675503 := by exact prefixLift 675503
  have htrace : WordTrace (prefixWord ++ tailWord_675503) baseStart_675503 baseEnd_675503 := by
    simpa [prefixWord, tailWord_675503, baseEnd_675503] using wordTrace_append hprefix tailTrace_675503
  have hstable : (prefixWord ++ tailWord_675503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675503).length < 2 ^ (prefixWord ++ tailWord_675503).sum := by decide
  have hdescent : baseEnd_675503 < baseStart_675503 := by decide
  rcases family_descends (prefixWord ++ tailWord_675503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675520 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_675520 : Nat := 118140960795 + 675520 * 2 ^ 59
def prefixEnd_675520 : Nat := 4983230072969 + 3 ^ 40 * 675520 * 2
def baseEnd_675520 : Nat := 308325734866935340971863

theorem tailTrace_675520 : CollatzResearch.WordTrace tailWord_675520 prefixEnd_675520 308325734866935340971863 := by
  unfold tailWord_675520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319119256356942238032007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16425492341809256317376009 12319119256356942238032007)
  ·
    refine ⟨18478678884535413357048011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12319119256356942238032007 18478678884535413357048011)
    ·
      refine ⟨27718018326803120035572017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18478678884535413357048011 27718018326803120035572017)
      ·
        refine ⟨20788513745102340026679013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27718018326803120035572017 20788513745102340026679013)
        ·
          refine ⟨3897846327206688755002315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20788513745102340026679013 3897846327206688755002315)
          ·
            refine ⟨5846769490810033132503473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897846327206688755002315 5846769490810033132503473)
            ·
              refine ⟨4385077118107524849377605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846769490810033132503473 4385077118107524849377605)
              ·
                refine ⟨822201959645160909258301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4385077118107524849377605 822201959645160909258301)
                ·
                  refine ⟨308325734866935340971863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822201959645160909258301 308325734866935340971863)
                  ·
                    rfl

theorem cell20_675520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_675520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675520 prefixEnd_675520 := by exact prefixLift 675520
  have htrace : WordTrace (prefixWord ++ tailWord_675520) baseStart_675520 baseEnd_675520 := by
    simpa [prefixWord, tailWord_675520, baseEnd_675520] using wordTrace_append hprefix tailTrace_675520
  have hstable : (prefixWord ++ tailWord_675520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675520).length < 2 ^ (prefixWord ++ tailWord_675520).sum := by decide
  have hdescent : baseEnd_675520 < baseStart_675520 := by decide
  rcases family_descends (prefixWord ++ tailWord_675520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675533 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_675533 : Nat := 118140960795 + 675533 * 2 ^ 59
def prefixEnd_675533 : Nat := 4983230072969 + 3 ^ 40 * 675533 * 2
def baseEnd_675533 : Nat := 308331668421165073538477

theorem tailTrace_675533 : CollatzResearch.WordTrace tailWord_675533 prefixEnd_675533 308331668421165073538477 := by
  unfold tailWord_675533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24638712661666787696287253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16425808441111191797524835 24638712661666787696287253)
  ·
    refine ⟨1154939656015630673263465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24638712661666787696287253 1154939656015630673263465)
    ·
      refine ⟨866204742011723004947599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154939656015630673263465 866204742011723004947599)
      ·
        refine ⟨1299307113017584507421399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866204742011723004947599 1299307113017584507421399)
        ·
          refine ⟨1948960669526376761132099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299307113017584507421399 1948960669526376761132099)
          ·
            refine ⟨2923441004289565141698149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948960669526376761132099 2923441004289565141698149)
            ·
              refine ⟨548145188304293464068403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2923441004289565141698149 548145188304293464068403)
              ·
                refine ⟨822217782456440196102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548145188304293464068403 822217782456440196102605)
                ·
                  refine ⟨308331668421165073538477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822217782456440196102605 308331668421165073538477)
                  ·
                    rfl

theorem cell20_675533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_675533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675533 prefixEnd_675533 := by exact prefixLift 675533
  have htrace : WordTrace (prefixWord ++ tailWord_675533) baseStart_675533 baseEnd_675533 := by
    simpa [prefixWord, tailWord_675533, baseEnd_675533] using wordTrace_append hprefix tailTrace_675533
  have hstable : (prefixWord ++ tailWord_675533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675533).length < 2 ^ (prefixWord ++ tailWord_675533).sum := by decide
  have hdescent : baseEnd_675533 < baseStart_675533 := by decide
  rcases family_descends (prefixWord ++ tailWord_675533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675537 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_675537 : Nat := 118140960795 + 675537 * 2 ^ 59
def prefixEnd_675537 : Nat := 4983230072969 + 3 ^ 40 * 675537 * 2
def baseEnd_675537 : Nat := 308333494130158837405127

theorem tailTrace_675537 : CollatzResearch.WordTrace tailWord_675537 prefixEnd_675537 308333494130158837405127 := by
  unfold tailWord_675537
  simp only [CollatzResearch.WordTrace]
  refine ⟨24638858553652296379432865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16425905702434864252955243 24638858553652296379432865)
  ·
    refine ⟨18479143915239222284574649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24638858553652296379432865 18479143915239222284574649)
    ·
      refine ⟨13859357936429416713430987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18479143915239222284574649 13859357936429416713430987)
      ·
        refine ⟨20789036904644125070146481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859357936429416713430987 20789036904644125070146481)
        ·
          refine ⟨15591777678483093802609861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20789036904644125070146481 15591777678483093802609861)
          ·
            refine ⟨2923458314715580087989349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15591777678483093802609861 2923458314715580087989349)
            ·
              refine ⟨548148434009171266498003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2923458314715580087989349 548148434009171266498003)
              ·
                refine ⟨822222651013756899747005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548148434009171266498003 822222651013756899747005)
                ·
                  refine ⟨308333494130158837405127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822222651013756899747005 308333494130158837405127)
                  ·
                    rfl

theorem cell20_675537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_675537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675537 prefixEnd_675537 := by exact prefixLift 675537
  have htrace : WordTrace (prefixWord ++ tailWord_675537) baseStart_675537 baseEnd_675537 := by
    simpa [prefixWord, tailWord_675537, baseEnd_675537] using wordTrace_append hprefix tailTrace_675537
  have hstable : (prefixWord ++ tailWord_675537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675537).length < 2 ^ (prefixWord ++ tailWord_675537).sum := by decide
  have hdescent : baseEnd_675537 < baseStart_675537 := by decide
  rcases family_descends (prefixWord ++ tailWord_675537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675596 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_675596 : Nat := 118140960795 + 675596 * 2 ^ 59
def prefixEnd_675596 : Nat := 4983230072969 + 3 ^ 40 * 675596 * 2
def baseEnd_675596 : Nat := 308360423337816854438219

theorem tailTrace_675596 : CollatzResearch.WordTrace tailWord_675596 prefixEnd_675596 308360423337816854438219 := by
  unfold tailWord_675596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320505230219274727915321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16427340306959032970553761 12320505230219274727915321)
  ·
    refine ⟨9240378922664456045936491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12320505230219274727915321 9240378922664456045936491)
    ·
      refine ⟨13860568383996684068904737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9240378922664456045936491 13860568383996684068904737)
      ·
        refine ⟨10395426287997513051678553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13860568383996684068904737 10395426287997513051678553)
        ·
          refine ⟨7796569715998134788758915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395426287997513051678553 7796569715998134788758915)
          ·
            refine ⟨11694854573997202183138373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796569715998134788758915 11694854573997202183138373)
            ·
              refine ⟨2192785232624475409338445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11694854573997202183138373 2192785232624475409338445)
              ·
                refine ⟨822294462234178278501917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2192785232624475409338445 822294462234178278501917)
                ·
                  refine ⟨308360423337816854438219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822294462234178278501917 308360423337816854438219)
                  ·
                    rfl

theorem cell20_675596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_675596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675596 prefixEnd_675596 := by exact prefixLift 675596
  have htrace : WordTrace (prefixWord ++ tailWord_675596) baseStart_675596 baseEnd_675596 := by
    simpa [prefixWord, tailWord_675596, baseEnd_675596] using wordTrace_append hprefix tailTrace_675596
  have hstable : (prefixWord ++ tailWord_675596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675596).length < 2 ^ (prefixWord ++ tailWord_675596).sum := by decide
  have hdescent : baseEnd_675596 < baseStart_675596 := by decide
  rcases family_descends (prefixWord ++ tailWord_675596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675634 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_675634 : Nat := 118140960795 + 675634 * 2 ^ 59
def prefixEnd_675634 : Nat := 4983230072969 + 3 ^ 40 * 675634 * 2
def baseEnd_675634 : Nat := 308377767573257611171397

theorem tailTrace_675634 : CollatzResearch.WordTrace tailWord_675634 prefixEnd_675634 308377767573257611171397 := by
  unfold tailWord_675634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160599108575220486428489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16428264289533921297142637 6160599108575220486428489)
  ·
    refine ⟨4620449331431415364821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6160599108575220486428489 4620449331431415364821367)
    ·
      refine ⟨6930673997147123047232051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620449331431415364821367 6930673997147123047232051)
      ·
        refine ⟨10396010995720684570848077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930673997147123047232051 10396010995720684570848077)
        ·
          refine ⟨3898504123395256714068029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10396010995720684570848077 3898504123395256714068029)
          ·
            refine ⟨1461939046273221267775511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3898504123395256714068029 1461939046273221267775511)
            ·
              refine ⟨2192908569409831901663267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461939046273221267775511 2192908569409831901663267)
              ·
                refine ⟨3289362854114747852494901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192908569409831901663267 3289362854114747852494901)
                ·
                  refine ⟨308377767573257611171397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3289362854114747852494901 308377767573257611171397)
                  ·
                    rfl

theorem cell20_675634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_675634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675634 prefixEnd_675634 := by exact prefixLift 675634
  have htrace : WordTrace (prefixWord ++ tailWord_675634) baseStart_675634 baseEnd_675634 := by
    simpa [prefixWord, tailWord_675634, baseEnd_675634] using wordTrace_append hprefix tailTrace_675634
  have hstable : (prefixWord ++ tailWord_675634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675634).length < 2 ^ (prefixWord ++ tailWord_675634).sum := by decide
  have hdescent : baseEnd_675634 < baseStart_675634 := by decide
  rcases family_descends (prefixWord ++ tailWord_675634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675651 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_675651 : Nat := 118140960795 + 675651 * 2 ^ 59
def prefixEnd_675651 : Nat := 4983230072969 + 3 ^ 40 * 675651 * 2
def baseEnd_675651 : Nat := 308385526836481107604661

theorem tailTrace_675651 : CollatzResearch.WordTrace tailWord_675651 prefixEnd_675651 308385526836481107604661 := by
  unfold tailWord_675651
  simp only [CollatzResearch.WordTrace]
  refine ⟨24643016475239293849082807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16428677650159529232721871 24643016475239293849082807)
  ·
    refine ⟨36964524712858940773624211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24643016475239293849082807 36964524712858940773624211)
    ·
      refine ⟨55446787069288411160436317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36964524712858940773624211 55446787069288411160436317)
      ·
        refine ⟨20792545150983154185163619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55446787069288411160436317 20792545150983154185163619)
        ·
          refine ⟨31188817726474731277745429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20792545150983154185163619 31188817726474731277745429)
          ·
            refine ⟨1461975830928503028644317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31188817726474731277745429 1461975830928503028644317)
            ·
              refine ⟨548240936598188635741619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1461975830928503028644317 548240936598188635741619)
              ·
                refine ⟨822361404897282953612429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548240936598188635741619 822361404897282953612429)
                ·
                  refine ⟨308385526836481107604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822361404897282953612429 308385526836481107604661)
                  ·
                    rfl

theorem cell20_675651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_675651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675651 prefixEnd_675651 := by exact prefixLift 675651
  have htrace : WordTrace (prefixWord ++ tailWord_675651) baseStart_675651 baseEnd_675651 := by
    simpa [prefixWord, tailWord_675651, baseEnd_675651] using wordTrace_append hprefix tailTrace_675651
  have hstable : (prefixWord ++ tailWord_675651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675651).length < 2 ^ (prefixWord ++ tailWord_675651).sum := by decide
  have hdescent : baseEnd_675651 < baseStart_675651 := by decide
  rcases family_descends (prefixWord ++ tailWord_675651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675661 : List Nat := [1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_675661 : Nat := 118140960795 + 675661 * 2 ^ 59
def prefixEnd_675661 : Nat := 4983230072969 + 3 ^ 40 * 675661 * 2
def baseEnd_675661 : Nat := 102796697036321839090429

theorem tailTrace_675661 : CollatzResearch.WordTrace tailWord_675661 prefixEnd_675661 102796697036321839090429 := by
  unfold tailWord_675661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24643381205203065556946837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16428920803468710371297891 24643381205203065556946837)
  ·
    refine ⟨1155158493993893697981883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24643381205203065556946837 1155158493993893697981883)
    ·
      refine ⟨1732737740990840546972825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155158493993893697981883 1732737740990840546972825)
      ·
        refine ⟨1299553305743130410229619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732737740990840546972825 1299553305743130410229619)
        ·
          refine ⟨1949329958614695615344429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299553305743130410229619 1949329958614695615344429)
          ·
            refine ⟨730998734480510855754161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1949329958614695615344429 730998734480510855754161)
            ·
              refine ⟨548249050860383141815621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730998734480510855754161 548249050860383141815621)
              ·
                refine ⟨102796697036321839090429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548249050860383141815621 102796697036321839090429)
                ·
                  rfl

theorem cell20_675661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_675661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675661 prefixEnd_675661 := by exact prefixLift 675661
  have htrace : WordTrace (prefixWord ++ tailWord_675661) baseStart_675661 baseEnd_675661 := by
    simpa [prefixWord, tailWord_675661, baseEnd_675661] using wordTrace_append hprefix tailTrace_675661
  have hstable : (prefixWord ++ tailWord_675661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675661).length < 2 ^ (prefixWord ++ tailWord_675661).sum := by decide
  have hdescent : baseEnd_675661 < baseStart_675661 := by decide
  rcases family_descends (prefixWord ++ tailWord_675661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675665 : List Nat := [1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_675665 : Nat := 118140960795 + 675665 * 2 ^ 59
def prefixEnd_675665 : Nat := 4983230072969 + 3 ^ 40 * 675665 * 2
def baseEnd_675665 : Nat := 102797305605986427045979

theorem tailTrace_675665 : CollatzResearch.WordTrace tailWord_675665 prefixEnd_675665 102797305605986427045979 := by
  unfold tailWord_675665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24643527097188574240092449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16429018064792382826728299 24643527097188574240092449)
  ·
    refine ⟨18482645322891430680069337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24643527097188574240092449 18482645322891430680069337)
    ·
      refine ⟨13861983992168573010052003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18482645322891430680069337 13861983992168573010052003)
      ·
        refine ⟨20792975988252859515078005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13861983992168573010052003 20792975988252859515078005)
        ·
          refine ⟨1949341498898705579538563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20792975988252859515078005 1949341498898705579538563)
          ·
            refine ⟨2924012248348058369307845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949341498898705579538563 2924012248348058369307845)
            ·
              refine ⟨548252296565260944245221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2924012248348058369307845 548252296565260944245221)
              ·
                refine ⟨102797305605986427045979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548252296565260944245221 102797305605986427045979)
                ·
                  rfl

theorem cell20_675665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_675665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675665 prefixEnd_675665 := by exact prefixLift 675665
  have htrace : WordTrace (prefixWord ++ tailWord_675665) baseStart_675665 baseEnd_675665 := by
    simpa [prefixWord, tailWord_675665, baseEnd_675665] using wordTrace_append hprefix tailTrace_675665
  have hstable : (prefixWord ++ tailWord_675665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675665).length < 2 ^ (prefixWord ++ tailWord_675665).sum := by decide
  have hdescent : baseEnd_675665 < baseStart_675665 := by decide
  rcases family_descends (prefixWord ++ tailWord_675665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675702 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_675702 : Nat := 118140960795 + 675702 * 2 ^ 59
def prefixEnd_675702 : Nat := 4983230072969 + 3 ^ 40 * 675702 * 2
def baseEnd_675702 : Nat := 308408804626151596904453

theorem tailTrace_675702 : CollatzResearch.WordTrace tailWord_675702 prefixEnd_675702 308408804626151596904453 := by
  unfold tailWord_675702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540304787378408097449335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16429917732036353039459573 1540304787378408097449335)
  ·
    refine ⟨2310457181067612146174003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1540304787378408097449335 2310457181067612146174003)
    ·
      refine ⟨3465685771601418219261005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310457181067612146174003 3465685771601418219261005)
      ·
        refine ⟨1299632164350531832222877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3465685771601418219261005 1299632164350531832222877)
        ·
          refine ⟨487362061631449437083579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1299632164350531832222877 487362061631449437083579)
          ·
            refine ⟨731043092447174155625369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487362061631449437083579 731043092447174155625369)
            ·
              refine ⟨548282319335380616719027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731043092447174155625369 548282319335380616719027)
              ·
                refine ⟨822423479003070925078541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548282319335380616719027 822423479003070925078541)
                ·
                  refine ⟨308408804626151596904453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822423479003070925078541 308408804626151596904453)
                  ·
                    rfl

theorem cell20_675702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_675702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675702 prefixEnd_675702 := by exact prefixLift 675702
  have htrace : WordTrace (prefixWord ++ tailWord_675702) baseStart_675702 baseEnd_675702 := by
    simpa [prefixWord, tailWord_675702, baseEnd_675702] using wordTrace_append hprefix tailTrace_675702
  have hstable : (prefixWord ++ tailWord_675702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675702).length < 2 ^ (prefixWord ++ tailWord_675702).sum := by decide
  have hdescent : baseEnd_675702 < baseStart_675702 := by decide
  rcases family_descends (prefixWord ++ tailWord_675702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675748 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_675748 : Nat := 118140960795 + 675748 * 2 ^ 59
def prefixEnd_675748 : Nat := 4983230072969 + 3 ^ 40 * 675748 * 2
def baseEnd_675748 : Nat := 308429800279579881370931

theorem tailTrace_675748 : CollatzResearch.WordTrace tailWord_675748 prefixEnd_675748 308429800279579881370931 := by
  unfold tailWord_675748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323277177943939707681949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16431036237258586276909265 12323277177943939707681949)
  ·
    refine ⟨4621228941728977390380731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12323277177943939707681949 4621228941728977390380731)
    ·
      refine ⟨6931843412593466085571097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621228941728977390380731 6931843412593466085571097)
      ·
        refine ⟨5198882559445099564178323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6931843412593466085571097 5198882559445099564178323)
        ·
          refine ⟨7798323839167649346267485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198882559445099564178323 7798323839167649346267485)
          ·
            refine ⟨2924371439687868504850307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7798323839167649346267485 2924371439687868504850307)
            ·
              refine ⟨4386557159531802757275461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924371439687868504850307 4386557159531802757275461)
              ·
                refine ⟨822479467412213016989149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4386557159531802757275461 822479467412213016989149)
                ·
                  refine ⟨308429800279579881370931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822479467412213016989149 308429800279579881370931)
                  ·
                    rfl

theorem cell20_675748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_675748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675748 prefixEnd_675748 := by exact prefixLift 675748
  have htrace : WordTrace (prefixWord ++ tailWord_675748) baseStart_675748 baseEnd_675748 := by
    simpa [prefixWord, tailWord_675748, baseEnd_675748] using wordTrace_append hprefix tailTrace_675748
  have hstable : (prefixWord ++ tailWord_675748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675748).length < 2 ^ (prefixWord ++ tailWord_675748).sum := by decide
  have hdescent : baseEnd_675748 < baseStart_675748 := by decide
  rcases family_descends (prefixWord ++ tailWord_675748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675751 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 2]
def baseStart_675751 : Nat := 118140960795 + 675751 * 2 ^ 59
def prefixEnd_675751 : Nat := 4983230072969 + 3 ^ 40 * 675751 * 2
def baseEnd_675751 : Nat := 308431169561325204270919

theorem tailTrace_675751 : CollatzResearch.WordTrace tailWord_675751 prefixEnd_675751 308431169561325204270919 := by
  unfold tailWord_675751
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646663774877010927723107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16431109183251340618482071 24646663774877010927723107)
  ·
    refine ⟨36969995662315516391584661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24646663774877010927723107 36969995662315516391584661)
    ·
      refine ⟨1732968546671039830855531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36969995662315516391584661 1732968546671039830855531)
      ·
        refine ⟨2599452820006559746283297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732968546671039830855531 2599452820006559746283297)
        ·
          refine ⟨1949589615004919809712473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599452820006559746283297 1949589615004919809712473)
          ·
            refine ⟨1462192211253689857284355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949589615004919809712473 1462192211253689857284355)
            ·
              refine ⟨2193288316880534785926533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462192211253689857284355 2193288316880534785926533)
              ·
                refine ⟨411241559415100272361225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2193288316880534785926533 411241559415100272361225)
                ·
                  refine ⟨308431169561325204270919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411241559415100272361225 308431169561325204270919)
                  ·
                    rfl

theorem cell20_675751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2].length) (baseStart_675751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675751 prefixEnd_675751 := by exact prefixLift 675751
  have htrace : WordTrace (prefixWord ++ tailWord_675751) baseStart_675751 baseEnd_675751 := by
    simpa [prefixWord, tailWord_675751, baseEnd_675751] using wordTrace_append hprefix tailTrace_675751
  have hstable : (prefixWord ++ tailWord_675751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675751).length < 2 ^ (prefixWord ++ tailWord_675751).sum := by decide
  have hdescent : baseEnd_675751 < baseStart_675751 := by decide
  rcases family_descends (prefixWord ++ tailWord_675751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675845 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_675845 : Nat := 118140960795 + 675845 * 2 ^ 59
def prefixEnd_675845 : Nat := 4983230072969 + 3 ^ 40 * 675845 * 2
def baseEnd_675845 : Nat := 308474073722678655137201

theorem tailTrace_675845 : CollatzResearch.WordTrace tailWord_675845 prefixEnd_675845 308474073722678655137201 := by
  unfold tailWord_675845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650092236536464981644989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16433394824357643321096659 24650092236536464981644989)
  ·
    refine ⟨9243784588701174368116871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24650092236536464981644989 9243784588701174368116871)
    ·
      refine ⟨13865676883051761552175307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243784588701174368116871 13865676883051761552175307)
      ·
        refine ⟨20798515324577642328262961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865676883051761552175307 20798515324577642328262961)
        ·
          refine ⟨15598886493433231746197221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798515324577642328262961 15598886493433231746197221)
          ·
            refine ⟨2924791217518730952411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15598886493433231746197221 2924791217518730952411979)
            ·
              refine ⟨4387186826278096428617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924791217518730952411979 4387186826278096428617969)
              ·
                refine ⟨3290390119708572321463477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4387186826278096428617969 3290390119708572321463477)
                ·
                  refine ⟨308474073722678655137201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290390119708572321463477 308474073722678655137201)
                  ·
                    rfl

theorem cell20_675845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_675845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675845 prefixEnd_675845 := by exact prefixLift 675845
  have htrace : WordTrace (prefixWord ++ tailWord_675845) baseStart_675845 baseEnd_675845 := by
    simpa [prefixWord, tailWord_675845, baseEnd_675845] using wordTrace_append hprefix tailTrace_675845
  have hstable : (prefixWord ++ tailWord_675845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675845).length < 2 ^ (prefixWord ++ tailWord_675845).sum := by decide
  have hdescent : baseEnd_675845 < baseStart_675845 := by decide
  rcases family_descends (prefixWord ++ tailWord_675845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675859 : List Nat := [1, 1, 1, 2, 1, 4, 10]
def baseStart_675859 : Nat := 118140960795 + 675859 * 2 ^ 59
def prefixEnd_675859 : Nat := 4983230072969 + 3 ^ 40 * 675859 * 2
def baseEnd_675859 : Nat := 34275607078239647630053

theorem tailTrace_675859 : CollatzResearch.WordTrace tailWord_675859 prefixEnd_675859 34275607078239647630053 := by
  unfold tailWord_675859
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650602858485745372654631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16433735238990496915103087 24650602858485745372654631)
  ·
    refine ⟨36975904287728618058981947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650602858485745372654631 36975904287728618058981947)
    ·
      refine ⟨55463856431592927088472921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36975904287728618058981947 55463856431592927088472921)
      ·
        refine ⟨41597892323694695316354691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55463856431592927088472921 41597892323694695316354691)
        ·
          refine ⟨62396838485542042974532037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41597892323694695316354691 62396838485542042974532037)
          ·
            refine ⟨11699407216039133057724757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62396838485542042974532037 11699407216039133057724757)
            ·
              refine ⟨34275607078239647630053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11699407216039133057724757 34275607078239647630053)
              ·
                rfl

theorem cell20_675859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_675859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675859 prefixEnd_675859 := by exact prefixLift 675859
  have htrace : WordTrace (prefixWord ++ tailWord_675859) baseStart_675859 baseEnd_675859 := by
    simpa [prefixWord, tailWord_675859, baseEnd_675859] using wordTrace_append hprefix tailTrace_675859
  have hstable : (prefixWord ++ tailWord_675859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675859).length < 2 ^ (prefixWord ++ tailWord_675859).sum := by decide
  have hdescent : baseEnd_675859 < baseStart_675859 := by decide
  rcases family_descends (prefixWord ++ tailWord_675859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675917 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_675917 : Nat := 118140960795 + 675917 * 2 ^ 59
def prefixEnd_675917 : Nat := 4983230072969 + 3 ^ 40 * 675917 * 2
def baseEnd_675917 : Nat := 308506936484566404736907

theorem tailTrace_675917 : CollatzResearch.WordTrace tailWord_675917 prefixEnd_675917 308506936484566404736907 := by
  unfold tailWord_675917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24652718292275621278266005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16435145528183747518844003 24652718292275621278266005)
  ·
    refine ⟨1155596169950419747418719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24652718292275621278266005 1155596169950419747418719)
    ·
      refine ⟨1733394254925629621128079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155596169950419747418719 1733394254925629621128079)
      ·
        refine ⟨2600091382388444431692119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733394254925629621128079 2600091382388444431692119)
        ·
          refine ⟨3900137073582666647538179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600091382388444431692119 3900137073582666647538179)
          ·
            refine ⟨5850205610373999971307269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900137073582666647538179 5850205610373999971307269)
            ·
              refine ⟨1096913551945124994620113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5850205610373999971307269 1096913551945124994620113)
              ·
                refine ⟨822685163958843745965085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096913551945124994620113 822685163958843745965085)
                ·
                  refine ⟨308506936484566404736907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822685163958843745965085 308506936484566404736907)
                  ·
                    rfl

theorem cell20_675917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_675917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675917 prefixEnd_675917 := by exact prefixLift 675917
  have htrace : WordTrace (prefixWord ++ tailWord_675917) baseStart_675917 baseEnd_675917 := by
    simpa [prefixWord, tailWord_675917, baseEnd_675917] using wordTrace_append hprefix tailTrace_675917
  have hstable : (prefixWord ++ tailWord_675917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675917).length < 2 ^ (prefixWord ++ tailWord_675917).sum := by decide
  have hdescent : baseEnd_675917 < baseStart_675917 := by decide
  rcases family_descends (prefixWord ++ tailWord_675917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675935 : List Nat := [1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_675935 : Nat := 118140960795 + 675935 * 2 ^ 59
def prefixEnd_675935 : Nat := 4983230072969 + 3 ^ 40 * 675935 * 2
def baseEnd_675935 : Nat := 102838384058346114045611

theorem tailTrace_675935 : CollatzResearch.WordTrace tailWord_675935 prefixEnd_675935 102838384058346114045611 := by
  unfold tailWord_675935
  simp only [CollatzResearch.WordTrace]
  refine ⟨24653374806210410352421259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16435583204140273568280839 24653374806210410352421259)
  ·
    refine ⟨36980062209315615528631889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24653374806210410352421259 36980062209315615528631889)
    ·
      refine ⟨27735046656986711646473917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36980062209315615528631889 27735046656986711646473917)
      ·
        refine ⟨10400642496370016867427719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27735046656986711646473917 10400642496370016867427719)
        ·
          refine ⟨15600963744555025301141579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10400642496370016867427719 15600963744555025301141579)
          ·
            refine ⟨23401445616832537951712369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15600963744555025301141579 23401445616832537951712369)
            ·
              refine ⟨17551084212624403463784277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23401445616832537951712369 17551084212624403463784277)
              ·
                refine ⟨102838384058346114045611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17551084212624403463784277 102838384058346114045611)
                ·
                  rfl

theorem cell20_675935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_675935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675935 prefixEnd_675935 := by exact prefixLift 675935
  have htrace : WordTrace (prefixWord ++ tailWord_675935) baseStart_675935 baseEnd_675935 := by
    simpa [prefixWord, tailWord_675935, baseEnd_675935] using wordTrace_append hprefix tailTrace_675935
  have hstable : (prefixWord ++ tailWord_675935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675935).length < 2 ^ (prefixWord ++ tailWord_675935).sum := by decide
  have hdescent : baseEnd_675935 < baseStart_675935 := by decide
  rcases family_descends (prefixWord ++ tailWord_675935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675976 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_675976 : Nat := 118140960795 + 675976 * 2 ^ 59
def prefixEnd_675976 : Nat := 4983230072969 + 3 ^ 40 * 675976 * 2
def baseEnd_675976 : Nat := 308533865692224421769999

theorem tailTrace_675976 : CollatzResearch.WordTrace tailWord_675976 prefixEnd_675976 308533865692224421769999 := by
  unfold tailWord_675976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327435099530937177331891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16436580132707916236442521 12327435099530937177331891)
  ·
    refine ⟨18491152649296405765997837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12327435099530937177331891 18491152649296405765997837)
    ·
      refine ⟨6934182243486152162249189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18491152649296405765997837 6934182243486152162249189)
      ·
        refine ⟨1300159170653653530421723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6934182243486152162249189 1300159170653653530421723)
        ·
          refine ⟨1950238755980480295632585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300159170653653530421723 1950238755980480295632585)
          ·
            refine ⟨1462679066985360221724439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950238755980480295632585 1462679066985360221724439)
            ·
              refine ⟨2194018600478040332586659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462679066985360221724439 2194018600478040332586659)
              ·
                refine ⟨3291027900717060498879989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194018600478040332586659 3291027900717060498879989)
                ·
                  refine ⟨308533865692224421769999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291027900717060498879989 308533865692224421769999)
                  ·
                    rfl

theorem cell20_675976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_675976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_675976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_675976 prefixEnd_675976 := by exact prefixLift 675976
  have htrace : WordTrace (prefixWord ++ tailWord_675976) baseStart_675976 baseEnd_675976 := by
    simpa [prefixWord, tailWord_675976, baseEnd_675976] using wordTrace_append hprefix tailTrace_675976
  have hstable : (prefixWord ++ tailWord_675976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675976).length < 2 ^ (prefixWord ++ tailWord_675976).sum := by decide
  have hdescent : baseEnd_675976 < baseStart_675976 := by decide
  rcases family_descends (prefixWord ++ tailWord_675976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676007 : List Nat := [1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_676007 : Nat := 118140960795 + 676007 * 2 ^ 59
def prefixEnd_676007 : Nat := 4983230072969 + 3 ^ 40 * 676007 * 2
def baseEnd_676007 : Nat := 102849338312308697245513

theorem tailTrace_676007 : CollatzResearch.WordTrace tailWord_676007 prefixEnd_676007 102849338312308697245513 := by
  unfold tailWord_676007
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656000861949566649042275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16437333907966377766028183 24656000861949566649042275)
  ·
    refine ⟨36984001292924349973563413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24656000861949566649042275 36984001292924349973563413)
    ·
      refine ⟨1733625060605828905010785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36984001292924349973563413 1733625060605828905010785)
      ·
        refine ⟨1300218795454371678758089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1733625060605828905010785 1300218795454371678758089)
        ·
          refine ⟨975164096590778759068567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300218795454371678758089 975164096590778759068567)
          ·
            refine ⟨1462746144886168138602851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975164096590778759068567 1462746144886168138602851)
            ·
              refine ⟨2194119217329252207904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462746144886168138602851 2194119217329252207904277)
              ·
                refine ⟨102849338312308697245513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194119217329252207904277 102849338312308697245513)
                ·
                  rfl

theorem cell20_676007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_676007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676007 prefixEnd_676007 := by exact prefixLift 676007
  have htrace : WordTrace (prefixWord ++ tailWord_676007) baseStart_676007 baseEnd_676007 := by
    simpa [prefixWord, tailWord_676007, baseEnd_676007] using wordTrace_append hprefix tailTrace_676007
  have hstable : (prefixWord ++ tailWord_676007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676007).length < 2 ^ (prefixWord ++ tailWord_676007).sum := by decide
  have hdescent : baseEnd_676007 < baseStart_676007 := by decide
  rcases family_descends (prefixWord ++ tailWord_676007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676020 : List Nat := [2, 5, 3, 1, 2, 1, 6]
def baseStart_676020 : Nat := 118140960795 + 676020 * 2 ^ 59
def prefixEnd_676020 : Nat := 4983230072969 + 3 ^ 40 * 676020 * 2
def baseEnd_676020 : Nat := 34283772054572869367017

theorem tailTrace_676020 : CollatzResearch.WordTrace tailWord_676020 prefixEnd_676020 34283772054572869367017 := by
  unfold tailWord_676020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328237505451234934632757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16437650007268313246177009 12328237505451234934632757)
  ·
    refine ⟨1155772266136053275121821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12328237505451234934632757 1155772266136053275121821)
    ·
      refine ⟨433414599801019978170683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155772266136053275121821 433414599801019978170683)
      ·
        refine ⟨650121899701529967256025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433414599801019978170683 650121899701529967256025)
        ·
          refine ⟨487591424776147475442019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650121899701529967256025 487591424776147475442019)
          ·
            refine ⟨731387137164221213163029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487591424776147475442019 731387137164221213163029)
            ·
              refine ⟨34283772054572869367017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 731387137164221213163029 34283772054572869367017)
              ·
                rfl

theorem cell20_676020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_676020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676020 prefixEnd_676020 := by exact prefixLift 676020
  have htrace : WordTrace (prefixWord ++ tailWord_676020) baseStart_676020 baseEnd_676020 := by
    simpa [prefixWord, tailWord_676020, baseEnd_676020] using wordTrace_append hprefix tailTrace_676020
  have hstable : (prefixWord ++ tailWord_676020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676020).length < 2 ^ (prefixWord ++ tailWord_676020).sum := by decide
  have hdescent : baseEnd_676020 < baseStart_676020 := by decide
  rcases family_descends (prefixWord ++ tailWord_676020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676034 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_676034 : Nat := 118140960795 + 676034 * 2 ^ 59
def prefixEnd_676034 : Nat := 4983230072969 + 3 ^ 40 * 676034 * 2
def baseEnd_676034 : Nat := 308560338472633997836429

theorem tailTrace_676034 : CollatzResearch.WordTrace tailWord_676034 prefixEnd_676034 308560338472633997836429 := by
  unfold tailWord_676034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164246408212937565068789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16437990421901166840183437 6164246408212937565068789)
  ·
    refine ⟨577898100769962896725199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6164246408212937565068789 577898100769962896725199)
    ·
      refine ⟨866847151154944345087799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577898100769962896725199 866847151154944345087799)
      ·
        refine ⟨1300270726732416517631699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866847151154944345087799 1300270726732416517631699)
        ·
          refine ⟨1950406090098624776447549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300270726732416517631699 1950406090098624776447549)
          ·
            refine ⟨731402283786984291167831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1950406090098624776447549 731402283786984291167831)
            ·
              refine ⟨1097103425680476436751747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731402283786984291167831 1097103425680476436751747)
              ·
                refine ⟨1645655138520714655127621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097103425680476436751747 1645655138520714655127621)
                ·
                  refine ⟨308560338472633997836429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645655138520714655127621 308560338472633997836429)
                  ·
                    rfl

theorem cell20_676034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_676034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676034 prefixEnd_676034 := by exact prefixLift 676034
  have htrace : WordTrace (prefixWord ++ tailWord_676034) baseStart_676034 baseEnd_676034 := by
    simpa [prefixWord, tailWord_676034, baseEnd_676034] using wordTrace_append hprefix tailTrace_676034
  have hstable : (prefixWord ++ tailWord_676034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676034).length < 2 ^ (prefixWord ++ tailWord_676034).sum := by decide
  have hdescent : baseEnd_676034 < baseStart_676034 := by decide
  rcases family_descends (prefixWord ++ tailWord_676034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676049 : List Nat := [1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_676049 : Nat := 118140960795 + 676049 * 2 ^ 59
def prefixEnd_676049 : Nat := 4983230072969 + 3 ^ 40 * 676049 * 2
def baseEnd_676049 : Nat := 102855728293786870778789

theorem tailTrace_676049 : CollatzResearch.WordTrace tailWord_676049 prefixEnd_676049 102855728293786870778789 := by
  unfold tailWord_676049
  simp only [CollatzResearch.WordTrace]
  refine ⟨24657532727797407822071201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16438355151864938548047467 24657532727797407822071201)
  ·
    refine ⟨18493149545848055866553401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24657532727797407822071201 18493149545848055866553401)
    ·
      refine ⟨13869862159386041899915051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18493149545848055866553401 13869862159386041899915051)
      ·
        refine ⟨20804793239079062849872577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13869862159386041899915051 20804793239079062849872577)
        ·
          refine ⟨15603594929309297137404433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20804793239079062849872577 15603594929309297137404433)
          ·
            refine ⟨11702696196981972853053325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15603594929309297137404433 11702696196981972853053325)
            ·
              refine ⟨4388511073868239819894997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11702696196981972853053325 4388511073868239819894997)
              ·
                refine ⟨102855728293786870778789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4388511073868239819894997 102855728293786870778789)
                ·
                  rfl

theorem cell20_676049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_676049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676049 prefixEnd_676049 := by exact prefixLift 676049
  have htrace : WordTrace (prefixWord ++ tailWord_676049) baseStart_676049 baseEnd_676049 := by
    simpa [prefixWord, tailWord_676049, baseEnd_676049] using wordTrace_append hprefix tailTrace_676049
  have hstable : (prefixWord ++ tailWord_676049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676049).length < 2 ^ (prefixWord ++ tailWord_676049).sum := by decide
  have hdescent : baseEnd_676049 < baseStart_676049 := by decide
  rcases family_descends (prefixWord ++ tailWord_676049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676090 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_676090 : Nat := 118140960795 + 676090 * 2 ^ 59
def prefixEnd_676090 : Nat := 4983230072969 + 3 ^ 40 * 676090 * 2
def baseEnd_676090 : Nat := 308585898398546691969533

theorem tailTrace_676090 : CollatzResearch.WordTrace tailWord_676090 prefixEnd_676090 308585898398546691969533 := by
  unfold tailWord_676090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164757030162217956078431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16439352080432581216209149 6164757030162217956078431)
  ·
    refine ⟨9247135545243326934117647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164757030162217956078431 9247135545243326934117647)
    ·
      refine ⟨13870703317864990401176471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247135545243326934117647 13870703317864990401176471)
      ·
        refine ⟨20806054976797485601764707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13870703317864990401176471 20806054976797485601764707)
        ·
          refine ⟨31209082465196228402647061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20806054976797485601764707 31209082465196228402647061)
          ·
            refine ⟨1462925740556073206374081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31209082465196228402647061 1462925740556073206374081)
            ·
              refine ⟨1097194305417054904780561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462925740556073206374081 1097194305417054904780561)
              ·
                refine ⟨822895729062791178585421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097194305417054904780561 822895729062791178585421)
                ·
                  refine ⟨308585898398546691969533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822895729062791178585421 308585898398546691969533)
                  ·
                    rfl

theorem cell20_676090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_676090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676090 prefixEnd_676090 := by exact prefixLift 676090
  have htrace : WordTrace (prefixWord ++ tailWord_676090) baseStart_676090 baseEnd_676090 := by
    simpa [prefixWord, tailWord_676090, baseEnd_676090] using wordTrace_append hprefix tailTrace_676090
  have hstable : (prefixWord ++ tailWord_676090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676090).length < 2 ^ (prefixWord ++ tailWord_676090).sum := by decide
  have hdescent : baseEnd_676090 < baseStart_676090 := by decide
  rcases family_descends (prefixWord ++ tailWord_676090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676100 : List Nat := [2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_676100 : Nat := 118140960795 + 676100 * 2 ^ 59
def prefixEnd_676100 : Nat := 4983230072969 + 3 ^ 40 * 676100 * 2
def baseEnd_676100 : Nat := 102863487557010367212053

theorem tailTrace_676100 : CollatzResearch.WordTrace tailWord_676100 prefixEnd_676100 102863487557010367212053 := by
  unfold tailWord_676100
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329696425306321766088877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16439595233741762354785169 12329696425306321766088877)
  ·
    refine ⟨4623636159489870662283329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12329696425306321766088877 4623636159489870662283329)
    ·
      refine ⟨3467727119617402996712497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623636159489870662283329 3467727119617402996712497)
      ·
        refine ⟨2600795339713052247534373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3467727119617402996712497 2600795339713052247534373)
        ·
          refine ⟨487649126196197296412695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2600795339713052247534373 487649126196197296412695)
          ·
            refine ⟨731473689294295944619043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487649126196197296412695 731473689294295944619043)
            ·
              refine ⟨1097210533941443916928565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731473689294295944619043 1097210533941443916928565)
              ·
                refine ⟨102863487557010367212053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1097210533941443916928565 102863487557010367212053)
                ·
                  rfl

theorem cell20_676100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_676100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676100 prefixEnd_676100 := by exact prefixLift 676100
  have htrace : WordTrace (prefixWord ++ tailWord_676100) baseStart_676100 baseEnd_676100 := by
    simpa [prefixWord, tailWord_676100, baseEnd_676100] using wordTrace_append hprefix tailTrace_676100
  have hstable : (prefixWord ++ tailWord_676100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676100).length < 2 ^ (prefixWord ++ tailWord_676100).sum := by decide
  have hdescent : baseEnd_676100 < baseStart_676100 := by decide
  rcases family_descends (prefixWord ++ tailWord_676100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676104 : List Nat := [2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_676104 : Nat := 118140960795 + 676104 * 2 ^ 59
def prefixEnd_676104 : Nat := 4983230072969 + 3 ^ 40 * 676104 * 2
def baseEnd_676104 : Nat := 102864096126674955167603

theorem tailTrace_676104 : CollatzResearch.WordTrace tailWord_676104 prefixEnd_676104 102864096126674955167603 := by
  unfold tailWord_676104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12329769371299076107661683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16439692495065434810215577 12329769371299076107661683)
  ·
    refine ⟨18494654056948614161492525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12329769371299076107661683 18494654056948614161492525)
    ·
      refine ⟨6935495271355730310559697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18494654056948614161492525 6935495271355730310559697)
      ·
        refine ⟨5201621453516797732919773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6935495271355730310559697 5201621453516797732919773)
        ·
          refine ⟨1950608045068799149844915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5201621453516797732919773 1950608045068799149844915)
          ·
            refine ⟨2925912067603198724767373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950608045068799149844915 2925912067603198724767373)
            ·
              refine ⟨1097217025351199521787765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2925912067603198724767373 1097217025351199521787765)
              ·
                refine ⟨102864096126674955167603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1097217025351199521787765 102864096126674955167603)
                ·
                  rfl

theorem cell20_676104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_676104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676104 prefixEnd_676104 := by exact prefixLift 676104
  have htrace : WordTrace (prefixWord ++ tailWord_676104) baseStart_676104 baseEnd_676104 := by
    simpa [prefixWord, tailWord_676104, baseEnd_676104] using wordTrace_append hprefix tailTrace_676104
  have hstable : (prefixWord ++ tailWord_676104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676104).length < 2 ^ (prefixWord ++ tailWord_676104).sum := by decide
  have hdescent : baseEnd_676104 < baseStart_676104 := by decide
  rcases family_descends (prefixWord ++ tailWord_676104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676141 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 3]
def baseStart_676141 : Nat := 118140960795 + 676141 * 2 ^ 59
def prefixEnd_676141 : Nat := 4983230072969 + 3 ^ 40 * 676141 * 2
def baseEnd_676141 : Nat := 308609176188217181269325

theorem tailTrace_676141 : CollatzResearch.WordTrace tailWord_676141 prefixEnd_676141 308609176188217181269325 := by
  unfold tailWord_676141
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660888243464107534420277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16440592162309405022946851 24660888243464107534420277)
  ·
    refine ⟨2311958272824760081351901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24660888243464107534420277 2311958272824760081351901)
    ·
      refine ⟨866984352309285030506963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2311958272824760081351901 866984352309285030506963)
      ·
        refine ⟨1300476528463927545760445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866984352309285030506963 1300476528463927545760445)
        ·
          refine ⟨487678698173972829660167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1300476528463927545760445 487678698173972829660167)
          ·
            refine ⟨731518047260959244490251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487678698173972829660167 731518047260959244490251)
            ·
              refine ⟨1097277070891438866735377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731518047260959244490251 1097277070891438866735377)
              ·
                refine ⟨822957803168579150051533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097277070891438866735377 822957803168579150051533)
                ·
                  refine ⟨308609176188217181269325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822957803168579150051533 308609176188217181269325)
                  ·
                    rfl

theorem cell20_676141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_676141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676141 prefixEnd_676141 := by exact prefixLift 676141
  have htrace : WordTrace (prefixWord ++ tailWord_676141) baseStart_676141 baseEnd_676141 := by
    simpa [prefixWord, tailWord_676141, baseEnd_676141] using wordTrace_append hprefix tailTrace_676141
  have hstable : (prefixWord ++ tailWord_676141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676141).length < 2 ^ (prefixWord ++ tailWord_676141).sum := by decide
  have hdescent : baseEnd_676141 < baseStart_676141 := by decide
  rcases family_descends (prefixWord ++ tailWord_676141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676145 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_676145 : Nat := 118140960795 + 676145 * 2 ^ 59
def prefixEnd_676145 : Nat := 4983230072969 + 3 ^ 40 * 676145 * 2
def baseEnd_676145 : Nat := 308611001897210945135975

theorem tailTrace_676145 : CollatzResearch.WordTrace tailWord_676145 prefixEnd_676145 308611001897210945135975 := by
  unfold tailWord_676145
  simp only [CollatzResearch.WordTrace]
  refine ⟨24661034135449616217565889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16440689423633077478377259 24661034135449616217565889)
  ·
    refine ⟨18495775601587212163174417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24661034135449616217565889 18495775601587212163174417)
    ·
      refine ⟨13871831701190409122380813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18495775601587212163174417 13871831701190409122380813)
      ·
        refine ⟨5201936887946403420892805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13871831701190409122380813 5201936887946403420892805)
        ·
          refine ⟨975363166489950641417401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5201936887946403420892805 975363166489950641417401)
          ·
            refine ⟨731522374867462981063051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975363166489950641417401 731522374867462981063051)
            ·
              refine ⟨1097283562301194471594577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731522374867462981063051 1097283562301194471594577)
              ·
                refine ⟨822962671725895853695933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097283562301194471594577 822962671725895853695933)
                ·
                  refine ⟨308611001897210945135975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822962671725895853695933 308611001897210945135975)
                  ·
                    rfl

theorem cell20_676145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_676145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676145 prefixEnd_676145 := by exact prefixLift 676145
  have htrace : WordTrace (prefixWord ++ tailWord_676145) baseStart_676145 baseEnd_676145 := by
    simpa [prefixWord, tailWord_676145, baseEnd_676145] using wordTrace_append hprefix tailTrace_676145
  have hstable : (prefixWord ++ tailWord_676145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676145).length < 2 ^ (prefixWord ++ tailWord_676145).sum := by decide
  have hdescent : baseEnd_676145 < baseStart_676145 := by decide
  rcases family_descends (prefixWord ++ tailWord_676145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676149 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_676149 : Nat := 118140960795 + 676149 * 2 ^ 59
def prefixEnd_676149 : Nat := 4983230072969 + 3 ^ 40 * 676149 * 2
def baseEnd_676149 : Nat := 308612827606204709002625

theorem tailTrace_676149 : CollatzResearch.WordTrace tailWord_676149 prefixEnd_676149 308612827606204709002625 := by
  unfold tailWord_676149
  simp only [CollatzResearch.WordTrace]
  refine ⟨24661180027435124900711501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16440786684956749933807667 24661180027435124900711501)
  ·
    refine ⟨9247942510288171837766813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24661180027435124900711501 9247942510288171837766813)
    ·
      refine ⟨3467978441358064439162555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9247942510288171837766813 3467978441358064439162555)
      ·
        refine ⟨5201967662037096658743833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467978441358064439162555 5201967662037096658743833)
        ·
          refine ⟨3901475746527822494057875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5201967662037096658743833 3901475746527822494057875)
          ·
            refine ⟨5852213619791733741086813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901475746527822494057875 5852213619791733741086813)
            ·
              refine ⟨2194580107421900152907555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5852213619791733741086813 2194580107421900152907555)
              ·
                refine ⟨3291870161132850229361333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194580107421900152907555 3291870161132850229361333)
                ·
                  refine ⟨308612827606204709002625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291870161132850229361333 308612827606204709002625)
                  ·
                    rfl

theorem cell20_676149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_676149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676149 prefixEnd_676149 := by exact prefixLift 676149
  have htrace : WordTrace (prefixWord ++ tailWord_676149) baseStart_676149 baseEnd_676149 := by
    simpa [prefixWord, tailWord_676149, baseEnd_676149] using wordTrace_append hprefix tailTrace_676149
  have hstable : (prefixWord ++ tailWord_676149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676149).length < 2 ^ (prefixWord ++ tailWord_676149).sum := by decide
  have hdescent : baseEnd_676149 < baseStart_676149 := by decide
  rcases family_descends (prefixWord ++ tailWord_676149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676180 : List Nat := [2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_676180 : Nat := 118140960795 + 676180 * 2 ^ 59
def prefixEnd_676180 : Nat := 4983230072969 + 3 ^ 40 * 676180 * 2
def baseEnd_676180 : Nat := 102875658950302126323055

theorem tailTrace_676180 : CollatzResearch.WordTrace tailWord_676180 prefixEnd_676180 102875658950302126323055 := by
  unfold tailWord_676180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12331155345161408597544997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16441540460215211463393329 12331155345161408597544997)
  ·
    refine ⟨2312091627217764112039687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12331155345161408597544997 2312091627217764112039687)
    ·
      refine ⟨3468137440826646168059531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312091627217764112039687 3468137440826646168059531)
      ·
        refine ⟨5202206161239969252089297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468137440826646168059531 5202206161239969252089297)
        ·
          refine ⟨3901654620929976939066973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202206161239969252089297 3901654620929976939066973)
          ·
            refine ⟨1463120482848741352150115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3901654620929976939066973 1463120482848741352150115)
            ·
              refine ⟨2194680724273112028225173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463120482848741352150115 2194680724273112028225173)
              ·
                refine ⟨102875658950302126323055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194680724273112028225173 102875658950302126323055)
                ·
                  rfl

theorem cell20_676180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_676180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676180 prefixEnd_676180 := by exact prefixLift 676180
  have htrace : WordTrace (prefixWord ++ tailWord_676180) baseStart_676180 baseEnd_676180 := by
    simpa [prefixWord, tailWord_676180, baseEnd_676180] using wordTrace_append hprefix tailTrace_676180
  have hstable : (prefixWord ++ tailWord_676180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676180).length < 2 ^ (prefixWord ++ tailWord_676180).sum := by decide
  have hdescent : baseEnd_676180 < baseStart_676180 := by decide
  rcases family_descends (prefixWord ++ tailWord_676180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676214 : List Nat := [5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_676214 : Nat := 118140960795 + 676214 * 2 ^ 59
def prefixEnd_676214 : Nat := 4983230072969 + 3 ^ 40 * 676214 * 2
def baseEnd_676214 : Nat := 102880831792451123945231

theorem tailTrace_676214 : CollatzResearch.WordTrace tailWord_676214 prefixEnd_676214 102880831792451123945231 := by
  unfold tailWord_676214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541471923262477562614231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16442367181466427334551797 1541471923262477562614231)
  ·
    refine ⟨2312207884893716343921347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1541471923262477562614231 2312207884893716343921347)
    ·
      refine ⟨3468311827340574515882021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312207884893716343921347 3468311827340574515882021)
      ·
        refine ⟨650308467626357721727879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3468311827340574515882021 650308467626357721727879)
        ·
          refine ⟨975462701439536582591819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650308467626357721727879 975462701439536582591819)
          ·
            refine ⟨1463194052159304873887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975462701439536582591819 1463194052159304873887729)
            ·
              refine ⟨1097395539119478655415797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463194052159304873887729 1097395539119478655415797)
              ·
                refine ⟨102880831792451123945231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1097395539119478655415797 102880831792451123945231)
                ·
                  rfl

theorem cell20_676214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_676214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676214 prefixEnd_676214 := by exact prefixLift 676214
  have htrace : WordTrace (prefixWord ++ tailWord_676214) baseStart_676214 baseEnd_676214 := by
    simpa [prefixWord, tailWord_676214, baseEnd_676214] using wordTrace_append hprefix tailTrace_676214
  have hstable : (prefixWord ++ tailWord_676214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676214).length < 2 ^ (prefixWord ++ tailWord_676214).sum := by decide
  have hdescent : baseEnd_676214 < baseStart_676214 := by decide
  rcases family_descends (prefixWord ++ tailWord_676214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676221 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_676221 : Nat := 118140960795 + 676221 * 2 ^ 59
def prefixEnd_676221 : Nat := 4983230072969 + 3 ^ 40 * 676221 * 2
def baseEnd_676221 : Nat := 308645690368092458602331

theorem tailTrace_676221 : CollatzResearch.WordTrace tailWord_676221 prefixEnd_676221 308645690368092458602331 := by
  unfold tailWord_676221
  simp only [CollatzResearch.WordTrace]
  refine ⟨24663806083174281197332517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16442537388782854131555011 24663806083174281197332517)
  ·
    refine ⟨4624463640595177724499847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24663806083174281197332517 4624463640595177724499847)
    ·
      refine ⟨6936695460892766586749771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624463640595177724499847 6936695460892766586749771)
      ·
        refine ⟨10405043191339149880124657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936695460892766586749771 10405043191339149880124657)
        ·
          refine ⟨7803782393504362410093493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10405043191339149880124657 7803782393504362410093493)
          ·
            refine ⟨731604599391033975946265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7803782393504362410093493 731604599391033975946265)
            ·
              refine ⟨548703449543275481959699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731604599391033975946265 548703449543275481959699)
              ·
                refine ⟨823055174314913222939549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548703449543275481959699 823055174314913222939549)
                ·
                  refine ⟨308645690368092458602331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823055174314913222939549 308645690368092458602331)
                  ·
                    rfl

theorem cell20_676221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_676221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676221 prefixEnd_676221 := by exact prefixLift 676221
  have htrace : WordTrace (prefixWord ++ tailWord_676221) baseStart_676221 baseEnd_676221 := by
    simpa [prefixWord, tailWord_676221, baseEnd_676221] using wordTrace_append hprefix tailTrace_676221
  have hstable : (prefixWord ++ tailWord_676221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676221).length < 2 ^ (prefixWord ++ tailWord_676221).sum := by decide
  have hdescent : baseEnd_676221 < baseStart_676221 := by decide
  rcases family_descends (prefixWord ++ tailWord_676221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676232 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_676232 : Nat := 118140960795 + 676232 * 2 ^ 59
def prefixEnd_676232 : Nat := 4983230072969 + 3 ^ 40 * 676232 * 2
def baseEnd_676232 : Nat := 308650711067825309235619

theorem tailTrace_676232 : CollatzResearch.WordTrace tailWord_676232 prefixEnd_676232 308650711067825309235619 := by
  unfold tailWord_676232
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332103643067215037991475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16442804857422953383988633 12332103643067215037991475)
  ·
    refine ⟨18498155464600822556987213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12332103643067215037991475 18498155464600822556987213)
    ·
      refine ⟨6936808299225308458870205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18498155464600822556987213 6936808299225308458870205)
      ·
        refine ⟨2601303112209490672076327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6936808299225308458870205 2601303112209490672076327)
        ·
          refine ⟨3901954668314236008114491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601303112209490672076327 3901954668314236008114491)
          ·
            refine ⟨5852932002471354012171737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901954668314236008114491 5852932002471354012171737)
            ·
              refine ⟨4389699001853515509128803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5852932002471354012171737 4389699001853515509128803)
              ·
                refine ⟨6584548502780273263693205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389699001853515509128803 6584548502780273263693205)
                ·
                  refine ⟨308650711067825309235619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6584548502780273263693205 308650711067825309235619)
                  ·
                    rfl

theorem cell20_676232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_676232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676232 prefixEnd_676232 := by exact prefixLift 676232
  have htrace : WordTrace (prefixWord ++ tailWord_676232) baseStart_676232 baseEnd_676232 := by
    simpa [prefixWord, tailWord_676232, baseEnd_676232] using wordTrace_append hprefix tailTrace_676232
  have hstable : (prefixWord ++ tailWord_676232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676232).length < 2 ^ (prefixWord ++ tailWord_676232).sum := by decide
  have hdescent : baseEnd_676232 < baseStart_676232 := by decide
  rcases family_descends (prefixWord ++ tailWord_676232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676249 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 2]
def baseStart_676249 : Nat := 118140960795 + 676249 * 2 ^ 59
def prefixEnd_676249 : Nat := 4983230072969 + 3 ^ 40 * 676249 * 2
def baseEnd_676249 : Nat := 308658470331048805668883

theorem tailTrace_676249 : CollatzResearch.WordTrace tailWord_676249 prefixEnd_676249 308658470331048805668883 := by
  unfold tailWord_676249
  simp only [CollatzResearch.WordTrace]
  refine ⟨24664827327072841979351801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16443218218048561319567867 24664827327072841979351801)
  ·
    refine ⟨18498620495304631484513851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24664827327072841979351801 18498620495304631484513851)
    ·
      refine ⟨27747930742956947226770777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18498620495304631484513851 27747930742956947226770777)
      ·
        refine ⟨20810948057217710420078083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27747930742956947226770777 20810948057217710420078083)
        ·
          refine ⟨31216422085826565630117125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20810948057217710420078083 31216422085826565630117125)
          ·
            refine ⟨5853079141092481055646961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31216422085826565630117125 5853079141092481055646961)
            ·
              refine ⟨4389809355819360791735221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853079141092481055646961 4389809355819360791735221)
              ·
                refine ⟨411544627108065074225177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4389809355819360791735221 411544627108065074225177)
                ·
                  refine ⟨308658470331048805668883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411544627108065074225177 308658470331048805668883)
                  ·
                    rfl

theorem cell20_676249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_676249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676249 prefixEnd_676249 := by exact prefixLift 676249
  have htrace : WordTrace (prefixWord ++ tailWord_676249) baseStart_676249 baseEnd_676249 := by
    simpa [prefixWord, tailWord_676249, baseEnd_676249] using wordTrace_append hprefix tailTrace_676249
  have hstable : (prefixWord ++ tailWord_676249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676249).length < 2 ^ (prefixWord ++ tailWord_676249).sum := by decide
  have hdescent : baseEnd_676249 < baseStart_676249 := by decide
  rcases family_descends (prefixWord ++ tailWord_676249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676359 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 2]
def baseStart_676359 : Nat := 118140960795 + 676359 * 2 ^ 59
def prefixEnd_676359 : Nat := 4983230072969 + 3 ^ 40 * 676359 * 2
def baseEnd_676359 : Nat := 308708677328377312001767

theorem tailTrace_676359 : CollatzResearch.WordTrace tailWord_676359 prefixEnd_676359 308708677328377312001767 := by
  unfold tailWord_676359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24668839356674330765856131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16445892904449553843904087 24668839356674330765856131)
  ·
    refine ⟨37003259035011496148784197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24668839356674330765856131 37003259035011496148784197)
    ·
      refine ⟨6938111069064655527897037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37003259035011496148784197 6938111069064655527897037)
      ·
        refine ⟨2601791650899245822961389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6938111069064655527897037 2601791650899245822961389)
        ·
          refine ⟨975671869087217183610521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2601791650899245822961389 975671869087217183610521)
          ·
            refine ⟨731753901815412887707891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975671869087217183610521 731753901815412887707891)
            ·
              refine ⟨1097630852723119331561837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731753901815412887707891 1097630852723119331561837)
              ·
                refine ⟨411611569771169749335689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1097630852723119331561837 411611569771169749335689)
                ·
                  refine ⟨308708677328377312001767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411611569771169749335689 308708677328377312001767)
                  ·
                    rfl

theorem cell20_676359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2].length) (baseStart_676359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676359 prefixEnd_676359 := by exact prefixLift 676359
  have htrace : WordTrace (prefixWord ++ tailWord_676359) baseStart_676359 baseEnd_676359 := by
    simpa [prefixWord, tailWord_676359, baseEnd_676359] using wordTrace_append hprefix tailTrace_676359
  have hstable : (prefixWord ++ tailWord_676359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676359).length < 2 ^ (prefixWord ++ tailWord_676359).sum := by decide
  have hdescent : baseEnd_676359 < baseStart_676359 := by decide
  rcases family_descends (prefixWord ++ tailWord_676359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676367 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_676367 : Nat := 118140960795 + 676367 * 2 ^ 59
def prefixEnd_676367 : Nat := 4983230072969 + 3 ^ 40 * 676367 * 2
def baseEnd_676367 : Nat := 308712328746364839735067

theorem tailTrace_676367 : CollatzResearch.WordTrace tailWord_676367 prefixEnd_676367 308712328746364839735067 := by
  unfold tailWord_676367
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669131140645348132147355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16446087427096898754764903 24669131140645348132147355)
  ·
    refine ⟨37003696710968022198221033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24669131140645348132147355 37003696710968022198221033)
    ·
      refine ⟨27752772533226016648665775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37003696710968022198221033 27752772533226016648665775)
      ·
        refine ⟨41629158799839024972998663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27752772533226016648665775 41629158799839024972998663)
        ·
          refine ⟨62443738199758537459497995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41629158799839024972998663 62443738199758537459497995)
          ·
            refine ⟨93665607299637806189246993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62443738199758537459497995 93665607299637806189246993)
            ·
              refine ⟨70249205474728354641935245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93665607299637806189246993 70249205474728354641935245)
              ·
                refine ⟨26343452053023132990725717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70249205474728354641935245 26343452053023132990725717)
                ·
                  refine ⟨308712328746364839735067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26343452053023132990725717 308712328746364839735067)
                  ·
                    rfl

theorem cell20_676367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_676367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676367 prefixEnd_676367 := by exact prefixLift 676367
  have htrace : WordTrace (prefixWord ++ tailWord_676367) baseStart_676367 baseEnd_676367 := by
    simpa [prefixWord, tailWord_676367, baseEnd_676367] using wordTrace_append hprefix tailTrace_676367
  have hstable : (prefixWord ++ tailWord_676367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676367).length < 2 ^ (prefixWord ++ tailWord_676367).sum := by decide
  have hdescent : baseEnd_676367 < baseStart_676367 := by decide
  rcases family_descends (prefixWord ++ tailWord_676367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676394 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_676394 : Nat := 118140960795 + 676394 * 2 ^ 59
def prefixEnd_676394 : Nat := 4983230072969 + 3 ^ 40 * 676394 * 2
def baseEnd_676394 : Nat := 308724652282072745834957

theorem tailTrace_676394 : CollatzResearch.WordTrace tailWord_676394 prefixEnd_676394 308724652282072745834957 := by
  unfold tailWord_676394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167528977886882935845059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16446743941031687828920157 6167528977886882935845059)
  ·
    refine ⟨9251293466830324403767589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167528977886882935845059 9251293466830324403767589)
    ·
      refine ⟨1734617525030685825706423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9251293466830324403767589 1734617525030685825706423)
      ·
        refine ⟨2601926287546028738559635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734617525030685825706423 2601926287546028738559635)
        ·
          refine ⟨3902889431319043107839453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601926287546028738559635 3902889431319043107839453)
          ·
            refine ⟨1463583536744641165439795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3902889431319043107839453 1463583536744641165439795)
            ·
              refine ⟨2195375305116961748159693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463583536744641165439795 2195375305116961748159693)
              ·
                refine ⟨823265739418860655559885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195375305116961748159693 823265739418860655559885)
                ·
                  refine ⟨308724652282072745834957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823265739418860655559885 308724652282072745834957)
                  ·
                    rfl

theorem cell20_676394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_676394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676394 prefixEnd_676394 := by exact prefixLift 676394
  have htrace : WordTrace (prefixWord ++ tailWord_676394) baseStart_676394 baseEnd_676394 := by
    simpa [prefixWord, tailWord_676394, baseEnd_676394] using wordTrace_append hprefix tailTrace_676394
  have hstable : (prefixWord ++ tailWord_676394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676394).length < 2 ^ (prefixWord ++ tailWord_676394).sum := by decide
  have hdescent : baseEnd_676394 < baseStart_676394 := by decide
  rcases family_descends (prefixWord ++ tailWord_676394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676439 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 2]
def baseStart_676439 : Nat := 118140960795 + 676439 * 2 ^ 59
def prefixEnd_676439 : Nat := 4983230072969 + 3 ^ 40 * 676439 * 2
def baseEnd_676439 : Nat := 308745191508252589334773

theorem tailTrace_676439 : CollatzResearch.WordTrace tailWord_676439 prefixEnd_676439 308745191508252589334773 := by
  unfold tailWord_676439
  simp only [CollatzResearch.WordTrace]
  refine ⟨24671757196384504428768371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16447838130923002952512247 24671757196384504428768371)
  ·
    refine ⟨37007635794576756643152557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24671757196384504428768371 37007635794576756643152557)
    ·
      refine ⟨13877863422966283741182209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37007635794576756643152557 13877863422966283741182209)
      ·
        refine ⟨10408397567224712805886657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13877863422966283741182209 10408397567224712805886657)
        ·
          refine ⟨7806298175418534604414993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10408397567224712805886657 7806298175418534604414993)
          ·
            refine ⟨5854723631563900953311245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806298175418534604414993 5854723631563900953311245)
            ·
              refine ⟨2195521361836462857491717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5854723631563900953311245 2195521361836462857491717)
              ·
                refine ⟨411660255344336785779697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2195521361836462857491717 411660255344336785779697)
                ·
                  refine ⟨308745191508252589334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411660255344336785779697 308745191508252589334773)
                  ·
                    rfl

theorem cell20_676439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2].length) (baseStart_676439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676439 prefixEnd_676439 := by exact prefixLift 676439
  have htrace : WordTrace (prefixWord ++ tailWord_676439) baseStart_676439 baseEnd_676439 := by
    simpa [prefixWord, tailWord_676439, baseEnd_676439] using wordTrace_append hprefix tailTrace_676439
  have hstable : (prefixWord ++ tailWord_676439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676439).length < 2 ^ (prefixWord ++ tailWord_676439).sum := by decide
  have hdescent : baseEnd_676439 < baseStart_676439 := by decide
  rcases family_descends (prefixWord ++ tailWord_676439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676543 : List Nat := [1, 1, 2, 2, 2, 6, 6]
def baseStart_676543 : Nat := 118140960795 + 676543 * 2 ^ 59
def prefixEnd_676543 : Nat := 4983230072969 + 3 ^ 40 * 676543 * 2
def baseEnd_676543 : Nat := 34310295549121161096409

theorem tailTrace_676543 : CollatzResearch.WordTrace tailWord_676543 prefixEnd_676543 34310295549121161096409 := by
  unfold tailWord_676543
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675550388007730190554283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16450366925338486793702855 24675550388007730190554283)
  ·
    refine ⟨37013325582011595285831425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24675550388007730190554283 37013325582011595285831425)
    ·
      refine ⟨27759994186508696464373569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37013325582011595285831425 27759994186508696464373569)
      ·
        refine ⟨20819995639881522348280177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27759994186508696464373569 20819995639881522348280177)
        ·
          refine ⟨15614996729911141761210133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20819995639881522348280177 15614996729911141761210133)
          ·
            refine ⟨731952971714584770056725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15614996729911141761210133 731952971714584770056725)
            ·
              refine ⟨34310295549121161096409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 731952971714584770056725 34310295549121161096409)
              ·
                rfl

theorem cell20_676543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_676543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676543 prefixEnd_676543 := by exact prefixLift 676543
  have htrace : WordTrace (prefixWord ++ tailWord_676543) baseStart_676543 baseEnd_676543 := by
    simpa [prefixWord, tailWord_676543, baseEnd_676543] using wordTrace_append hprefix tailTrace_676543
  have hstable : (prefixWord ++ tailWord_676543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676543).length < 2 ^ (prefixWord ++ tailWord_676543).sum := by decide
  have hdescent : baseEnd_676543 < baseStart_676543 := by decide
  rcases family_descends (prefixWord ++ tailWord_676543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676567 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_676567 : Nat := 118140960795 + 676567 * 2 ^ 59
def prefixEnd_676567 : Nat := 4983230072969 + 3 ^ 40 * 676567 * 2
def baseEnd_676567 : Nat := 308803614196053033067583

theorem tailTrace_676567 : CollatzResearch.WordTrace tailWord_676567 prefixEnd_676567 308803614196053033067583 := by
  unfold tailWord_676567
  simp only [CollatzResearch.WordTrace]
  refine ⟨24676425739920782289427955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16450950493280521526285303 24676425739920782289427955)
  ·
    refine ⟨37014638609881173434141933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24676425739920782289427955 37014638609881173434141933)
    ·
      refine ⟨13880489478705440037803225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37014638609881173434141933 13880489478705440037803225)
      ·
        refine ⟨10410367109029080028352419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13880489478705440037803225 10410367109029080028352419)
        ·
          refine ⟨15615550663543620042528629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10410367109029080028352419 15615550663543620042528629)
          ·
            refine ⟨1463957874707214378987059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15615550663543620042528629 1463957874707214378987059)
            ·
              refine ⟨2195936812060821568480589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463957874707214378987059 2195936812060821568480589)
              ·
                refine ⟨823476304522808088180221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195936812060821568480589 823476304522808088180221)
                ·
                  refine ⟨308803614196053033067583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823476304522808088180221 308803614196053033067583)
                  ·
                    rfl

theorem cell20_676567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_676567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676567 prefixEnd_676567 := by exact prefixLift 676567
  have htrace : WordTrace (prefixWord ++ tailWord_676567) baseStart_676567 baseEnd_676567 := by
    simpa [prefixWord, tailWord_676567, baseEnd_676567] using wordTrace_append hprefix tailTrace_676567
  have hstable : (prefixWord ++ tailWord_676567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676567).length < 2 ^ (prefixWord ++ tailWord_676567).sum := by decide
  have hdescent : baseEnd_676567 < baseStart_676567 := by decide
  rcases family_descends (prefixWord ++ tailWord_676567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676581 : List Nat := [1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_676581 : Nat := 118140960795 + 676581 * 2 ^ 59
def prefixEnd_676581 : Nat := 4983230072969 + 3 ^ 40 * 676581 * 2
def baseEnd_676581 : Nat := 102936668059177068866953

theorem tailTrace_676581 : CollatzResearch.WordTrace tailWord_676581 prefixEnd_676581 102936668059177068866953 := by
  unfold tailWord_676581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24676936361870062680437597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16451290907913375120291731 24676936361870062680437597)
  ·
    refine ⟨9253851135701273505164099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24676936361870062680437597 9253851135701273505164099)
    ·
      refine ⟨13880776703551910257746149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253851135701273505164099 13880776703551910257746149)
      ·
        refine ⟨2602645631915983173327403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13880776703551910257746149 2602645631915983173327403)
        ·
          refine ⟨3903968447873974759991105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602645631915983173327403 3903968447873974759991105)
          ·
            refine ⟨2927976335905481069993329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903968447873974759991105 2927976335905481069993329)
            ·
              refine ⟨2195982251929110802494997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927976335905481069993329 2195982251929110802494997)
              ·
                refine ⟨102936668059177068866953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2195982251929110802494997 102936668059177068866953)
                ·
                  rfl

theorem cell20_676581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_676581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676581 prefixEnd_676581 := by exact prefixLift 676581
  have htrace : WordTrace (prefixWord ++ tailWord_676581) baseStart_676581 baseEnd_676581 := by
    simpa [prefixWord, tailWord_676581, baseEnd_676581] using wordTrace_append hprefix tailTrace_676581
  have hstable : (prefixWord ++ tailWord_676581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676581).length < 2 ^ (prefixWord ++ tailWord_676581).sum := by decide
  have hdescent : baseEnd_676581 < baseStart_676581 := by decide
  rcases family_descends (prefixWord ++ tailWord_676581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676605 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_676605 : Nat := 118140960795 + 676605 * 2 ^ 59
def prefixEnd_676605 : Nat := 4983230072969 + 3 ^ 40 * 676605 * 2
def baseEnd_676605 : Nat := 308820958431493789800761

theorem tailTrace_676605 : CollatzResearch.WordTrace tailWord_676605 prefixEnd_676605 308820958431493789800761 := by
  unfold tailWord_676605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24677811713783114779311269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16451874475855409852874179 24677811713783114779311269)
  ·
    refine ⟨4627089696334334021120863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24677811713783114779311269 4627089696334334021120863)
    ·
      refine ⟨6940634544501501031681295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627089696334334021120863 6940634544501501031681295)
      ·
        refine ⟨10410951816752251547521943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940634544501501031681295 10410951816752251547521943)
        ·
          refine ⟨15616427725128377321282915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10410951816752251547521943 15616427725128377321282915)
          ·
            refine ⟨23424641587692565981924373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15616427725128377321282915 23424641587692565981924373)
            ·
              refine ⟨1098030074423089030402705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23424641587692565981924373 1098030074423089030402705)
              ·
                refine ⟨823522555817316772802029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098030074423089030402705 823522555817316772802029)
                ·
                  refine ⟨308820958431493789800761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823522555817316772802029 308820958431493789800761)
                  ·
                    rfl

theorem cell20_676605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_676605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676605 prefixEnd_676605 := by exact prefixLift 676605
  have htrace : WordTrace (prefixWord ++ tailWord_676605) baseStart_676605 baseEnd_676605 := by
    simpa [prefixWord, tailWord_676605, baseEnd_676605] using wordTrace_append hprefix tailTrace_676605
  have hstable : (prefixWord ++ tailWord_676605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676605).length < 2 ^ (prefixWord ++ tailWord_676605).sum := by decide
  have hdescent : baseEnd_676605 < baseStart_676605 := by decide
  rcases family_descends (prefixWord ++ tailWord_676605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676612 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_676612 : Nat := 118140960795 + 676612 * 2 ^ 59
def prefixEnd_676612 : Nat := 4983230072969 + 3 ^ 40 * 676612 * 2
def baseEnd_676612 : Nat := 308824153422232876567399

theorem tailTrace_676612 : CollatzResearch.WordTrace tailWord_676612 prefixEnd_676612 308824153422232876567399 := by
  unfold tailWord_676612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339033512378877487408045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16452044683171836649877393 12339033512378877487408045)
  ·
    refine ⟨4627137567142079057778017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12339033512378877487408045 4627137567142079057778017)
    ·
      refine ⟨3470353175356559293333513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4627137567142079057778017 3470353175356559293333513)
      ·
        refine ⟨2602764881517419470000135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3470353175356559293333513 2602764881517419470000135)
        ·
          refine ⟨3904147322276129205000203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602764881517419470000135 3904147322276129205000203)
          ·
            refine ⟨5856220983414193807500305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904147322276129205000203 5856220983414193807500305)
            ·
              refine ⟨4392165737560645355625229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5856220983414193807500305 4392165737560645355625229)
              ·
                refine ⟨1647062151585242008359461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392165737560645355625229 1647062151585242008359461)
                ·
                  refine ⟨308824153422232876567399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647062151585242008359461 308824153422232876567399)
                  ·
                    rfl

theorem cell20_676612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_676612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676612 prefixEnd_676612 := by exact prefixLift 676612
  have htrace : WordTrace (prefixWord ++ tailWord_676612) baseStart_676612 baseEnd_676612 := by
    simpa [prefixWord, tailWord_676612, baseEnd_676612] using wordTrace_append hprefix tailTrace_676612
  have hstable : (prefixWord ++ tailWord_676612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676612).length < 2 ^ (prefixWord ++ tailWord_676612).sum := by decide
  have hdescent : baseEnd_676612 < baseStart_676612 := by decide
  rcases family_descends (prefixWord ++ tailWord_676612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676636 : List Nat := [2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_676636 : Nat := 118140960795 + 676636 * 2 ^ 59
def prefixEnd_676636 : Nat := 4983230072969 + 3 ^ 40 * 676636 * 2
def baseEnd_676636 : Nat := 102945035892065153255767

theorem tailTrace_676636 : CollatzResearch.WordTrace tailWord_676636 prefixEnd_676636 102945035892065153255767 := by
  unfold tailWord_676636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339471188335403536844881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16452628251113871382459841 12339471188335403536844881)
  ·
    refine ⟨9254603391251552652633661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12339471188335403536844881 9254603391251552652633661)
    ·
      refine ⟨3470476271719332244737623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9254603391251552652633661 3470476271719332244737623)
      ·
        refine ⟨5205714407578998367106435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3470476271719332244737623 5205714407578998367106435)
        ·
          refine ⟨7808571611368497550659653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205714407578998367106435 7808571611368497550659653)
          ·
            refine ⟨1464107177131593290748685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7808571611368497550659653 1464107177131593290748685)
            ·
              refine ⟨549040191424347484030757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1464107177131593290748685 549040191424347484030757)
              ·
                refine ⟨102945035892065153255767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549040191424347484030757 102945035892065153255767)
                ·
                  rfl

theorem cell20_676636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_676636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676636 prefixEnd_676636 := by exact prefixLift 676636
  have htrace : WordTrace (prefixWord ++ tailWord_676636) baseStart_676636 baseEnd_676636 := by
    simpa [prefixWord, tailWord_676636, baseEnd_676636] using wordTrace_append hprefix tailTrace_676636
  have hstable : (prefixWord ++ tailWord_676636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676636).length < 2 ^ (prefixWord ++ tailWord_676636).sum := by decide
  have hdescent : baseEnd_676636 < baseStart_676636 := by decide
  rcases family_descends (prefixWord ++ tailWord_676636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676653 : List Nat := [1, 5, 3, 2, 1, 1, 7]
def baseStart_676653 : Nat := 118140960795 + 676653 * 2 ^ 59
def prefixEnd_676653 : Nat := 4983230072969 + 3 ^ 40 * 676653 * 2
def baseEnd_676653 : Nat := 34315874104379884022285

theorem tailTrace_676653 : CollatzResearch.WordTrace tailWord_676653 prefixEnd_676653 34315874104379884022285 := by
  unfold tailWord_676653
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679562417609218977058613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16453041611739479318039075 24679562417609218977058613)
  ·
    refine ⟨2313708976650864279099245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24679562417609218977058613 2313708976650864279099245)
    ·
      refine ⟨867640866244074104662217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2313708976650864279099245 867640866244074104662217)
      ·
        refine ⟨650730649683055578496663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867640866244074104662217 650730649683055578496663)
        ·
          refine ⟨976095974524583367744995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650730649683055578496663 976095974524583367744995)
          ·
            refine ⟨1464143961786875051617493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976095974524583367744995 1464143961786875051617493)
            ·
              refine ⟨34315874104379884022285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1464143961786875051617493 34315874104379884022285)
              ·
                rfl

theorem cell20_676653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_676653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676653 prefixEnd_676653 := by exact prefixLift 676653
  have htrace : WordTrace (prefixWord ++ tailWord_676653) baseStart_676653 baseEnd_676653 := by
    simpa [prefixWord, tailWord_676653, baseEnd_676653] using wordTrace_append hprefix tailTrace_676653
  have hstable : (prefixWord ++ tailWord_676653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676653).length < 2 ^ (prefixWord ++ tailWord_676653).sum := by decide
  have hdescent : baseEnd_676653 < baseStart_676653 := by decide
  rcases family_descends (prefixWord ++ tailWord_676653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676660 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_676660 : Nat := 118140960795 + 676660 * 2 ^ 59
def prefixEnd_676660 : Nat := 4983230072969 + 3 ^ 40 * 676660 * 2
def baseEnd_676660 : Nat := 308846061930158042967203

theorem tailTrace_676660 : CollatzResearch.WordTrace tailWord_676660 prefixEnd_676660 308846061930158042967203 := by
  unfold tailWord_676660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339908864291929586281717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16453211819055906115042289 12339908864291929586281717)
  ·
    refine ⟨1156866456027368398713911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12339908864291929586281717 1156866456027368398713911)
    ·
      refine ⟨1735299684041052598070867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156866456027368398713911 1735299684041052598070867)
      ·
        refine ⟨2602949526061578897106301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735299684041052598070867 2602949526061578897106301)
        ·
          refine ⟨976106072273092086414863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602949526061578897106301 976106072273092086414863)
          ·
            refine ⟨1464159108409638129622295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976106072273092086414863 1464159108409638129622295)
            ·
              refine ⟨2196238662614457194433443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464159108409638129622295 2196238662614457194433443)
              ·
                refine ⟨3294357993921685791650165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196238662614457194433443 3294357993921685791650165)
                ·
                  refine ⟨308846061930158042967203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294357993921685791650165 308846061930158042967203)
                  ·
                    rfl

theorem cell20_676660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_676660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676660 prefixEnd_676660 := by exact prefixLift 676660
  have htrace : WordTrace (prefixWord ++ tailWord_676660) baseStart_676660 baseEnd_676660 := by
    simpa [prefixWord, tailWord_676660, baseEnd_676660] using wordTrace_append hprefix tailTrace_676660
  have hstable : (prefixWord ++ tailWord_676660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676660).length < 2 ^ (prefixWord ++ tailWord_676660).sum := by decide
  have hdescent : baseEnd_676660 < baseStart_676660 := by decide
  rcases family_descends (prefixWord ++ tailWord_676660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676664 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_676664 : Nat := 118140960795 + 676664 * 2 ^ 59
def prefixEnd_676664 : Nat := 4983230072969 + 3 ^ 40 * 676664 * 2
def baseEnd_676664 : Nat := 308847887639151806833853

theorem tailTrace_676664 : CollatzResearch.WordTrace tailWord_676664 prefixEnd_676664 308847887639151806833853 := by
  unfold tailWord_676664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339981810284683927854523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16453309080379578570472697 12339981810284683927854523)
  ·
    refine ⟨18509972715427025891781785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12339981810284683927854523 18509972715427025891781785)
    ·
      refine ⟨13882479536570269418836339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18509972715427025891781785 13882479536570269418836339)
      ·
        refine ⟨20823719304855404128254509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882479536570269418836339 20823719304855404128254509)
        ·
          refine ⟨7808894739320776548095441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20823719304855404128254509 7808894739320776548095441)
          ·
            refine ⟨5856671054490582411071581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7808894739320776548095441 5856671054490582411071581)
            ·
              refine ⟨2196251645433968404151843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5856671054490582411071581 2196251645433968404151843)
              ·
                refine ⟨3294377468150952606227765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196251645433968404151843 3294377468150952606227765)
                ·
                  refine ⟨308847887639151806833853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294377468150952606227765 308847887639151806833853)
                  ·
                    rfl

theorem cell20_676664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_676664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676664 prefixEnd_676664 := by exact prefixLift 676664
  have htrace : WordTrace (prefixWord ++ tailWord_676664) baseStart_676664 baseEnd_676664 := by
    simpa [prefixWord, tailWord_676664, baseEnd_676664] using wordTrace_append hprefix tailTrace_676664
  have hstable : (prefixWord ++ tailWord_676664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676664).length < 2 ^ (prefixWord ++ tailWord_676664).sum := by decide
  have hdescent : baseEnd_676664 < baseStart_676664 := by decide
  rcases family_descends (prefixWord ++ tailWord_676664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676695 : List Nat := [1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_676695 : Nat := 118140960795 + 676695 * 2 ^ 59
def prefixEnd_676695 : Nat := 4983230072969 + 3 ^ 40 * 676695 * 2
def baseEnd_676695 : Nat := 102954012294617825600131

theorem tailTrace_676695 : CollatzResearch.WordTrace tailWord_676695 prefixEnd_676695 102954012294617825600131 := by
  unfold tailWord_676695
  simp only [CollatzResearch.WordTrace]
  refine ⟨24681094283457060150087539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16454062855638040100058359 24681094283457060150087539)
  ·
    refine ⟨37021641425185590225131309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24681094283457060150087539 37021641425185590225131309)
    ·
      refine ⟨13883115534444596334424241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37021641425185590225131309 13883115534444596334424241)
      ·
        refine ⟨10412336650833447250818181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13883115534444596334424241 10412336650833447250818181)
        ·
          refine ⟨1952313122031271359528409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10412336650833447250818181 1952313122031271359528409)
          ·
            refine ⟨1464234841523453519646307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1952313122031271359528409 1464234841523453519646307)
            ·
              refine ⟨2196352262285180279469461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464234841523453519646307 2196352262285180279469461)
              ·
                refine ⟨102954012294617825600131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2196352262285180279469461 102954012294617825600131)
                ·
                  rfl

theorem cell20_676695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_676695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676695 prefixEnd_676695 := by exact prefixLift 676695
  have htrace : WordTrace (prefixWord ++ tailWord_676695) baseStart_676695 baseEnd_676695 := by
    simpa [prefixWord, tailWord_676695, baseEnd_676695] using wordTrace_append hprefix tailTrace_676695
  have hstable : (prefixWord ++ tailWord_676695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676695).length < 2 ^ (prefixWord ++ tailWord_676695).sum := by decide
  have hdescent : baseEnd_676695 < baseStart_676695 := by decide
  rcases family_descends (prefixWord ++ tailWord_676695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676709 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_676709 : Nat := 118140960795 + 676709 * 2 ^ 59
def prefixEnd_676709 : Nat := 4983230072969 + 3 ^ 40 * 676709 * 2
def baseEnd_676709 : Nat := 308868426865331650333669

theorem tailTrace_676709 : CollatzResearch.WordTrace tailWord_676709 prefixEnd_676709 308868426865331650333669 := by
  unfold tailWord_676709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24681604905406340541097181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16454403270270893694064787 24681604905406340541097181)
  ·
    refine ⟨9255601839527377702911443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24681604905406340541097181 9255601839527377702911443)
    ·
      refine ⟨13883402759291066554367165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9255601839527377702911443 13883402759291066554367165)
      ·
        refine ⟨5206276034734149957887687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13883402759291066554367165 5206276034734149957887687)
        ·
          refine ⟨7809414052101224936831531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206276034734149957887687 7809414052101224936831531)
          ·
            refine ⟨11714121078151837405247297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809414052101224936831531 11714121078151837405247297)
            ·
              refine ⟨8785590808613878053935473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11714121078151837405247297 8785590808613878053935473)
              ·
                refine ⟨6589193106460408540451605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8785590808613878053935473 6589193106460408540451605)
                ·
                  refine ⟨308868426865331650333669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6589193106460408540451605 308868426865331650333669)
                  ·
                    rfl

theorem cell20_676709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_676709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676709 prefixEnd_676709 := by exact prefixLift 676709
  have htrace : WordTrace (prefixWord ++ tailWord_676709) baseStart_676709 baseEnd_676709 := by
    simpa [prefixWord, tailWord_676709, baseEnd_676709] using wordTrace_append hprefix tailTrace_676709
  have hstable : (prefixWord ++ tailWord_676709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676709).length < 2 ^ (prefixWord ++ tailWord_676709).sum := by decide
  have hdescent : baseEnd_676709 < baseStart_676709 := by decide
  rcases family_descends (prefixWord ++ tailWord_676709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676747 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_676747 : Nat := 118140960795 + 676747 * 2 ^ 59
def prefixEnd_676747 : Nat := 4983230072969 + 3 ^ 40 * 676747 * 2
def baseEnd_676747 : Nat := 308885771100772407066847

theorem tailTrace_676747 : CollatzResearch.WordTrace tailWord_676747 prefixEnd_676747 308885771100772407066847 := by
  unfold tailWord_676747
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682990879268673030980495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16455327252845782020653663 24682990879268673030980495)
  ·
    refine ⟨37024486318903009546470743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24682990879268673030980495 37024486318903009546470743)
    ·
      refine ⟨55536729478354514319706115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37024486318903009546470743 55536729478354514319706115)
      ·
        refine ⟨83305094217531771479559173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55536729478354514319706115 83305094217531771479559173)
        ·
          refine ⟨15619705165787207152417345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83305094217531771479559173 15619705165787207152417345)
          ·
            refine ⟨11714778874340405364313009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15619705165787207152417345 11714778874340405364313009)
            ·
              refine ⟨8786084155755304023234757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11714778874340405364313009 8786084155755304023234757)
              ·
                refine ⟨1647390779204119504356517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8786084155755304023234757 1647390779204119504356517)
                ·
                  refine ⟨308885771100772407066847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647390779204119504356517 308885771100772407066847)
                  ·
                    rfl

theorem cell20_676747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_676747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676747 prefixEnd_676747 := by exact prefixLift 676747
  have htrace : WordTrace (prefixWord ++ tailWord_676747) baseStart_676747 baseEnd_676747 := by
    simpa [prefixWord, tailWord_676747, baseEnd_676747] using wordTrace_append hprefix tailTrace_676747
  have hstable : (prefixWord ++ tailWord_676747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676747).length < 2 ^ (prefixWord ++ tailWord_676747).sum := by decide
  have hdescent : baseEnd_676747 < baseStart_676747 := by decide
  rcases family_descends (prefixWord ++ tailWord_676747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676874 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_676874 : Nat := 118140960795 + 676874 * 2 ^ 59
def prefixEnd_676874 : Nat := 4983230072969 + 3 ^ 40 * 676874 * 2
def baseEnd_676874 : Nat := 308943737361324409832995

theorem tailTrace_676874 : CollatzResearch.WordTrace tailWord_676874 prefixEnd_676874 308943737361324409832995 := by
  unfold tailWord_676874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171905737452143430213419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16458415299872382480569117 6171905737452143430213419)
  ·
    refine ⟨9257858606178215145320129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6171905737452143430213419 9257858606178215145320129)
    ·
      refine ⟨6943393954633661358990097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9257858606178215145320129 6943393954633661358990097)
      ·
        refine ⟨5207545465975246019242573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6943393954633661358990097 5207545465975246019242573)
        ·
          refine ⟨1952829549740717257215965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5207545465975246019242573 1952829549740717257215965)
          ·
            refine ⟨732311081152768971455987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1952829549740717257215965 732311081152768971455987)
            ·
              refine ⟨1098466621729153457183981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732311081152768971455987 1098466621729153457183981)
              ·
                refine ⟨411924983148432546443993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098466621729153457183981 411924983148432546443993)
                ·
                  refine ⟨308943737361324409832995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411924983148432546443993 308943737361324409832995)
                  ·
                    rfl

theorem cell20_676874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_676874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676874 prefixEnd_676874 := by exact prefixLift 676874
  have htrace : WordTrace (prefixWord ++ tailWord_676874) baseStart_676874 baseEnd_676874 := by
    simpa [prefixWord, tailWord_676874, baseEnd_676874] using wordTrace_append hprefix tailTrace_676874
  have hstable : (prefixWord ++ tailWord_676874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676874).length < 2 ^ (prefixWord ++ tailWord_676874).sum := by decide
  have hdescent : baseEnd_676874 < baseStart_676874 := by decide
  rcases family_descends (prefixWord ++ tailWord_676874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676885 : List Nat := [1, 3, 2, 1, 4, 3, 6]
def baseStart_676885 : Nat := 118140960795 + 676885 * 2 ^ 59
def prefixEnd_676885 : Nat := 4983230072969 + 3 ^ 40 * 676885 * 2
def baseEnd_676885 : Nat := 34327639784561917829587

theorem tailTrace_676885 : CollatzResearch.WordTrace tailWord_676885 prefixEnd_676885 34327639784561917829587 := by
  unfold tailWord_676885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688024152768722599504109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16458682768512481733002739 24688024152768722599504109)
  ·
    refine ⟨9258009057288270974814041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24688024152768722599504109 9258009057288270974814041)
    ·
      refine ⟨6943506792966203231110531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9258009057288270974814041 6943506792966203231110531)
      ·
        refine ⟨10415260189449304846665797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943506792966203231110531 10415260189449304846665797)
        ·
          refine ⟨1952861285521744658749837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10415260189449304846665797 1952861285521744658749837)
          ·
            refine ⟨732322982070654247031189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1952861285521744658749837 732322982070654247031189)
            ·
              refine ⟨34327639784561917829587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 732322982070654247031189 34327639784561917829587)
              ·
                rfl

theorem cell20_676885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_676885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676885 prefixEnd_676885 := by exact prefixLift 676885
  have htrace : WordTrace (prefixWord ++ tailWord_676885) baseStart_676885 baseEnd_676885 := by
    simpa [prefixWord, tailWord_676885, baseEnd_676885] using wordTrace_append hprefix tailTrace_676885
  have hstable : (prefixWord ++ tailWord_676885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676885).length < 2 ^ (prefixWord ++ tailWord_676885).sum := by decide
  have hdescent : baseEnd_676885 < baseStart_676885 := by decide
  rcases family_descends (prefixWord ++ tailWord_676885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676957 : List Nat := [1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_676957 : Nat := 118140960795 + 676957 * 2 ^ 59
def prefixEnd_676957 : Nat := 4983230072969 + 3 ^ 40 * 676957 * 2
def baseEnd_676957 : Nat := 102993873607648336688663

theorem tailTrace_676957 : CollatzResearch.WordTrace tailWord_676957 prefixEnd_676957 102993873607648336688663 := by
  unfold tailWord_676957
  simp only [CollatzResearch.WordTrace]
  refine ⟨24690650208507878896125125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16460433472338585930750083 24690650208507878896125125)
  ·
    refine ⟨4629496914095227293023461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24690650208507878896125125 4629496914095227293023461)
    ·
      refine ⟨868030671392855117441899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4629496914095227293023461 868030671392855117441899)
      ·
        refine ⟨1302046007089282676162849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868030671392855117441899 1302046007089282676162849)
        ·
          refine ⟨976534505316962007122137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302046007089282676162849 976534505316962007122137)
          ·
            refine ⟨732400878987721505341603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976534505316962007122137 732400878987721505341603)
            ·
              refine ⟨1098601318481582258012405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732400878987721505341603 1098601318481582258012405)
              ·
                refine ⟨102993873607648336688663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1098601318481582258012405 102993873607648336688663)
                ·
                  rfl

theorem cell20_676957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_676957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676957 prefixEnd_676957 := by exact prefixLift 676957
  have htrace : WordTrace (prefixWord ++ tailWord_676957) baseStart_676957 baseEnd_676957 := by
    simpa [prefixWord, tailWord_676957, baseEnd_676957] using wordTrace_append hprefix tailTrace_676957
  have hstable : (prefixWord ++ tailWord_676957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676957).length < 2 ^ (prefixWord ++ tailWord_676957).sum := by decide
  have hdescent : baseEnd_676957 < baseStart_676957 := by decide
  rcases family_descends (prefixWord ++ tailWord_676957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676975 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_676975 : Nat := 118140960795 + 676975 * 2 ^ 59
def prefixEnd_676975 : Nat := 4983230072969 + 3 ^ 40 * 676975 * 2
def baseEnd_676975 : Nat := 308989836513416947465915

theorem tailTrace_676975 : CollatzResearch.WordTrace tailWord_676975 prefixEnd_676975 308989836513416947465915 := by
  unfold tailWord_676975
  simp only [CollatzResearch.WordTrace]
  refine ⟨24691306722442667970280379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16460871148295111980186919 24691306722442667970280379)
  ·
    refine ⟨37036960083664001955420569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24691306722442667970280379 37036960083664001955420569)
    ·
      refine ⟨27777720062748001466565427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37036960083664001955420569 27777720062748001466565427)
      ·
        refine ⟨41666580094122002199848141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27777720062748001466565427 41666580094122002199848141)
        ·
          refine ⟨15624967535295750824943053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41666580094122002199848141 15624967535295750824943053)
          ·
            refine ⟨5859362825735906559353645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15624967535295750824943053 5859362825735906559353645)
            ·
              refine ⟨2197261059650964959757617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5859362825735906559353645 2197261059650964959757617)
              ·
                refine ⟨1647945794738223719818213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197261059650964959757617 1647945794738223719818213)
                ·
                  refine ⟨308989836513416947465915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647945794738223719818213 308989836513416947465915)
                  ·
                    rfl

theorem cell20_676975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_676975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676975 prefixEnd_676975 := by exact prefixLift 676975
  have htrace : WordTrace (prefixWord ++ tailWord_676975) baseStart_676975 baseEnd_676975 := by
    simpa [prefixWord, tailWord_676975, baseEnd_676975] using wordTrace_append hprefix tailTrace_676975
  have hstable : (prefixWord ++ tailWord_676975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676975).length < 2 ^ (prefixWord ++ tailWord_676975).sum := by decide
  have hdescent : baseEnd_676975 < baseStart_676975 := by decide
  rcases family_descends (prefixWord ++ tailWord_676975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676992 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_676992 : Nat := 118140960795 + 676992 * 2 ^ 59
def prefixEnd_676992 : Nat := 4983230072969 + 3 ^ 40 * 676992 * 2
def baseEnd_676992 : Nat := 308997595776640443899179

theorem tailTrace_676992 : CollatzResearch.WordTrace tailWord_676992 prefixEnd_676992 308997595776640443899179 := by
  unfold tailWord_676992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345963381690539936824615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16461284508920719915766153 12345963381690539936824615)
  ·
    refine ⟨18518945072535809905236923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12345963381690539936824615 18518945072535809905236923)
    ·
      refine ⟨27778417608803714857855385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18518945072535809905236923 27778417608803714857855385)
      ·
        refine ⟨20833813206602786143391539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27778417608803714857855385 20833813206602786143391539)
        ·
          refine ⟨31250719809904179215087309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20833813206602786143391539 31250719809904179215087309)
          ·
            refine ⟨11719019928714067205657741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31250719809904179215087309 11719019928714067205657741)
            ·
              refine ⟨4394632473267775202121653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11719019928714067205657741 4394632473267775202121653)
              ·
                refine ⟨411996794368853925198905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4394632473267775202121653 411996794368853925198905)
                ·
                  refine ⟨308997595776640443899179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411996794368853925198905 308997595776640443899179)
                  ·
                    rfl

theorem cell20_676992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_676992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_676992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_676992 prefixEnd_676992 := by exact prefixLift 676992
  have htrace : WordTrace (prefixWord ++ tailWord_676992) baseStart_676992 baseEnd_676992 := by
    simpa [prefixWord, tailWord_676992, baseEnd_676992] using wordTrace_append hprefix tailTrace_676992
  have hstable : (prefixWord ++ tailWord_676992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676992).length < 2 ^ (prefixWord ++ tailWord_676992).sum := by decide
  have hdescent : baseEnd_676992 < baseStart_676992 := by decide
  rcases family_descends (prefixWord ++ tailWord_676992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677096 : List Nat := [2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_677096 : Nat := 118140960795 + 677096 * 2 ^ 59
def prefixEnd_677096 : Nat := 4983230072969 + 3 ^ 40 * 677096 * 2
def baseEnd_677096 : Nat := 103015021403492768144029

theorem tailTrace_677096 : CollatzResearch.WordTrace tailWord_677096 prefixEnd_677096 103015021403492768144029 := by
  unfold tailWord_677096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347859977502152817717571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16463813303336203756956761 12347859977502152817717571)
  ·
    refine ⟨18521789966253229226576357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12347859977502152817717571 18521789966253229226576357)
    ·
      refine ⟨3472835618672480479983067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18521789966253229226576357 3472835618672480479983067)
      ·
        refine ⟨5209253428008720719974601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472835618672480479983067 5209253428008720719974601)
        ·
          refine ⟨3906940071006540539980951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5209253428008720719974601 3906940071006540539980951)
          ·
            refine ⟨5860410106509810809971427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906940071006540539980951 5860410106509810809971427)
            ·
              refine ⟨8790615159764716214957141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860410106509810809971427 8790615159764716214957141)
              ·
                refine ⟨103015021403492768144029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8790615159764716214957141 103015021403492768144029)
                ·
                  rfl

theorem cell20_677096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_677096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677096 prefixEnd_677096 := by exact prefixLift 677096
  have htrace : WordTrace (prefixWord ++ tailWord_677096) baseStart_677096 baseEnd_677096 := by
    simpa [prefixWord, tailWord_677096, baseEnd_677096] using wordTrace_append hprefix tailTrace_677096
  have hstable : (prefixWord ++ tailWord_677096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677096).length < 2 ^ (prefixWord ++ tailWord_677096).sum := by decide
  have hdescent : baseEnd_677096 < baseStart_677096 := by decide
  rcases family_descends (prefixWord ++ tailWord_677096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677123 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 2]
def baseStart_677123 : Nat := 118140960795 + 677123 * 2 ^ 59
def prefixEnd_677123 : Nat := 4983230072969 + 3 ^ 40 * 677123 * 2
def baseEnd_677123 : Nat := 309057387746186210531977

theorem tailTrace_677123 : CollatzResearch.WordTrace tailWord_677123 prefixEnd_677123 309057387746186210531977 := by
  unfold tailWord_677123
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696704725906489246668023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464469817270992831112015 24696704725906489246668023)
  ·
    refine ⟨37045057088859733870002035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24696704725906489246668023 37045057088859733870002035)
    ·
      refine ⟨55567585633289600805003053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37045057088859733870002035 55567585633289600805003053)
      ·
        refine ⟨20837844612483600301876145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55567585633289600805003053 20837844612483600301876145)
        ·
          refine ⟨15628383459362700226407109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20837844612483600301876145 15628383459362700226407109)
          ·
            refine ⟨2930321898630506292451333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15628383459362700226407109 2930321898630506292451333)
            ·
              refine ⟨549435355993219929834625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2930321898630506292451333 549435355993219929834625)
              ·
                refine ⟨412076516994914947375969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549435355993219929834625 412076516994914947375969)
                ·
                  refine ⟨309057387746186210531977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412076516994914947375969 309057387746186210531977)
                  ·
                    rfl

theorem cell20_677123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2].length) (baseStart_677123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677123 prefixEnd_677123 := by exact prefixLift 677123
  have htrace : WordTrace (prefixWord ++ tailWord_677123) baseStart_677123 baseEnd_677123 := by
    simpa [prefixWord, tailWord_677123, baseEnd_677123] using wordTrace_append hprefix tailTrace_677123
  have hstable : (prefixWord ++ tailWord_677123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677123).length < 2 ^ (prefixWord ++ tailWord_677123).sum := by decide
  have hdescent : baseEnd_677123 < baseStart_677123 := by decide
  rcases family_descends (prefixWord ++ tailWord_677123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677141 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_677141 : Nat := 118140960795 + 677141 * 2 ^ 59
def prefixEnd_677141 : Nat := 4983230072969 + 3 ^ 40 * 677141 * 2
def baseEnd_677141 : Nat := 309065603436658147931903

theorem tailTrace_677141 : CollatzResearch.WordTrace tailWord_677141 prefixEnd_677141 309065603436658147931903 := by
  unfold tailWord_677141
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697361239841278320823277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464907493227518880548851 24697361239841278320823277)
  ·
    refine ⟨9261510464940479370308729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24697361239841278320823277 9261510464940479370308729)
    ·
      refine ⟨6946132848705359527731547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9261510464940479370308729 6946132848705359527731547)
      ·
        refine ⟨10419199273058039291597321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6946132848705359527731547 10419199273058039291597321)
        ·
          refine ⟨7814399454793529468697991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10419199273058039291597321 7814399454793529468697991)
          ·
            refine ⟨11721599182190294203046987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814399454793529468697991 11721599182190294203046987)
            ·
              refine ⟨17582398773285441304570481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721599182190294203046987 17582398773285441304570481)
              ·
                refine ⟨13186799079964080978427861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17582398773285441304570481 13186799079964080978427861)
                ·
                  refine ⟨309065603436658147931903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13186799079964080978427861 309065603436658147931903)
                  ·
                    rfl

theorem cell20_677141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_677141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677141 prefixEnd_677141 := by exact prefixLift 677141
  have htrace : WordTrace (prefixWord ++ tailWord_677141) baseStart_677141 baseEnd_677141 := by
    simpa [prefixWord, tailWord_677141, baseEnd_677141] using wordTrace_append hprefix tailTrace_677141
  have hstable : (prefixWord ++ tailWord_677141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677141).length < 2 ^ (prefixWord ++ tailWord_677141).sum := by decide
  have hdescent : baseEnd_677141 < baseStart_677141 := by decide
  rcases family_descends (prefixWord ++ tailWord_677141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677182 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_677182 : Nat := 118140960795 + 677182 * 2 ^ 59
def prefixEnd_677182 : Nat := 4983230072969 + 3 ^ 40 * 677182 * 2
def baseEnd_677182 : Nat := 309084316953844227565069

theorem tailTrace_677182 : CollatzResearch.WordTrace tailWord_677182 prefixEnd_677182 309084316953844227565069 := by
  unfold tailWord_677182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087357079086592790383225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16465904421795161548710533 3087357079086592790383225)
  ·
    refine ⟨2315517809314944592787419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3087357079086592790383225 2315517809314944592787419)
    ·
      refine ⟨3473276713972416889181129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315517809314944592787419 3473276713972416889181129)
      ·
        refine ⟨2604957535479312666885847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3473276713972416889181129 2604957535479312666885847)
        ·
          refine ⟨3907436303218969000328771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604957535479312666885847 3907436303218969000328771)
          ·
            refine ⟨5861154454828453500493157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907436303218969000328771 5861154454828453500493157)
            ·
              refine ⟨1098966460280335031342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5861154454828453500493157 1098966460280335031342467)
              ·
                refine ⟨1648449690420502547013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098966460280335031342467 1648449690420502547013701)
                ·
                  refine ⟨309084316953844227565069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648449690420502547013701 309084316953844227565069)
                  ·
                    rfl

theorem cell20_677182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_677182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677182 prefixEnd_677182 := by exact prefixLift 677182
  have htrace : WordTrace (prefixWord ++ tailWord_677182) baseStart_677182 baseEnd_677182 := by
    simpa [prefixWord, tailWord_677182, baseEnd_677182] using wordTrace_append hprefix tailTrace_677182
  have hstable : (prefixWord ++ tailWord_677182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677182).length < 2 ^ (prefixWord ++ tailWord_677182).sum := by decide
  have hdescent : baseEnd_677182 < baseStart_677182 := by decide
  rcases family_descends (prefixWord ++ tailWord_677182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677234 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_677234 : Nat := 118140960795 + 677234 * 2 ^ 59
def prefixEnd_677234 : Nat := 4983230072969 + 3 ^ 40 * 677234 * 2
def baseEnd_677234 : Nat := 309108051170763157831523

theorem tailTrace_677234 : CollatzResearch.WordTrace tailWord_677234 prefixEnd_677234 309108051170763157831523 := by
  unfold tailWord_677234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175188307126088800989689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16467168819002903469305837 6175188307126088800989689)
  ·
    refine ⟨4631391230344566600742267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6175188307126088800989689 4631391230344566600742267)
    ·
      refine ⟨6947086845516849901113401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631391230344566600742267 6947086845516849901113401)
      ·
        refine ⟨5210315134137637425835051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6947086845516849901113401 5210315134137637425835051)
        ·
          refine ⟨7815472701206456138752577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210315134137637425835051 7815472701206456138752577)
          ·
            refine ⟨5861604525904842104064433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7815472701206456138752577 5861604525904842104064433)
            ·
              refine ⟨4396203394428631578048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861604525904842104064433 4396203394428631578048325)
              ·
                refine ⟨824288136455368420884061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396203394428631578048325 824288136455368420884061)
                ·
                  refine ⟨309108051170763157831523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824288136455368420884061 309108051170763157831523)
                  ·
                    rfl

theorem cell20_677234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_677234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677234 prefixEnd_677234 := by exact prefixLift 677234
  have htrace : WordTrace (prefixWord ++ tailWord_677234) baseStart_677234 baseEnd_677234 := by
    simpa [prefixWord, tailWord_677234, baseEnd_677234] using wordTrace_append hprefix tailTrace_677234
  have hstable : (prefixWord ++ tailWord_677234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677234).length < 2 ^ (prefixWord ++ tailWord_677234).sum := by decide
  have hdescent : baseEnd_677234 < baseStart_677234 := by decide
  rcases family_descends (prefixWord ++ tailWord_677234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677237 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_677237 : Nat := 118140960795 + 677237 * 2 ^ 59
def prefixEnd_677237 : Nat := 4983230072969 + 3 ^ 40 * 677237 * 2
def baseEnd_677237 : Nat := 309109420452508480731511

theorem tailTrace_677237 : CollatzResearch.WordTrace tailWord_677237 prefixEnd_677237 309109420452508480731511 := by
  unfold tailWord_677237
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700862647493486716317965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467241764995657810878643 24700862647493486716317965)
  ·
    refine ⟨9262823492810057518619237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24700862647493486716317965 9262823492810057518619237)
    ·
      refine ⟨1736779404901885784741107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9262823492810057518619237 1736779404901885784741107)
      ·
        refine ⟨2605169107352828677111661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736779404901885784741107 2605169107352828677111661)
        ·
          refine ⟨976938415257310753916873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2605169107352828677111661 976938415257310753916873)
          ·
            refine ⟨732703811442983065437655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976938415257310753916873 732703811442983065437655)
            ·
              refine ⟨1099055717164474598156483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732703811442983065437655 1099055717164474598156483)
              ·
                refine ⟨1648583575746711897234725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099055717164474598156483 1648583575746711897234725)
                ·
                  refine ⟨309109420452508480731511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648583575746711897234725 309109420452508480731511)
                  ·
                    rfl

theorem cell20_677237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_677237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677237 prefixEnd_677237 := by exact prefixLift 677237
  have htrace : WordTrace (prefixWord ++ tailWord_677237) baseStart_677237 baseEnd_677237 := by
    simpa [prefixWord, tailWord_677237, baseEnd_677237] using wordTrace_append hprefix tailTrace_677237
  have hstable : (prefixWord ++ tailWord_677237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677237).length < 2 ^ (prefixWord ++ tailWord_677237).sum := by decide
  have hdescent : baseEnd_677237 < baseStart_677237 := by decide
  rcases family_descends (prefixWord ++ tailWord_677237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677241 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_677241 : Nat := 118140960795 + 677241 * 2 ^ 59
def prefixEnd_677241 : Nat := 4983230072969 + 3 ^ 40 * 677241 * 2
def baseEnd_677241 : Nat := 309111246161502244598161

theorem tailTrace_677241 : CollatzResearch.WordTrace tailWord_677241 prefixEnd_677241 309111246161502244598161 := by
  unfold tailWord_677241
  simp only [CollatzResearch.WordTrace]
  refine ⟨24701008539478995399463577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467339026319330266309051 24701008539478995399463577)
  ·
    refine ⟨18525756404609246549597683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24701008539478995399463577 18525756404609246549597683)
    ·
      refine ⟨27788634606913869824396525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18525756404609246549597683 27788634606913869824396525)
      ·
        refine ⟨10420737977592701184148697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27788634606913869824396525 10420737977592701184148697)
        ·
          refine ⟨7815553483194525888111523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10420737977592701184148697 7815553483194525888111523)
          ·
            refine ⟨11723330224791788832167285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815553483194525888111523 11723330224791788832167285)
            ·
              refine ⟨1099062208574230203015683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11723330224791788832167285 1099062208574230203015683)
              ·
                refine ⟨1648593312861345304523525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099062208574230203015683 1648593312861345304523525)
                ·
                  refine ⟨309111246161502244598161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648593312861345304523525 309111246161502244598161)
                  ·
                    rfl

theorem cell20_677241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_677241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677241 prefixEnd_677241 := by exact prefixLift 677241
  have htrace : WordTrace (prefixWord ++ tailWord_677241) baseStart_677241 baseEnd_677241 := by
    simpa [prefixWord, tailWord_677241, baseEnd_677241] using wordTrace_append hprefix tailTrace_677241
  have hstable : (prefixWord ++ tailWord_677241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677241).length < 2 ^ (prefixWord ++ tailWord_677241).sum := by decide
  have hdescent : baseEnd_677241 < baseStart_677241 := by decide
  rcases family_descends (prefixWord ++ tailWord_677241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677251 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 3]
def baseStart_677251 : Nat := 118140960795 + 677251 * 2 ^ 59
def prefixEnd_677251 : Nat := 4983230072969 + 3 ^ 40 * 677251 * 2
def baseEnd_677251 : Nat := 309115810433986654264787

theorem tailTrace_677251 : CollatzResearch.WordTrace tailWord_677251 prefixEnd_677251 309115810433986654264787 := by
  unfold tailWord_677251
  simp only [CollatzResearch.WordTrace]
  refine ⟨24701373269442767107327607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467582179628511404885071 24701373269442767107327607)
  ·
    refine ⟨37052059904164150660991411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24701373269442767107327607 37052059904164150660991411)
    ·
      refine ⟨55578089856246225991487117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37052059904164150660991411 55578089856246225991487117)
      ·
        refine ⟨20841783696092334746807669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55578089856246225991487117 20841783696092334746807669)
        ·
          refine ⟨1953917221508656382513219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20841783696092334746807669 1953917221508656382513219)
          ·
            refine ⟨2930875832262984573769829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953917221508656382513219 2930875832262984573769829)
            ·
              refine ⟨549539218549309607581843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2930875832262984573769829 549539218549309607581843)
              ·
                refine ⟨824308827823964411372765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549539218549309607581843 824308827823964411372765)
                ·
                  refine ⟨309115810433986654264787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824308827823964411372765 309115810433986654264787)
                  ·
                    rfl

theorem cell20_677251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3].length) (baseStart_677251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677251 prefixEnd_677251 := by exact prefixLift 677251
  have htrace : WordTrace (prefixWord ++ tailWord_677251) baseStart_677251 baseEnd_677251 := by
    simpa [prefixWord, tailWord_677251, baseEnd_677251] using wordTrace_append hprefix tailTrace_677251
  have hstable : (prefixWord ++ tailWord_677251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677251).length < 2 ^ (prefixWord ++ tailWord_677251).sum := by decide
  have hdescent : baseEnd_677251 < baseStart_677251 := by decide
  rcases family_descends (prefixWord ++ tailWord_677251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677288 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_677288 : Nat := 118140960795 + 677288 * 2 ^ 59
def prefixEnd_677288 : Nat := 4983230072969 + 3 ^ 40 * 677288 * 2
def baseEnd_677288 : Nat := 309132698242178970031303

theorem tailTrace_677288 : CollatzResearch.WordTrace tailWord_677288 prefixEnd_677288 309132698242178970031303 := by
  unfold tailWord_677288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351361385154361213212259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16468481846872481617616345 12351361385154361213212259)
  ·
    refine ⟨18527042077731541819818389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12351361385154361213212259 18527042077731541819818389)
    ·
      refine ⟨868455097393666022803987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18527042077731541819818389 868455097393666022803987)
      ·
        refine ⟨1302682646090499034205981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868455097393666022803987 1302682646090499034205981)
        ·
          refine ⟨488505992283937137827243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1302682646090499034205981 488505992283937137827243)
          ·
            refine ⟨732758988425905706740865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488505992283937137827243 732758988425905706740865)
            ·
              refine ⟨549569241319429280055649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732758988425905706740865 549569241319429280055649)
              ·
                refine ⟨412176930989571960041737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549569241319429280055649 412176930989571960041737)
                ·
                  refine ⟨309132698242178970031303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412176930989571960041737 309132698242178970031303)
                  ·
                    rfl

theorem cell20_677288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_677288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677288 prefixEnd_677288 := by exact prefixLift 677288
  have htrace : WordTrace (prefixWord ++ tailWord_677288) baseStart_677288 baseEnd_677288 := by
    simpa [prefixWord, tailWord_677288, baseEnd_677288] using wordTrace_append hprefix tailTrace_677288
  have hstable : (prefixWord ++ tailWord_677288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677288).length < 2 ^ (prefixWord ++ tailWord_677288).sum := by decide
  have hdescent : baseEnd_677288 < baseStart_677288 := by decide
  rcases family_descends (prefixWord ++ tailWord_677288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677396 : List Nat := [2, 4, 3, 1, 2, 2, 6]
def baseStart_677396 : Nat := 118140960795 + 677396 * 2 ^ 59
def prefixEnd_677396 : Nat := 4983230072969 + 3 ^ 40 * 677396 * 2
def baseEnd_677396 : Nat := 34353554709445621603429

theorem tailTrace_677396 : CollatzResearch.WordTrace tailWord_677396 prefixEnd_677396 34353554709445621603429 := by
  unfold tailWord_677396
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353330926958728435678021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16471107902611637914237361 12353330926958728435678021)
  ·
    refine ⟨2316249548804761581689629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12353330926958728435678021 2316249548804761581689629)
    ·
      refine ⟨868593580801785593133611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2316249548804761581689629 868593580801785593133611)
      ·
        refine ⟨1302890371202678389700417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868593580801785593133611 1302890371202678389700417)
        ·
          refine ⟨977167778402008792275313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302890371202678389700417 977167778402008792275313)
          ·
            refine ⟨732875833801506594206485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977167778402008792275313 732875833801506594206485)
            ·
              refine ⟨34353554709445621603429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 732875833801506594206485 34353554709445621603429)
              ·
                rfl

theorem cell20_677396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_677396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677396 prefixEnd_677396 := by exact prefixLift 677396
  have htrace : WordTrace (prefixWord ++ tailWord_677396) baseStart_677396 baseEnd_677396 := by
    simpa [prefixWord, tailWord_677396, baseEnd_677396] using wordTrace_append hprefix tailTrace_677396
  have hstable : (prefixWord ++ tailWord_677396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677396).length < 2 ^ (prefixWord ++ tailWord_677396).sum := by decide
  have hdescent : baseEnd_677396 < baseStart_677396 := by decide
  rcases family_descends (prefixWord ++ tailWord_677396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677407 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_677407 : Nat := 118140960795 + 677407 * 2 ^ 59
def prefixEnd_677407 : Nat := 4983230072969 + 3 ^ 40 * 677407 * 2
def baseEnd_677407 : Nat := 309187013084743445064149

theorem tailTrace_677407 : CollatzResearch.WordTrace tailWord_677407 prefixEnd_677407 309187013084743445064149 := by
  unfold tailWord_677407
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707063056877605750006475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16471375371251737166670983 24707063056877605750006475)
  ·
    refine ⟨37060594585316408625009713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24707063056877605750006475 37060594585316408625009713)
    ·
      refine ⟨27795445938987306468757285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37060594585316408625009713 27795445938987306468757285)
      ·
        refine ⟨5211646113560119962891991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27795445938987306468757285 5211646113560119962891991)
        ·
          refine ⟨7817469170340179944337987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211646113560119962891991 7817469170340179944337987)
          ·
            refine ⟨11726203755510269916506981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817469170340179944337987 11726203755510269916506981)
            ·
              refine ⟨2198663204158175609345059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11726203755510269916506981 2198663204158175609345059)
              ·
                refine ⟨3297994806237263414017589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198663204158175609345059 3297994806237263414017589)
                ·
                  refine ⟨309187013084743445064149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297994806237263414017589 309187013084743445064149)
                  ·
                    rfl

theorem cell20_677407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_677407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677407 prefixEnd_677407 := by exact prefixLift 677407
  have htrace : WordTrace (prefixWord ++ tailWord_677407) baseStart_677407 baseEnd_677407 := by
    simpa [prefixWord, tailWord_677407, baseEnd_677407] using wordTrace_append hprefix tailTrace_677407
  have hstable : (prefixWord ++ tailWord_677407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677407).length < 2 ^ (prefixWord ++ tailWord_677407).sum := by decide
  have hdescent : baseEnd_677407 < baseStart_677407 := by decide
  rcases family_descends (prefixWord ++ tailWord_677407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677410 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_677410 : Nat := 118140960795 + 677410 * 2 ^ 59
def prefixEnd_677410 : Nat := 4983230072969 + 3 ^ 40 * 677410 * 2
def baseEnd_677410 : Nat := 309188382366488767964137

theorem tailTrace_677410 : CollatzResearch.WordTrace tailWord_677410 prefixEnd_677410 309188382366488767964137 := by
  unfold tailWord_677410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176793118966684315591421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16471448317244491508243789 6176793118966684315591421)
  ·
    refine ⟨2316297419612506618346783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6176793118966684315591421 2316297419612506618346783)
    ·
      refine ⟨3474446129418759927520175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2316297419612506618346783 3474446129418759927520175)
      ·
        refine ⟨5211669194128139891280263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474446129418759927520175 5211669194128139891280263)
        ·
          refine ⟨7817503791192209836920395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5211669194128139891280263 7817503791192209836920395)
          ·
            refine ⟨11726255686788314755380593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817503791192209836920395 11726255686788314755380593)
            ·
              refine ⟨8794691765091236066535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11726255686788314755380593 8794691765091236066535445)
              ·
                refine ⟨412251176488651690618849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8794691765091236066535445 412251176488651690618849)
                ·
                  refine ⟨309188382366488767964137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412251176488651690618849 309188382366488767964137)
                  ·
                    rfl

theorem cell20_677410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_677410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677410 prefixEnd_677410 := by exact prefixLift 677410
  have htrace : WordTrace (prefixWord ++ tailWord_677410) baseStart_677410 baseEnd_677410 := by
    simpa [prefixWord, tailWord_677410, baseEnd_677410] using wordTrace_append hprefix tailTrace_677410
  have hstable : (prefixWord ++ tailWord_677410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677410).length < 2 ^ (prefixWord ++ tailWord_677410).sum := by decide
  have hdescent : baseEnd_677410 < baseStart_677410 := by decide
  rcases family_descends (prefixWord ++ tailWord_677410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677476 : List Nat := [2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_677476 : Nat := 118140960795 + 677476 * 2 ^ 59
def prefixEnd_677476 : Nat := 4983230072969 + 3 ^ 40 * 677476 * 2
def baseEnd_677476 : Nat := 103072835521628623921289

theorem tailTrace_677476 : CollatzResearch.WordTrace tailWord_677476 prefixEnd_677476 103072835521628623921289 := by
  unfold tailWord_677476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12354789846813815267134141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16473053129085087022845521 12354789846813815267134141)
  ·
    refine ⟨4633046192555180725175303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12354789846813815267134141 4633046192555180725175303)
    ·
      refine ⟨6949569288832771087762955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633046192555180725175303 6949569288832771087762955)
      ·
        refine ⟨10424353933249156631644433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949569288832771087762955 10424353933249156631644433)
        ·
          refine ⟨7818265449936867473733325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10424353933249156631644433 7818265449936867473733325)
          ·
            refine ⟨2931849543726325302649997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7818265449936867473733325 2931849543726325302649997)
            ·
              refine ⟨1099443578897371988493749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2931849543726325302649997 1099443578897371988493749)
              ·
                refine ⟨103072835521628623921289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1099443578897371988493749 103072835521628623921289)
                ·
                  rfl

theorem cell20_677476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_677476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677476 prefixEnd_677476 := by exact prefixLift 677476
  have htrace : WordTrace (prefixWord ++ tailWord_677476) baseStart_677476 baseEnd_677476 := by
    simpa [prefixWord, tailWord_677476, baseEnd_677476] using wordTrace_append hprefix tailTrace_677476
  have hstable : (prefixWord ++ tailWord_677476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677476).length < 2 ^ (prefixWord ++ tailWord_677476).sum := by decide
  have hdescent : baseEnd_677476 < baseStart_677476 := by decide
  rcases family_descends (prefixWord ++ tailWord_677476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677486 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_677486 : Nat := 118140960795 + 677486 * 2 ^ 59
def prefixEnd_677486 : Nat := 4983230072969 + 3 ^ 40 * 677486 * 2
def baseEnd_677486 : Nat := 309223070837370281430493

theorem tailTrace_677486 : CollatzResearch.WordTrace tailWord_677486 prefixEnd_677486 309223070837370281430493 := by
  unfold tailWord_677486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088743052948925280266539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16473296282394268161421541 3088743052948925280266539)
  ·
    refine ⟨4633114579423387920399809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088743052948925280266539 4633114579423387920399809)
    ·
      refine ⟨3474835934567540940299857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4633114579423387920399809 3474835934567540940299857)
      ·
        refine ⟨2606126950925655705224893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3474835934567540940299857 2606126950925655705224893)
        ·
          refine ⟨977297606597120889459335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2606126950925655705224893 977297606597120889459335)
          ·
            refine ⟨1465946409895681334189003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977297606597120889459335 1465946409895681334189003)
            ·
              refine ⟨2198919614843522001283505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465946409895681334189003 2198919614843522001283505)
              ·
                refine ⟨1649189711132641500962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198919614843522001283505 1649189711132641500962629)
                ·
                  refine ⟨309223070837370281430493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649189711132641500962629 309223070837370281430493)
                  ·
                    rfl

theorem cell20_677486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_677486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677486 prefixEnd_677486 := by exact prefixLift 677486
  have htrace : WordTrace (prefixWord ++ tailWord_677486) baseStart_677486 baseEnd_677486 := by
    simpa [prefixWord, tailWord_677486, baseEnd_677486] using wordTrace_append hprefix tailTrace_677486
  have hstable : (prefixWord ++ tailWord_677486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677486).length < 2 ^ (prefixWord ++ tailWord_677486).sum := by decide
  have hdescent : baseEnd_677486 < baseStart_677486 := by decide
  rcases family_descends (prefixWord ++ tailWord_677486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677514 : List Nat := [3, 1, 2, 3, 2, 2, 7]
def baseStart_677514 : Nat := 118140960795 + 677514 * 2 ^ 59
def prefixEnd_677514 : Nat := 4983230072969 + 3 ^ 40 * 677514 * 2
def baseEnd_677514 : Nat := 34359538977814069833005

theorem tailTrace_677514 : CollatzResearch.WordTrace tailWord_677514 prefixEnd_677514 34359538977814069833005 := by
  unfold tailWord_677514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177741416872490756037899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16473977111659975349434397 6177741416872490756037899)
  ·
    refine ⟨9266612125308736134056849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6177741416872490756037899 9266612125308736134056849)
    ·
      refine ⟨6949959093981552100542637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9266612125308736134056849 6949959093981552100542637)
      ·
        refine ⟨2606234660243082037703489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6949959093981552100542637 2606234660243082037703489)
        ·
          refine ⟨1954675995182311528277617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2606234660243082037703489 1954675995182311528277617)
          ·
            refine ⟨1466006996386733646208213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954675995182311528277617 1466006996386733646208213)
            ·
              refine ⟨34359538977814069833005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1466006996386733646208213 34359538977814069833005)
              ·
                rfl

theorem cell20_677514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_677514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677514 prefixEnd_677514 := by exact prefixLift 677514
  have htrace : WordTrace (prefixWord ++ tailWord_677514) baseStart_677514 baseEnd_677514 := by
    simpa [prefixWord, tailWord_677514, baseEnd_677514] using wordTrace_append hprefix tailTrace_677514
  have hstable : (prefixWord ++ tailWord_677514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677514).length < 2 ^ (prefixWord ++ tailWord_677514).sum := by decide
  have hdescent : baseEnd_677514 < baseStart_677514 := by decide
  rcases family_descends (prefixWord ++ tailWord_677514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677521 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_677521 : Nat := 118140960795 + 677521 * 2 ^ 59
def prefixEnd_677521 : Nat := 4983230072969 + 3 ^ 40 * 677521 * 2
def baseEnd_677521 : Nat := 309239045791065715263683

theorem tailTrace_677521 : CollatzResearch.WordTrace tailWord_677521 prefixEnd_677521 309239045791065715263683 := by
  unfold tailWord_677521
  simp only [CollatzResearch.WordTrace]
  refine ⟨24711220978464603219656417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16474147318976402146437611 24711220978464603219656417)
  ·
    refine ⟨18533415733848452414742313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24711220978464603219656417 18533415733848452414742313)
    ·
      refine ⟨13900061800386339311056735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18533415733848452414742313 13900061800386339311056735)
      ·
        refine ⟨20850092700579508966585103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900061800386339311056735 20850092700579508966585103)
        ·
          refine ⟨31275139050869263449877655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20850092700579508966585103 31275139050869263449877655)
          ·
            refine ⟨46912708576303895174816483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31275139050869263449877655 46912708576303895174816483)
            ·
              refine ⟨70369062864455842762224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46912708576303895174816483 70369062864455842762224725)
              ·
                refine ⟨824637455442841907369821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 70369062864455842762224725 824637455442841907369821)
                ·
                  refine ⟨309239045791065715263683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824637455442841907369821 309239045791065715263683)
                  ·
                    rfl

theorem cell20_677521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_677521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677521 prefixEnd_677521 := by exact prefixLift 677521
  have htrace : WordTrace (prefixWord ++ tailWord_677521) baseStart_677521 baseEnd_677521 := by
    simpa [prefixWord, tailWord_677521, baseEnd_677521] using wordTrace_append hprefix tailTrace_677521
  have hstable : (prefixWord ++ tailWord_677521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677521).length < 2 ^ (prefixWord ++ tailWord_677521).sum := by decide
  have hdescent : baseEnd_677521 < baseStart_677521 := by decide
  rcases family_descends (prefixWord ++ tailWord_677521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677534 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_677534 : Nat := 118140960795 + 677534 * 2 ^ 59
def prefixEnd_677534 : Nat := 4983230072969 + 3 ^ 40 * 677534 * 2
def baseEnd_677534 : Nat := 309244979345295447830297

theorem tailTrace_677534 : CollatzResearch.WordTrace tailWord_677534 prefixEnd_677534 309244979345295447830297 := by
  unfold tailWord_677534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088961890927188304984957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16474463418278337626586437 3088961890927188304984957)
  ·
    refine ⟨1158360709097695614369359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3088961890927188304984957 1158360709097695614369359)
    ·
      refine ⟨1737541063646543421554039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158360709097695614369359 1737541063646543421554039)
      ·
        refine ⟨2606311595469815132331059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737541063646543421554039 2606311595469815132331059)
        ·
          refine ⟨3909467393204722698496589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606311595469815132331059 3909467393204722698496589)
          ·
            refine ⟨1466050272451771011936221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3909467393204722698496589 1466050272451771011936221)
            ·
              refine ⟨549768852169414129476083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1466050272451771011936221 549768852169414129476083)
              ·
                refine ⟨824653278254121194214125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549768852169414129476083 824653278254121194214125)
                ·
                  refine ⟨309244979345295447830297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824653278254121194214125 309244979345295447830297)
                  ·
                    rfl

theorem cell20_677534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_677534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677534 prefixEnd_677534 := by exact prefixLift 677534
  have htrace : WordTrace (prefixWord ++ tailWord_677534) baseStart_677534 baseEnd_677534 := by
    simpa [prefixWord, tailWord_677534, baseEnd_677534] using wordTrace_append hprefix tailTrace_677534
  have hstable : (prefixWord ++ tailWord_677534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677534).length < 2 ^ (prefixWord ++ tailWord_677534).sum := by decide
  have hdescent : baseEnd_677534 < baseStart_677534 := by decide
  rcases family_descends (prefixWord ++ tailWord_677534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677544 : List Nat := [2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_677544 : Nat := 118140960795 + 677544 * 2 ^ 59
def prefixEnd_677544 : Nat := 4983230072969 + 3 ^ 40 * 677544 * 2
def baseEnd_677544 : Nat := 103083181205926619165641

theorem tailTrace_677544 : CollatzResearch.WordTrace tailWord_677544 prefixEnd_677544 103083181205926619165641 := by
  unfold tailWord_677544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356029928690639073871843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16474706571587518765162457 12356029928690639073871843)
  ·
    refine ⟨18534044893035958610807765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356029928690639073871843 18534044893035958610807765)
    ·
      refine ⟨434391677180530279940807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18534044893035958610807765 434391677180530279940807)
      ·
        refine ⟨651587515770795419911211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434391677180530279940807 651587515770795419911211)
        ·
          refine ⟨977381273656193129866817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651587515770795419911211 977381273656193129866817)
          ·
            refine ⟨733035955242144847400113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977381273656193129866817 733035955242144847400113)
            ·
              refine ⟨549776966431608635550085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733035955242144847400113 549776966431608635550085)
              ·
                refine ⟨103083181205926619165641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549776966431608635550085 103083181205926619165641)
                ·
                  rfl

theorem cell20_677544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_677544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677544 prefixEnd_677544 := by exact prefixLift 677544
  have htrace : WordTrace (prefixWord ++ tailWord_677544) baseStart_677544 baseEnd_677544 := by
    simpa [prefixWord, tailWord_677544, baseEnd_677544] using wordTrace_append hprefix tailTrace_677544
  have hstable : (prefixWord ++ tailWord_677544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677544).length < 2 ^ (prefixWord ++ tailWord_677544).sum := by decide
  have hdescent : baseEnd_677544 < baseStart_677544 := by decide
  rcases family_descends (prefixWord ++ tailWord_677544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677552 : List Nat := [2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_677552 : Nat := 118140960795 + 677552 * 2 ^ 59
def prefixEnd_677552 : Nat := 4983230072969 + 3 ^ 40 * 677552 * 2
def baseEnd_677552 : Nat := 103084398345255795076741

theorem tailTrace_677552 : CollatzResearch.WordTrace tailWord_677552 prefixEnd_677552 103084398345255795076741 := by
  unfold tailWord_677552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356175820676147757017455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16474901094234863676023273 12356175820676147757017455)
  ·
    refine ⟨18534263731014221635526183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356175820676147757017455 18534263731014221635526183)
    ·
      refine ⟨27801395596521332453289275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18534263731014221635526183 27801395596521332453289275)
      ·
        refine ⟨41702093394781998679933913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27801395596521332453289275 41702093394781998679933913)
        ·
          refine ⟨31276570046086499009950435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41702093394781998679933913 31276570046086499009950435)
          ·
            refine ⟨46914855069129748514925653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31276570046086499009950435 46914855069129748514925653)
            ·
              refine ⟨549783457841364240409285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 46914855069129748514925653 549783457841364240409285)
              ·
                refine ⟨103084398345255795076741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549783457841364240409285 103084398345255795076741)
                ·
                  rfl

theorem cell20_677552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_677552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677552 prefixEnd_677552 := by exact prefixLift 677552
  have htrace : WordTrace (prefixWord ++ tailWord_677552) baseStart_677552 baseEnd_677552 := by
    simpa [prefixWord, tailWord_677552, baseEnd_677552] using wordTrace_append hprefix tailTrace_677552
  have hstable : (prefixWord ++ tailWord_677552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677552).length < 2 ^ (prefixWord ++ tailWord_677552).sum := by decide
  have hdescent : baseEnd_677552 < baseStart_677552 := by decide
  rcases family_descends (prefixWord ++ tailWord_677552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677558 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_677558 : Nat := 118140960795 + 677558 * 2 ^ 59
def prefixEnd_677558 : Nat := 4983230072969 + 3 ^ 40 * 677558 * 2
def baseEnd_677558 : Nat := 309255933599258031030199

theorem tailTrace_677558 : CollatzResearch.WordTrace tailWord_677558 prefixEnd_677558 309255933599258031030199 := by
  unfold tailWord_677558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544535654958159908672083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16475046986220372359168885 1544535654958159908672083)
  ·
    refine ⟨2316803482437239863008125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544535654958159908672083 2316803482437239863008125)
    ·
      refine ⟨868801305913964948628047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2316803482437239863008125 868801305913964948628047)
      ·
        refine ⟨1303201958870947422942071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868801305913964948628047 1303201958870947422942071)
        ·
          refine ⟨1954802938306421134413107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303201958870947422942071 1954802938306421134413107)
          ·
            refine ⟨2932204407459631701619661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954802938306421134413107 2932204407459631701619661)
            ·
              refine ⟨1099576652797361888107373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932204407459631701619661 1099576652797361888107373)
              ·
                refine ⟨412341244799010708040265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099576652797361888107373 412341244799010708040265)
                ·
                  refine ⟨309255933599258031030199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412341244799010708040265 309255933599258031030199)
                  ·
                    rfl

theorem cell20_677558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_677558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677558 prefixEnd_677558 := by exact prefixLift 677558
  have htrace : WordTrace (prefixWord ++ tailWord_677558) baseStart_677558 baseEnd_677558 := by
    simpa [prefixWord, tailWord_677558, baseEnd_677558] using wordTrace_append hprefix tailTrace_677558
  have hstable : (prefixWord ++ tailWord_677558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677558).length < 2 ^ (prefixWord ++ tailWord_677558).sum := by decide
  have hdescent : baseEnd_677558 < baseStart_677558 := by decide
  rcases family_descends (prefixWord ++ tailWord_677558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677559 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_677559 : Nat := 118140960795 + 677559 * 2 ^ 59
def prefixEnd_677559 : Nat := 4983230072969 + 3 ^ 40 * 677559 * 2
def baseEnd_677559 : Nat := 309256390026506471996861

theorem tailTrace_677559 : CollatzResearch.WordTrace tailWord_677559 prefixEnd_677559 309256390026506471996861 := by
  unfold tailWord_677559
  simp only [CollatzResearch.WordTrace]
  refine ⟨24712606952326935709539731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16475071301551290473026487 24712606952326935709539731)
  ·
    refine ⟨37068910428490403564309597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24712606952326935709539731 37068910428490403564309597)
    ·
      refine ⟨13900841410683901336616099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37068910428490403564309597 13900841410683901336616099)
      ·
        refine ⟨20851262116025852004924149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900841410683901336616099 20851262116025852004924149)
        ·
          refine ⟨1954805823377423625461639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20851262116025852004924149 1954805823377423625461639)
          ·
            refine ⟨2932208735066135438192459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954805823377423625461639 2932208735066135438192459)
            ·
              refine ⟨4398313102599203157288689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932208735066135438192459 4398313102599203157288689)
              ·
                refine ⟨3298734826949402367966517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398313102599203157288689 3298734826949402367966517)
                ·
                  refine ⟨309256390026506471996861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3298734826949402367966517 309256390026506471996861)
                  ·
                    rfl

theorem cell20_677559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_677559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677559 prefixEnd_677559 := by exact prefixLift 677559
  have htrace : WordTrace (prefixWord ++ tailWord_677559) baseStart_677559 baseEnd_677559 := by
    simpa [prefixWord, tailWord_677559, baseEnd_677559] using wordTrace_append hprefix tailTrace_677559
  have hstable : (prefixWord ++ tailWord_677559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677559).length < 2 ^ (prefixWord ++ tailWord_677559).sum := by decide
  have hdescent : baseEnd_677559 < baseStart_677559 := by decide
  rcases family_descends (prefixWord ++ tailWord_677559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677562 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_677562 : Nat := 118140960795 + 677562 * 2 ^ 59
def prefixEnd_677562 : Nat := 4983230072969 + 3 ^ 40 * 677562 * 2
def baseEnd_677562 : Nat := 309257759308251794896849

theorem tailTrace_677562 : CollatzResearch.WordTrace tailWord_677562 prefixEnd_677562 309257759308251794896849 := by
  unfold tailWord_677562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178179092829016805474735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16475144247544044814599293 6178179092829016805474735)
  ·
    refine ⟨9267268639243525208212103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178179092829016805474735 9267268639243525208212103)
    ·
      refine ⟨13900902958865287812318155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9267268639243525208212103 13900902958865287812318155)
      ·
        refine ⟨20851354438297931718477233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13900902958865287812318155 20851354438297931718477233)
        ·
          refine ⟨15638515828723448788857925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20851354438297931718477233 15638515828723448788857925)
          ·
            refine ⟨2932221717885646647910861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15638515828723448788857925 2932221717885646647910861)
            ·
              refine ⟨1099583144207117492966573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932221717885646647910861 1099583144207117492966573)
              ·
                refine ⟨412343679077669059862465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099583144207117492966573 412343679077669059862465)
                ·
                  refine ⟨309257759308251794896849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412343679077669059862465 309257759308251794896849)
                  ·
                    rfl

theorem cell20_677562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_677562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677562 prefixEnd_677562 := by exact prefixLift 677562
  have htrace : WordTrace (prefixWord ++ tailWord_677562) baseStart_677562 baseEnd_677562 := by
    simpa [prefixWord, tailWord_677562, baseEnd_677562] using wordTrace_append hprefix tailTrace_677562
  have hstable : (prefixWord ++ tailWord_677562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677562).length < 2 ^ (prefixWord ++ tailWord_677562).sum := by decide
  have hdescent : baseEnd_677562 < baseStart_677562 := by decide
  rcases family_descends (prefixWord ++ tailWord_677562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677583 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 2]
def baseStart_677583 : Nat := 118140960795 + 677583 * 2 ^ 59
def prefixEnd_677583 : Nat := 4983230072969 + 3 ^ 40 * 677583 * 2
def baseEnd_677583 : Nat := 309267344280469055196763

theorem tailTrace_677583 : CollatzResearch.WordTrace tailWord_677583 prefixEnd_677583 309267344280469055196763 := by
  unfold tailWord_677583
  simp only [CollatzResearch.WordTrace]
  refine ⟨24713482304239987808413403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16475654869493325205608935 24713482304239987808413403)
  ·
    refine ⟨37070223456359981712620105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24713482304239987808413403 37070223456359981712620105)
    ·
      refine ⟨27802667592269986284465079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37070223456359981712620105 27802667592269986284465079)
      ·
        refine ⟨41704001388404979426697619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27802667592269986284465079 41704001388404979426697619)
        ·
          refine ⟨62556002082607469140046429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41704001388404979426697619 62556002082607469140046429)
          ·
            refine ⟨23458500780977800927517411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62556002082607469140046429 23458500780977800927517411)
            ·
              refine ⟨35187751171466701391276117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23458500780977800927517411 35187751171466701391276117)
              ·
                refine ⟨412356459040625406929017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 35187751171466701391276117 412356459040625406929017)
                ·
                  refine ⟨309267344280469055196763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412356459040625406929017 309267344280469055196763)
                  ·
                    rfl

theorem cell20_677583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2].length) (baseStart_677583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677583 prefixEnd_677583 := by exact prefixLift 677583
  have htrace : WordTrace (prefixWord ++ tailWord_677583) baseStart_677583 baseEnd_677583 := by
    simpa [prefixWord, tailWord_677583, baseEnd_677583] using wordTrace_append hprefix tailTrace_677583
  have hstable : (prefixWord ++ tailWord_677583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677583).length < 2 ^ (prefixWord ++ tailWord_677583).sum := by decide
  have hdescent : baseEnd_677583 < baseStart_677583 := by decide
  rcases family_descends (prefixWord ++ tailWord_677583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677593 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 3]
def baseStart_677593 : Nat := 118140960795 + 677593 * 2 ^ 59
def prefixEnd_677593 : Nat := 4983230072969 + 3 ^ 40 * 677593 * 2
def baseEnd_677593 : Nat := 309271908552953464863389

theorem tailTrace_677593 : CollatzResearch.WordTrace tailWord_677593 prefixEnd_677593 309271908552953464863389 := by
  unfold tailWord_677593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24713847034203759516277433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16475898022802506344184955 24713847034203759516277433)
  ·
    refine ⟨18535385275652819637208075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24713847034203759516277433 18535385275652819637208075)
    ·
      refine ⟨27803077913479229455812113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535385275652819637208075 27803077913479229455812113)
      ·
        refine ⟨20852308435109422091859085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27803077913479229455812113 20852308435109422091859085)
        ·
          refine ⟨7819615663166033284447157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20852308435109422091859085 7819615663166033284447157)
          ·
            refine ⟨733088968421815620416921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7819615663166033284447157 733088968421815620416921)
            ·
              refine ⟨549816726316361715312691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733088968421815620416921 549816726316361715312691)
              ·
                refine ⟨824725089474542572969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549816726316361715312691 824725089474542572969037)
                ·
                  refine ⟨309271908552953464863389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824725089474542572969037 309271908552953464863389)
                  ·
                    rfl

theorem cell20_677593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_677593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677593 prefixEnd_677593 := by exact prefixLift 677593
  have htrace : WordTrace (prefixWord ++ tailWord_677593) baseStart_677593 baseEnd_677593 := by
    simpa [prefixWord, tailWord_677593, baseEnd_677593] using wordTrace_append hprefix tailTrace_677593
  have hstable : (prefixWord ++ tailWord_677593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677593).length < 2 ^ (prefixWord ++ tailWord_677593).sum := by decide
  have hdescent : baseEnd_677593 < baseStart_677593 := by decide
  rcases family_descends (prefixWord ++ tailWord_677593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677604 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_677604 : Nat := 118140960795 + 677604 * 2 ^ 59
def prefixEnd_677604 : Nat := 4983230072969 + 3 ^ 40 * 677604 * 2
def baseEnd_677604 : Nat := 309276929252686315496677

theorem tailTrace_677604 : CollatzResearch.WordTrace tailWord_677604 prefixEnd_677604 309276929252686315496677 := by
  unfold tailWord_677604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357124118581954197463933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16476165491442605596618577 12357124118581954197463933)
  ·
    refine ⟨4633921544468232824048975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12357124118581954197463933 4633921544468232824048975)
    ·
      refine ⟨6950882316702349236073463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633921544468232824048975 6950882316702349236073463)
      ·
        refine ⟨10426323475053523854110195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6950882316702349236073463 10426323475053523854110195)
        ·
          refine ⟨15639485212580285781165293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426323475053523854110195 15639485212580285781165293)
          ·
            refine ⟨5864806954717607167936985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15639485212580285781165293 5864806954717607167936985)
            ·
              refine ⟨4398605216038205375952739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864806954717607167936985 4398605216038205375952739)
              ·
                refine ⟨6597907824057308063929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398605216038205375952739 6597907824057308063929109)
                ·
                  refine ⟨309276929252686315496677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6597907824057308063929109 309276929252686315496677)
                  ·
                    rfl

theorem cell20_677604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_677604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677604 prefixEnd_677604 := by exact prefixLift 677604
  have htrace : WordTrace (prefixWord ++ tailWord_677604) baseStart_677604 baseEnd_677604 := by
    simpa [prefixWord, tailWord_677604, baseEnd_677604] using wordTrace_append hprefix tailTrace_677604
  have hstable : (prefixWord ++ tailWord_677604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677604).length < 2 ^ (prefixWord ++ tailWord_677604).sum := by decide
  have hdescent : baseEnd_677604 < baseStart_677604 := by decide
  rcases family_descends (prefixWord ++ tailWord_677604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677611 : List Nat := [1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_677611 : Nat := 118140960795 + 677611 * 2 ^ 59
def prefixEnd_677611 : Nat := 4983230072969 + 3 ^ 40 * 677611 * 2
def baseEnd_677611 : Nat := 103093374747808467421105

theorem tailTrace_677611 : CollatzResearch.WordTrace tailWord_677611 prefixEnd_677611 103093374747808467421105 := by
  unfold tailWord_677611
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714503548138548590432687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16476335698759032393621791 24714503548138548590432687)
  ·
    refine ⟨37071755322207822885649031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24714503548138548590432687 37071755322207822885649031)
    ·
      refine ⟨55607632983311734328473547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37071755322207822885649031 55607632983311734328473547)
      ·
        refine ⟨83411449474967601492710321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55607632983311734328473547 83411449474967601492710321)
        ·
          refine ⟨62558587106225701119532741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83411449474967601492710321 62558587106225701119532741)
          ·
            refine ⟨11729735082417318959912389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62558587106225701119532741 11729735082417318959912389)
            ·
              refine ⟨2199325327953247304983573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11729735082417318959912389 2199325327953247304983573)
              ·
                refine ⟨103093374747808467421105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199325327953247304983573 103093374747808467421105)
                ·
                  rfl

theorem cell20_677611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_677611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677611 prefixEnd_677611 := by exact prefixLift 677611
  have htrace : WordTrace (prefixWord ++ tailWord_677611) baseStart_677611 baseEnd_677611 := by
    simpa [prefixWord, tailWord_677611, baseEnd_677611] using wordTrace_append hprefix tailTrace_677611
  have hstable : (prefixWord ++ tailWord_677611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677611).length < 2 ^ (prefixWord ++ tailWord_677611).sum := by decide
  have hdescent : baseEnd_677611 < baseStart_677611 := by decide
  rcases family_descends (prefixWord ++ tailWord_677611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677635 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_677635 : Nat := 118140960795 + 677635 * 2 ^ 59
def prefixEnd_677635 : Nat := 4983230072969 + 3 ^ 40 * 677635 * 2
def baseEnd_677635 : Nat := 309291078497387985463217

theorem tailTrace_677635 : CollatzResearch.WordTrace tailWord_677635 prefixEnd_677635 309291078497387985463217 := by
  unfold tailWord_677635
  simp only [CollatzResearch.WordTrace]
  refine ⟨24715378900051600689306359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16476919266701067126204239 24715378900051600689306359)
  ·
    refine ⟨37073068350077401033959539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24715378900051600689306359 37073068350077401033959539)
    ·
      refine ⟨55609602525116101550939309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37073068350077401033959539 55609602525116101550939309)
      ·
        refine ⟨20853600946918538081602241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55609602525116101550939309 20853600946918538081602241)
        ·
          refine ⟨15640200710188903561201681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20853600946918538081602241 15640200710188903561201681)
          ·
            refine ⟨11730150532641677670901261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15640200710188903561201681 11730150532641677670901261)
            ·
              refine ⟨4398806449740629126587973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11730150532641677670901261 4398806449740629126587973)
              ·
                refine ⟨824776209326367961235245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4398806449740629126587973 824776209326367961235245)
                ·
                  refine ⟨309291078497387985463217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824776209326367961235245 309291078497387985463217)
                  ·
                    rfl

theorem cell20_677635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_677635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677635 prefixEnd_677635 := by exact prefixLift 677635
  have htrace : WordTrace (prefixWord ++ tailWord_677635) baseStart_677635 baseEnd_677635 := by
    simpa [prefixWord, tailWord_677635, baseEnd_677635] using wordTrace_append hprefix tailTrace_677635
  have hstable : (prefixWord ++ tailWord_677635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677635).length < 2 ^ (prefixWord ++ tailWord_677635).sum := by decide
  have hdescent : baseEnd_677635 < baseStart_677635 := by decide
  rcases family_descends (prefixWord ++ tailWord_677635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677676 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_677676 : Nat := 118140960795 + 677676 * 2 ^ 59
def prefixEnd_677676 : Nat := 4983230072969 + 3 ^ 40 * 677676 * 2
def baseEnd_677676 : Nat := 309309792014574065096383

theorem tailTrace_677676 : CollatzResearch.WordTrace tailWord_677676 prefixEnd_677676 309309792014574065096383 := by
  unfold tailWord_677676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12358437146451532345774441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16477916195268709794365921 12358437146451532345774441)
  ·
    refine ⟨9268827859838649259330831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12358437146451532345774441 9268827859838649259330831)
    ·
      refine ⟨13903241789757973888996247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268827859838649259330831 13903241789757973888996247)
      ·
        refine ⟨20854862684636960833494371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903241789757973888996247 20854862684636960833494371)
        ·
          refine ⟨31282294026955441250241557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20854862684636960833494371 31282294026955441250241557)
          ·
            refine ⟨1466357532513536308605073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31282294026955441250241557 1466357532513536308605073)
            ·
              refine ⟨1099768149385152231453805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466357532513536308605073 1099768149385152231453805)
              ·
                refine ⟨412413056019432086795177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099768149385152231453805 412413056019432086795177)
                ·
                  refine ⟨309309792014574065096383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412413056019432086795177 309309792014574065096383)
                  ·
                    rfl

theorem cell20_677676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_677676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677676 prefixEnd_677676 := by exact prefixLift 677676
  have htrace : WordTrace (prefixWord ++ tailWord_677676) baseStart_677676 baseEnd_677676 := by
    simpa [prefixWord, tailWord_677676, baseEnd_677676] using wordTrace_append hprefix tailTrace_677676
  have hstable : (prefixWord ++ tailWord_677676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677676).length < 2 ^ (prefixWord ++ tailWord_677676).sum := by decide
  have hdescent : baseEnd_677676 < baseStart_677676 := by decide
  rcases family_descends (prefixWord ++ tailWord_677676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677686 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_677686 : Nat := 118140960795 + 677686 * 2 ^ 59
def prefixEnd_677686 : Nat := 4983230072969 + 3 ^ 40 * 677686 * 2
def baseEnd_677686 : Nat := 309314356287058474763009

theorem tailTrace_677686 : CollatzResearch.WordTrace tailWord_677686 prefixEnd_677686 309314356287058474763009 := by
  unfold tailWord_677686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544827438929177274963307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16478159348577890932941941 1544827438929177274963307)
  ·
    refine ⟨2317241158393765912444961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544827438929177274963307 2317241158393765912444961)
    ·
      refine ⟨1737930868795324434333721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317241158393765912444961 1737930868795324434333721)
      ·
        refine ⟨1303448151596493325750291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1737930868795324434333721 1303448151596493325750291)
        ·
          refine ⟨1955172227394739988625437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303448151596493325750291 1955172227394739988625437)
          ·
            refine ⟨733189585273027495734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1955172227394739988625437 733189585273027495734539)
            ·
              refine ⟨1099784377909541243601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733189585273027495734539 1099784377909541243601809)
              ·
                refine ⟨824838283432155932701357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099784377909541243601809 824838283432155932701357)
                ·
                  refine ⟨309314356287058474763009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824838283432155932701357 309314356287058474763009)
                  ·
                    rfl

theorem cell20_677686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_677686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677686 prefixEnd_677686 := by exact prefixLift 677686
  have htrace : WordTrace (prefixWord ++ tailWord_677686) baseStart_677686 baseEnd_677686 := by
    simpa [prefixWord, tailWord_677686, baseEnd_677686] using wordTrace_append hprefix tailTrace_677686
  have hstable : (prefixWord ++ tailWord_677686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677686).length < 2 ^ (prefixWord ++ tailWord_677686).sum := by decide
  have hdescent : baseEnd_677686 < baseStart_677686 := by decide
  rcases family_descends (prefixWord ++ tailWord_677686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677690 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_677690 : Nat := 118140960795 + 677690 * 2 ^ 59
def prefixEnd_677690 : Nat := 4983230072969 + 3 ^ 40 * 677690 * 2
def baseEnd_677690 : Nat := 309316181996052238629659

theorem tailTrace_677690 : CollatzResearch.WordTrace tailWord_677690 prefixEnd_677690 309316181996052238629659 := by
  unfold tailWord_677690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179346228713086270639631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16478256609901563388372349 6179346228713086270639631)
  ·
    refine ⟨9269019343069629405959447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179346228713086270639631 9269019343069629405959447)
    ·
      refine ⟨13903529014604444108939171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9269019343069629405959447 13903529014604444108939171)
      ·
        refine ⟨20855293521906666163408757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903529014604444108939171 20855293521906666163408757)
        ·
          refine ⟨1955183767678749952819571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20855293521906666163408757 1955183767678749952819571)
          ·
            refine ⟨2932775651518124929229357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955183767678749952819571 2932775651518124929229357)
            ·
              refine ⟨1099790869319296848461009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932775651518124929229357 1099790869319296848461009)
              ·
                refine ⟨824843151989472636345757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099790869319296848461009 824843151989472636345757)
                ·
                  refine ⟨309316181996052238629659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824843151989472636345757 309316181996052238629659)
                  ·
                    rfl

theorem cell20_677690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_677690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677690 prefixEnd_677690 := by exact prefixLift 677690
  have htrace : WordTrace (prefixWord ++ tailWord_677690) baseStart_677690 baseEnd_677690 := by
    simpa [prefixWord, tailWord_677690, baseEnd_677690] using wordTrace_append hprefix tailTrace_677690
  have hstable : (prefixWord ++ tailWord_677690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677690).length < 2 ^ (prefixWord ++ tailWord_677690).sum := by decide
  have hdescent : baseEnd_677690 < baseStart_677690 := by decide
  rcases family_descends (prefixWord ++ tailWord_677690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677731 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 2]
def baseStart_677731 : Nat := 118140960795 + 677731 * 2 ^ 59
def prefixEnd_677731 : Nat := 4983230072969 + 3 ^ 40 * 677731 * 2
def baseEnd_677731 : Nat := 309334895513238318262825

theorem tailTrace_677731 : CollatzResearch.WordTrace tailWord_677731 prefixEnd_677731 309334895513238318262825 := by
  unfold tailWord_677731
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718880307703809084801047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16479253538469206056534031 24718880307703809084801047)
  ·
    refine ⟨37078320461555713627201571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24718880307703809084801047 37078320461555713627201571)
    ·
      refine ⟨55617480692333570440802357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37078320461555713627201571 55617480692333570440802357)
      ·
        refine ⟨5214138814906272228825221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55617480692333570440802357 5214138814906272228825221)
        ·
          refine ⟨977651027794926042904729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5214138814906272228825221 977651027794926042904729)
          ·
            refine ⟨733238270846194532178547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977651027794926042904729 733238270846194532178547)
            ·
              refine ⟨1099857406269291798267821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733238270846194532178547 1099857406269291798267821)
              ·
                refine ⟨412446527350984424350433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099857406269291798267821 412446527350984424350433)
                ·
                  refine ⟨309334895513238318262825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412446527350984424350433 309334895513238318262825)
                  ·
                    rfl

theorem cell20_677731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 2].length) (baseStart_677731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677731 prefixEnd_677731 := by exact prefixLift 677731
  have htrace : WordTrace (prefixWord ++ tailWord_677731) baseStart_677731 baseEnd_677731 := by
    simpa [prefixWord, tailWord_677731, baseEnd_677731] using wordTrace_append hprefix tailTrace_677731
  have hstable : (prefixWord ++ tailWord_677731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677731).length < 2 ^ (prefixWord ++ tailWord_677731).sum := by decide
  have hdescent : baseEnd_677731 < baseStart_677731 := by decide
  rcases family_descends (prefixWord ++ tailWord_677731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677738 : List Nat := [3, 1, 3, 4, 2, 1, 6]
def baseStart_677738 : Nat := 118140960795 + 677738 * 2 ^ 59
def prefixEnd_677738 : Nat := 4983230072969 + 3 ^ 40 * 677738 * 2
def baseEnd_677738 : Nat := 34370898944886378336607

theorem tailTrace_677738 : CollatzResearch.WordTrace tailWord_677738 prefixEnd_677738 34370898944886378336607 := by
  unfold tailWord_677738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179783904669612320076467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16479423745785632853537245 6179783904669612320076467)
  ·
    refine ⟨9269675857004418480114701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179783904669612320076467 9269675857004418480114701)
    ·
      refine ⟨3476128446376656930043013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9269675857004418480114701 3476128446376656930043013)
      ·
        refine ⟨651774083695623174383065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3476128446376656930043013 651774083695623174383065)
        ·
          refine ⟨488830562771717380787299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651774083695623174383065 488830562771717380787299)
          ·
            refine ⟨733245844157576071180949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488830562771717380787299 733245844157576071180949)
            ·
              refine ⟨34370898944886378336607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 733245844157576071180949 34370898944886378336607)
              ·
                rfl

theorem cell20_677738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_677738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677738 prefixEnd_677738 := by exact prefixLift 677738
  have htrace : WordTrace (prefixWord ++ tailWord_677738) baseStart_677738 baseEnd_677738 := by
    simpa [prefixWord, tailWord_677738, baseEnd_677738] using wordTrace_append hprefix tailTrace_677738
  have hstable : (prefixWord ++ tailWord_677738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677738).length < 2 ^ (prefixWord ++ tailWord_677738).sum := by decide
  have hdescent : baseEnd_677738 < baseStart_677738 := by decide
  rcases family_descends (prefixWord ++ tailWord_677738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677742 : List Nat := [4, 1, 2, 3, 1, 1, 8]
def baseStart_677742 : Nat := 118140960795 + 677742 * 2 ^ 59
def prefixEnd_677742 : Nat := 4983230072969 + 3 ^ 40 * 677742 * 2
def baseEnd_677742 : Nat := 34371101801441240988457

theorem tailTrace_677742 : CollatzResearch.WordTrace tailWord_677742 prefixEnd_677742 34371101801441240988457 := by
  unfold tailWord_677742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089910188832994745431435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16479521007109305308967653 3089910188832994745431435)
  ·
    refine ⟨4634865283249492118147153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089910188832994745431435 4634865283249492118147153)
    ·
      refine ⟨3476148962437119088610365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4634865283249492118147153 3476148962437119088610365)
      ·
        refine ⟨1303555860913919658228887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3476148962437119088610365 1303555860913919658228887)
        ·
          refine ⟨1955333791370879487343331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303555860913919658228887 1955333791370879487343331)
          ·
            refine ⟨2933000687056319231014997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955333791370879487343331 2933000687056319231014997)
            ·
              refine ⟨34371101801441240988457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2933000687056319231014997 34371101801441240988457)
              ·
                rfl

theorem cell20_677742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_677742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677742 prefixEnd_677742 := by exact prefixLift 677742
  have htrace : WordTrace (prefixWord ++ tailWord_677742) baseStart_677742 baseEnd_677742 := by
    simpa [prefixWord, tailWord_677742, baseEnd_677742] using wordTrace_append hprefix tailTrace_677742
  have hstable : (prefixWord ++ tailWord_677742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677742).length < 2 ^ (prefixWord ++ tailWord_677742).sum := by decide
  have hdescent : baseEnd_677742 < baseStart_677742 := by decide
  rcases family_descends (prefixWord ++ tailWord_677742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677749 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_677749 : Nat := 118140960795 + 677749 * 2 ^ 59
def prefixEnd_677749 : Nat := 4983230072969 + 3 ^ 40 * 677749 * 2
def baseEnd_677749 : Nat := 309343111203710255662751

theorem tailTrace_677749 : CollatzResearch.WordTrace tailWord_677749 prefixEnd_677749 309343111203710255662751 := by
  unfold tailWord_677749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719536821638598158956301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16479691214425732105970867 24719536821638598158956301)
  ·
    refine ⟨9269826308114474309608613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24719536821638598158956301 9269826308114474309608613)
    ·
      refine ⟨1738092432771463933051615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9269826308114474309608613 1738092432771463933051615)
      ·
        refine ⟨2607138649157195899577423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738092432771463933051615 2607138649157195899577423)
        ·
          refine ⟨3910707973735793849366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607138649157195899577423 3910707973735793849366135)
          ·
            refine ⟨5866061960603690774049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910707973735793849366135 5866061960603690774049203)
            ·
              refine ⟨8799092940905536161073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866061960603690774049203 8799092940905536161073805)
              ·
                refine ⟨3299659852839576060402677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8799092940905536161073805 3299659852839576060402677)
                ·
                  refine ⟨309343111203710255662751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3299659852839576060402677 309343111203710255662751)
                  ·
                    rfl

theorem cell20_677749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_677749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677749 prefixEnd_677749 := by exact prefixLift 677749
  have htrace : WordTrace (prefixWord ++ tailWord_677749) baseStart_677749 baseEnd_677749 := by
    simpa [prefixWord, tailWord_677749, baseEnd_677749] using wordTrace_append hprefix tailTrace_677749
  have hstable : (prefixWord ++ tailWord_677749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677749).length < 2 ^ (prefixWord ++ tailWord_677749).sum := by decide
  have hdescent : baseEnd_677749 < baseStart_677749 := by decide
  rcases family_descends (prefixWord ++ tailWord_677749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677763 : List Nat := [1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_677763 : Nat := 118140960795 + 677763 * 2 ^ 59
def prefixEnd_677763 : Nat := 4983230072969 + 3 ^ 40 * 677763 * 2
def baseEnd_677763 : Nat := 103116500395062809732009

theorem tailTrace_677763 : CollatzResearch.WordTrace tailWord_677763 prefixEnd_677763 103116500395062809732009 := by
  unfold tailWord_677763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720047443587878549965943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16480031629058585699977295 24720047443587878549965943)
  ·
    refine ⟨37080071165381817824948915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24720047443587878549965943 37080071165381817824948915)
    ·
      refine ⟨55620106748072726737423373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37080071165381817824948915 55620106748072726737423373)
      ·
        refine ⟨20857540030527272526533765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55620106748072726737423373 20857540030527272526533765)
        ·
          refine ⟨3910788755723863598725081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20857540030527272526533765 3910788755723863598725081)
          ·
            refine ⟨2933091566792897699043811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910788755723863598725081 2933091566792897699043811)
            ·
              refine ⟨4399637350189346548565717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933091566792897699043811 4399637350189346548565717)
              ·
                refine ⟨103116500395062809732009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4399637350189346548565717 103116500395062809732009)
                ·
                  rfl

theorem cell20_677763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_677763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677763 prefixEnd_677763 := by exact prefixLift 677763
  have htrace : WordTrace (prefixWord ++ tailWord_677763) baseStart_677763 baseEnd_677763 := by
    simpa [prefixWord, tailWord_677763, baseEnd_677763] using wordTrace_append hprefix tailTrace_677763
  have hstable : (prefixWord ++ tailWord_677763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677763).length < 2 ^ (prefixWord ++ tailWord_677763).sum := by decide
  have hdescent : baseEnd_677763 < baseStart_677763 := by decide
  rcases family_descends (prefixWord ++ tailWord_677763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677780 : List Nat := [2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_677780 : Nat := 118140960795 + 677780 * 2 ^ 59
def prefixEnd_677780 : Nat := 4983230072969 + 3 ^ 40 * 677780 * 2
def baseEnd_677780 : Nat := 103119086816137308543097

theorem tailTrace_677780 : CollatzResearch.WordTrace tailWord_677780 prefixEnd_677780 103119086816137308543097 := by
  unfold tailWord_677780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360333742263145226667397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16480444989684193635556529 12360333742263145226667397)
  ·
    refine ⟨2317562576674339730000137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12360333742263145226667397 2317562576674339730000137)
    ·
      refine ⟨1738171932505754797500103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317562576674339730000137 1738171932505754797500103)
      ·
        refine ⟨2607257898758632196250155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738171932505754797500103 2607257898758632196250155)
        ·
          refine ⟨3910886848137948294375233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607257898758632196250155 3910886848137948294375233)
          ·
            refine ⟨2933165136103461220781425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910886848137948294375233 2933165136103461220781425)
            ·
              refine ⟨2199873852077595915586069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933165136103461220781425 2199873852077595915586069)
              ·
                refine ⟨103119086816137308543097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199873852077595915586069 103119086816137308543097)
                ·
                  rfl

theorem cell20_677780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_677780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677780 prefixEnd_677780 := by exact prefixLift 677780
  have htrace : WordTrace (prefixWord ++ tailWord_677780) baseStart_677780 baseEnd_677780 := by
    simpa [prefixWord, tailWord_677780, baseEnd_677780] using wordTrace_append hprefix tailTrace_677780
  have hstable : (prefixWord ++ tailWord_677780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677780).length < 2 ^ (prefixWord ++ tailWord_677780).sum := by decide
  have hdescent : baseEnd_677780 < baseStart_677780 := by decide
  rcases family_descends (prefixWord ++ tailWord_677780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677800 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_677800 : Nat := 118140960795 + 677800 * 2 ^ 59
def prefixEnd_677800 : Nat := 4983230072969 + 3 ^ 40 * 677800 * 2
def baseEnd_677800 : Nat := 309366388993380744962543

theorem tailTrace_677800 : CollatzResearch.WordTrace tailWord_677800 prefixEnd_677800 309366388993380744962543 := by
  unfold tailWord_677800
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360698472226916934531427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16480931296302555912708569 12360698472226916934531427)
  ·
    refine ⟨18541047708340375401797141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12360698472226916934531427 18541047708340375401797141)
    ·
      refine ⟨869111611328455096959241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18541047708340375401797141 869111611328455096959241)
      ·
        refine ⟨651833708496341322719431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869111611328455096959241 651833708496341322719431)
        ·
          refine ⟨977750562744511984079147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651833708496341322719431 977750562744511984079147)
          ·
            refine ⟨1466625844116767976118721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977750562744511984079147 1466625844116767976118721)
            ·
              refine ⟨1099969383087575982089041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466625844116767976118721 1099969383087575982089041)
              ·
                refine ⟨824977037315681986566781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099969383087575982089041 824977037315681986566781)
                ·
                  refine ⟨309366388993380744962543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824977037315681986566781 309366388993380744962543)
                  ·
                    rfl

theorem cell20_677800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_677800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677800 prefixEnd_677800 := by exact prefixLift 677800
  have htrace : WordTrace (prefixWord ++ tailWord_677800) baseStart_677800 baseEnd_677800 := by
    simpa [prefixWord, tailWord_677800, baseEnd_677800] using wordTrace_append hprefix tailTrace_677800
  have hstable : (prefixWord ++ tailWord_677800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677800).length < 2 ^ (prefixWord ++ tailWord_677800).sum := by decide
  have hdescent : baseEnd_677800 < baseStart_677800 := by decide
  rcases family_descends (prefixWord ++ tailWord_677800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677811 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 2]
def baseStart_677811 : Nat := 118140960795 + 677811 * 2 ^ 59
def prefixEnd_677811 : Nat := 4983230072969 + 3 ^ 40 * 677811 * 2
def baseEnd_677811 : Nat := 309371409693113595595831

theorem tailTrace_677811 : CollatzResearch.WordTrace tailWord_677811 prefixEnd_677811 309371409693113595595831 := by
  unfold tailWord_677811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24721798147413982747713287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16481198764942655165142191 24721798147413982747713287)
  ·
    refine ⟨37082697221120974121569931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24721798147413982747713287 37082697221120974121569931)
    ·
      refine ⟨55624045831681461182354897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37082697221120974121569931 55624045831681461182354897)
      ·
        refine ⟨41718034373761095886766173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55624045831681461182354897 41718034373761095886766173)
        ·
          refine ⟨15644262890160410957537315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41718034373761095886766173 15644262890160410957537315)
          ·
            refine ⟨23466394335240616436305973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15644262890160410957537315 23466394335240616436305973)
            ·
              refine ⟨2199974468928807790903685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23466394335240616436305973 2199974468928807790903685)
              ·
                refine ⟨412495212924151460794441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2199974468928807790903685 412495212924151460794441)
                ·
                  refine ⟨309371409693113595595831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412495212924151460794441 309371409693113595595831)
                  ·
                    rfl

theorem cell20_677811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2].length) (baseStart_677811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677811 prefixEnd_677811 := by exact prefixLift 677811
  have htrace : WordTrace (prefixWord ++ tailWord_677811) baseStart_677811 baseEnd_677811 := by
    simpa [prefixWord, tailWord_677811, baseEnd_677811] using wordTrace_append hprefix tailTrace_677811
  have hstable : (prefixWord ++ tailWord_677811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677811).length < 2 ^ (prefixWord ++ tailWord_677811).sum := by decide
  have hdescent : baseEnd_677811 < baseStart_677811 := by decide
  rcases family_descends (prefixWord ++ tailWord_677811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677832 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_677832 : Nat := 118140960795 + 677832 * 2 ^ 59
def prefixEnd_677832 : Nat := 4983230072969 + 3 ^ 40 * 677832 * 2
def baseEnd_677832 : Nat := 309380994665330855895745

theorem tailTrace_677832 : CollatzResearch.WordTrace tailWord_677832 prefixEnd_677832 309380994665330855895745 := by
  unfold tailWord_677832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12361282040168951667113875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16481709386891935556151833 12361282040168951667113875)
  ·
    refine ⟨18541923060253427500670813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12361282040168951667113875 18541923060253427500670813)
    ·
      refine ⟨6953221147595035312751555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18541923060253427500670813 6953221147595035312751555)
      ·
        refine ⟨10429831721392552969127333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953221147595035312751555 10429831721392552969127333)
        ·
          refine ⟨1955593447761103681711375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10429831721392552969127333 1955593447761103681711375)
          ·
            refine ⟨2933390171641655522567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955593447761103681711375 2933390171641655522567063)
            ·
              refine ⟨4400085257462483283850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933390171641655522567063 4400085257462483283850595)
              ·
                refine ⟨6600127886193724925775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400085257462483283850595 6600127886193724925775893)
                ·
                  refine ⟨309380994665330855895745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600127886193724925775893 309380994665330855895745)
                  ·
                    rfl

theorem cell20_677832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_677832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677832 prefixEnd_677832 := by exact prefixLift 677832
  have htrace : WordTrace (prefixWord ++ tailWord_677832) baseStart_677832 baseEnd_677832 := by
    simpa [prefixWord, tailWord_677832, baseEnd_677832] using wordTrace_append hprefix tailTrace_677832
  have hstable : (prefixWord ++ tailWord_677832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677832).length < 2 ^ (prefixWord ++ tailWord_677832).sum := by decide
  have hdescent : baseEnd_677832 < baseStart_677832 := by decide
  rcases family_descends (prefixWord ++ tailWord_677832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677852 : List Nat := [2, 2, 6, 1, 1, 1, 7]
def baseStart_677852 : Nat := 118140960795 + 677852 * 2 ^ 59
def prefixEnd_677852 : Nat := 4983230072969 + 3 ^ 40 * 677852 * 2
def baseEnd_677852 : Nat := 34376680356699963914333

theorem tailTrace_677852 : CollatzResearch.WordTrace tailWord_677852 prefixEnd_677852 34376680356699963914333 := by
  unfold tailWord_677852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12361646770132723374977905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16482195693510297833303873 12361646770132723374977905)
  ·
    refine ⟨9271235077599542531233429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12361646770132723374977905 9271235077599542531233429)
    ·
      refine ⟨434589144262478556151567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9271235077599542531233429 434589144262478556151567)
      ·
        refine ⟨651883716393717834227351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434589144262478556151567 651883716393717834227351)
        ·
          refine ⟨977825574590576751341027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651883716393717834227351 977825574590576751341027)
          ·
            refine ⟨1466738361885865127011541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977825574590576751341027 1466738361885865127011541)
            ·
              refine ⟨34376680356699963914333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1466738361885865127011541 34376680356699963914333)
              ·
                rfl

theorem cell20_677852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_677852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677852 prefixEnd_677852 := by exact prefixLift 677852
  have htrace : WordTrace (prefixWord ++ tailWord_677852) baseStart_677852 baseEnd_677852 := by
    simpa [prefixWord, tailWord_677852, baseEnd_677852] using wordTrace_append hprefix tailTrace_677852
  have hstable : (prefixWord ++ tailWord_677852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677852).length < 2 ^ (prefixWord ++ tailWord_677852).sum := by decide
  have hdescent : baseEnd_677852 < baseStart_677852 := by decide
  rcases family_descends (prefixWord ++ tailWord_677852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677911 : List Nat := [1, 1, 3, 5, 3, 1, 6]
def baseStart_677911 : Nat := 118140960795 + 677911 * 2 ^ 59
def prefixEnd_677911 : Nat := 4983230072969 + 3 ^ 40 * 677911 * 2
def baseEnd_677911 : Nat := 34379672490884188029121

theorem tailTrace_677911 : CollatzResearch.WordTrace tailWord_677911 prefixEnd_677911 34379672490884188029121 := by
  unfold tailWord_677911
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725445447051699826353587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16483630298034466550902391 24725445447051699826353587)
  ·
    refine ⟨37088168170577549739530381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24725445447051699826353587 37088168170577549739530381)
    ·
      refine ⟨13908063063966581152323893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37088168170577549739530381 13908063063966581152323893)
      ·
        refine ⟨1303880912246866983030365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13908063063966581152323893 1303880912246866983030365)
        ·
          refine ⟨488955342092575118636387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1303880912246866983030365 488955342092575118636387)
          ·
            refine ⟨733433013138862677954581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488955342092575118636387 733433013138862677954581)
            ·
              refine ⟨34379672490884188029121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 733433013138862677954581 34379672490884188029121)
              ·
                rfl

theorem cell20_677911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_677911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677911 prefixEnd_677911 := by exact prefixLift 677911
  have htrace : WordTrace (prefixWord ++ tailWord_677911) baseStart_677911 baseEnd_677911 := by
    simpa [prefixWord, tailWord_677911, baseEnd_677911] using wordTrace_append hprefix tailTrace_677911
  have hstable : (prefixWord ++ tailWord_677911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677911).length < 2 ^ (prefixWord ++ tailWord_677911).sum := by decide
  have hdescent : baseEnd_677911 < baseStart_677911 := by decide
  rcases family_descends (prefixWord ++ tailWord_677911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677921 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 2]
def baseStart_677921 : Nat := 118140960795 + 677921 * 2 ^ 59
def prefixEnd_677921 : Nat := 4983230072969 + 3 ^ 40 * 677921 * 2
def baseEnd_677921 : Nat := 309421616690442101928715

theorem tailTrace_677921 : CollatzResearch.WordTrace tailWord_677921 prefixEnd_677921 309421616690442101928715 := by
  unfold tailWord_677921
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725810177015471534217617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16483873451343647689478411 24725810177015471534217617)
  ·
    refine ⟨18544357632761603650663213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24725810177015471534217617 18544357632761603650663213)
    ·
      refine ⟨6954134112285601368998705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18544357632761603650663213 6954134112285601368998705)
      ·
        refine ⟨5215600584214201026749029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6954134112285601368998705 5215600584214201026749029)
        ·
          refine ⟨977925109540162692515443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5215600584214201026749029 977925109540162692515443)
          ·
            refine ⟨1466887664310244038773165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977925109540162692515443 1466887664310244038773165)
            ·
              refine ⟨550082874116341514539937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1466887664310244038773165 550082874116341514539937)
              ·
                refine ⟨412562155587256135904953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550082874116341514539937 412562155587256135904953)
                ·
                  refine ⟨309421616690442101928715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412562155587256135904953 309421616690442101928715)
                  ·
                    rfl

theorem cell20_677921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_677921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677921 prefixEnd_677921 := by exact prefixLift 677921
  have htrace : WordTrace (prefixWord ++ tailWord_677921) baseStart_677921 baseEnd_677921 := by
    simpa [prefixWord, tailWord_677921, baseEnd_677921] using wordTrace_append hprefix tailTrace_677921
  have hstable : (prefixWord ++ tailWord_677921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677921).length < 2 ^ (prefixWord ++ tailWord_677921).sum := by decide
  have hdescent : baseEnd_677921 < baseStart_677921 := by decide
  rcases family_descends (prefixWord ++ tailWord_677921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677925 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_677925 : Nat := 118140960795 + 677925 * 2 ^ 59
def prefixEnd_677925 : Nat := 4983230072969 + 3 ^ 40 * 677925 * 2
def baseEnd_677925 : Nat := 309423442399435865795365

theorem tailTrace_677925 : CollatzResearch.WordTrace tailWord_677925 prefixEnd_677925 309423442399435865795365 := by
  unfold tailWord_677925
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725956069000980217363229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16483970712667320144908819 24725956069000980217363229)
  ·
    refine ⟨9272233525875367581511211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24725956069000980217363229 9272233525875367581511211)
    ·
      refine ⟨13908350288813051372266817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272233525875367581511211 13908350288813051372266817)
      ·
        refine ⟨10431262716609788529200113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13908350288813051372266817 10431262716609788529200113)
        ·
          refine ⟨7823447037457341396900085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10431262716609788529200113 7823447037457341396900085)
          ·
            refine ⟨733448159761625755959383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7823447037457341396900085 733448159761625755959383)
            ·
              refine ⟨1100172239642438633939075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733448159761625755959383 1100172239642438633939075)
              ·
                refine ⟨1650258359463657950908613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100172239642438633939075 1650258359463657950908613)
                ·
                  refine ⟨309423442399435865795365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650258359463657950908613 309423442399435865795365)
                  ·
                    rfl

theorem cell20_677925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_677925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677925 prefixEnd_677925 := by exact prefixLift 677925
  have htrace : WordTrace (prefixWord ++ tailWord_677925) baseStart_677925 baseEnd_677925 := by
    simpa [prefixWord, tailWord_677925, baseEnd_677925] using wordTrace_append hprefix tailTrace_677925
  have hstable : (prefixWord ++ tailWord_677925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677925).length < 2 ^ (prefixWord ++ tailWord_677925).sum := by decide
  have hdescent : baseEnd_677925 < baseStart_677925 := by decide
  rcases family_descends (prefixWord ++ tailWord_677925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677960 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_677960 : Nat := 118140960795 + 677960 * 2 ^ 59
def prefixEnd_677960 : Nat := 4983230072969 + 3 ^ 40 * 677960 * 2
def baseEnd_677960 : Nat := 309439417353131299628555

theorem tailTrace_677960 : CollatzResearch.WordTrace tailWord_677960 prefixEnd_677960 309439417353131299628555 := by
  unfold tailWord_677960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363616311937090597443667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16484821749249454129924889 12363616311937090597443667)
  ·
    refine ⟨18545424467905635896165501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12363616311937090597443667 18545424467905635896165501)
    ·
      refine ⟨6954534175464613461062063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18545424467905635896165501 6954534175464613461062063)
      ·
        refine ⟨10431801263196920191593095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6954534175464613461062063 10431801263196920191593095)
        ·
          refine ⟨15647701894795380287389643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10431801263196920191593095 15647701894795380287389643)
          ·
            refine ⟨23471552842193070431084465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647701894795380287389643 23471552842193070431084465)
            ·
              refine ⟨17603664631644802823313349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23471552842193070431084465 17603664631644802823313349)
              ·
                refine ⟨3300687118433400529371253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17603664631644802823313349 3300687118433400529371253)
                ·
                  refine ⟨309439417353131299628555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300687118433400529371253 309439417353131299628555)
                  ·
                    rfl

theorem cell20_677960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_677960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677960 prefixEnd_677960 := by exact prefixLift 677960
  have htrace : WordTrace (prefixWord ++ tailWord_677960) baseStart_677960 baseEnd_677960 := by
    simpa [prefixWord, tailWord_677960, baseEnd_677960] using wordTrace_append hprefix tailTrace_677960
  have hstable : (prefixWord ++ tailWord_677960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677960).length < 2 ^ (prefixWord ++ tailWord_677960).sum := by decide
  have hdescent : baseEnd_677960 < baseStart_677960 := by decide
  rcases family_descends (prefixWord ++ tailWord_677960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677967 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_677967 : Nat := 118140960795 + 677967 * 2 ^ 59
def prefixEnd_677967 : Nat := 4983230072969 + 3 ^ 40 * 677967 * 2
def baseEnd_677967 : Nat := 309442612343870386395193

theorem tailTrace_677967 : CollatzResearch.WordTrace tailWord_677967 prefixEnd_677967 309442612343870386395193 := by
  unfold tailWord_677967
  simp only [CollatzResearch.WordTrace]
  refine ⟨24727487934848821390392155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16484991956565880926928103 24727487934848821390392155)
  ·
    refine ⟨37091231902273232085588233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24727487934848821390392155 37091231902273232085588233)
    ·
      refine ⟨27818423926704924064191175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37091231902273232085588233 27818423926704924064191175)
      ·
        refine ⟨41727635890057386096286763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27818423926704924064191175 41727635890057386096286763)
        ·
          refine ⟨62591453835086079144430145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41727635890057386096286763 62591453835086079144430145)
          ·
            refine ⟨46943590376314559358322609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62591453835086079144430145 46943590376314559358322609)
            ·
              refine ⟨35207692782235919518741957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46943590376314559358322609 35207692782235919518741957)
              ·
                refine ⟨6601442396669234909764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35207692782235919518741957 6601442396669234909764117)
                ·
                  refine ⟨309442612343870386395193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6601442396669234909764117 309442612343870386395193)
                  ·
                    rfl

theorem cell20_677967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_677967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677967 prefixEnd_677967 := by exact prefixLift 677967
  have htrace : WordTrace (prefixWord ++ tailWord_677967) baseStart_677967 baseEnd_677967 := by
    simpa [prefixWord, tailWord_677967, baseEnd_677967] using wordTrace_append hprefix tailTrace_677967
  have hstable : (prefixWord ++ tailWord_677967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677967).length < 2 ^ (prefixWord ++ tailWord_677967).sum := by decide
  have hdescent : baseEnd_677967 < baseStart_677967 := by decide
  rcases family_descends (prefixWord ++ tailWord_677967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677970 : List Nat := [3, 2, 2, 1, 5, 7]
def baseStart_677970 : Nat := 118140960795 + 677970 * 2 ^ 59
def prefixEnd_677970 : Nat := 4983230072969 + 3 ^ 40 * 677970 * 2
def baseEnd_677970 : Nat := 11460888208356137381303

theorem tailTrace_677970 : CollatzResearch.WordTrace tailWord_677970 prefixEnd_677970 11460888208356137381303 := by
  unfold tailWord_677970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181899338459488225687841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16485064902558635268500909 6181899338459488225687841)
  ·
    refine ⟨4636424503844616169265881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181899338459488225687841 4636424503844616169265881)
    ·
      refine ⟨3477318377883462126949411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4636424503844616169265881 3477318377883462126949411)
      ·
        refine ⟨5215977566825193190424117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477318377883462126949411 5215977566825193190424117)
        ·
          refine ⟨488997896889861861602261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5215977566825193190424117 488997896889861861602261)
          ·
            refine ⟨11460888208356137381303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 488997896889861861602261 11460888208356137381303)
            ·
              rfl

theorem cell20_677970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 7].length) (baseStart_677970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677970 prefixEnd_677970 := by exact prefixLift 677970
  have htrace : WordTrace (prefixWord ++ tailWord_677970) baseStart_677970 baseEnd_677970 := by
    simpa [prefixWord, tailWord_677970, baseEnd_677970] using wordTrace_append hprefix tailTrace_677970
  have hstable : (prefixWord ++ tailWord_677970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677970).length < 2 ^ (prefixWord ++ tailWord_677970).sum := by decide
  have hdescent : baseEnd_677970 < baseStart_677970 := by decide
  rcases family_descends (prefixWord ++ tailWord_677970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677977 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_677977 : Nat := 118140960795 + 677977 * 2 ^ 59
def prefixEnd_677977 : Nat := 4983230072969 + 3 ^ 40 * 677977 * 2
def baseEnd_677977 : Nat := 309447176616354796061819

theorem tailTrace_677977 : CollatzResearch.WordTrace tailWord_677977 prefixEnd_677977 309447176616354796061819 := by
  unfold tailWord_677977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24727852664812593098256185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16485235109875062065504123 24727852664812593098256185)
  ·
    refine ⟨18545889498609444823692139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24727852664812593098256185 18545889498609444823692139)
    ·
      refine ⟨27818834247914167235538209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18545889498609444823692139 27818834247914167235538209)
      ·
        refine ⟨20864125685935625426653657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27818834247914167235538209 20864125685935625426653657)
        ·
          refine ⟨15648094264451719069990243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20864125685935625426653657 15648094264451719069990243)
          ·
            refine ⟨23472141396677578604985365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15648094264451719069990243 23472141396677578604985365)
            ·
              refine ⟨1100256627969261497108689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23472141396677578604985365 1100256627969261497108689)
              ·
                refine ⟨825192470976946122831517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100256627969261497108689 825192470976946122831517)
                ·
                  refine ⟨309447176616354796061819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825192470976946122831517 309447176616354796061819)
                  ·
                    rfl

theorem cell20_677977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_677977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677977 prefixEnd_677977 := by exact prefixLift 677977
  have htrace : WordTrace (prefixWord ++ tailWord_677977) baseStart_677977 baseEnd_677977 := by
    simpa [prefixWord, tailWord_677977, baseEnd_677977] using wordTrace_append hprefix tailTrace_677977
  have hstable : (prefixWord ++ tailWord_677977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677977).length < 2 ^ (prefixWord ++ tailWord_677977).sum := by decide
  have hdescent : baseEnd_677977 < baseStart_677977 := by decide
  rcases family_descends (prefixWord ++ tailWord_677977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677980 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_677980 : Nat := 118140960795 + 677980 * 2 ^ 59
def prefixEnd_677980 : Nat := 4983230072969 + 3 ^ 40 * 677980 * 2
def baseEnd_677980 : Nat := 309448545898100118961807

theorem tailTrace_677980 : CollatzResearch.WordTrace tailWord_677980 prefixEnd_677980 309448545898100118961807 := by
  unfold tailWord_677980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363981041900862305307697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16485308055867816407076929 12363981041900862305307697)
  ·
    refine ⟨9272985781425646728980773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12363981041900862305307697 9272985781425646728980773)
    ·
      refine ⟨1738684834017308761683895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9272985781425646728980773 1738684834017308761683895)
      ·
        refine ⟨2608027251025963142525843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738684834017308761683895 2608027251025963142525843)
        ·
          refine ⟨3912040876538944713788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608027251025963142525843 3912040876538944713788765)
          ·
            refine ⟨1467015328702104267670787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3912040876538944713788765 1467015328702104267670787)
            ·
              refine ⟨2200522993053156401506181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467015328702104267670787 2200522993053156401506181)
              ·
                refine ⟨412598061197466825282409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2200522993053156401506181 412598061197466825282409)
                ·
                  refine ⟨309448545898100118961807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412598061197466825282409 309448545898100118961807)
                  ·
                    rfl

theorem cell20_677980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_677980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_677980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_677980 prefixEnd_677980 := by exact prefixLift 677980
  have htrace : WordTrace (prefixWord ++ tailWord_677980) baseStart_677980 baseEnd_677980 := by
    simpa [prefixWord, tailWord_677980, baseEnd_677980] using wordTrace_append hprefix tailTrace_677980
  have hstable : (prefixWord ++ tailWord_677980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677980).length < 2 ^ (prefixWord ++ tailWord_677980).sum := by decide
  have hdescent : baseEnd_677980 < baseStart_677980 := by decide
  rcases family_descends (prefixWord ++ tailWord_677980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678039 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_678039 : Nat := 118140960795 + 678039 * 2 ^ 59
def prefixEnd_678039 : Nat := 4983230072969 + 3 ^ 40 * 678039 * 2
def baseEnd_678039 : Nat := 309475475105758135994899

theorem tailTrace_678039 : CollatzResearch.WordTrace tailWord_678039 prefixEnd_678039 309475475105758135994899 := by
  unfold tailWord_678039
  simp only [CollatzResearch.WordTrace]
  refine ⟨24730113990587977687013171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16486742660391985124675447 24730113990587977687013171)
  ·
    refine ⟨37095170985881966530519757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24730113990587977687013171 37095170985881966530519757)
    ·
      refine ⟨13910689119705737448944909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37095170985881966530519757 13910689119705737448944909)
      ·
        refine ⟨5216508419889651543354341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13910689119705737448944909 5216508419889651543354341)
        ·
          refine ⟨978095328729309664378939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5216508419889651543354341 978095328729309664378939)
          ·
            refine ⟨1467142993093964496568409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978095328729309664378939 1467142993093964496568409)
            ·
              refine ⟨1100357244820473372426307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467142993093964496568409 1100357244820473372426307)
              ·
                refine ⟨1650535867230710058639461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100357244820473372426307 1650535867230710058639461)
                ·
                  refine ⟨309475475105758135994899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650535867230710058639461 309475475105758135994899)
                  ·
                    rfl

theorem cell20_678039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_678039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678039 prefixEnd_678039 := by exact prefixLift 678039
  have htrace : WordTrace (prefixWord ++ tailWord_678039) baseStart_678039 baseEnd_678039 := by
    simpa [prefixWord, tailWord_678039, baseEnd_678039] using wordTrace_append hprefix tailTrace_678039
  have hstable : (prefixWord ++ tailWord_678039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678039).length < 2 ^ (prefixWord ++ tailWord_678039).sum := by decide
  have hdescent : baseEnd_678039 < baseStart_678039 := by decide
  rcases family_descends (prefixWord ++ tailWord_678039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678074 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_678074 : Nat := 118140960795 + 678074 * 2 ^ 59
def prefixEnd_678074 : Nat := 4983230072969 + 3 ^ 40 * 678074 * 2
def baseEnd_678074 : Nat := 309491450059453569828089

theorem tailTrace_678074 : CollatzResearch.WordTrace tailWord_678074 prefixEnd_678074 309491450059453569828089 := by
  unfold tailWord_678074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182847636365294666134319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16487593696974119109691517 6182847636365294666134319)
  ·
    refine ⟨9274271454547941999201479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6182847636365294666134319 9274271454547941999201479)
    ·
      refine ⟨13911407181821912998802219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9274271454547941999201479 13911407181821912998802219)
      ·
        refine ⟨20867110772732869498203329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911407181821912998802219 20867110772732869498203329)
        ·
          refine ⟨15650333079549652123652497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20867110772732869498203329 15650333079549652123652497)
          ·
            refine ⟨11737749809662239092739373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15650333079549652123652497 11737749809662239092739373)
            ·
              refine ⟨4401656178623339659777265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11737749809662239092739373 4401656178623339659777265)
              ·
                refine ⟨3301242133967504744832949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401656178623339659777265 3301242133967504744832949)
                ·
                  refine ⟨309491450059453569828089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301242133967504744832949 309491450059453569828089)
                  ·
                    rfl

theorem cell20_678074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_678074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678074 prefixEnd_678074 := by exact prefixLift 678074
  have htrace : WordTrace (prefixWord ++ tailWord_678074) baseStart_678074 baseEnd_678074 := by
    simpa [prefixWord, tailWord_678074, baseEnd_678074] using wordTrace_append hprefix tailTrace_678074
  have hstable : (prefixWord ++ tailWord_678074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678074).length < 2 ^ (prefixWord ++ tailWord_678074).sum := by decide
  have hdescent : baseEnd_678074 < baseStart_678074 := by decide
  rcases family_descends (prefixWord ++ tailWord_678074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678084 : List Nat := [2, 3, 3, 1, 2, 3, 6]
def baseStart_678084 : Nat := 118140960795 + 678084 * 2 ^ 59
def prefixEnd_678084 : Nat := 4983230072969 + 3 ^ 40 * 678084 * 2
def baseEnd_678084 : Nat := 34388446036881997721635

theorem tailTrace_678084 : CollatzResearch.WordTrace tailWord_678084 prefixEnd_678084 34388446036881997721635 := by
  unfold tailWord_678084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365877637712475186200653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16487836850283300248267537 12365877637712475186200653)
  ·
    refine ⟨4637204114142178194825245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12365877637712475186200653 4637204114142178194825245)
    ·
      refine ⟨1738951542803316823059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4637204114142178194825245 1738951542803316823059467)
      ·
        refine ⟨2608427314204975234589201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738951542803316823059467 2608427314204975234589201)
        ·
          refine ⟨1956320485653731425941901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608427314204975234589201 1956320485653731425941901)
          ·
            refine ⟨733620182120149284728213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956320485653731425941901 733620182120149284728213)
            ·
              refine ⟨34388446036881997721635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 733620182120149284728213 34388446036881997721635)
              ·
                rfl

theorem cell20_678084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_678084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678084 prefixEnd_678084 := by exact prefixLift 678084
  have htrace : WordTrace (prefixWord ++ tailWord_678084) baseStart_678084 baseEnd_678084 := by
    simpa [prefixWord, tailWord_678084, baseEnd_678084] using wordTrace_append hprefix tailTrace_678084
  have hstable : (prefixWord ++ tailWord_678084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678084).length < 2 ^ (prefixWord ++ tailWord_678084).sum := by decide
  have hdescent : baseEnd_678084 < baseStart_678084 := by decide
  rcases family_descends (prefixWord ++ tailWord_678084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678146 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_678146 : Nat := 118140960795 + 678146 * 2 ^ 59
def prefixEnd_678146 : Nat := 4983230072969 + 3 ^ 40 * 678146 * 2
def baseEnd_678146 : Nat := 309524312821341319427795

theorem tailTrace_678146 : CollatzResearch.WordTrace tailWord_678146 prefixEnd_678146 309524312821341319427795 := by
  unfold tailWord_678146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183504150300083740289573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16489344400800223307438861 6183504150300083740289573)
  ·
    refine ⟨1159407028181265701304295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6183504150300083740289573 1159407028181265701304295)
    ·
      refine ⟨1739110542271898551956443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1159407028181265701304295 1739110542271898551956443)
      ·
        refine ⟨2608665813407847827934665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739110542271898551956443 2608665813407847827934665)
        ·
          refine ⟨1956499360055885870950999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608665813407847827934665 1956499360055885870950999)
          ·
            refine ⟨2934749040083828806426499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956499360055885870950999 2934749040083828806426499)
            ·
              refine ⟨4402123560125743209639749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934749040083828806426499 4402123560125743209639749)
              ·
                refine ⟨825398167523576851807453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4402123560125743209639749 825398167523576851807453)
                ·
                  refine ⟨309524312821341319427795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825398167523576851807453 309524312821341319427795)
                  ·
                    rfl

theorem cell20_678146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_678146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678146 prefixEnd_678146 := by exact prefixLift 678146
  have htrace : WordTrace (prefixWord ++ tailWord_678146) baseStart_678146 baseEnd_678146 := by
    simpa [prefixWord, tailWord_678146, baseEnd_678146] using wordTrace_append hprefix tailTrace_678146
  have hstable : (prefixWord ++ tailWord_678146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678146).length < 2 ^ (prefixWord ++ tailWord_678146).sum := by decide
  have hdescent : baseEnd_678146 < baseStart_678146 := by decide
  rcases family_descends (prefixWord ++ tailWord_678146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678153 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 2]
def baseStart_678153 : Nat := 118140960795 + 678153 * 2 ^ 59
def prefixEnd_678153 : Nat := 4983230072969 + 3 ^ 40 * 678153 * 2
def baseEnd_678153 : Nat := 309527507812080406194433

theorem tailTrace_678153 : CollatzResearch.WordTrace tailWord_678153 prefixEnd_678153 309527507812080406194433 := by
  unfold tailWord_678153
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734271912174975156663113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16489514608116650104442075 24734271912174975156663113)
  ·
    refine ⟨18550703934131231367497335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24734271912174975156663113 18550703934131231367497335)
    ·
      refine ⟨27826055901196847051246003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18550703934131231367497335 27826055901196847051246003)
      ·
        refine ⟨41739083851795270576869005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27826055901196847051246003 41739083851795270576869005)
        ·
          refine ⟨15652156444423226466325877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41739083851795270576869005 15652156444423226466325877)
          ·
            refine ⟨1467389666664677481218051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15652156444423226466325877 1467389666664677481218051)
            ·
              refine ⟨2201084499997016221827077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467389666664677481218051 2201084499997016221827077)
              ·
                refine ⟨412703343749440541592577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2201084499997016221827077 412703343749440541592577)
                ·
                  refine ⟨309527507812080406194433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412703343749440541592577 309527507812080406194433)
                  ·
                    rfl

theorem cell20_678153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_678153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678153 prefixEnd_678153 := by exact prefixLift 678153
  have htrace : WordTrace (prefixWord ++ tailWord_678153) baseStart_678153 baseEnd_678153 := by
    simpa [prefixWord, tailWord_678153, baseEnd_678153] using wordTrace_append hprefix tailTrace_678153
  have hstable : (prefixWord ++ tailWord_678153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678153).length < 2 ^ (prefixWord ++ tailWord_678153).sum := by decide
  have hdescent : baseEnd_678153 < baseStart_678153 := by decide
  rcases family_descends (prefixWord ++ tailWord_678153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678167 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_678167 : Nat := 118140960795 + 678167 * 2 ^ 59
def prefixEnd_678167 : Nat := 4983230072969 + 3 ^ 40 * 678167 * 2
def baseEnd_678167 : Nat := 309533897793558579727709

theorem tailTrace_678167 : CollatzResearch.WordTrace tailWord_678167 prefixEnd_678167 309533897793558579727709 := by
  unfold tailWord_678167
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734782534124255547672755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16489855022749503698448503 24734782534124255547672755)
  ·
    refine ⟨37102173801186383321509133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24734782534124255547672755 37102173801186383321509133)
    ·
      refine ⟨13913315175444893745565925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37102173801186383321509133 13913315175444893745565925)
      ·
        refine ⟨2608746595395917577293611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13913315175444893745565925 2608746595395917577293611)
        ·
          refine ⟨3913119893093876365940417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608746595395917577293611 3913119893093876365940417)
          ·
            refine ⟨2934839919820407274455313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3913119893093876365940417 2934839919820407274455313)
            ·
              refine ⟨2201129939865305455841485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934839919820407274455313 2201129939865305455841485)
              ·
                refine ⟨825423727449489545940557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201129939865305455841485 825423727449489545940557)
                ·
                  refine ⟨309533897793558579727709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825423727449489545940557 309533897793558579727709)
                  ·
                    rfl

theorem cell20_678167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_678167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678167 prefixEnd_678167 := by exact prefixLift 678167
  have htrace : WordTrace (prefixWord ++ tailWord_678167) baseStart_678167 baseEnd_678167 := by
    simpa [prefixWord, tailWord_678167, baseEnd_678167] using wordTrace_append hprefix tailTrace_678167
  have hstable : (prefixWord ++ tailWord_678167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678167).length < 2 ^ (prefixWord ++ tailWord_678167).sum := by decide
  have hdescent : baseEnd_678167 < baseStart_678167 := by decide
  rcases family_descends (prefixWord ++ tailWord_678167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678195 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_678195 : Nat := 118140960795 + 678195 * 2 ^ 59
def prefixEnd_678195 : Nat := 4983230072969 + 3 ^ 40 * 678195 * 2
def baseEnd_678195 : Nat := 309546677756514926794261

theorem tailTrace_678195 : CollatzResearch.WordTrace tailWord_678195 prefixEnd_678195 309546677756514926794261 := by
  unfold tailWord_678195
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735803778022816329692039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16490535852015210886461359 24735803778022816329692039)
  ·
    refine ⟨37103705667034224494538059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24735803778022816329692039 37103705667034224494538059)
    ·
      refine ⟨55655558500551336741807089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37103705667034224494538059 55655558500551336741807089)
      ·
        refine ⟨41741668875413502556355317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55655558500551336741807089 41741668875413502556355317)
        ·
          refine ⟨3913281457070015864658311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41741668875413502556355317 3913281457070015864658311)
          ·
            refine ⟨5869922185605023796987467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913281457070015864658311 5869922185605023796987467)
            ·
              refine ⟨8804883278407535695481201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869922185605023796987467 8804883278407535695481201)
              ·
                refine ⟨6603662458805651771610901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8804883278407535695481201 6603662458805651771610901)
                ·
                  refine ⟨309546677756514926794261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6603662458805651771610901 309546677756514926794261)
                  ·
                    rfl

theorem cell20_678195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_678195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678195 prefixEnd_678195 := by exact prefixLift 678195
  have htrace : WordTrace (prefixWord ++ tailWord_678195) baseStart_678195 baseEnd_678195 := by
    simpa [prefixWord, tailWord_678195, baseEnd_678195] using wordTrace_append hprefix tailTrace_678195
  have hstable : (prefixWord ++ tailWord_678195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678195).length < 2 ^ (prefixWord ++ tailWord_678195).sum := by decide
  have hdescent : baseEnd_678195 < baseStart_678195 := by decide
  rcases family_descends (prefixWord ++ tailWord_678195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678238 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_678238 : Nat := 118140960795 + 678238 * 2 ^ 59
def prefixEnd_678238 : Nat := 4983230072969 + 3 ^ 40 * 678238 * 2
def baseEnd_678238 : Nat := 309566304128197888360753

theorem tailTrace_678238 : CollatzResearch.WordTrace tailWord_678238 prefixEnd_678238 309566304128197888360753 := by
  unfold tailWord_678238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092171514608379334188421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16491581411244689782338245 3092171514608379334188421)
  ·
    refine ⟨579782158989071125160329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3092171514608379334188421 579782158989071125160329)
    ·
      refine ⟨434836619241803343870247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579782158989071125160329 434836619241803343870247)
      ·
        refine ⟨652254928862705015805371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434836619241803343870247 652254928862705015805371)
        ·
          refine ⟨978382393294057523708057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652254928862705015805371 978382393294057523708057)
          ·
            refine ⟨733786794970543142781043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978382393294057523708057 733786794970543142781043)
            ·
              refine ⟨1100680192455814714171565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733786794970543142781043 1100680192455814714171565)
              ·
                refine ⟨412755072170930517814337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100680192455814714171565 412755072170930517814337)
                ·
                  refine ⟨309566304128197888360753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412755072170930517814337 309566304128197888360753)
                  ·
                    rfl

theorem cell20_678238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_678238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678238 prefixEnd_678238 := by exact prefixLift 678238
  have htrace : WordTrace (prefixWord ++ tailWord_678238) baseStart_678238 baseEnd_678238 := by
    simpa [prefixWord, tailWord_678238, baseEnd_678238] using wordTrace_append hprefix tailTrace_678238
  have hstable : (prefixWord ++ tailWord_678238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678238).length < 2 ^ (prefixWord ++ tailWord_678238).sum := by decide
  have hdescent : baseEnd_678238 < baseStart_678238 := by decide
  rcases family_descends (prefixWord ++ tailWord_678238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678281 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_678281 : Nat := 118140960795 + 678281 * 2 ^ 59
def prefixEnd_678281 : Nat := 4983230072969 + 3 ^ 40 * 678281 * 2
def baseEnd_678281 : Nat := 309585930499880849927243

theorem tailTrace_678281 : CollatzResearch.WordTrace tailWord_678281 prefixEnd_678281 309585930499880849927243 := by
  unfold tailWord_678281
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738940455711253017322697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16492626970474168678215131 24738940455711253017322697)
  ·
    refine ⟨18554205341783439762992023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24738940455711253017322697 18554205341783439762992023)
    ·
      refine ⟨27831308012675159644488035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18554205341783439762992023 27831308012675159644488035)
      ·
        refine ⟨41746962019012739466732053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27831308012675159644488035 41746962019012739466732053)
        ·
          refine ⟨1956888844641222162503065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41746962019012739466732053 1956888844641222162503065)
          ·
            refine ⟨1467666633480916621877299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956888844641222162503065 1467666633480916621877299)
            ·
              refine ⟨2201499950221374932815949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467666633480916621877299 2201499950221374932815949)
              ·
                refine ⟨825562481333015599805981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201499950221374932815949 825562481333015599805981)
                ·
                  refine ⟨309585930499880849927243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825562481333015599805981 309585930499880849927243)
                  ·
                    rfl

theorem cell20_678281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_678281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678281 prefixEnd_678281 := by exact prefixLift 678281
  have htrace : WordTrace (prefixWord ++ tailWord_678281) baseStart_678281 baseEnd_678281 := by
    simpa [prefixWord, tailWord_678281, baseEnd_678281] using wordTrace_append hprefix tailTrace_678281
  have hstable : (prefixWord ++ tailWord_678281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678281).length < 2 ^ (prefixWord ++ tailWord_678281).sum := by decide
  have hdescent : baseEnd_678281 < baseStart_678281 := by decide
  rcases family_descends (prefixWord ++ tailWord_678281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678314 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_678314 : Nat := 118140960795 + 678314 * 2 ^ 59
def prefixEnd_678314 : Nat := 4983230072969 + 3 ^ 40 * 678314 * 2
def baseEnd_678314 : Nat := 309600992599079401827109

theorem tailTrace_678314 : CollatzResearch.WordTrace tailWord_678314 prefixEnd_678314 309600992599079401827109 := by
  unfold tailWord_678314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185036016147924913318499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16493429376394466435515997 6185036016147924913318499)
  ·
    refine ⟨9277554024221887369977749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6185036016147924913318499 9277554024221887369977749)
    ·
      refine ⟨434885344885400970467707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9277554024221887369977749 434885344885400970467707)
      ·
        refine ⟨652328017328101455701561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434885344885400970467707 652328017328101455701561)
        ·
          refine ⟨489246012996076091776171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652328017328101455701561 489246012996076091776171)
          ·
            refine ⟨733869019494114137664257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489246012996076091776171 733869019494114137664257)
            ·
              refine ⟨550401764620585603248193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733869019494114137664257 550401764620585603248193)
              ·
                refine ⟨412801323465439202436145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550401764620585603248193 412801323465439202436145)
                ·
                  refine ⟨309600992599079401827109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412801323465439202436145 309600992599079401827109)
                  ·
                    rfl

theorem cell20_678314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_678314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678314 prefixEnd_678314 := by exact prefixLift 678314
  have htrace : WordTrace (prefixWord ++ tailWord_678314) baseStart_678314 baseEnd_678314 := by
    simpa [prefixWord, tailWord_678314, baseEnd_678314] using wordTrace_append hprefix tailTrace_678314
  have hstable : (prefixWord ++ tailWord_678314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678314).length < 2 ^ (prefixWord ++ tailWord_678314).sum := by decide
  have hdescent : baseEnd_678314 < baseStart_678314 := by decide
  rcases family_descends (prefixWord ++ tailWord_678314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678333 : List Nat := [1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_678333 : Nat := 118140960795 + 678333 * 2 ^ 59
def prefixEnd_678333 : Nat := 4983230072969 + 3 ^ 40 * 678333 * 2
def baseEnd_678333 : Nat := 103203221572266593397899

theorem tailTrace_678333 : CollatzResearch.WordTrace tailWord_678333 prefixEnd_678333 103203221572266593397899 := by
  unfold tailWord_678333
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740837051522865898215653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16493891367681910598810435 24740837051522865898215653)
  ·
    refine ⟨4638906947160537355915435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24740837051522865898215653 4638906947160537355915435)
    ·
      refine ⟨6958360420740806033873153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4638906947160537355915435 6958360420740806033873153)
      ·
        refine ⟨5218770315555604525404865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6958360420740806033873153 5218770315555604525404865)
        ·
          refine ⟨3914077736666703394053649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5218770315555604525404865 3914077736666703394053649)
          ·
            refine ⟨2935558302500027545540237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914077736666703394053649 2935558302500027545540237)
            ·
              refine ⟨1100834363437510329577589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935558302500027545540237 1100834363437510329577589)
              ·
                refine ⟨103203221572266593397899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100834363437510329577589 103203221572266593397899)
                ·
                  rfl

theorem cell20_678333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_678333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678333 prefixEnd_678333 := by exact prefixLift 678333
  have htrace : WordTrace (prefixWord ++ tailWord_678333) baseStart_678333 baseEnd_678333 := by
    simpa [prefixWord, tailWord_678333, baseEnd_678333] using wordTrace_append hprefix tailTrace_678333
  have hstable : (prefixWord ++ tailWord_678333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678333).length < 2 ^ (prefixWord ++ tailWord_678333).sum := by decide
  have hdescent : baseEnd_678333 < baseStart_678333 := by decide
  rcases family_descends (prefixWord ++ tailWord_678333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678370 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_678370 : Nat := 118140960795 + 678370 * 2 ^ 59
def prefixEnd_678370 : Nat := 4983230072969 + 3 ^ 40 * 678370 * 2
def baseEnd_678370 : Nat := 309626552524992095960213

theorem tailTrace_678370 : CollatzResearch.WordTrace tailWord_678370 prefixEnd_678370 309626552524992095960213 := by
  unfold tailWord_678370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185546638097205304328141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16494791034925880811541709 6185546638097205304328141)
  ·
    refine ⟨2319579989286451989123053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6185546638097205304328141 2319579989286451989123053)
    ·
      refine ⟨869842495982419495921145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2319579989286451989123053 869842495982419495921145)
      ·
        refine ⟨652381871986814621940859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869842495982419495921145 652381871986814621940859)
        ·
          refine ⟨978572807980221932911289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652381871986814621940859 978572807980221932911289)
          ·
            refine ⟨733929605985166449683467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978572807980221932911289 733929605985166449683467)
            ·
              refine ⟨1100894408977749674525201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733929605985166449683467 1100894408977749674525201)
              ·
                refine ⟨825670806733312255893901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100894408977749674525201 825670806733312255893901)
                ·
                  refine ⟨309626552524992095960213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825670806733312255893901 309626552524992095960213)
                  ·
                    rfl

theorem cell20_678370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_678370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678370 prefixEnd_678370 := by exact prefixLift 678370
  have htrace : WordTrace (prefixWord ++ tailWord_678370) baseStart_678370 baseEnd_678370 := by
    simpa [prefixWord, tailWord_678370, baseEnd_678370] using wordTrace_append hprefix tailTrace_678370
  have hstable : (prefixWord ++ tailWord_678370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678370).length < 2 ^ (prefixWord ++ tailWord_678370).sum := by decide
  have hdescent : baseEnd_678370 < baseStart_678370 := by decide
  rcases family_descends (prefixWord ++ tailWord_678370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678371 : List Nat := [1, 1, 1, 6, 3, 1, 7]
def baseStart_678371 : Nat := 118140960795 + 678371 * 2 ^ 59
def prefixEnd_678371 : Nat := 4983230072969 + 3 ^ 40 * 678371 * 2
def baseEnd_678371 : Nat := 34403000994693392991875

theorem tailTrace_678371 : CollatzResearch.WordTrace tailWord_678371 prefixEnd_678371 34403000994693392991875 := by
  unfold tailWord_678371
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742223025385198388098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16494815350256798925399311 24742223025385198388098967)
  ·
    refine ⟨37113334538077797582148451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24742223025385198388098967 37113334538077797582148451)
    ·
      refine ⟨55670001807116696373222677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37113334538077797582148451 55670001807116696373222677)
      ·
        refine ⟨2609531334708595142494813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55670001807116696373222677 2609531334708595142494813)
        ·
          refine ⟨978574250515723178435555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2609531334708595142494813 978574250515723178435555)
          ·
            refine ⟨1467861375773584767653333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978574250515723178435555 1467861375773584767653333)
            ·
              refine ⟨34403000994693392991875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1467861375773584767653333 34403000994693392991875)
              ·
                rfl

theorem cell20_678371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_678371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678371 prefixEnd_678371 := by exact prefixLift 678371
  have htrace : WordTrace (prefixWord ++ tailWord_678371) baseStart_678371 baseEnd_678371 := by
    simpa [prefixWord, tailWord_678371, baseEnd_678371] using wordTrace_append hprefix tailTrace_678371
  have hstable : (prefixWord ++ tailWord_678371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678371).length < 2 ^ (prefixWord ++ tailWord_678371).sum := by decide
  have hdescent : baseEnd_678371 < baseStart_678371 := by decide
  rcases family_descends (prefixWord ++ tailWord_678371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678381 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_678381 : Nat := 118140960795 + 678381 * 2 ^ 59
def prefixEnd_678381 : Nat := 4983230072969 + 3 ^ 40 * 678381 * 2
def baseEnd_678381 : Nat := 309631573224724946593501

theorem tailTrace_678381 : CollatzResearch.WordTrace tailWord_678381 prefixEnd_678381 309631573224724946593501 := by
  unfold tailWord_678381
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742587755348970095962997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16495058503565980063975331 24742587755348970095962997)
  ·
    refine ⟨2319617602063965946496531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24742587755348970095962997 2319617602063965946496531)
    ·
      refine ⟨3479426403095948919744797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319617602063965946496531 3479426403095948919744797)
      ·
        refine ⟨1304784901160980844904299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3479426403095948919744797 1304784901160980844904299)
        ·
          refine ⟨1957177351741471267356449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304784901160980844904299 1957177351741471267356449)
          ·
            refine ⟨1467883013806103450517337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1957177351741471267356449 1467883013806103450517337)
            ·
              refine ⟨1100912260354577587888003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467883013806103450517337 1100912260354577587888003)
              ·
                refine ⟨1651368390531866381832005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100912260354577587888003 1651368390531866381832005)
                ·
                  refine ⟨309631573224724946593501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651368390531866381832005 309631573224724946593501)
                  ·
                    rfl

theorem cell20_678381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_678381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678381 prefixEnd_678381 := by exact prefixLift 678381
  have htrace : WordTrace (prefixWord ++ tailWord_678381) baseStart_678381 baseEnd_678381 := by
    simpa [prefixWord, tailWord_678381, baseEnd_678381] using wordTrace_append hprefix tailTrace_678381
  have hstable : (prefixWord ++ tailWord_678381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678381).length < 2 ^ (prefixWord ++ tailWord_678381).sum := by decide
  have hdescent : baseEnd_678381 < baseStart_678381 := by decide
  rcases family_descends (prefixWord ++ tailWord_678381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678392 : List Nat := [2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_678392 : Nat := 118140960795 + 678392 * 2 ^ 59
def prefixEnd_678392 : Nat := 4983230072969 + 3 ^ 40 * 678392 * 2
def baseEnd_678392 : Nat := 103212197974819265742263

theorem tailTrace_678392 : CollatzResearch.WordTrace tailWord_678392 prefixEnd_678392 103212197974819265742263 := by
  unfold tailWord_678392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371494479154559487306715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16495325972206079316408953 12371494479154559487306715)
  ·
    refine ⟨18557241718731839230960073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371494479154559487306715 18557241718731839230960073)
    ·
      refine ⟨13917931289048879423220055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18557241718731839230960073 13917931289048879423220055)
      ·
        refine ⟨20876896933573319134830083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13917931289048879423220055 20876896933573319134830083)
        ·
          refine ⟨31315345400359978702245125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20876896933573319134830083 31315345400359978702245125)
          ·
            refine ⟨5871627262567496006670961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31315345400359978702245125 5871627262567496006670961)
            ·
              refine ⟨4403720446925622005003221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871627262567496006670961 4403720446925622005003221)
              ·
                refine ⟨103212197974819265742263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4403720446925622005003221 103212197974819265742263)
                ·
                  rfl

theorem cell20_678392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_678392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678392 prefixEnd_678392 := by exact prefixLift 678392
  have htrace : WordTrace (prefixWord ++ tailWord_678392) baseStart_678392 baseEnd_678392 := by
    simpa [prefixWord, tailWord_678392, baseEnd_678392] using wordTrace_append hprefix tailTrace_678392
  have hstable : (prefixWord ++ tailWord_678392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678392).length < 2 ^ (prefixWord ++ tailWord_678392).sum := by decide
  have hdescent : baseEnd_678392 < baseStart_678392 := by decide
  rcases family_descends (prefixWord ++ tailWord_678392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678436 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_678436 : Nat := 118140960795 + 678436 * 2 ^ 59
def prefixEnd_678436 : Nat := 4983230072969 + 3 ^ 40 * 678436 * 2
def baseEnd_678436 : Nat := 309656676723389199759943

theorem tailTrace_678436 : CollatzResearch.WordTrace tailWord_678436 prefixEnd_678436 309656676723389199759943 := by
  unfold tailWord_678436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372296885074857244607581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16496395846766476326143441 12372296885074857244607581)
  ·
    refine ⟨4639611331903071466727843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12372296885074857244607581 4639611331903071466727843)
    ·
      refine ⟨6959416997854607200091765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639611331903071466727843 6959416997854607200091765)
      ·
        refine ⟨652445343548869425008603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6959416997854607200091765 652445343548869425008603)
        ·
          refine ⟨978668015323304137512905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652445343548869425008603 978668015323304137512905)
          ·
            refine ⟨734001011492478103134679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978668015323304137512905 734001011492478103134679)
            ·
              refine ⟨1101001517238717154702019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734001011492478103134679 1101001517238717154702019)
              ·
                refine ⟨1651502275858075732053029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101001517238717154702019 1651502275858075732053029)
                ·
                  refine ⟨309656676723389199759943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651502275858075732053029 309656676723389199759943)
                  ·
                    rfl

theorem cell20_678436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_678436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678436 prefixEnd_678436 := by exact prefixLift 678436
  have htrace : WordTrace (prefixWord ++ tailWord_678436) baseStart_678436 baseEnd_678436 := by
    simpa [prefixWord, tailWord_678436, baseEnd_678436] using wordTrace_append hprefix tailTrace_678436
  have hstable : (prefixWord ++ tailWord_678436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678436).length < 2 ^ (prefixWord ++ tailWord_678436).sum := by decide
  have hdescent : baseEnd_678436 < baseStart_678436 := by decide
  rcases family_descends (prefixWord ++ tailWord_678436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678446 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_678446 : Nat := 118140960795 + 678446 * 2 ^ 59
def prefixEnd_678446 : Nat := 4983230072969 + 3 ^ 40 * 678446 * 2
def baseEnd_678446 : Nat := 309661240995873609426569

theorem tailTrace_678446 : CollatzResearch.WordTrace tailWord_678446 prefixEnd_678446 309661240995873609426569 := by
  unfold tailWord_678446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093119812514185774634899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16496639000075657464719461 3093119812514185774634899)
  ·
    refine ⟨4639679718771278661952349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093119812514185774634899 4639679718771278661952349)
    ·
      refine ⟨1739879894539229498232131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4639679718771278661952349 1739879894539229498232131)
      ·
        refine ⟨2609819841808844247348197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739879894539229498232131 2609819841808844247348197)
        ·
          refine ⟨489341220339158296377787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2609819841808844247348197 489341220339158296377787)
          ·
            refine ⟨734011830508737444566681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489341220339158296377787 734011830508737444566681)
            ·
              refine ⟨550508872881553083425011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734011830508737444566681 550508872881553083425011)
              ·
                refine ⟨825763309322329625137517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550508872881553083425011 825763309322329625137517)
                ·
                  refine ⟨309661240995873609426569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825763309322329625137517 309661240995873609426569)
                  ·
                    rfl

theorem cell20_678446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_678446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678446 prefixEnd_678446 := by exact prefixLift 678446
  have htrace : WordTrace (prefixWord ++ tailWord_678446) baseStart_678446 baseEnd_678446 := by
    simpa [prefixWord, tailWord_678446, baseEnd_678446] using wordTrace_append hprefix tailTrace_678446
  have hstable : (prefixWord ++ tailWord_678446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678446).length < 2 ^ (prefixWord ++ tailWord_678446).sum := by decide
  have hdescent : baseEnd_678446 < baseStart_678446 := by decide
  rcases family_descends (prefixWord ++ tailWord_678446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678475 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_678475 : Nat := 118140960795 + 678475 * 2 ^ 59
def prefixEnd_678475 : Nat := 4983230072969 + 3 ^ 40 * 678475 * 2
def baseEnd_678475 : Nat := 309674477386078397459783

theorem tailTrace_678475 : CollatzResearch.WordTrace tailWord_678475 prefixEnd_678475 309674477386078397459783 := by
  unfold tailWord_678475
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746016217008424149884879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16497344144672282766589919 24746016217008424149884879)
  ·
    refine ⟨37119024325512636224827319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24746016217008424149884879 37119024325512636224827319)
    ·
      refine ⟨55678536488268954337240979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37119024325512636224827319 55678536488268954337240979)
      ·
        refine ⟨83517804732403431505861469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55678536488268954337240979 83517804732403431505861469)
        ·
          refine ⟨31319176774651286814698051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83517804732403431505861469 31319176774651286814698051)
          ·
            refine ⟨46978765161976930222047077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31319176774651286814698051 46978765161976930222047077)
            ·
              refine ⟨8808518467870674416633827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46978765161976930222047077 8808518467870674416633827)
              ·
                refine ⟨13212777701806011624950741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808518467870674416633827 13212777701806011624950741)
                ·
                  refine ⟨309674477386078397459783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13212777701806011624950741 309674477386078397459783)
                  ·
                    rfl

theorem cell20_678475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_678475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678475 prefixEnd_678475 := by exact prefixLift 678475
  have htrace : WordTrace (prefixWord ++ tailWord_678475) baseStart_678475 baseEnd_678475 := by
    simpa [prefixWord, tailWord_678475, baseEnd_678475] using wordTrace_append hprefix tailTrace_678475
  have hstable : (prefixWord ++ tailWord_678475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678475).length < 2 ^ (prefixWord ++ tailWord_678475).sum := by decide
  have hdescent : baseEnd_678475 < baseStart_678475 := by decide
  rcases family_descends (prefixWord ++ tailWord_678475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678498 : List Nat := [3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_678498 : Nat := 118140960795 + 678498 * 2 ^ 59
def prefixEnd_678498 : Nat := 4983230072969 + 3 ^ 40 * 678498 * 2
def baseEnd_678498 : Nat := 103228325070930846564341

theorem tailTrace_678498 : CollatzResearch.WordTrace tailWord_678498 prefixEnd_678498 103228325070930846564341 := by
  unfold tailWord_678498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186713773981274769493037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16497903397283399385314765 6186713773981274769493037)
  ·
    refine ⟨2320017665242978038559889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6186713773981274769493037 2320017665242978038559889)
    ·
      refine ⟨1740013248932233528919917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2320017665242978038559889 1740013248932233528919917)
      ·
        refine ⟨652504968349587573344969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1740013248932233528919917 652504968349587573344969)
        ·
          refine ⟨489378726262190680008727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652504968349587573344969 489378726262190680008727)
          ·
            refine ⟨734068089393286020013091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489378726262190680008727 734068089393286020013091)
            ·
              refine ⟨1101102134089929030019637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734068089393286020013091 1101102134089929030019637)
              ·
                refine ⟨103228325070930846564341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1101102134089929030019637 103228325070930846564341)
                ·
                  rfl

theorem cell20_678498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_678498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678498 prefixEnd_678498 := by exact prefixLift 678498
  have htrace : WordTrace (prefixWord ++ tailWord_678498) baseStart_678498 baseEnd_678498 := by
    simpa [prefixWord, tailWord_678498, baseEnd_678498] using wordTrace_append hprefix tailTrace_678498
  have hstable : (prefixWord ++ tailWord_678498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678498).length < 2 ^ (prefixWord ++ tailWord_678498).sum := by decide
  have hdescent : baseEnd_678498 < baseStart_678498 := by decide
  rcases family_descends (prefixWord ++ tailWord_678498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678499 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_678499 : Nat := 118140960795 + 678499 * 2 ^ 59
def prefixEnd_678499 : Nat := 4983230072969 + 3 ^ 40 * 678499 * 2
def baseEnd_678499 : Nat := 309685431640040980659685

theorem tailTrace_678499 : CollatzResearch.WordTrace tailWord_678499 prefixEnd_678499 309685431640040980659685 := by
  unfold tailWord_678499
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746891568921476248758551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16497927712614317499172367 24746891568921476248758551)
  ·
    refine ⟨37120337353382214373137827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24746891568921476248758551 37120337353382214373137827)
    ·
      refine ⟨55680506030073321559706741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37120337353382214373137827 55680506030073321559706741)
      ·
        refine ⟨5220047440319373896222507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55680506030073321559706741 5220047440319373896222507)
        ·
          refine ⟨7830071160479060844333761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220047440319373896222507 7830071160479060844333761)
          ·
            refine ⟨5872553370359295633250321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830071160479060844333761 5872553370359295633250321)
            ·
              refine ⟨4404415027769471724937741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872553370359295633250321 4404415027769471724937741)
              ·
                refine ⟨1651655635413551896851653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4404415027769471724937741 1651655635413551896851653)
                ·
                  refine ⟨309685431640040980659685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651655635413551896851653 309685431640040980659685)
                  ·
                    rfl

theorem cell20_678499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_678499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678499 prefixEnd_678499 := by exact prefixLift 678499
  have htrace : WordTrace (prefixWord ++ tailWord_678499) baseStart_678499 baseEnd_678499 := by
    simpa [prefixWord, tailWord_678499, baseEnd_678499] using wordTrace_append hprefix tailTrace_678499
  have hstable : (prefixWord ++ tailWord_678499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678499).length < 2 ^ (prefixWord ++ tailWord_678499).sum := by decide
  have hdescent : baseEnd_678499 < baseStart_678499 := by decide
  rcases family_descends (prefixWord ++ tailWord_678499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678509 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_678509 : Nat := 118140960795 + 678509 * 2 ^ 59
def prefixEnd_678509 : Nat := 4983230072969 + 3 ^ 40 * 678509 * 2
def baseEnd_678509 : Nat := 309689995912525390326311

theorem tailTrace_678509 : CollatzResearch.WordTrace tailWord_678509 prefixEnd_678509 309689995912525390326311 := by
  unfold tailWord_678509
  simp only [CollatzResearch.WordTrace]
  refine ⟨24747256298885247956622581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16498170865923498637748387 24747256298885247956622581)
  ·
    refine ⟨2320055278020491995933367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24747256298885247956622581 2320055278020491995933367)
    ·
      refine ⟨3480082917030737993900051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320055278020491995933367 3480082917030737993900051)
      ·
        refine ⟨5220124375546106990850077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480082917030737993900051 5220124375546106990850077)
        ·
          refine ⟨1957546640829790121568779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5220124375546106990850077 1957546640829790121568779)
          ·
            refine ⟨2936319961244685182353169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957546640829790121568779 2936319961244685182353169)
            ·
              refine ⟨2202239970933513886764877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936319961244685182353169 2202239970933513886764877)
              ·
                refine ⟨825839989100067707536829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2202239970933513886764877 825839989100067707536829)
                ·
                  refine ⟨309689995912525390326311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825839989100067707536829 309689995912525390326311)
                  ·
                    rfl

theorem cell20_678509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_678509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678509 prefixEnd_678509 := by exact prefixLift 678509
  have htrace : WordTrace (prefixWord ++ tailWord_678509) baseStart_678509 baseEnd_678509 := by
    simpa [prefixWord, tailWord_678509, baseEnd_678509] using wordTrace_append hprefix tailTrace_678509
  have hstable : (prefixWord ++ tailWord_678509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678509).length < 2 ^ (prefixWord ++ tailWord_678509).sum := by decide
  have hdescent : baseEnd_678509 < baseStart_678509 := by decide
  rcases family_descends (prefixWord ++ tailWord_678509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678513 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_678513 : Nat := 118140960795 + 678513 * 2 ^ 59
def prefixEnd_678513 : Nat := 4983230072969 + 3 ^ 40 * 678513 * 2
def baseEnd_678513 : Nat := 309691821621519154192961

theorem tailTrace_678513 : CollatzResearch.WordTrace tailWord_678513 prefixEnd_678513 309691821621519154192961 := by
  unfold tailWord_678513
  simp only [CollatzResearch.WordTrace]
  refine ⟨24747402190870756639768193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16498268127247171093178795 24747402190870756639768193)
  ·
    refine ⟨18560551643153067479826145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24747402190870756639768193 18560551643153067479826145)
    ·
      refine ⟨13920413732364800609869609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18560551643153067479826145 13920413732364800609869609)
      ·
        refine ⟨10440310299273600457402207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13920413732364800609869609 10440310299273600457402207)
        ·
          refine ⟨15660465448910400686103311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10440310299273600457402207 15660465448910400686103311)
          ·
            refine ⟨23490698173365601029154967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660465448910400686103311 23490698173365601029154967)
            ·
              refine ⟨35236047260048401543732451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23490698173365601029154967 35236047260048401543732451)
              ·
                refine ⟨52854070890072602315598677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35236047260048401543732451 52854070890072602315598677)
                ·
                  refine ⟨309691821621519154192961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52854070890072602315598677 309691821621519154192961)
                  ·
                    rfl

theorem cell20_678513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_678513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678513 prefixEnd_678513 := by exact prefixLift 678513
  have htrace : WordTrace (prefixWord ++ tailWord_678513) baseStart_678513 baseEnd_678513 := by
    simpa [prefixWord, tailWord_678513, baseEnd_678513] using wordTrace_append hprefix tailTrace_678513
  have hstable : (prefixWord ++ tailWord_678513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678513).length < 2 ^ (prefixWord ++ tailWord_678513).sum := by decide
  have hdescent : baseEnd_678513 < baseStart_678513 := by decide
  rcases family_descends (prefixWord ++ tailWord_678513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678533 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 2]
def baseStart_678533 : Nat := 118140960795 + 678533 * 2 ^ 59
def prefixEnd_678533 : Nat := 4983230072969 + 3 ^ 40 * 678533 * 2
def baseEnd_678533 : Nat := 309700950166487973526213

theorem tailTrace_678533 : CollatzResearch.WordTrace tailWord_678533 prefixEnd_678533 309700950166487973526213 := by
  unfold tailWord_678533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24748131650798300055496253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16498754433865533370330835 24748131650798300055496253)
  ·
    refine ⟨9280549369049362520811095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24748131650798300055496253 9280549369049362520811095)
    ·
      refine ⟨13920824053574043781216643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9280549369049362520811095 13920824053574043781216643)
      ·
        refine ⟨20881236080361065671824965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13920824053574043781216643 20881236080361065671824965)
        ·
          refine ⟨3915231765067699813467181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20881236080361065671824965 3915231765067699813467181)
          ·
            refine ⟨1468211911900387430050193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3915231765067699813467181 1468211911900387430050193)
            ·
              refine ⟨1101158933925290572537645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468211911900387430050193 1101158933925290572537645)
              ·
                refine ⟨412934600221983964701617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101158933925290572537645 412934600221983964701617)
                ·
                  refine ⟨309700950166487973526213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412934600221983964701617 309700950166487973526213)
                  ·
                    rfl

theorem cell20_678533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_678533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678533 prefixEnd_678533 := by exact prefixLift 678533
  have htrace : WordTrace (prefixWord ++ tailWord_678533) baseStart_678533 baseEnd_678533 := by
    simpa [prefixWord, tailWord_678533, baseEnd_678533] using wordTrace_append hprefix tailTrace_678533
  have hstable : (prefixWord ++ tailWord_678533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678533).length < 2 ^ (prefixWord ++ tailWord_678533).sum := by decide
  have hdescent : baseEnd_678533 < baseStart_678533 := by decide
  rcases family_descends (prefixWord ++ tailWord_678533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678575 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_678575 : Nat := 118140960795 + 678575 * 2 ^ 59
def prefixEnd_678575 : Nat := 4983230072969 + 3 ^ 40 * 678575 * 2
def baseEnd_678575 : Nat := 309720120110922494126041

theorem tailTrace_678575 : CollatzResearch.WordTrace tailWord_678575 prefixEnd_678575 309720120110922494126041 := by
  unfold tailWord_678575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24749663516646141228525179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16499775677764094152350119 24749663516646141228525179)
  ·
    refine ⟨37124495274969211842787769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24749663516646141228525179 37124495274969211842787769)
    ·
      refine ⟨27843371456226908882090827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37124495274969211842787769 27843371456226908882090827)
      ·
        refine ⟨41765057184340363323136241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27843371456226908882090827 41765057184340363323136241)
        ·
          refine ⟨31323792888255272492352181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41765057184340363323136241 31323792888255272492352181)
          ·
            refine ⟨2936605583273931796158017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31323792888255272492352181 2936605583273931796158017)
            ·
              refine ⟨2202454187455448847118513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936605583273931796158017 2202454187455448847118513)
              ·
                refine ⟨1651840640591586635338885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202454187455448847118513 1651840640591586635338885)
                ·
                  refine ⟨309720120110922494126041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651840640591586635338885 309720120110922494126041)
                  ·
                    rfl

theorem cell20_678575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_678575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678575 prefixEnd_678575 := by exact prefixLift 678575
  have htrace : WordTrace (prefixWord ++ tailWord_678575) baseStart_678575 baseEnd_678575 := by
    simpa [prefixWord, tailWord_678575, baseEnd_678575] using wordTrace_append hprefix tailTrace_678575
  have hstable : (prefixWord ++ tailWord_678575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678575).length < 2 ^ (prefixWord ++ tailWord_678575).sum := by decide
  have hdescent : baseEnd_678575 < baseStart_678575 := by decide
  rcases family_descends (prefixWord ++ tailWord_678575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678605 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 4]
def baseStart_678605 : Nat := 118140960795 + 678605 * 2 ^ 59
def prefixEnd_678605 : Nat := 4983230072969 + 3 ^ 40 * 678605 * 2
def baseEnd_678605 : Nat := 309733812928375723125919

theorem tailTrace_678605 : CollatzResearch.WordTrace tailWord_678605 prefixEnd_678605 309733812928375723125919 := by
  unfold tailWord_678605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24750757706537456352117269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16500505137691637568078179 24750757706537456352117269)
  ·
    refine ⟨1160191767493943266505497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24750757706537456352117269 1160191767493943266505497)
    ·
      refine ⟨870143825620457449879123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160191767493943266505497 870143825620457449879123)
      ·
        refine ⟨1305215738430686174818685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870143825620457449879123 1305215738430686174818685)
        ·
          refine ⟨489455901911507315557007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1305215738430686174818685 489455901911507315557007)
          ·
            refine ⟨734183852867260973335511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489455901911507315557007 734183852867260973335511)
            ·
              refine ⟨1101275779300891460003267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734183852867260973335511 1101275779300891460003267)
              ·
                refine ⟨1651913668951337190004901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101275779300891460003267 1651913668951337190004901)
                ·
                  refine ⟨309733812928375723125919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651913668951337190004901 309733812928375723125919)
                  ·
                    rfl

theorem cell20_678605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_678605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678605 prefixEnd_678605 := by exact prefixLift 678605
  have htrace : WordTrace (prefixWord ++ tailWord_678605) baseStart_678605 baseEnd_678605 := by
    simpa [prefixWord, tailWord_678605, baseEnd_678605] using wordTrace_append hprefix tailTrace_678605
  have hstable : (prefixWord ++ tailWord_678605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678605).length < 2 ^ (prefixWord ++ tailWord_678605).sum := by decide
  have hdescent : baseEnd_678605 < baseStart_678605 := by decide
  rcases family_descends (prefixWord ++ tailWord_678605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678606 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_678606 : Nat := 118140960795 + 678606 * 2 ^ 59
def prefixEnd_678606 : Nat := 4983230072969 + 3 ^ 40 * 678606 * 2
def baseEnd_678606 : Nat := 309734269355624164092581

theorem tailTrace_678606 : CollatzResearch.WordTrace tailWord_678606 prefixEnd_678606 309734269355624164092581 := by
  unfold tailWord_678606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093849272441729190362959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16500529453022555681935781 3093849272441729190362959)
  ·
    refine ⟨4640773908662593785544439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093849272441729190362959 4640773908662593785544439)
    ·
      refine ⟨6961160862993890678316659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640773908662593785544439 6961160862993890678316659)
      ·
        refine ⟨10441741294490836017474989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961160862993890678316659 10441741294490836017474989)
        ·
          refine ⟨3915652985434063506553121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10441741294490836017474989 3915652985434063506553121)
          ·
            refine ⟨2936739739075547629914841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915652985434063506553121 2936739739075547629914841)
            ·
              refine ⟨2202554804306660722436131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936739739075547629914841 2202554804306660722436131)
              ·
                refine ⟨3303832206459991083654197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202554804306660722436131 3303832206459991083654197)
                ·
                  refine ⟨309734269355624164092581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3303832206459991083654197 309734269355624164092581)
                  ·
                    rfl

theorem cell20_678606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_678606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678606 prefixEnd_678606 := by exact prefixLift 678606
  have htrace : WordTrace (prefixWord ++ tailWord_678606) baseStart_678606 baseEnd_678606 := by
    simpa [prefixWord, tailWord_678606, baseEnd_678606] using wordTrace_append hprefix tailTrace_678606
  have hstable : (prefixWord ++ tailWord_678606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678606).length < 2 ^ (prefixWord ++ tailWord_678606).sum := by decide
  have hdescent : baseEnd_678606 < baseStart_678606 := by decide
  rcases family_descends (prefixWord ++ tailWord_678606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678609 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 2]
def baseStart_678609 : Nat := 118140960795 + 678609 * 2 ^ 59
def prefixEnd_678609 : Nat := 4983230072969 + 3 ^ 40 * 678609 * 2
def baseEnd_678609 : Nat := 309735638637369486992569

theorem tailTrace_678609 : CollatzResearch.WordTrace tailWord_678609 prefixEnd_678609 309735638637369486992569 := by
  unfold tailWord_678609
  simp only [CollatzResearch.WordTrace]
  refine ⟨24750903598522965035262881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16500602399015310023508587 24750903598522965035262881)
  ·
    refine ⟨18563177698892223776447161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24750903598522965035262881 18563177698892223776447161)
    ·
      refine ⟨13922383274169167832335371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18563177698892223776447161 13922383274169167832335371)
      ·
        refine ⟨20883574911253751748503057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13922383274169167832335371 20883574911253751748503057)
        ·
          refine ⟨15662681183440313811377293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20883574911253751748503057 15662681183440313811377293)
          ·
            refine ⟨5873505443790117679266485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15662681183440313811377293 5873505443790117679266485)
            ·
              refine ⟨550641135355323532431233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5873505443790117679266485 550641135355323532431233)
              ·
                refine ⟨412980851516492649323425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550641135355323532431233 412980851516492649323425)
                ·
                  refine ⟨309735638637369486992569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412980851516492649323425 309735638637369486992569)
                  ·
                    rfl

theorem cell20_678609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_678609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678609 prefixEnd_678609 := by exact prefixLift 678609
  have htrace : WordTrace (prefixWord ++ tailWord_678609) baseStart_678609 baseEnd_678609 := by
    simpa [prefixWord, tailWord_678609, baseEnd_678609] using wordTrace_append hprefix tailTrace_678609
  have hstable : (prefixWord ++ tailWord_678609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678609).length < 2 ^ (prefixWord ++ tailWord_678609).sum := by decide
  have hdescent : baseEnd_678609 < baseStart_678609 := by decide
  rcases family_descends (prefixWord ++ tailWord_678609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678623 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 3]
def baseStart_678623 : Nat := 118140960795 + 678623 * 2 ^ 59
def prefixEnd_678623 : Nat := 4983230072969 + 3 ^ 40 * 678623 * 2
def baseEnd_678623 : Nat := 309742028618847660525845

theorem tailTrace_678623 : CollatzResearch.WordTrace tailWord_678623 prefixEnd_678623 309742028618847660525845 := by
  unfold tailWord_678623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751414220472245426272523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16500942813648163617515015 24751414220472245426272523)
  ·
    refine ⟨37127121330708368139408785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24751414220472245426272523 37127121330708368139408785)
    ·
      refine ⟨27845340998031276104556589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37127121330708368139408785 27845340998031276104556589)
      ·
        refine ⟨10442002874261728539208721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27845340998031276104556589 10442002874261728539208721)
        ·
          refine ⟨7831502155696296404406541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10442002874261728539208721 7831502155696296404406541)
          ·
            refine ⟨2936813308386111151652453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7831502155696296404406541 2936813308386111151652453)
            ·
              refine ⟨550652495322395840934835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2936813308386111151652453 550652495322395840934835)
              ·
                refine ⟨825978742983593761402253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550652495322395840934835 825978742983593761402253)
                ·
                  refine ⟨309742028618847660525845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825978742983593761402253 309742028618847660525845)
                  ·
                    rfl

theorem cell20_678623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_678623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678623 prefixEnd_678623 := by exact prefixLift 678623
  have htrace : WordTrace (prefixWord ++ tailWord_678623) baseStart_678623 baseEnd_678623 := by
    simpa [prefixWord, tailWord_678623, baseEnd_678623] using wordTrace_append hprefix tailTrace_678623
  have hstable : (prefixWord ++ tailWord_678623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678623).length < 2 ^ (prefixWord ++ tailWord_678623).sum := by decide
  have hdescent : baseEnd_678623 < baseStart_678623 := by decide
  rcases family_descends (prefixWord ++ tailWord_678623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678664 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_678664 : Nat := 118140960795 + 678664 * 2 ^ 59
def prefixEnd_678664 : Nat := 4983230072969 + 3 ^ 40 * 678664 * 2
def baseEnd_678664 : Nat := 309760742136033740159011

theorem tailTrace_678664 : CollatzResearch.WordTrace tailWord_678664 prefixEnd_678664 309760742136033740159011 := by
  unfold tailWord_678664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376454806661854714257523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16501939742215806285676697 12376454806661854714257523)
  ·
    refine ⟨18564682209992782071386285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376454806661854714257523 18564682209992782071386285)
    ·
      refine ⟨6961755828747293276769857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18564682209992782071386285 6961755828747293276769857)
      ·
        refine ⟨5221316871560469957577393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6961755828747293276769857 5221316871560469957577393)
        ·
          refine ⟨3915987653670352468183045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5221316871560469957577393 3915987653670352468183045)
          ·
            refine ⟨734247685063191087784321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3915987653670352468183045 734247685063191087784321)
            ·
              refine ⟨550685763797393315838241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734247685063191087784321 550685763797393315838241)
              ·
                refine ⟨413014322848044986878681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550685763797393315838241 413014322848044986878681)
                ·
                  refine ⟨309760742136033740159011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413014322848044986878681 309760742136033740159011)
                  ·
                    rfl

theorem cell20_678664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_678664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678664 prefixEnd_678664 := by exact prefixLift 678664
  have htrace : WordTrace (prefixWord ++ tailWord_678664) baseStart_678664 baseEnd_678664 := by
    simpa [prefixWord, tailWord_678664, baseEnd_678664] using wordTrace_append hprefix tailTrace_678664
  have hstable : (prefixWord ++ tailWord_678664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678664).length < 2 ^ (prefixWord ++ tailWord_678664).sum := by decide
  have hdescent : baseEnd_678664 < baseStart_678664 := by decide
  rcases family_descends (prefixWord ++ tailWord_678664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678665 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_678665 : Nat := 118140960795 + 678665 * 2 ^ 59
def prefixEnd_678665 : Nat := 4983230072969 + 3 ^ 40 * 678665 * 2
def baseEnd_678665 : Nat := 309761198563282181125673

theorem tailTrace_678665 : CollatzResearch.WordTrace tailWord_678665 prefixEnd_678665 309761198563282181125673 := by
  unfold tailWord_678665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24752946086320086599301449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16501964057546724399534299 24752946086320086599301449)
  ·
    refine ⟨18564709564740064949476087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24752946086320086599301449 18564709564740064949476087)
    ·
      refine ⟨27847064347110097424214131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18564709564740064949476087 27847064347110097424214131)
      ·
        refine ⟨41770596520665146136321197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847064347110097424214131 41770596520665146136321197)
        ·
          refine ⟨15663973695249429801120449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41770596520665146136321197 15663973695249429801120449)
          ·
            refine ⟨11747980271437072350840337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15663973695249429801120449 11747980271437072350840337)
            ·
              refine ⟨8810985203577804263130253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747980271437072350840337 8810985203577804263130253)
              ·
                refine ⟨3304119451341676598673845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8810985203577804263130253 3304119451341676598673845)
                ·
                  refine ⟨309761198563282181125673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304119451341676598673845 309761198563282181125673)
                  ·
                    rfl

theorem cell20_678665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_678665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678665 prefixEnd_678665 := by exact prefixLift 678665
  have htrace : WordTrace (prefixWord ++ tailWord_678665) baseStart_678665 baseEnd_678665 := by
    simpa [prefixWord, tailWord_678665, baseEnd_678665] using wordTrace_append hprefix tailTrace_678665
  have hstable : (prefixWord ++ tailWord_678665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678665).length < 2 ^ (prefixWord ++ tailWord_678665).sum := by decide
  have hdescent : baseEnd_678665 < baseStart_678665 := by decide
  rcases family_descends (prefixWord ++ tailWord_678665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678682 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_678682 : Nat := 118140960795 + 678682 * 2 ^ 59
def prefixEnd_678682 : Nat := 4983230072969 + 3 ^ 40 * 678682 * 2
def baseEnd_678682 : Nat := 309768957826505677558937

theorem tailTrace_678682 : CollatzResearch.WordTrace tailWord_678682 prefixEnd_678682 309768957826505677558937 := by
  unfold tailWord_678682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188391531814624625667575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16502377418172332335113533 6188391531814624625667575)
  ·
    refine ⟨9282587297721936938501363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188391531814624625667575 9282587297721936938501363)
    ·
      refine ⟨13923880946582905407752045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282587297721936938501363 13923880946582905407752045)
      ·
        refine ⟨5221455354968589527907017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13923880946582905407752045 5221455354968589527907017)
        ·
          refine ⟨3916091516226442145930263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5221455354968589527907017 3916091516226442145930263)
          ·
            refine ⟨5874137274339663218895395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916091516226442145930263 5874137274339663218895395)
            ·
              refine ⟨8811205911509494828343093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874137274339663218895395 8811205911509494828343093)
              ·
                refine ⟨826050554204015140157165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8811205911509494828343093 826050554204015140157165)
                ·
                  refine ⟨309768957826505677558937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826050554204015140157165 309768957826505677558937)
                  ·
                    rfl

theorem cell20_678682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_678682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678682 prefixEnd_678682 := by exact prefixLift 678682
  have htrace : WordTrace (prefixWord ++ tailWord_678682) baseStart_678682 baseEnd_678682 := by
    simpa [prefixWord, tailWord_678682, baseEnd_678682] using wordTrace_append hprefix tailTrace_678682
  have hstable : (prefixWord ++ tailWord_678682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678682).length < 2 ^ (prefixWord ++ tailWord_678682).sum := by decide
  have hdescent : baseEnd_678682 < baseStart_678682 := by decide
  rcases family_descends (prefixWord ++ tailWord_678682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678685 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_678685 : Nat := 118140960795 + 678685 * 2 ^ 59
def prefixEnd_678685 : Nat := 4983230072969 + 3 ^ 40 * 678685 * 2
def baseEnd_678685 : Nat := 309770327108251000458925

theorem tailTrace_678685 : CollatzResearch.WordTrace tailWord_678685 prefixEnd_678685 309770327108251000458925 := by
  unfold tailWord_678685
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753675546247630015029509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502450364165086676686339 24753675546247630015029509)
  ·
    refine ⟨4641314164921430627818033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24753675546247630015029509 4641314164921430627818033)
    ·
      refine ⟨3480985623691072970863525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4641314164921430627818033 3480985623691072970863525)
      ·
        refine ⟨652684804442076182036911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3480985623691072970863525 652684804442076182036911)
        ·
          refine ⟨979027206663114273055367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652684804442076182036911 979027206663114273055367)
          ·
            refine ⟨1468540809994671409583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979027206663114273055367 1468540809994671409583051)
            ·
              refine ⟨2202811214992007114374577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468540809994671409583051 2202811214992007114374577)
              ·
                refine ⟨1652108411244005335780933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202811214992007114374577 1652108411244005335780933)
                ·
                  refine ⟨309770327108251000458925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652108411244005335780933 309770327108251000458925)
                  ·
                    rfl

theorem cell20_678685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_678685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678685 prefixEnd_678685 := by exact prefixLift 678685
  have htrace : WordTrace (prefixWord ++ tailWord_678685) baseStart_678685 baseEnd_678685 := by
    simpa [prefixWord, tailWord_678685, baseEnd_678685] using wordTrace_append hprefix tailTrace_678685
  have hstable : (prefixWord ++ tailWord_678685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678685).length < 2 ^ (prefixWord ++ tailWord_678685).sum := by decide
  have hdescent : baseEnd_678685 < baseStart_678685 := by decide
  rcases family_descends (prefixWord ++ tailWord_678685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678689 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_678689 : Nat := 118140960795 + 678689 * 2 ^ 59
def prefixEnd_678689 : Nat := 4983230072969 + 3 ^ 40 * 678689 * 2
def baseEnd_678689 : Nat := 309772152817244764325575

theorem tailTrace_678689 : CollatzResearch.WordTrace tailWord_678689 prefixEnd_678689 309772152817244764325575 := by
  unfold tailWord_678689
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753821438233138698175121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502547625488759132116747 24753821438233138698175121)
  ·
    refine ⟨18565366078674854023631341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24753821438233138698175121 18565366078674854023631341)
    ·
      refine ⟨6962012279503070258861753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18565366078674854023631341 6962012279503070258861753)
      ·
        refine ⟨5221509209627302694146315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6962012279503070258861753 5221509209627302694146315)
        ·
          refine ⟨7832263814440954041219473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221509209627302694146315 7832263814440954041219473)
          ·
            refine ⟨5874197860830715530914605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832263814440954041219473 5874197860830715530914605)
            ·
              refine ⟨2202824197811518324092977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5874197860830715530914605 2202824197811518324092977)
              ·
                refine ⟨1652118148358638743069733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202824197811518324092977 1652118148358638743069733)
                ·
                  refine ⟨309772152817244764325575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652118148358638743069733 309772152817244764325575)
                  ·
                    rfl

theorem cell20_678689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_678689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678689 prefixEnd_678689 := by exact prefixLift 678689
  have htrace : WordTrace (prefixWord ++ tailWord_678689) baseStart_678689 baseEnd_678689 := by
    simpa [prefixWord, tailWord_678689, baseEnd_678689] using wordTrace_append hprefix tailTrace_678689
  have hstable : (prefixWord ++ tailWord_678689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678689).length < 2 ^ (prefixWord ++ tailWord_678689).sum := by decide
  have hdescent : baseEnd_678689 < baseStart_678689 := by decide
  rcases family_descends (prefixWord ++ tailWord_678689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678692 : List Nat := [2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_678692 : Nat := 118140960795 + 678692 * 2 ^ 59
def prefixEnd_678692 : Nat := 4983230072969 + 3 ^ 40 * 678692 * 2
def baseEnd_678692 : Nat := 103257840699663362408521

theorem tailTrace_678692 : CollatzResearch.WordTrace tailWord_678692 prefixEnd_678692 103257840699663362408521 := by
  unfold tailWord_678692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376965428611135105267165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16502620571481513473689553 12376965428611135105267165)
  ·
    refine ⟨4641362035729175664475187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12376965428611135105267165 4641362035729175664475187)
    ·
      refine ⟨6962043053593763496712781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641362035729175664475187 6962043053593763496712781)
      ·
        refine ⟨2610766145097661311267293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6962043053593763496712781 2610766145097661311267293)
        ·
          refine ⟨979037304411622991725235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2610766145097661311267293 979037304411622991725235)
          ·
            refine ⟨1468555956617434487587853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979037304411622991725235 1468555956617434487587853)
            ·
              refine ⟨550708483731537932845445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1468555956617434487587853 550708483731537932845445)
              ·
                refine ⟨103257840699663362408521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550708483731537932845445 103257840699663362408521)
                ·
                  rfl

theorem cell20_678692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_678692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678692 prefixEnd_678692 := by exact prefixLift 678692
  have htrace : WordTrace (prefixWord ++ tailWord_678692) baseStart_678692 baseEnd_678692 := by
    simpa [prefixWord, tailWord_678692, baseEnd_678692] using wordTrace_append hprefix tailTrace_678692
  have hstable : (prefixWord ++ tailWord_678692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678692).length < 2 ^ (prefixWord ++ tailWord_678692).sum := by decide
  have hdescent : baseEnd_678692 < baseStart_678692 := by decide
  rcases family_descends (prefixWord ++ tailWord_678692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678702 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_678702 : Nat := 118140960795 + 678702 * 2 ^ 59
def prefixEnd_678702 : Nat := 4983230072969 + 3 ^ 40 * 678702 * 2
def baseEnd_678702 : Nat := 309778086371474496892189

theorem tailTrace_678702 : CollatzResearch.WordTrace tailWord_678702 prefixEnd_678702 309778086371474496892189 := by
  unfold tailWord_678702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094286948398255239799795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16502863724790694612265573 3094286948398255239799795)
  ·
    refine ⟨4641430422597382859699693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3094286948398255239799795 4641430422597382859699693)
    ·
      refine ⟨1740536408474018572387385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4641430422597382859699693 1740536408474018572387385)
      ·
        refine ⟨1305402306355513929290539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1740536408474018572387385 1305402306355513929290539)
        ·
          refine ⟨1958103459533270893935809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305402306355513929290539 1958103459533270893935809)
          ·
            refine ⟨1468577594649953170451857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958103459533270893935809 1468577594649953170451857)
            ·
              refine ⟨1101433195987464877838893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468577594649953170451857 1101433195987464877838893)
              ·
                refine ⟨413037448495299329189585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101433195987464877838893 413037448495299329189585)
                ·
                  refine ⟨309778086371474496892189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413037448495299329189585 309778086371474496892189)
                  ·
                    rfl

theorem cell20_678702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_678702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678702 prefixEnd_678702 := by exact prefixLift 678702
  have htrace : WordTrace (prefixWord ++ tailWord_678702) baseStart_678702 baseEnd_678702 := by
    simpa [prefixWord, tailWord_678702, baseEnd_678702] using wordTrace_append hprefix tailTrace_678702
  have hstable : (prefixWord ++ tailWord_678702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678702).length < 2 ^ (prefixWord ++ tailWord_678702).sum := by decide
  have hdescent : baseEnd_678702 < baseStart_678702 := by decide
  rcases family_descends (prefixWord ++ tailWord_678702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678733 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_678733 : Nat := 118140960795 + 678733 * 2 ^ 59
def prefixEnd_678733 : Nat := 4983230072969 + 3 ^ 40 * 678733 * 2
def baseEnd_678733 : Nat := 309792235616176166858729

theorem tailTrace_678733 : CollatzResearch.WordTrace tailWord_678733 prefixEnd_678733 309792235616176166858729 := by
  unfold tailWord_678733
  simp only [CollatzResearch.WordTrace]
  refine ⟨24755426250073734212776853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16503617500049156141851235 24755426250073734212776853)
  ·
    refine ⟨1160410605472206291223915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24755426250073734212776853 1160410605472206291223915)
    ·
      refine ⟨1740615908208309436835873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1160410605472206291223915 1740615908208309436835873)
      ·
        refine ⟨1305461931156232077626905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1740615908208309436835873 1305461931156232077626905)
        ·
          refine ⟨979096448367174058220179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1305461931156232077626905 979096448367174058220179)
          ·
            refine ⟨1468644672550761087330269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979096448367174058220179 1468644672550761087330269)
            ·
              refine ⟨550741752206535407748851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1468644672550761087330269 550741752206535407748851)
              ·
                refine ⟨826112628309803111623277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550741752206535407748851 826112628309803111623277)
                ·
                  refine ⟨309792235616176166858729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826112628309803111623277 309792235616176166858729)
                  ·
                    rfl

theorem cell20_678733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_678733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678733 prefixEnd_678733 := by exact prefixLift 678733
  have htrace : WordTrace (prefixWord ++ tailWord_678733) baseStart_678733 baseEnd_678733 := by
    simpa [prefixWord, tailWord_678733, baseEnd_678733] using wordTrace_append hprefix tailTrace_678733
  have hstable : (prefixWord ++ tailWord_678733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678733).length < 2 ^ (prefixWord ++ tailWord_678733).sum := by decide
  have hdescent : baseEnd_678733 < baseStart_678733 := by decide
  rcases family_descends (prefixWord ++ tailWord_678733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678779 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_678779 : Nat := 118140960795 + 678779 * 2 ^ 59
def prefixEnd_678779 : Nat := 4983230072969 + 3 ^ 40 * 678779 * 2
def baseEnd_678779 : Nat := 309813231269604451325207

theorem tailTrace_678779 : CollatzResearch.WordTrace tailWord_678779 prefixEnd_678779 309813231269604451325207 := by
  unfold tailWord_678779
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757104007907084068951391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16504736005271389379300927 24757104007907084068951391)
  ·
    refine ⟨37135656011860626103427087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24757104007907084068951391 37135656011860626103427087)
    ·
      refine ⟨55703484017790939155140631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37135656011860626103427087 55703484017790939155140631)
      ·
        refine ⟨83555226026686408732710947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55703484017790939155140631 83555226026686408732710947)
        ·
          refine ⟨125332839040029613099066421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83555226026686408732710947 125332839040029613099066421)
          ·
            refine ⟨11749953660002776228037477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125332839040029613099066421 11749953660002776228037477)
            ·
              refine ⟨2203116311250520542757027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11749953660002776228037477 2203116311250520542757027)
              ·
                refine ⟨3304674466875780814135541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203116311250520542757027 3304674466875780814135541)
                ·
                  refine ⟨309813231269604451325207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304674466875780814135541 309813231269604451325207)
                  ·
                    rfl

theorem cell20_678779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_678779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678779 prefixEnd_678779 := by exact prefixLift 678779
  have htrace : WordTrace (prefixWord ++ tailWord_678779) baseStart_678779 baseEnd_678779 := by
    simpa [prefixWord, tailWord_678779, baseEnd_678779] using wordTrace_append hprefix tailTrace_678779
  have hstable : (prefixWord ++ tailWord_678779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678779).length < 2 ^ (prefixWord ++ tailWord_678779).sum := by decide
  have hdescent : baseEnd_678779 < baseStart_678779 := by decide
  rcases family_descends (prefixWord ++ tailWord_678779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678792 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_678792 : Nat := 118140960795 + 678792 * 2 ^ 59
def prefixEnd_678792 : Nat := 4983230072969 + 3 ^ 40 * 678792 * 2
def baseEnd_678792 : Nat := 309819164823834183891821

theorem tailTrace_678792 : CollatzResearch.WordTrace tailWord_678792 prefixEnd_678792 309819164823834183891821 := by
  unfold tailWord_678792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378789078429993644587315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16505052104573324859449753 12378789078429993644587315)
  ·
    refine ⟨18568183617644990466880973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12378789078429993644587315 18568183617644990466880973)
    ·
      refine ⟨6963068856616871425080365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18568183617644990466880973 6963068856616871425080365)
      ·
        refine ⟨2611150821231326784405137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6963068856616871425080365 2611150821231326784405137)
        ·
          refine ⟨1958363115923495088303853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2611150821231326784405137 1958363115923495088303853)
          ·
            refine ⟨734386168471310658113945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1958363115923495088303853 734386168471310658113945)
            ·
              refine ⟨550789626353482993585459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734386168471310658113945 550789626353482993585459)
              ·
                refine ⟨826184439530224490378189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550789626353482993585459 826184439530224490378189)
                ·
                  refine ⟨309819164823834183891821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826184439530224490378189 309819164823834183891821)
                  ·
                    rfl

theorem cell20_678792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_678792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678792 prefixEnd_678792 := by exact prefixLift 678792
  have htrace : WordTrace (prefixWord ++ tailWord_678792) baseStart_678792 baseEnd_678792 := by
    simpa [prefixWord, tailWord_678792, baseEnd_678792] using wordTrace_append hprefix tailTrace_678792
  have hstable : (prefixWord ++ tailWord_678792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678792).length < 2 ^ (prefixWord ++ tailWord_678792).sum := by decide
  have hdescent : baseEnd_678792 < baseStart_678792 := by decide
  rcases family_descends (prefixWord ++ tailWord_678792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678820 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_678820 : Nat := 118140960795 + 678820 * 2 ^ 59
def prefixEnd_678820 : Nat := 4983230072969 + 3 ^ 40 * 678820 * 2
def baseEnd_678820 : Nat := 309831944786790530958373

theorem tailTrace_678820 : CollatzResearch.WordTrace tailWord_678820 prefixEnd_678820 309831944786790530958373 := by
  unfold tailWord_678820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379299700379274035596957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16505732933839032047462609 12379299700379274035596957)
  ·
    refine ⟨4642237387642227763348859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12379299700379274035596957 4642237387642227763348859)
    ·
      refine ⟨6963356081463341645023289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4642237387642227763348859 6963356081463341645023289)
      ·
        refine ⟨5222517061097506233767467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6963356081463341645023289 5222517061097506233767467)
        ·
          refine ⟨7833775591646259350651201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222517061097506233767467 7833775591646259350651201)
          ·
            refine ⟨5875331693734694512988401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833775591646259350651201 5875331693734694512988401)
            ·
              refine ⟨4406498770301020884741301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875331693734694512988401 4406498770301020884741301)
              ·
                refine ⟨413109259715720707944497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4406498770301020884741301 413109259715720707944497)
                ·
                  refine ⟨309831944786790530958373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413109259715720707944497 309831944786790530958373)
                  ·
                    rfl

theorem cell20_678820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_678820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678820 prefixEnd_678820 := by exact prefixLift 678820
  have htrace : WordTrace (prefixWord ++ tailWord_678820) baseStart_678820 baseEnd_678820 := by
    simpa [prefixWord, tailWord_678820, baseEnd_678820] using wordTrace_append hprefix tailTrace_678820
  have hstable : (prefixWord ++ tailWord_678820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678820).length < 2 ^ (prefixWord ++ tailWord_678820).sum := by decide
  have hdescent : baseEnd_678820 < baseStart_678820 := by decide
  rcases family_descends (prefixWord ++ tailWord_678820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678833 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 2]
def baseStart_678833 : Nat := 118140960795 + 678833 * 2 ^ 59
def prefixEnd_678833 : Nat := 4983230072969 + 3 ^ 40 * 678833 * 2
def baseEnd_678833 : Nat := 309837878341020263524987

theorem tailTrace_678833 : CollatzResearch.WordTrace tailWord_678833 prefixEnd_678833 309837878341020263524987 := by
  unfold tailWord_678833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24759073549711451291417153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16506049033140967527611435 24759073549711451291417153)
  ·
    refine ⟨18569305162283588468562865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24759073549711451291417153 18569305162283588468562865)
    ·
      refine ⟨13926978871712691351422149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18569305162283588468562865 13926978871712691351422149)
      ·
        refine ⟨2611308538446129628391653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13926978871712691351422149 2611308538446129628391653)
        ·
          refine ⟨489620350958649305323435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2611308538446129628391653 489620350958649305323435)
          ·
            refine ⟨734430526437973957985153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489620350958649305323435 734430526437973957985153)
            ·
              refine ⟨550822894828480468488865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734430526437973957985153 550822894828480468488865)
              ·
                refine ⟨413117171121360351366649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550822894828480468488865 413117171121360351366649)
                ·
                  refine ⟨309837878341020263524987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413117171121360351366649 309837878341020263524987)
                  ·
                    rfl

theorem cell20_678833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_678833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678833 prefixEnd_678833 := by exact prefixLift 678833
  have htrace : WordTrace (prefixWord ++ tailWord_678833) baseStart_678833 baseEnd_678833 := by
    simpa [prefixWord, tailWord_678833, baseEnd_678833] using wordTrace_append hprefix tailTrace_678833
  have hstable : (prefixWord ++ tailWord_678833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678833).length < 2 ^ (prefixWord ++ tailWord_678833).sum := by decide
  have hdescent : baseEnd_678833 < baseStart_678833 := by decide
  rcases family_descends (prefixWord ++ tailWord_678833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678848 : List Nat := [2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_678848 : Nat := 118140960795 + 678848 * 2 ^ 59
def prefixEnd_678848 : Nat := 4983230072969 + 3 ^ 40 * 678848 * 2
def baseEnd_678848 : Nat := 103281574916582292674975

theorem tailTrace_678848 : CollatzResearch.WordTrace tailWord_678848 prefixEnd_678848 103281574916582292674975 := by
  unfold tailWord_678848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379810322328554426606599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16506413763104739235475465 12379810322328554426606599)
  ·
    refine ⟨18569715483492831639909899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12379810322328554426606599 18569715483492831639909899)
    ·
      refine ⟨27854573225239247459864849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569715483492831639909899 27854573225239247459864849)
      ·
        refine ⟨20890929918929435594898637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27854573225239247459864849 20890929918929435594898637)
        ·
          refine ⟨7834098719598538348086989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20890929918929435594898637 7834098719598538348086989)
          ·
            refine ⟨2937787019849451880532621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7834098719598538348086989 2937787019849451880532621)
            ·
              refine ⟨1101670132443544455199733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2937787019849451880532621 1101670132443544455199733)
              ·
                refine ⟨103281574916582292674975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1101670132443544455199733 103281574916582292674975)
                ·
                  rfl

theorem cell20_678848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_678848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678848 prefixEnd_678848 := by exact prefixLift 678848
  have htrace : WordTrace (prefixWord ++ tailWord_678848) baseStart_678848 baseEnd_678848 := by
    simpa [prefixWord, tailWord_678848, baseEnd_678848] using wordTrace_append hprefix tailTrace_678848
  have hstable : (prefixWord ++ tailWord_678848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678848).length < 2 ^ (prefixWord ++ tailWord_678848).sum := by decide
  have hdescent : baseEnd_678848 < baseStart_678848 := by decide
  rcases family_descends (prefixWord ++ tailWord_678848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678885 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 3]
def baseStart_678885 : Nat := 118140960795 + 678885 * 2 ^ 59
def prefixEnd_678885 : Nat := 4983230072969 + 3 ^ 40 * 678885 * 2
def baseEnd_678885 : Nat := 309861612557939193791441

theorem tailTrace_678885 : CollatzResearch.WordTrace tailWord_678885 prefixEnd_678885 309861612557939193791441 := by
  unfold tailWord_678885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24760970145523064172310109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16507313430348709448206739 24760970145523064172310109)
  ·
    refine ⟨9285363804571149064616291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24760970145523064172310109 9285363804571149064616291)
    ·
      refine ⟨13928045706856723596924437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285363804571149064616291 13928045706856723596924437)
      ·
        refine ⟨652877142508908918605833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13928045706856723596924437 652877142508908918605833)
        ·
          refine ⟨489657856881681688954375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652877142508908918605833 489657856881681688954375)
          ·
            refine ⟨734486785322522533431563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489657856881681688954375 734486785322522533431563)
            ·
              refine ⟨1101730177983783800147345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734486785322522533431563 1101730177983783800147345)
              ·
                refine ⟨826297633487837850110509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101730177983783800147345 826297633487837850110509)
                ·
                  refine ⟨309861612557939193791441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826297633487837850110509 309861612557939193791441)
                  ·
                    rfl

theorem cell20_678885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_678885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678885 prefixEnd_678885 := by exact prefixLift 678885
  have htrace : WordTrace (prefixWord ++ tailWord_678885) baseStart_678885 baseEnd_678885 := by
    simpa [prefixWord, tailWord_678885, baseEnd_678885] using wordTrace_append hprefix tailTrace_678885
  have hstable : (prefixWord ++ tailWord_678885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678885).length < 2 ^ (prefixWord ++ tailWord_678885).sum := by decide
  have hdescent : baseEnd_678885 < baseStart_678885 := by decide
  rcases family_descends (prefixWord ++ tailWord_678885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678907 : List Nat := [1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_678907 : Nat := 118140960795 + 678907 * 2 ^ 59
def prefixEnd_678907 : Nat := 4983230072969 + 3 ^ 40 * 678907 * 2
def baseEnd_678907 : Nat := 103290551319134965019339

theorem tailTrace_678907 : CollatzResearch.WordTrace tailWord_678907 prefixEnd_678907 103290551319134965019339 := by
  unfold tailWord_678907
  simp only [CollatzResearch.WordTrace]
  refine ⟨24761772551443361929610975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16507848367628907953073983 24761772551443361929610975)
  ·
    refine ⟨37142658827165042894416463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24761772551443361929610975 37142658827165042894416463)
    ·
      refine ⟨55713988240747564341624695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37142658827165042894416463 55713988240747564341624695)
      ·
        refine ⟨83570982361121346512437043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55713988240747564341624695 83570982361121346512437043)
        ·
          refine ⟨125356473541682019768655565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83570982361121346512437043 125356473541682019768655565)
          ·
            refine ⟨47008677578130757413245837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125356473541682019768655565 47008677578130757413245837)
            ·
              refine ⟨17628254091799034029967189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47008677578130757413245837 17628254091799034029967189)
              ·
                refine ⟨103290551319134965019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17628254091799034029967189 103290551319134965019339)
                ·
                  rfl

theorem cell20_678907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_678907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678907 prefixEnd_678907 := by exact prefixLift 678907
  have htrace : WordTrace (prefixWord ++ tailWord_678907) baseStart_678907 baseEnd_678907 := by
    simpa [prefixWord, tailWord_678907, baseEnd_678907] using wordTrace_append hprefix tailTrace_678907
  have hstable : (prefixWord ++ tailWord_678907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678907).length < 2 ^ (prefixWord ++ tailWord_678907).sum := by decide
  have hdescent : baseEnd_678907 < baseStart_678907 := by decide
  rcases family_descends (prefixWord ++ tailWord_678907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678924 : List Nat := [2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_678924 : Nat := 118140960795 + 678924 * 2 ^ 59
def prefixEnd_678924 : Nat := 4983230072969 + 3 ^ 40 * 678924 * 2
def baseEnd_678924 : Nat := 103293137740209463830427

theorem tailTrace_678924 : CollatzResearch.WordTrace tailWord_678924 prefixEnd_678924 103293137740209463830427 := by
  unfold tailWord_678924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381196296190886916489913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16508261728254515888653217 12381196296190886916489913)
  ·
    refine ⟨9285897222143165187367435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12381196296190886916489913 9285897222143165187367435)
    ·
      refine ⟨13928845833214747781051153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285897222143165187367435 13928845833214747781051153)
      ·
        refine ⟨10446634374911060835788365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13928845833214747781051153 10446634374911060835788365)
        ·
          refine ⟨3917487890591647813420637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10446634374911060835788365 3917487890591647813420637)
          ·
            refine ⟨1469057958971867930032739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3917487890591647813420637 1469057958971867930032739)
            ·
              refine ⟨2203586938457801895049109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469057958971867930032739 2203586938457801895049109)
              ·
                refine ⟨103293137740209463830427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203586938457801895049109 103293137740209463830427)
                ·
                  rfl

theorem cell20_678924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_678924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678924 prefixEnd_678924 := by exact prefixLift 678924
  have htrace : WordTrace (prefixWord ++ tailWord_678924) baseStart_678924 baseEnd_678924 := by
    simpa [prefixWord, tailWord_678924, baseEnd_678924] using wordTrace_append hprefix tailTrace_678924
  have hstable : (prefixWord ++ tailWord_678924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678924).length < 2 ^ (prefixWord ++ tailWord_678924).sum := by decide
  have hdescent : baseEnd_678924 < baseStart_678924 := by decide
  rcases family_descends (prefixWord ++ tailWord_678924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678941 : List Nat := [1, 4, 2, 2, 3, 2, 6]
def baseStart_678941 : Nat := 118140960795 + 678941 * 2 ^ 59
def prefixEnd_678941 : Nat := 4983230072969 + 3 ^ 40 * 678941 * 2
def baseEnd_678941 : Nat := 34431908053761320880505

theorem tailTrace_678941 : CollatzResearch.WordTrace tailWord_678941 prefixEnd_678941 34431908053761320880505 := by
  unfold tailWord_678941
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763012633320185736348677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16508675088880123824232451 24763012633320185736348677)
  ·
    refine ⟨4643064868747534825565377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24763012633320185736348677 4643064868747534825565377)
    ·
      refine ⟨3482298651560651119174033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4643064868747534825565377 3482298651560651119174033)
      ·
        refine ⟨2611723988670488339380525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3482298651560651119174033 2611723988670488339380525)
        ·
          refine ⟨979396495751433127267697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2611723988670488339380525 979396495751433127267697)
          ·
            refine ⟨734547371813574845450773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979396495751433127267697 734547371813574845450773)
            ·
              refine ⟨34431908053761320880505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 734547371813574845450773 34431908053761320880505)
              ·
                rfl

theorem cell20_678941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_678941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678941 prefixEnd_678941 := by exact prefixLift 678941
  have htrace : WordTrace (prefixWord ++ tailWord_678941) baseStart_678941 baseEnd_678941 := by
    simpa [prefixWord, tailWord_678941, baseEnd_678941] using wordTrace_append hprefix tailTrace_678941
  have hstable : (prefixWord ++ tailWord_678941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678941).length < 2 ^ (prefixWord ++ tailWord_678941).sum := by decide
  have hdescent : baseEnd_678941 < baseStart_678941 := by decide
  rcases family_descends (prefixWord ++ tailWord_678941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678948 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_678948 : Nat := 118140960795 + 678948 * 2 ^ 59
def prefixEnd_678948 : Nat := 4983230072969 + 3 ^ 40 * 678948 * 2
def baseEnd_678948 : Nat := 309890367474590974691183

theorem tailTrace_678948 : CollatzResearch.WordTrace tailWord_678948 prefixEnd_678948 309890367474590974691183 := by
  unfold tailWord_678948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381633972147412965926749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16508845296196550621235665 12381633972147412965926749)
  ·
    refine ⟨4643112739555279862222531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12381633972147412965926749 4643112739555279862222531)
    ·
      refine ⟨6964669109332919793333797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643112739555279862222531 6964669109332919793333797)
      ·
        refine ⟨1305875457999922461250087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6964669109332919793333797 1305875457999922461250087)
        ·
          refine ⟨1958813186999883691875131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305875457999922461250087 1958813186999883691875131)
          ·
            refine ⟨2938219780499825537812697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958813186999883691875131 2938219780499825537812697)
            ·
              refine ⟨2203664835374869153359523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938219780499825537812697 2203664835374869153359523)
              ·
                refine ⟨3305497253062303730039285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203664835374869153359523 3305497253062303730039285)
                ·
                  refine ⟨309890367474590974691183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3305497253062303730039285 309890367474590974691183)
                  ·
                    rfl

theorem cell20_678948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_678948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678948 prefixEnd_678948 := by exact prefixLift 678948
  have htrace : WordTrace (prefixWord ++ tailWord_678948) baseStart_678948 baseEnd_678948 := by
    simpa [prefixWord, tailWord_678948, baseEnd_678948] using wordTrace_append hprefix tailTrace_678948
  have hstable : (prefixWord ++ tailWord_678948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678948).length < 2 ^ (prefixWord ++ tailWord_678948).sum := by decide
  have hdescent : baseEnd_678948 < baseStart_678948 := by decide
  rcases family_descends (prefixWord ++ tailWord_678948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678951 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_678951 : Nat := 118140960795 + 678951 * 2 ^ 59
def prefixEnd_678951 : Nat := 4983230072969 + 3 ^ 40 * 678951 * 2
def baseEnd_678951 : Nat := 309891736756336297591171

theorem tailTrace_678951 : CollatzResearch.WordTrace tailWord_678951 prefixEnd_678951 309891736756336297591171 := by
  unfold tailWord_678951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763377363283957444212707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16508918242189304962808471 24763377363283957444212707)
  ·
    refine ⟨37145066044925936166319061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24763377363283957444212707 37145066044925936166319061)
    ·
      refine ⟨870587485427951628898103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37145066044925936166319061 870587485427951628898103)
      ·
        refine ⟨1305881228141927443347155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870587485427951628898103 1305881228141927443347155)
        ·
          refine ⟨1958821842212891165020733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305881228141927443347155 1958821842212891165020733)
          ·
            refine ⟨734558190829834186882775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1958821842212891165020733 734558190829834186882775)
            ·
              refine ⟨1101837286244751280324163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734558190829834186882775 1101837286244751280324163)
              ·
                refine ⟨1652755929367126920486245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101837286244751280324163 1652755929367126920486245)
                ·
                  refine ⟨309891736756336297591171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652755929367126920486245 309891736756336297591171)
                  ·
                    rfl

theorem cell20_678951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_678951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678951 prefixEnd_678951 := by exact prefixLift 678951
  have htrace : WordTrace (prefixWord ++ tailWord_678951) baseStart_678951 baseEnd_678951 := by
    simpa [prefixWord, tailWord_678951, baseEnd_678951] using wordTrace_append hprefix tailTrace_678951
  have hstable : (prefixWord ++ tailWord_678951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678951).length < 2 ^ (prefixWord ++ tailWord_678951).sum := by decide
  have hdescent : baseEnd_678951 < baseStart_678951 := by decide
  rcases family_descends (prefixWord ++ tailWord_678951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678962 : List Nat := [3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_678962 : Nat := 118140960795 + 678962 * 2 ^ 59
def prefixEnd_678962 : Nat := 4983230072969 + 3 ^ 40 * 678962 * 2
def baseEnd_678962 : Nat := 103298919152023049408153

theorem tailTrace_678962 : CollatzResearch.WordTrace tailWord_678962 prefixEnd_678962 103298919152023049408153 := by
  unfold tailWord_678962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6190944641561026580715785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16509185710829404215242093 6190944641561026580715785)
  ·
    refine ⟨4643208481170769935536839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6190944641561026580715785 4643208481170769935536839)
    ·
      refine ⟨6964812721756154903305259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643208481170769935536839 6964812721756154903305259)
      ·
        refine ⟨10447219082634232354957889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964812721756154903305259 10447219082634232354957889)
        ·
          refine ⟨7835414311975674266218417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447219082634232354957889 7835414311975674266218417)
          ·
            refine ⟨5876560733981755699663813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835414311975674266218417 5876560733981755699663813)
            ·
              refine ⟨1101855137621579193686965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5876560733981755699663813 1101855137621579193686965)
              ·
                refine ⟨103298919152023049408153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1101855137621579193686965 103298919152023049408153)
                ·
                  rfl

theorem cell20_678962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_678962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678962 prefixEnd_678962 := by exact prefixLift 678962
  have htrace : WordTrace (prefixWord ++ tailWord_678962) baseStart_678962 baseEnd_678962 := by
    simpa [prefixWord, tailWord_678962, baseEnd_678962] using wordTrace_append hprefix tailTrace_678962
  have hstable : (prefixWord ++ tailWord_678962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678962).length < 2 ^ (prefixWord ++ tailWord_678962).sum := by decide
  have hdescent : baseEnd_678962 < baseStart_678962 := by decide
  rcases family_descends (prefixWord ++ tailWord_678962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678976 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_678976 : Nat := 118140960795 + 678976 * 2 ^ 59
def prefixEnd_678976 : Nat := 4983230072969 + 3 ^ 40 * 678976 * 2
def baseEnd_678976 : Nat := 309903147437547321757735

theorem tailTrace_678976 : CollatzResearch.WordTrace tailWord_678976 prefixEnd_678976 309903147437547321757735 := by
  unfold tailWord_678976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12382144594096693356936391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16509526125462257809248521 12382144594096693356936391)
  ·
    refine ⟨18573216891145040035404587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12382144594096693356936391 18573216891145040035404587)
    ·
      refine ⟨27859825336717560053106881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18573216891145040035404587 27859825336717560053106881)
      ·
        refine ⟨20894869002538170039830161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27859825336717560053106881 20894869002538170039830161)
        ·
          refine ⟨15671151751903627529872621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20894869002538170039830161 15671151751903627529872621)
          ·
            refine ⟨5876681906963860323702233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15671151751903627529872621 5876681906963860323702233)
            ·
              refine ⟨4407511430222895242776675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876681906963860323702233 4407511430222895242776675)
              ·
                refine ⟨6611267145334342864165013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407511430222895242776675 6611267145334342864165013)
                ·
                  refine ⟨309903147437547321757735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6611267145334342864165013 309903147437547321757735)
                  ·
                    rfl

theorem cell20_678976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_678976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_678976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_678976 prefixEnd_678976 := by exact prefixLift 678976
  have htrace : WordTrace (prefixWord ++ tailWord_678976) baseStart_678976 baseEnd_678976 := by
    simpa [prefixWord, tailWord_678976, baseEnd_678976] using wordTrace_append hprefix tailTrace_678976
  have hstable : (prefixWord ++ tailWord_678976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678976).length < 2 ^ (prefixWord ++ tailWord_678976).sum := by decide
  have hdescent : baseEnd_678976 < baseStart_678976 := by decide
  rcases family_descends (prefixWord ++ tailWord_678976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679069 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_679069 : Nat := 118140960795 + 679069 * 2 ^ 59
def prefixEnd_679069 : Nat := 4983230072969 + 3 ^ 40 * 679069 * 2
def baseEnd_679069 : Nat := 309945595171652331657355

theorem tailTrace_679069 : CollatzResearch.WordTrace tailWord_679069 prefixEnd_679069 309945595171652331657355 := by
  unfold tailWord_679069
  simp only [CollatzResearch.WordTrace]
  refine ⟨24767681176856463597008261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16511787451237642398005507 24767681176856463597008261)
  ·
    refine ⟨4643940220660586924439049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24767681176856463597008261 4643940220660586924439049)
    ·
      refine ⟨3482955165495440193329287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4643940220660586924439049 3482955165495440193329287)
      ·
        refine ⟨5224432748243160289993931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3482955165495440193329287 5224432748243160289993931)
        ·
          refine ⟨7836649122364740434990897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224432748243160289993931 7836649122364740434990897)
          ·
            refine ⟨5877486841773555326243173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7836649122364740434990897 5877486841773555326243173)
            ·
              refine ⟨1102028782832541623670595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5877486841773555326243173 1102028782832541623670595)
              ·
                refine ⟨1653043174248812435505893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102028782832541623670595 1653043174248812435505893)
                ·
                  refine ⟨309945595171652331657355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653043174248812435505893 309945595171652331657355)
                  ·
                    rfl

theorem cell20_679069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_679069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679069 prefixEnd_679069 := by exact prefixLift 679069
  have htrace : WordTrace (prefixWord ++ tailWord_679069) baseStart_679069 baseEnd_679069 := by
    simpa [prefixWord, tailWord_679069, baseEnd_679069] using wordTrace_append hprefix tailTrace_679069
  have hstable : (prefixWord ++ tailWord_679069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679069).length < 2 ^ (prefixWord ++ tailWord_679069).sum := by decide
  have hdescent : baseEnd_679069 < baseStart_679069 := by decide
  rcases family_descends (prefixWord ++ tailWord_679069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 2]
def baseStart_679107 : Nat := 118140960795 + 679107 * 2 ^ 59
def prefixEnd_679107 : Nat := 4983230072969 + 3 ^ 40 * 679107 * 2
def baseEnd_679107 : Nat := 309962939407093088390533

theorem tailTrace_679107 : CollatzResearch.WordTrace tailWord_679107 prefixEnd_679107 309962939407093088390533 := by
  unfold tailWord_679107
  simp only [CollatzResearch.WordTrace]
  refine ⟨24769067150718796086891575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16512711433812530724594383 24769067150718796086891575)
  ·
    refine ⟨37153600726078194130337363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24769067150718796086891575 37153600726078194130337363)
    ·
      refine ⟨55730401089117291195506045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37153600726078194130337363 55730401089117291195506045)
      ·
        refine ⟨20898900408418984198314767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55730401089117291195506045 20898900408418984198314767)
        ·
          refine ⟨31348350612628476297472151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20898900408418984198314767 31348350612628476297472151)
          ·
            refine ⟨47022525918942714446208227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31348350612628476297472151 47022525918942714446208227)
            ·
              refine ⟨70533788878414071669312341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47022525918942714446208227 70533788878414071669312341)
              ·
                refine ⟨413283919209457451187377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 70533788878414071669312341 413283919209457451187377)
                ·
                  refine ⟨309962939407093088390533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413283919209457451187377 309962939407093088390533)
                  ·
                    rfl

theorem cell20_679107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 2].length) (baseStart_679107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679107 prefixEnd_679107 := by exact prefixLift 679107
  have htrace : WordTrace (prefixWord ++ tailWord_679107) baseStart_679107 baseEnd_679107 := by
    simpa [prefixWord, tailWord_679107, baseEnd_679107] using wordTrace_append hprefix tailTrace_679107
  have hstable : (prefixWord ++ tailWord_679107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679107).length < 2 ^ (prefixWord ++ tailWord_679107).sum := by decide
  have hdescent : baseEnd_679107 < baseStart_679107 := by decide
  rcases family_descends (prefixWord ++ tailWord_679107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679114 : List Nat := [3, 1, 2, 1, 3, 4, 6]
def baseStart_679114 : Nat := 118140960795 + 679114 * 2 ^ 59
def prefixEnd_679114 : Nat := 4983230072969 + 3 ^ 40 * 679114 * 2
def baseEnd_679114 : Nat := 34440681599759130573019

theorem tailTrace_679114 : CollatzResearch.WordTrace tailWord_679114 prefixEnd_679114 34440681599759130573019 := by
  unfold tailWord_679114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192330615423359070599099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16512881641128957521597597 6192330615423359070599099)
  ·
    refine ⟨9288495923135038605898649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6192330615423359070599099 9288495923135038605898649)
    ·
      refine ⟨6966371942351278954423987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9288495923135038605898649 6966371942351278954423987)
      ·
        refine ⟨10449557913526918431635981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6966371942351278954423987 10449557913526918431635981)
        ·
          refine ⟨3918584217572594411863493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10449557913526918431635981 3918584217572594411863493)
          ·
            refine ⟨734734540794861452224405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3918584217572594411863493 734734540794861452224405)
            ·
              refine ⟨34440681599759130573019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 734734540794861452224405 34440681599759130573019)
              ·
                rfl

theorem cell20_679114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_679114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679114 prefixEnd_679114 := by exact prefixLift 679114
  have htrace : WordTrace (prefixWord ++ tailWord_679114) baseStart_679114 baseEnd_679114 := by
    simpa [prefixWord, tailWord_679114, baseEnd_679114] using wordTrace_append hprefix tailTrace_679114
  have hstable : (prefixWord ++ tailWord_679114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679114).length < 2 ^ (prefixWord ++ tailWord_679114).sum := by decide
  have hdescent : baseEnd_679114 < baseStart_679114 := by decide
  rcases family_descends (prefixWord ++ tailWord_679114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679121 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_679121 : Nat := 118140960795 + 679121 * 2 ^ 59
def prefixEnd_679121 : Nat := 4983230072969 + 3 ^ 40 * 679121 * 2
def baseEnd_679121 : Nat := 309969329388571261923809

theorem tailTrace_679121 : CollatzResearch.WordTrace tailWord_679121 prefixEnd_679121 309969329388571261923809 := by
  unfold tailWord_679121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24769577772668076477901217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16513051848445384318600811 24769577772668076477901217)
  ·
    refine ⟨18577183329501057358425913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24769577772668076477901217 18577183329501057358425913)
    ·
      refine ⟨13932887497125793018819435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18577183329501057358425913 13932887497125793018819435)
      ·
        refine ⟨20899331245688689528229153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13932887497125793018819435 20899331245688689528229153)
        ·
          refine ⟨15674498434266517146171865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20899331245688689528229153 15674498434266517146171865)
          ·
            refine ⟨11755873825699887859628899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15674498434266517146171865 11755873825699887859628899)
            ·
              refine ⟨17633810738549831789443349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755873825699887859628899 17633810738549831789443349)
              ·
                refine ⟨826584878369523365130157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17633810738549831789443349 826584878369523365130157)
                ·
                  refine ⟨309969329388571261923809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826584878369523365130157 309969329388571261923809)
                  ·
                    rfl

theorem cell20_679121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_679121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679121 prefixEnd_679121 := by exact prefixLift 679121
  have htrace : WordTrace (prefixWord ++ tailWord_679121) baseStart_679121 baseEnd_679121 := by
    simpa [prefixWord, tailWord_679121, baseEnd_679121] using wordTrace_append hprefix tailTrace_679121
  have hstable : (prefixWord ++ tailWord_679121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679121).length < 2 ^ (prefixWord ++ tailWord_679121).sum := by decide
  have hdescent : baseEnd_679121 < baseStart_679121 := by decide
  rcases family_descends (prefixWord ++ tailWord_679121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679135 : List Nat := [1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_679135 : Nat := 118140960795 + 679135 * 2 ^ 59
def prefixEnd_679135 : Nat := 4983230072969 + 3 ^ 40 * 679135 * 2
def baseEnd_679135 : Nat := 103325239790016478485695

theorem tailTrace_679135 : CollatzResearch.WordTrace tailWord_679135 prefixEnd_679135 103325239790016478485695 := by
  unfold tailWord_679135
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770088394617356868910859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16513392263078237912607239 24770088394617356868910859)
  ·
    refine ⟨37155132591926035303366289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24770088394617356868910859 37155132591926035303366289)
    ·
      refine ⟨27866349443944526477524717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37155132591926035303366289 27866349443944526477524717)
      ·
        refine ⟨10449881041479197429071769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27866349443944526477524717 10449881041479197429071769)
        ·
          refine ⟨7837410781109398071803827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10449881041479197429071769 7837410781109398071803827)
          ·
            refine ⟨11756116171664097107705741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837410781109398071803827 11756116171664097107705741)
            ·
              refine ⟨4408543564374036415389653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11756116171664097107705741 4408543564374036415389653)
              ·
                refine ⟨103325239790016478485695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4408543564374036415389653 103325239790016478485695)
                ·
                  rfl

theorem cell20_679135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_679135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679135 prefixEnd_679135 := by exact prefixLift 679135
  have htrace : WordTrace (prefixWord ++ tailWord_679135) baseStart_679135 baseEnd_679135 := by
    simpa [prefixWord, tailWord_679135, baseEnd_679135] using wordTrace_append hprefix tailTrace_679135
  have hstable : (prefixWord ++ tailWord_679135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679135).length < 2 ^ (prefixWord ++ tailWord_679135).sum := by decide
  have hdescent : baseEnd_679135 < baseStart_679135 := by decide
  rcases family_descends (prefixWord ++ tailWord_679135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679179 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 2]
def baseStart_679179 : Nat := 118140960795 + 679179 * 2 ^ 59
def prefixEnd_679179 : Nat := 4983230072969 + 3 ^ 40 * 679179 * 2
def baseEnd_679179 : Nat := 309995802168980837990239

theorem tailTrace_679179 : CollatzResearch.WordTrace tailWord_679179 prefixEnd_679179 309995802168980837990239 := by
  unfold tailWord_679179
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771693206457952383512591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16514462137638634922341727 24771693206457952383512591)
  ·
    refine ⟨37157539809686928575268887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24771693206457952383512591 37157539809686928575268887)
    ·
      refine ⟨55736309714530392862903331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37157539809686928575268887 55736309714530392862903331)
      ·
        refine ⟨83604464571795589294354997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55736309714530392862903331 83604464571795589294354997)
        ·
          refine ⟨7837918553605836496345781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83604464571795589294354997 7837918553605836496345781)
          ·
            refine ⟨734804864400547171532417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7837918553605836496345781 734804864400547171532417)
            ·
              refine ⟨551103648300410378649313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734804864400547171532417 551103648300410378649313)
              ·
                refine ⟨413327736225307783986985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551103648300410378649313 413327736225307783986985)
                ·
                  refine ⟨309995802168980837990239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413327736225307783986985 309995802168980837990239)
                  ·
                    rfl

theorem cell20_679179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2].length) (baseStart_679179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679179 prefixEnd_679179 := by exact prefixLift 679179
  have htrace : WordTrace (prefixWord ++ tailWord_679179) baseStart_679179 baseEnd_679179 := by
    simpa [prefixWord, tailWord_679179, baseEnd_679179] using wordTrace_append hprefix tailTrace_679179
  have hstable : (prefixWord ++ tailWord_679179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679179).length < 2 ^ (prefixWord ++ tailWord_679179).sum := by decide
  have hdescent : baseEnd_679179 < baseStart_679179 := by decide
  rcases family_descends (prefixWord ++ tailWord_679179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679249 : List Nat := [1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_679249 : Nat := 118140960795 + 679249 * 2 ^ 59
def prefixEnd_679249 : Nat := 4983230072969 + 3 ^ 40 * 679249 * 2
def baseEnd_679249 : Nat := 103342584025457235218873

theorem tailTrace_679249 : CollatzResearch.WordTrace tailWord_679249 prefixEnd_679249 103342584025457235218873 := by
  unfold tailWord_679249
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774246316204354338560801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16516164210802902892373867 24774246316204354338560801)
  ·
    refine ⟨18580684737153265753920601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24774246316204354338560801 18580684737153265753920601)
    ·
      refine ⟨13935513552864949315440451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18580684737153265753920601 13935513552864949315440451)
      ·
        refine ⟨20903270329297423973160677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935513552864949315440451 20903270329297423973160677)
        ·
          refine ⟨3919363186743266994967627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20903270329297423973160677 3919363186743266994967627)
          ·
            refine ⟨5879044780114900492451441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919363186743266994967627 5879044780114900492451441)
            ·
              refine ⟨4409283585086175369338581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879044780114900492451441 4409283585086175369338581)
              ·
                refine ⟨103342584025457235218873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4409283585086175369338581 103342584025457235218873)
                ·
                  rfl

theorem cell20_679249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_679249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679249 prefixEnd_679249 := by exact prefixLift 679249
  have htrace : WordTrace (prefixWord ++ tailWord_679249) baseStart_679249 baseEnd_679249 := by
    simpa [prefixWord, tailWord_679249, baseEnd_679249] using wordTrace_append hprefix tailTrace_679249
  have hstable : (prefixWord ++ tailWord_679249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679249).length < 2 ^ (prefixWord ++ tailWord_679249).sum := by decide
  have hdescent : baseEnd_679249 < baseStart_679249 := by decide
  rcases family_descends (prefixWord ++ tailWord_679249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679266 : List Nat := [3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_679266 : Nat := 118140960795 + 679266 * 2 ^ 59
def prefixEnd_679266 : Nat := 4983230072969 + 3 ^ 40 * 679266 * 2
def baseEnd_679266 : Nat := 103345170446531734029961

theorem tailTrace_679266 : CollatzResearch.WordTrace tailWord_679266 prefixEnd_679266 103345170446531734029961 := by
  unfold tailWord_679266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193716589285691560482413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16516577571428510827953101 6193716589285691560482413)
  ·
    refine ⟨2322643720982134335180905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6193716589285691560482413 2322643720982134335180905)
    ·
      refine ⟨1741982790736600751385679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2322643720982134335180905 1741982790736600751385679)
      ·
        refine ⟨2612974186104901127078519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741982790736600751385679 2612974186104901127078519)
        ·
          refine ⟨3919461279157351690617779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612974186104901127078519 3919461279157351690617779)
          ·
            refine ⟨5879191918736027535926669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919461279157351690617779 5879191918736027535926669)
            ·
              refine ⟨2204696969526010325972501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5879191918736027535926669 2204696969526010325972501)
              ·
                refine ⟨103345170446531734029961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2204696969526010325972501 103345170446531734029961)
                ·
                  rfl

theorem cell20_679266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_679266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679266 prefixEnd_679266 := by exact prefixLift 679266
  have htrace : WordTrace (prefixWord ++ tailWord_679266) baseStart_679266 baseEnd_679266 := by
    simpa [prefixWord, tailWord_679266, baseEnd_679266] using wordTrace_append hprefix tailTrace_679266
  have hstable : (prefixWord ++ tailWord_679266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679266).length < 2 ^ (prefixWord ++ tailWord_679266).sum := by decide
  have hdescent : baseEnd_679266 < baseStart_679266 := by decide
  rcases family_descends (prefixWord ++ tailWord_679266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679272 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_679272 : Nat := 118140960795 + 679272 * 2 ^ 59
def prefixEnd_679272 : Nat := 4983230072969 + 3 ^ 40 * 679272 * 2
def baseEnd_679272 : Nat := 310038249903085847889859

theorem tailTrace_679272 : CollatzResearch.WordTrace tailWord_679272 prefixEnd_679272 310038249903085847889859 := by
  unfold tailWord_679272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387542597560514633324035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16516723463414019511098713 12387542597560514633324035)
  ·
    refine ⟨18581313896340771949986053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387542597560514633324035 18581313896340771949986053)
    ·
      refine ⟨3483996355563894740622385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18581313896340771949986053 3483996355563894740622385)
      ·
        refine ⟨2612997266672921055466789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483996355563894740622385 2612997266672921055466789)
        ·
          refine ⟨489936987501172697900023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2612997266672921055466789 489936987501172697900023)
          ·
            refine ⟨734905481251759046850035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489936987501172697900023 734905481251759046850035)
            ·
              refine ⟨1102358221877638570275053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734905481251759046850035 1102358221877638570275053)
              ·
                refine ⟨413384333204114463853145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1102358221877638570275053 413384333204114463853145)
                ·
                  refine ⟨310038249903085847889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413384333204114463853145 310038249903085847889859)
                  ·
                    rfl

theorem cell20_679272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_679272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679272 prefixEnd_679272 := by exact prefixLift 679272
  have htrace : WordTrace (prefixWord ++ tailWord_679272) baseStart_679272 baseEnd_679272 := by
    simpa [prefixWord, tailWord_679272, baseEnd_679272] using wordTrace_append hprefix tailTrace_679272
  have hstable : (prefixWord ++ tailWord_679272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679272).length < 2 ^ (prefixWord ++ tailWord_679272).sum := by decide
  have hdescent : baseEnd_679272 < baseStart_679272 := by decide
  rcases family_descends (prefixWord ++ tailWord_679272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679276 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 2]
def baseStart_679276 : Nat := 118140960795 + 679276 * 2 ^ 59
def prefixEnd_679276 : Nat := 4983230072969 + 3 ^ 40 * 679276 * 2
def baseEnd_679276 : Nat := 310040075612079611756509

theorem tailTrace_679276 : CollatzResearch.WordTrace tailWord_679276 prefixEnd_679276 310040075612079611756509 := by
  unfold tailWord_679276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387615543553268974896841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16516820724737691966529121 12387615543553268974896841)
  ·
    refine ⟨9290711657664951731172631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12387615543553268974896841 9290711657664951731172631)
    ·
      refine ⟨13936067486497427596758947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9290711657664951731172631 13936067486497427596758947)
      ·
        refine ⟨20904101229746141395138421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13936067486497427596758947 20904101229746141395138421)
        ·
          refine ⟨1959759490288700755794227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20904101229746141395138421 1959759490288700755794227)
          ·
            refine ⟨2939639235433051133691341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959759490288700755794227 2939639235433051133691341)
            ·
              refine ⟨1102364713287394175134253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2939639235433051133691341 1102364713287394175134253)
              ·
                refine ⟨413386767482772815675345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1102364713287394175134253 413386767482772815675345)
                ·
                  refine ⟨310040075612079611756509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413386767482772815675345 310040075612079611756509)
                  ·
                    rfl

theorem cell20_679276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_679276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679276 prefixEnd_679276 := by exact prefixLift 679276
  have htrace : WordTrace (prefixWord ++ tailWord_679276) baseStart_679276 baseEnd_679276 := by
    simpa [prefixWord, tailWord_679276, baseEnd_679276] using wordTrace_append hprefix tailTrace_679276
  have hstable : (prefixWord ++ tailWord_679276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679276).length < 2 ^ (prefixWord ++ tailWord_679276).sum := by decide
  have hdescent : baseEnd_679276 < baseStart_679276 := by decide
  rcases family_descends (prefixWord ++ tailWord_679276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679304 : List Nat := [2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_679304 : Nat := 118140960795 + 679304 * 2 ^ 59
def prefixEnd_679304 : Nat := 4983230072969 + 3 ^ 40 * 679304 * 2
def baseEnd_679304 : Nat := 103350951858345319607687

theorem tailTrace_679304 : CollatzResearch.WordTrace tailWord_679304 prefixEnd_679304 103350951858345319607687 := by
  unfold tailWord_679304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388126165502549365906483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16517501554003399154541977 12388126165502549365906483)
  ·
    refine ⟨18582189248253824048859725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12388126165502549365906483 18582189248253824048859725)
    ·
      refine ⟨6968320968095184018322397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18582189248253824048859725 6968320968095184018322397)
      ·
        refine ⟨2613120363035694006870899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6968320968095184018322397 2613120363035694006870899)
        ·
          refine ⟨3919680544553541010306349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613120363035694006870899 3919680544553541010306349)
          ·
            refine ⟨1469880204207577878864881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3919680544553541010306349 1469880204207577878864881)
            ·
              refine ⟨1102410153155683409148661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469880204207577878864881 1102410153155683409148661)
              ·
                refine ⟨103350951858345319607687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102410153155683409148661 103350951858345319607687)
                ·
                  rfl

theorem cell20_679304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_679304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679304 prefixEnd_679304 := by exact prefixLift 679304
  have htrace : WordTrace (prefixWord ++ tailWord_679304) baseStart_679304 baseEnd_679304 := by
    simpa [prefixWord, tailWord_679304, baseEnd_679304] using wordTrace_append hprefix tailTrace_679304
  have hstable : (prefixWord ++ tailWord_679304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679304).length < 2 ^ (prefixWord ++ tailWord_679304).sum := by decide
  have hdescent : baseEnd_679304 < baseStart_679304 := by decide
  rcases family_descends (prefixWord ++ tailWord_679304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679352 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_679352 : Nat := 118140960795 + 679352 * 2 ^ 59
def prefixEnd_679352 : Nat := 4983230072969 + 3 ^ 40 * 679352 * 2
def baseEnd_679352 : Nat := 310074764082961125222865

theorem tailTrace_679352 : CollatzResearch.WordTrace tailWord_679352 prefixEnd_679352 310074764082961125222865 := by
  unfold tailWord_679352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389001517415601464780155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16518668689887468619706873 12389001517415601464780155)
  ·
    refine ⟨18583502276123402197170233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12389001517415601464780155 18583502276123402197170233)
    ·
      refine ⟨13937626707092551647877675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18583502276123402197170233 13937626707092551647877675)
      ·
        refine ⟨20906440060638827471816513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13937626707092551647877675 20906440060638827471816513)
        ·
          refine ⟨15679830045479120603862385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20906440060638827471816513 15679830045479120603862385)
          ·
            refine ⟨11759872534109340452896789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679830045479120603862385 11759872534109340452896789)
            ·
              refine ⟨551244025036375333729537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11759872534109340452896789 551244025036375333729537)
              ·
                refine ⟨413433018777281500297153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551244025036375333729537 413433018777281500297153)
                ·
                  refine ⟨310074764082961125222865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413433018777281500297153 310074764082961125222865)
                  ·
                    rfl

theorem cell20_679352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_679352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679352 prefixEnd_679352 := by exact prefixLift 679352
  have htrace : WordTrace (prefixWord ++ tailWord_679352) baseStart_679352 baseEnd_679352 := by
    simpa [prefixWord, tailWord_679352, baseEnd_679352] using wordTrace_append hprefix tailTrace_679352
  have hstable : (prefixWord ++ tailWord_679352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679352).length < 2 ^ (prefixWord ++ tailWord_679352).sum := by decide
  have hdescent : baseEnd_679352 < baseStart_679352 := by decide
  rcases family_descends (prefixWord ++ tailWord_679352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679363 : List Nat := [1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_679363 : Nat := 118140960795 + 679363 * 2 ^ 59
def prefixEnd_679363 : Nat := 4983230072969 + 3 ^ 40 * 679363 * 2
def baseEnd_679363 : Nat := 103359928260897991952051

theorem tailTrace_679363 : CollatzResearch.WordTrace tailWord_679363 prefixEnd_679363 103359928260897991952051 := by
  unfold tailWord_679363
  simp only [CollatzResearch.WordTrace]
  refine ⟨24778404237791351808210743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16518936158527567872140495 24778404237791351808210743)
  ·
    refine ⟨37167606356687027712316115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24778404237791351808210743 37167606356687027712316115)
    ·
      refine ⟨55751409535030541568474173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37167606356687027712316115 55751409535030541568474173)
      ·
        refine ⟨20906778575636453088177815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55751409535030541568474173 20906778575636453088177815)
        ·
          refine ⟨31360167863454679632266723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20906778575636453088177815 31360167863454679632266723)
          ·
            refine ⟨47040251795182019448400085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31360167863454679632266723 47040251795182019448400085)
            ·
              refine ⟨1102505901449578580821877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47040251795182019448400085 1102505901449578580821877)
              ·
                refine ⟨103359928260897991952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102505901449578580821877 103359928260897991952051)
                ·
                  rfl

theorem cell20_679363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_679363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679363 prefixEnd_679363 := by exact prefixLift 679363
  have htrace : WordTrace (prefixWord ++ tailWord_679363) baseStart_679363 baseEnd_679363 := by
    simpa [prefixWord, tailWord_679363, baseEnd_679363] using wordTrace_append hprefix tailTrace_679363
  have hstable : (prefixWord ++ tailWord_679363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679363).length < 2 ^ (prefixWord ++ tailWord_679363).sum := by decide
  have hdescent : baseEnd_679363 < baseStart_679363 := by decide
  rcases family_descends (prefixWord ++ tailWord_679363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679432 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_679432 : Nat := 118140960795 + 679432 * 2 ^ 59
def prefixEnd_679432 : Nat := 4983230072969 + 3 ^ 40 * 679432 * 2
def baseEnd_679432 : Nat := 310111278262836402555871

theorem tailTrace_679432 : CollatzResearch.WordTrace tailWord_679432 prefixEnd_679432 310111278262836402555871 := by
  unfold tailWord_679432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390460437270688296236275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16520613916360917728315033 12390460437270688296236275)
  ·
    refine ⟨18585690655906032444354413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12390460437270688296236275 18585690655906032444354413)
    ·
      refine ⟨6969633995964762166632905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18585690655906032444354413 6969633995964762166632905)
      ·
        refine ⟨5227225496973571624974679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969633995964762166632905 5227225496973571624974679)
        ·
          refine ⟨7840838245460357437462019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227225496973571624974679 7840838245460357437462019)
          ·
            refine ⟨11761257368190536156193029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840838245460357437462019 11761257368190536156193029)
            ·
              refine ⟨2205235756535725529286193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11761257368190536156193029 2205235756535725529286193)
              ·
                refine ⟨1653926817401794146964645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205235756535725529286193 1653926817401794146964645)
                ·
                  refine ⟨310111278262836402555871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653926817401794146964645 310111278262836402555871)
                  ·
                    rfl

theorem cell20_679432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_679432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679432 prefixEnd_679432 := by exact prefixLift 679432
  have htrace : WordTrace (prefixWord ++ tailWord_679432) baseStart_679432 baseEnd_679432 := by
    simpa [prefixWord, tailWord_679432, baseEnd_679432] using wordTrace_append hprefix tailTrace_679432
  have hstable : (prefixWord ++ tailWord_679432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679432).length < 2 ^ (prefixWord ++ tailWord_679432).sum := by decide
  have hdescent : baseEnd_679432 < baseStart_679432 := by decide
  rcases family_descends (prefixWord ++ tailWord_679432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679435 : List Nat := [1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_679435 : Nat := 118140960795 + 679435 * 2 ^ 59
def prefixEnd_679435 : Nat := 4983230072969 + 3 ^ 40 * 679435 * 2
def baseEnd_679435 : Nat := 103370882514860575151953

theorem tailTrace_679435 : CollatzResearch.WordTrace tailWord_679435 prefixEnd_679435 103370882514860575151953 := by
  unfold tailWord_679435
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781030293530508104831759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16520686862353672069887839 24781030293530508104831759)
  ·
    refine ⟨37171545440295762157247639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781030293530508104831759 37171545440295762157247639)
    ·
      refine ⟨55757318160443643235871459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37171545440295762157247639 55757318160443643235871459)
      ·
        refine ⟨83635977240665464853807189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55757318160443643235871459 83635977240665464853807189)
        ·
          refine ⟨980109108289048416255553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 83635977240665464853807189 980109108289048416255553)
          ·
            refine ⟨735081831216786312191665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980109108289048416255553 735081831216786312191665)
            ·
              refine ⟨551311373412589734143749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735081831216786312191665 551311373412589734143749)
              ·
                refine ⟨103370882514860575151953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551311373412589734143749 103370882514860575151953)
                ·
                  rfl

theorem cell20_679435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_679435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679435 prefixEnd_679435 := by exact prefixLift 679435
  have htrace : WordTrace (prefixWord ++ tailWord_679435) baseStart_679435 baseEnd_679435 := by
    simpa [prefixWord, tailWord_679435, baseEnd_679435] using wordTrace_append hprefix tailTrace_679435
  have hstable : (prefixWord ++ tailWord_679435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679435).length < 2 ^ (prefixWord ++ tailWord_679435).sum := by decide
  have hdescent : baseEnd_679435 < baseStart_679435 := by decide
  rcases family_descends (prefixWord ++ tailWord_679435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679456 : List Nat := [2, 1, 1, 6, 1, 3, 6]
def baseStart_679456 : Nat := 118140960795 + 679456 * 2 ^ 59
def prefixEnd_679456 : Nat := 4983230072969 + 3 ^ 40 * 679456 * 2
def baseEnd_679456 : Nat := 34458025835199887306197

theorem tailTrace_679456 : CollatzResearch.WordTrace tailWord_679456 prefixEnd_679456 34458025835199887306197 := by
  unfold tailWord_679456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390898113227214345673111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16521197484302952460897481 12390898113227214345673111)
  ·
    refine ⟨18586347169840821518509667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12390898113227214345673111 18586347169840821518509667)
    ·
      refine ⟨27879520754761232277764501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18586347169840821518509667 27879520754761232277764501)
      ·
        refine ⟨1306852535379432763020211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27879520754761232277764501 1306852535379432763020211)
        ·
          refine ⟨1960278803069149144530317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306852535379432763020211 1960278803069149144530317)
          ·
            refine ⟨735104551150930929198869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1960278803069149144530317 735104551150930929198869)
            ·
              refine ⟨34458025835199887306197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 735104551150930929198869 34458025835199887306197)
              ·
                rfl

theorem cell20_679456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_679456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679456 prefixEnd_679456 := by exact prefixLift 679456
  have htrace : WordTrace (prefixWord ++ tailWord_679456) baseStart_679456 baseEnd_679456 := by
    simpa [prefixWord, tailWord_679456, baseEnd_679456] using wordTrace_append hprefix tailTrace_679456
  have hstable : (prefixWord ++ tailWord_679456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679456).length < 2 ^ (prefixWord ++ tailWord_679456).sum := by decide
  have hdescent : baseEnd_679456 < baseStart_679456 := by decide
  rcases family_descends (prefixWord ++ tailWord_679456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679477 : List Nat := [1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_679477 : Nat := 118140960795 + 679477 * 2 ^ 59
def prefixEnd_679477 : Nat := 4983230072969 + 3 ^ 40 * 679477 * 2
def baseEnd_679477 : Nat := 103377272496338748685229

theorem tailTrace_679477 : CollatzResearch.WordTrace tailWord_679477 prefixEnd_679477 103377272496338748685229 := by
  unfold tailWord_679477
  simp only [CollatzResearch.WordTrace]
  refine ⟨24782562159378349277860685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16521708106252232851907123 24782562159378349277860685)
  ·
    refine ⟨9293460809766880979197757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24782562159378349277860685 9293460809766880979197757)
    ·
      refine ⟨3485047803662580367199159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9293460809766880979197757 3485047803662580367199159)
      ·
        refine ⟨5227571705493870550798739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485047803662580367199159 5227571705493870550798739)
        ·
          refine ⟨7841357558240805826198109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227571705493870550798739 7841357558240805826198109)
          ·
            refine ⟨2940509084340302184824291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7841357558240805826198109 2940509084340302184824291)
            ·
              refine ⟨4410763626510453277236437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940509084340302184824291 4410763626510453277236437)
              ·
                refine ⟨103377272496338748685229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4410763626510453277236437 103377272496338748685229)
                ·
                  rfl

theorem cell20_679477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_679477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679477 prefixEnd_679477 := by exact prefixLift 679477
  have htrace : WordTrace (prefixWord ++ tailWord_679477) baseStart_679477 baseEnd_679477 := by
    simpa [prefixWord, tailWord_679477, baseEnd_679477] using wordTrace_append hprefix tailTrace_679477
  have hstable : (prefixWord ++ tailWord_679477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679477).length < 2 ^ (prefixWord ++ tailWord_679477).sum := by decide
  have hdescent : baseEnd_679477 < baseStart_679477 := by decide
  rcases family_descends (prefixWord ++ tailWord_679477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679480 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_679480 : Nat := 118140960795 + 679480 * 2 ^ 59
def prefixEnd_679480 : Nat := 4983230072969 + 3 ^ 40 * 679480 * 2
def baseEnd_679480 : Nat := 310133186770761568955675

theorem tailTrace_679480 : CollatzResearch.WordTrace tailWord_679480 prefixEnd_679480 310133186770761568955675 := by
  unfold tailWord_679480
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391335789183740395109947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16521781052244987193479929 12391335789183740395109947)
  ·
    refine ⟨18587003683775610592664921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12391335789183740395109947 18587003683775610592664921)
    ·
      refine ⟨13940252762831707944498691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18587003683775610592664921 13940252762831707944498691)
      ·
        refine ⟨20910379144247561916748037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940252762831707944498691 20910379144247561916748037)
        ·
          refine ⟨3920696089546417859390257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20910379144247561916748037 3920696089546417859390257)
          ·
            refine ⟨2940522067159813394542693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3920696089546417859390257 2940522067159813394542693)
            ·
              refine ⟨551347887592465011476755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2940522067159813394542693 551347887592465011476755)
              ·
                refine ⟨827021831388697517215133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551347887592465011476755 827021831388697517215133)
                ·
                  refine ⟨310133186770761568955675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827021831388697517215133 310133186770761568955675)
                  ·
                    rfl

theorem cell20_679480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_679480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679480 prefixEnd_679480 := by exact prefixLift 679480
  have htrace : WordTrace (prefixWord ++ tailWord_679480) baseStart_679480 baseEnd_679480 := by
    simpa [prefixWord, tailWord_679480, baseEnd_679480] using wordTrace_append hprefix tailTrace_679480
  have hstable : (prefixWord ++ tailWord_679480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679480).length < 2 ^ (prefixWord ++ tailWord_679480).sum := by decide
  have hdescent : baseEnd_679480 < baseStart_679480 := by decide
  rcases family_descends (prefixWord ++ tailWord_679480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679517 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 2]
def baseStart_679517 : Nat := 118140960795 + 679517 * 2 ^ 59
def prefixEnd_679517 : Nat := 4983230072969 + 3 ^ 40 * 679517 * 2
def baseEnd_679517 : Nat := 310150074578953884722191

theorem tailTrace_679517 : CollatzResearch.WordTrace tailWord_679517 prefixEnd_679517 310150074578953884722191 := by
  unfold tailWord_679517
  simp only [CollatzResearch.WordTrace]
  refine ⟨24784021079233436109316805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16522680719488957406211203 24784021079233436109316805)
  ·
    refine ⟨4647003952356269270496901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24784021079233436109316805 4647003952356269270496901)
    ·
      refine ⟨871313241066800488218169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4647003952356269270496901 871313241066800488218169)
      ·
        refine ⟨653484930800100366163627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871313241066800488218169 653484930800100366163627)
        ·
          refine ⟨980227396200150549245441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653484930800100366163627 980227396200150549245441)
          ·
            refine ⟨735170547150112911934081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980227396200150549245441 735170547150112911934081)
            ·
              refine ⟨551377910362584683950561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735170547150112911934081 551377910362584683950561)
              ·
                refine ⟨413533432771938512962921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551377910362584683950561 413533432771938512962921)
                ·
                  refine ⟨310150074578953884722191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413533432771938512962921 310150074578953884722191)
                  ·
                    rfl

theorem cell20_679517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_679517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679517 prefixEnd_679517 := by exact prefixLift 679517
  have htrace : WordTrace (prefixWord ++ tailWord_679517) baseStart_679517 baseEnd_679517 := by
    simpa [prefixWord, tailWord_679517, baseEnd_679517] using wordTrace_append hprefix tailTrace_679517
  have hstable : (prefixWord ++ tailWord_679517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679517).length < 2 ^ (prefixWord ++ tailWord_679517).sum := by decide
  have hdescent : baseEnd_679517 < baseStart_679517 := by decide
  rcases family_descends (prefixWord ++ tailWord_679517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679563 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 2]
def baseStart_679563 : Nat := 118140960795 + 679563 * 2 ^ 59
def prefixEnd_679563 : Nat := 4983230072969 + 3 ^ 40 * 679563 * 2
def baseEnd_679563 : Nat := 310171070232382169188669

theorem tailTrace_679563 : CollatzResearch.WordTrace tailWord_679563 prefixEnd_679563 310171070232382169188669 := by
  unfold tailWord_679563
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785698837066785965491343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16523799224711190643660895 24785698837066785965491343)
  ·
    refine ⟨37178548255600178948237015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24785698837066785965491343 37178548255600178948237015)
    ·
      refine ⟨55767822383400268422355523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37178548255600178948237015 55767822383400268422355523)
      ·
        refine ⟨83651733575100402633533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55767822383400268422355523 83651733575100402633533285)
        ·
          refine ⟨15684700045331325493787491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83651733575100402633533285 15684700045331325493787491)
          ·
            refine ⟨23527050067996988240681237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15684700045331325493787491 23527050067996988240681237)
            ·
              refine ⟨1102830471937358823781933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23527050067996988240681237 1102830471937358823781933)
              ·
                refine ⟨413561426976509558918225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1102830471937358823781933 413561426976509558918225)
                ·
                  refine ⟨310171070232382169188669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413561426976509558918225 310171070232382169188669)
                  ·
                    rfl

theorem cell20_679563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2].length) (baseStart_679563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679563 prefixEnd_679563 := by exact prefixLift 679563
  have htrace : WordTrace (prefixWord ++ tailWord_679563) baseStart_679563 baseEnd_679563 := by
    simpa [prefixWord, tailWord_679563, baseEnd_679563] using wordTrace_append hprefix tailTrace_679563
  have hstable : (prefixWord ++ tailWord_679563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679563).length < 2 ^ (prefixWord ++ tailWord_679563).sum := by decide
  have hdescent : baseEnd_679563 < baseStart_679563 := by decide
  rcases family_descends (prefixWord ++ tailWord_679563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679570 : List Nat := [3, 2, 3, 1, 3, 1, 7]
def baseStart_679570 : Nat := 118140960795 + 679570 * 2 ^ 59
def prefixEnd_679570 : Nat := 4983230072969 + 3 ^ 40 * 679570 * 2
def baseEnd_679570 : Nat := 34463807247013472883923

theorem tailTrace_679570 : CollatzResearch.WordTrace tailWord_679570 prefixEnd_679570 34463807247013472883923 := by
  unfold tailWord_679570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196488537010356540249041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16523969432027617440664109 6196488537010356540249041)
  ·
    refine ⟨4647366402757767405186781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6196488537010356540249041 4647366402757767405186781)
    ·
      refine ⟨1742762401034162776945043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4647366402757767405186781 1742762401034162776945043)
      ·
        refine ⟨2614143601551244165417565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742762401034162776945043 2614143601551244165417565)
        ·
          refine ⟨980303850581716562031587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2614143601551244165417565 980303850581716562031587)
          ·
            refine ⟨1470455775872574843047381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980303850581716562031587 1470455775872574843047381)
            ·
              refine ⟨34463807247013472883923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1470455775872574843047381 34463807247013472883923)
              ·
                rfl

theorem cell20_679570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_679570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679570 prefixEnd_679570 := by exact prefixLift 679570
  have htrace : WordTrace (prefixWord ++ tailWord_679570) baseStart_679570 baseEnd_679570 := by
    simpa [prefixWord, tailWord_679570, baseEnd_679570] using wordTrace_append hprefix tailTrace_679570
  have hstable : (prefixWord ++ tailWord_679570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679570).length < 2 ^ (prefixWord ++ tailWord_679570).sum := by decide
  have hdescent : baseEnd_679570 < baseStart_679570 := by decide
  rcases family_descends (prefixWord ++ tailWord_679570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679584 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_679584 : Nat := 118140960795 + 679584 * 2 ^ 59
def prefixEnd_679584 : Nat := 4983230072969 + 3 ^ 40 * 679584 * 2
def baseEnd_679584 : Nat := 310180655204599429488583

theorem tailTrace_679584 : CollatzResearch.WordTrace tailWord_679584 prefixEnd_679584 310180655204599429488583 := by
  unfold tailWord_679584
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393232384995353276002903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16524309846660471034670537 12393232384995353276002903)
  ·
    refine ⟨18589848577493029914004355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393232384995353276002903 18589848577493029914004355)
    ·
      refine ⟨27884772866239544871006533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18589848577493029914004355 27884772866239544871006533)
      ·
        refine ⟨5228394912419914663313725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27884772866239544871006533 5228394912419914663313725)
        ·
          refine ⟨1960648092157467998742647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5228394912419914663313725 1960648092157467998742647)
          ·
            refine ⟨2940972138236201998113971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960648092157467998742647 2940972138236201998113971)
            ·
              refine ⟨4411458207354302997170957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940972138236201998113971 4411458207354302997170957)
              ·
                refine ⟨1654296827757863623939109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4411458207354302997170957 1654296827757863623939109)
                ·
                  refine ⟨310180655204599429488583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654296827757863623939109 310180655204599429488583)
                  ·
                    rfl

theorem cell20_679584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_679584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679584 prefixEnd_679584 := by exact prefixLift 679584
  have htrace : WordTrace (prefixWord ++ tailWord_679584) baseStart_679584 baseEnd_679584 := by
    simpa [prefixWord, tailWord_679584, baseEnd_679584] using wordTrace_append hprefix tailTrace_679584
  have hstable : (prefixWord ++ tailWord_679584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679584).length < 2 ^ (prefixWord ++ tailWord_679584).sum := by decide
  have hdescent : baseEnd_679584 < baseStart_679584 := by decide
  rcases family_descends (prefixWord ++ tailWord_679584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679645 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 3]
def baseStart_679645 : Nat := 118140960795 + 679645 * 2 ^ 59
def prefixEnd_679645 : Nat := 4983230072969 + 3 ^ 40 * 679645 * 2
def baseEnd_679645 : Nat := 310208497266754328455001

theorem tailTrace_679645 : CollatzResearch.WordTrace tailWord_679645 prefixEnd_679645 310208497266754328455001 := by
  unfold tailWord_679645
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788689622769713969976389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16525793081846475979984259 24788689622769713969976389)
  ·
    refine ⟨4647879304269321369370573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24788689622769713969976389 4647879304269321369370573)
    ·
      refine ⟨1742954739100995513513965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4647879304269321369370573 1742954739100995513513965)
      ·
        refine ⟨653608027162873317567737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1742954739100995513513965 653608027162873317567737)
        ·
          refine ⟨490206020372154988175803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653608027162873317567737 490206020372154988175803)
          ·
            refine ⟨735309030558232482263705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490206020372154988175803 735309030558232482263705)
            ·
              refine ⟨551481772918674361697779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735309030558232482263705 551481772918674361697779)
              ·
                refine ⟨827222659378011542546669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551481772918674361697779 827222659378011542546669)
                ·
                  refine ⟨310208497266754328455001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827222659378011542546669 310208497266754328455001)
                  ·
                    rfl

theorem cell20_679645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_679645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679645 prefixEnd_679645 := by exact prefixLift 679645
  have htrace : WordTrace (prefixWord ++ tailWord_679645) baseStart_679645 baseEnd_679645 := by
    simpa [prefixWord, tailWord_679645, baseEnd_679645] using wordTrace_append hprefix tailTrace_679645
  have hstable : (prefixWord ++ tailWord_679645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679645).length < 2 ^ (prefixWord ++ tailWord_679645).sum := by decide
  have hdescent : baseEnd_679645 < baseStart_679645 := by decide
  rcases family_descends (prefixWord ++ tailWord_679645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679649 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 3]
def baseStart_679649 : Nat := 118140960795 + 679649 * 2 ^ 59
def prefixEnd_679649 : Nat := 4983230072969 + 3 ^ 40 * 679649 * 2
def baseEnd_679649 : Nat := 310210322975748092321651

theorem tailTrace_679649 : CollatzResearch.WordTrace tailWord_679649 prefixEnd_679649 310210322975748092321651 := by
  unfold tailWord_679649
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788835514755222653122001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16525890343170148435414667 24788835514755222653122001)
  ·
    refine ⟨18591626636066416989841501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24788835514755222653122001 18591626636066416989841501)
    ·
      refine ⟨6971859988524906371190563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18591626636066416989841501 6971859988524906371190563)
      ·
        refine ⟨10457789982787359556785845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971859988524906371190563 10457789982787359556785845)
        ·
          refine ⟨980417810886314958448673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10457789982787359556785845 980417810886314958448673)
          ·
            refine ⟨735313358164736218836505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980417810886314958448673 735313358164736218836505)
            ·
              refine ⟨551485018623552164127379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735313358164736218836505 551485018623552164127379)
              ·
                refine ⟨827227527935328246191069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551485018623552164127379 827227527935328246191069)
                ·
                  refine ⟨310210322975748092321651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827227527935328246191069 310210322975748092321651)
                  ·
                    rfl

theorem cell20_679649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_679649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679649 prefixEnd_679649 := by exact prefixLift 679649
  have htrace : WordTrace (prefixWord ++ tailWord_679649) baseStart_679649 baseEnd_679649 := by
    simpa [prefixWord, tailWord_679649, baseEnd_679649] using wordTrace_append hprefix tailTrace_679649
  have hstable : (prefixWord ++ tailWord_679649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679649).length < 2 ^ (prefixWord ++ tailWord_679649).sum := by decide
  have hdescent : baseEnd_679649 < baseStart_679649 := by decide
  rcases family_descends (prefixWord ++ tailWord_679649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679653 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_679653 : Nat := 118140960795 + 679653 * 2 ^ 59
def prefixEnd_679653 : Nat := 4983230072969 + 3 ^ 40 * 679653 * 2
def baseEnd_679653 : Nat := 310212148684741856188301

theorem tailTrace_679653 : CollatzResearch.WordTrace tailWord_679653 prefixEnd_679653 310212148684741856188301 := by
  unfold tailWord_679653
  simp only [CollatzResearch.WordTrace]
  refine ⟨24788981406740731336267613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16525987604493820890845075 24788981406740731336267613)
  ·
    refine ⟨9295868027527774251100355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24788981406740731336267613 9295868027527774251100355)
    ·
      refine ⟨13943802041291661376650533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295868027527774251100355 13943802041291661376650533)
      ·
        refine ⟨2614462882742186508121975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13943802041291661376650533 2614462882742186508121975)
        ·
          refine ⟨3921694324113279762182963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614462882742186508121975 3921694324113279762182963)
          ·
            refine ⟨5882541486169919643274445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921694324113279762182963 5882541486169919643274445)
            ·
              refine ⟨2205953057313719866227917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5882541486169919643274445 2205953057313719866227917)
              ·
                refine ⟨827232396492644949835469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205953057313719866227917 827232396492644949835469)
                ·
                  refine ⟨310212148684741856188301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827232396492644949835469 310212148684741856188301)
                  ·
                    rfl

theorem cell20_679653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_679653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679653 prefixEnd_679653 := by exact prefixLift 679653
  have htrace : WordTrace (prefixWord ++ tailWord_679653) baseStart_679653 baseEnd_679653 := by
    simpa [prefixWord, tailWord_679653, baseEnd_679653] using wordTrace_append hprefix tailTrace_679653
  have hstable : (prefixWord ++ tailWord_679653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679653).length < 2 ^ (prefixWord ++ tailWord_679653).sum := by decide
  have hdescent : baseEnd_679653 < baseStart_679653 := by decide
  rcases family_descends (prefixWord ++ tailWord_679653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679686 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_679686 : Nat := 118140960795 + 679686 * 2 ^ 59
def prefixEnd_679686 : Nat := 4983230072969 + 3 ^ 40 * 679686 * 2
def baseEnd_679686 : Nat := 310227210783940408088167

theorem tailTrace_679686 : CollatzResearch.WordTrace tailWord_679686 prefixEnd_679686 310227210783940408088167 := by
  unfold tailWord_679686
  simp only [CollatzResearch.WordTrace]
  refine ⟨774693281738161811631841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16526790010414118648145941 774693281738161811631841)
  ·
    refine ⟨581019961303621358723881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 774693281738161811631841 581019961303621358723881)
    ·
      refine ⟨435764970977716019042911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581019961303621358723881 435764970977716019042911)
      ·
        refine ⟨653647456466574028564367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435764970977716019042911 653647456466574028564367)
        ·
          refine ⟨980471184699861042846551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653647456466574028564367 980471184699861042846551)
          ·
            refine ⟨1470706777049791564269827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980471184699861042846551 1470706777049791564269827)
            ·
              refine ⟨2206060165574687346404741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470706777049791564269827 2206060165574687346404741)
              ·
                refine ⟨413636281045253877450889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2206060165574687346404741 413636281045253877450889)
                ·
                  refine ⟨310227210783940408088167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413636281045253877450889 310227210783940408088167)
                  ·
                    rfl

theorem cell20_679686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_679686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679686 prefixEnd_679686 := by exact prefixLift 679686
  have htrace : WordTrace (prefixWord ++ tailWord_679686) baseStart_679686 baseEnd_679686 := by
    simpa [prefixWord, tailWord_679686, baseEnd_679686] using wordTrace_append hprefix tailTrace_679686
  have hstable : (prefixWord ++ tailWord_679686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679686).length < 2 ^ (prefixWord ++ tailWord_679686).sum := by decide
  have hdescent : baseEnd_679686 < baseStart_679686 := by decide
  rcases family_descends (prefixWord ++ tailWord_679686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679694 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_679694 : Nat := 118140960795 + 679694 * 2 ^ 59
def prefixEnd_679694 : Nat := 4983230072969 + 3 ^ 40 * 679694 * 2
def baseEnd_679694 : Nat := 310230862201927935821467

theorem tailTrace_679694 : CollatzResearch.WordTrace tailWord_679694 prefixEnd_679694 310230862201927935821467 := by
  unfold tailWord_679694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098809599949024417313767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16526984533061463559006757 3098809599949024417313767)
  ·
    refine ⟨4648214399923536625970651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3098809599949024417313767 4648214399923536625970651)
    ·
      refine ⟨6972321599885304938955977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648214399923536625970651 6972321599885304938955977)
      ·
        refine ⟨5229241199913978704216983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6972321599885304938955977 5229241199913978704216983)
        ·
          refine ⟨7843861799870968056325475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229241199913978704216983 7843861799870968056325475)
          ·
            refine ⟨11765792699806452084488213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7843861799870968056325475 11765792699806452084488213)
            ·
              refine ⟨551521532803427441460385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11765792699806452084488213 551521532803427441460385)
              ·
                refine ⟨413641149602570581095289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551521532803427441460385 413641149602570581095289)
                ·
                  refine ⟨310230862201927935821467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413641149602570581095289 310230862201927935821467)
                  ·
                    rfl

theorem cell20_679694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_679694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679694 prefixEnd_679694 := by exact prefixLift 679694
  have htrace : WordTrace (prefixWord ++ tailWord_679694) baseStart_679694 baseEnd_679694 := by
    simpa [prefixWord, tailWord_679694, baseEnd_679694] using wordTrace_append hprefix tailTrace_679694
  have hstable : (prefixWord ++ tailWord_679694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679694).length < 2 ^ (prefixWord ++ tailWord_679694).sum := by decide
  have hdescent : baseEnd_679694 < baseStart_679694 := by decide
  rcases family_descends (prefixWord ++ tailWord_679694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679732 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_679732 : Nat := 118140960795 + 679732 * 2 ^ 59
def prefixEnd_679732 : Nat := 4983230072969 + 3 ^ 40 * 679732 * 2
def baseEnd_679732 : Nat := 310248206437368692554645

theorem tailTrace_679732 : CollatzResearch.WordTrace tailWord_679732 prefixEnd_679732 310248206437368692554645 := by
  unfold tailWord_679732
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395931386727263914196725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16527908515636351885595633 12395931386727263914196725)
  ·
    refine ⟨1162118567505680991955943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12395931386727263914196725 1162118567505680991955943)
    ·
      refine ⟨1743177851258521487933915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162118567505680991955943 1743177851258521487933915)
      ·
        refine ⟨2614766776887782231900873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743177851258521487933915 2614766776887782231900873)
        ·
          refine ⟨1961075082665836673925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2614766776887782231900873 1961075082665836673925655)
          ·
            refine ⟨2941612623998755010888483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961075082665836673925655 2941612623998755010888483)
            ·
              refine ⟨4412418935998132516332725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941612623998755010888483 4412418935998132516332725)
              ·
                refine ⟨413664275249824923406193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4412418935998132516332725 413664275249824923406193)
                ·
                  refine ⟨310248206437368692554645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413664275249824923406193 310248206437368692554645)
                  ·
                    rfl

theorem cell20_679732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_679732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679732 prefixEnd_679732 := by exact prefixLift 679732
  have htrace : WordTrace (prefixWord ++ tailWord_679732) baseStart_679732 baseEnd_679732 := by
    simpa [prefixWord, tailWord_679732, baseEnd_679732] using wordTrace_append hprefix tailTrace_679732
  have hstable : (prefixWord ++ tailWord_679732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679732).length < 2 ^ (prefixWord ++ tailWord_679732).sum := by decide
  have hdescent : baseEnd_679732 < baseStart_679732 := by decide
  rcases family_descends (prefixWord ++ tailWord_679732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679743 : List Nat := [1, 1, 2, 2, 6, 1, 7]
def baseStart_679743 : Nat := 118140960795 + 679743 * 2 ^ 59
def prefixEnd_679743 : Nat := 4983230072969 + 3 ^ 40 * 679743 * 2
def baseEnd_679743 : Nat := 34472580793011282576437

theorem tailTrace_679743 : CollatzResearch.WordTrace tailWord_679743 prefixEnd_679743 34472580793011282576437 := by
  unfold tailWord_679743
  simp only [CollatzResearch.WordTrace]
  refine ⟨24792263976414676707043883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16528175984276451138029255 24792263976414676707043883)
  ·
    refine ⟨37188395964622015060565825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24792263976414676707043883 37188395964622015060565825)
    ·
      refine ⟨27891296973466511295424369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37188395964622015060565825 27891296973466511295424369)
      ·
        refine ⟨20918472730099883471568277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27891296973466511295424369 20918472730099883471568277)
        ·
          refine ⟨980553409223432037729763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20918472730099883471568277 980553409223432037729763)
          ·
            refine ⟨1470830113835148056594645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980553409223432037729763 1470830113835148056594645)
            ·
              refine ⟨34472580793011282576437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1470830113835148056594645 34472580793011282576437)
              ·
                rfl

theorem cell20_679743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_679743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679743 prefixEnd_679743 := by exact prefixLift 679743
  have htrace : WordTrace (prefixWord ++ tailWord_679743) baseStart_679743 baseEnd_679743 := by
    simpa [prefixWord, tailWord_679743, baseEnd_679743] using wordTrace_append hprefix tailTrace_679743
  have hstable : (prefixWord ++ tailWord_679743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679743).length < 2 ^ (prefixWord ++ tailWord_679743).sum := by decide
  have hdescent : baseEnd_679743 < baseStart_679743 := by decide
  rcases family_descends (prefixWord ++ tailWord_679743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679788 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_679788 : Nat := 118140960795 + 679788 * 2 ^ 59
def prefixEnd_679788 : Nat := 4983230072969 + 3 ^ 40 * 679788 * 2
def baseEnd_679788 : Nat := 310273766363281386687749

theorem tailTrace_679788 : CollatzResearch.WordTrace tailWord_679788 prefixEnd_679788 310273766363281386687749 := by
  unfold tailWord_679788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12396952630625824696216009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16529270174167766261621345 12396952630625824696216009)
  ·
    refine ⟨9297714472969368522162007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12396952630625824696216009 9297714472969368522162007)
    ·
      refine ⟨13946571709454052783243011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9297714472969368522162007 13946571709454052783243011)
      ·
        refine ⟨20919857564181079174864517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13946571709454052783243011 20919857564181079174864517)
        ·
          refine ⟨3922473293283952345287097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20919857564181079174864517 3922473293283952345287097)
          ·
            refine ⟨2941854969962964258965323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922473293283952345287097 2941854969962964258965323)
            ·
              refine ⟨4412782454944446388447985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941854969962964258965323 4412782454944446388447985)
              ·
                refine ⟨3309586841208334791335989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412782454944446388447985 3309586841208334791335989)
                ·
                  refine ⟨310273766363281386687749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3309586841208334791335989 310273766363281386687749)
                  ·
                    rfl

theorem cell20_679788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_679788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679788 prefixEnd_679788 := by exact prefixLift 679788
  have htrace : WordTrace (prefixWord ++ tailWord_679788) baseStart_679788 baseEnd_679788 := by
    simpa [prefixWord, tailWord_679788, baseEnd_679788] using wordTrace_append hprefix tailTrace_679788
  have hstable : (prefixWord ++ tailWord_679788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679788).length < 2 ^ (prefixWord ++ tailWord_679788).sum := by decide
  have hdescent : baseEnd_679788 < baseStart_679788 := by decide
  rcases family_descends (prefixWord ++ tailWord_679788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679802 : List Nat := [3, 1, 1, 1, 1, 1, 12]
def baseStart_679802 : Nat := 118140960795 + 679802 * 2 ^ 59
def prefixEnd_679802 : Nat := 4983230072969 + 3 ^ 40 * 679802 * 2
def baseEnd_679802 : Nat := 34475572927195506691225

theorem tailTrace_679802 : CollatzResearch.WordTrace tailWord_679802 prefixEnd_679802 34475572927195506691225 := by
  unfold tailWord_679802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198603970800232445860415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16529610588800619855627773 6198603970800232445860415)
  ·
    refine ⟨9297905956200348668790623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6198603970800232445860415 9297905956200348668790623)
    ·
      refine ⟨13946858934300523003185935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9297905956200348668790623 13946858934300523003185935)
      ·
        refine ⟨20920288401450784504778903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13946858934300523003185935 20920288401450784504778903)
        ·
          refine ⟨31380432602176176757168355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920288401450784504778903 31380432602176176757168355)
          ·
            refine ⟨47070648903264265135752533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31380432602176176757168355 47070648903264265135752533)
            ·
              refine ⟨34475572927195506691225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47070648903264265135752533 34475572927195506691225)
              ·
                rfl

theorem cell20_679802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_679802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679802 prefixEnd_679802 := by exact prefixLift 679802
  have htrace : WordTrace (prefixWord ++ tailWord_679802) baseStart_679802 baseEnd_679802 := by
    simpa [prefixWord, tailWord_679802, baseEnd_679802] using wordTrace_append hprefix tailTrace_679802
  have hstable : (prefixWord ++ tailWord_679802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679802).length < 2 ^ (prefixWord ++ tailWord_679802).sum := by decide
  have hdescent : baseEnd_679802 < baseStart_679802 := by decide
  rcases family_descends (prefixWord ++ tailWord_679802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679812 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_679812 : Nat := 118140960795 + 679812 * 2 ^ 59
def prefixEnd_679812 : Nat := 4983230072969 + 3 ^ 40 * 679812 * 2
def baseEnd_679812 : Nat := 310284720617243969887651

theorem tailTrace_679812 : CollatzResearch.WordTrace tailWord_679812 prefixEnd_679812 310284720617243969887651 := by
  unfold tailWord_679812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12397390306582350745652845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16529853742109800994203793 12397390306582350745652845)
  ·
    refine ⟨4649021364968381529619817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12397390306582350745652845 4649021364968381529619817)
    ·
      refine ⟨3486766023726286147214863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4649021364968381529619817 3486766023726286147214863)
      ·
        refine ⟨5230149035589429220822295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486766023726286147214863 5230149035589429220822295)
        ·
          refine ⟨7845223553384143831233443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230149035589429220822295 7845223553384143831233443)
          ·
            refine ⟨11767835330076215746850165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845223553384143831233443 11767835330076215746850165)
            ·
              refine ⟨1103234562194645226267203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11767835330076215746850165 1103234562194645226267203)
              ·
                refine ⟨1654851843291967839400805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103234562194645226267203 1654851843291967839400805)
                ·
                  refine ⟨310284720617243969887651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654851843291967839400805 310284720617243969887651)
                  ·
                    rfl

theorem cell20_679812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_679812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679812 prefixEnd_679812 := by exact prefixLift 679812
  have htrace : WordTrace (prefixWord ++ tailWord_679812) baseStart_679812 baseEnd_679812 := by
    simpa [prefixWord, tailWord_679812, baseEnd_679812] using wordTrace_append hprefix tailTrace_679812
  have hstable : (prefixWord ++ tailWord_679812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679812).length < 2 ^ (prefixWord ++ tailWord_679812).sum := by decide
  have hdescent : baseEnd_679812 < baseStart_679812 := by decide
  rcases family_descends (prefixWord ++ tailWord_679812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679818 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_679818 : Nat := 118140960795 + 679818 * 2 ^ 59
def prefixEnd_679818 : Nat := 4983230072969 + 3 ^ 40 * 679818 * 2
def baseEnd_679818 : Nat := 310287459180734615687627

theorem tailTrace_679818 : CollatzResearch.WordTrace tailWord_679818 prefixEnd_679818 310287459180734615687627 := by
  unfold tailWord_679818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198749862785741129006027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16529999634095309677349405 6198749862785741129006027)
  ·
    refine ⟨9298124794178611693509041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6198749862785741129006027 9298124794178611693509041)
    ·
      refine ⟨6973593595633958770131781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9298124794178611693509041 6973593595633958770131781)
      ·
        refine ⟨1307548799181367269399709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6973593595633958770131781 1307548799181367269399709)
        ·
          refine ⟨490330799693012726024891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1307548799181367269399709 490330799693012726024891)
          ·
            refine ⟨735496199539519089037337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490330799693012726024891 735496199539519089037337)
            ·
              refine ⟨551622149654639316778003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735496199539519089037337 551622149654639316778003)
              ·
                refine ⟨827433224481958975167005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551622149654639316778003 827433224481958975167005)
                ·
                  refine ⟨310287459180734615687627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827433224481958975167005 310287459180734615687627)
                  ·
                    rfl

theorem cell20_679818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_679818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679818 prefixEnd_679818 := by exact prefixLift 679818
  have htrace : WordTrace (prefixWord ++ tailWord_679818) baseStart_679818 baseEnd_679818 := by
    simpa [prefixWord, tailWord_679818, baseEnd_679818] using wordTrace_append hprefix tailTrace_679818
  have hstable : (prefixWord ++ tailWord_679818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679818).length < 2 ^ (prefixWord ++ tailWord_679818).sum := by decide
  have hdescent : baseEnd_679818 < baseStart_679818 := by decide
  rcases family_descends (prefixWord ++ tailWord_679818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679833 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_679833 : Nat := 118140960795 + 679833 * 2 ^ 59
def prefixEnd_679833 : Nat := 4983230072969 + 3 ^ 40 * 679833 * 2
def baseEnd_679833 : Nat := 310294305589461230187565

theorem tailTrace_679833 : CollatzResearch.WordTrace tailWord_679833 prefixEnd_679833 310294305589461230187565 := by
  unfold tailWord_679833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24795546546088622077820153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16530364364059081385213435 24795546546088622077820153)
  ·
    refine ⟨18596659909566466558365115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24795546546088622077820153 18596659909566466558365115)
    ·
      refine ⟨27894989864349699837547673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18596659909566466558365115 27894989864349699837547673)
      ·
        refine ⟨20921242398262274878160755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27894989864349699837547673 20921242398262274878160755)
        ·
          refine ⟨31381863597393412317241133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20921242398262274878160755 31381863597393412317241133)
          ·
            refine ⟨11768198849022529618965425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31381863597393412317241133 11768198849022529618965425)
            ·
              refine ⟨8826149136766897214224069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11768198849022529618965425 8826149136766897214224069)
              ·
                refine ⟨1654902963143793227667013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8826149136766897214224069 1654902963143793227667013)
                ·
                  refine ⟨310294305589461230187565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654902963143793227667013 310294305589461230187565)
                  ·
                    rfl

theorem cell20_679833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_679833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679833 prefixEnd_679833 := by exact prefixLift 679833
  have htrace : WordTrace (prefixWord ++ tailWord_679833) baseStart_679833 baseEnd_679833 := by
    simpa [prefixWord, tailWord_679833, baseEnd_679833] using wordTrace_append hprefix tailTrace_679833
  have hstable : (prefixWord ++ tailWord_679833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679833).length < 2 ^ (prefixWord ++ tailWord_679833).sum := by decide
  have hdescent : baseEnd_679833 < baseStart_679833 := by decide
  rcases family_descends (prefixWord ++ tailWord_679833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679871 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_679871 : Nat := 118140960795 + 679871 * 2 ^ 59
def prefixEnd_679871 : Nat := 4983230072969 + 3 ^ 40 * 679871 * 2
def baseEnd_679871 : Nat := 310311649824901986920743

theorem tailTrace_679871 : CollatzResearch.WordTrace tailWord_679871 prefixEnd_679871 310311649824901986920743 := by
  unfold tailWord_679871
  simp only [CollatzResearch.WordTrace]
  refine ⟨24796932519950954567703467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16531288346633969711802311 24796932519950954567703467)
  ·
    refine ⟨37195398779926431851555201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24796932519950954567703467 37195398779926431851555201)
    ·
      refine ⟨27896549084944823888666401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37195398779926431851555201 27896549084944823888666401)
      ·
        refine ⟨20922411813708617916499801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27896549084944823888666401 20922411813708617916499801)
        ·
          refine ⟨15691808860281463437374851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20922411813708617916499801 15691808860281463437374851)
          ·
            refine ⟨23537713290422195156062277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15691808860281463437374851 23537713290422195156062277)
            ·
              refine ⟨4413321241954161591761677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23537713290422195156062277 4413321241954161591761677)
              ·
                refine ⟨1654995465732810596910629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4413321241954161591761677 1654995465732810596910629)
                ·
                  refine ⟨310311649824901986920743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654995465732810596910629 310311649824901986920743)
                  ·
                    rfl

theorem cell20_679871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_679871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679871 prefixEnd_679871 := by exact prefixLift 679871
  have htrace : WordTrace (prefixWord ++ tailWord_679871) baseStart_679871 baseEnd_679871 := by
    simpa [prefixWord, tailWord_679871, baseEnd_679871] using wordTrace_append hprefix tailTrace_679871
  have hstable : (prefixWord ++ tailWord_679871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679871).length < 2 ^ (prefixWord ++ tailWord_679871).sum := by decide
  have hdescent : baseEnd_679871 < baseStart_679871 := by decide
  rcases family_descends (prefixWord ++ tailWord_679871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679895 : List Nat := [1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_679895 : Nat := 118140960795 + 679895 * 2 ^ 59
def prefixEnd_679895 : Nat := 4983230072969 + 3 ^ 40 * 679895 * 2
def baseEnd_679895 : Nat := 103440868026288190040215

theorem tailTrace_679895 : CollatzResearch.WordTrace tailWord_679895 prefixEnd_679895 103440868026288190040215 := by
  unfold tailWord_679895
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797807871864006666577139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16531871914576004444384759 24797807871864006666577139)
  ·
    refine ⟨37196711807796009999865709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24797807871864006666577139 37196711807796009999865709)
    ·
      refine ⟨13948766927923503749949641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37196711807796009999865709 13948766927923503749949641)
      ·
        refine ⟨10461575195942627812462231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13948766927923503749949641 10461575195942627812462231)
        ·
          refine ⟨15692362793913941718693347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10461575195942627812462231 15692362793913941718693347)
          ·
            refine ⟨23538544190870912578040021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15692362793913941718693347 23538544190870912578040021)
            ·
              refine ⟨551684629473537013547813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23538544190870912578040021 551684629473537013547813)
              ·
                refine ⟨103440868026288190040215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551684629473537013547813 103440868026288190040215)
                ·
                  rfl

theorem cell20_679895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_679895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679895 prefixEnd_679895 := by exact prefixLift 679895
  have htrace : WordTrace (prefixWord ++ tailWord_679895) baseStart_679895 baseEnd_679895 := by
    simpa [prefixWord, tailWord_679895, baseEnd_679895] using wordTrace_append hprefix tailTrace_679895
  have hstable : (prefixWord ++ tailWord_679895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679895).length < 2 ^ (prefixWord ++ tailWord_679895).sum := by decide
  have hdescent : baseEnd_679895 < baseStart_679895 := by decide
  rcases family_descends (prefixWord ++ tailWord_679895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679942 : List Nat := [6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_679942 : Nat := 118140960795 + 679942 * 2 ^ 59
def prefixEnd_679942 : Nat := 4983230072969 + 3 ^ 40 * 679942 * 2
def baseEnd_679942 : Nat := 103448018719847098517929

theorem tailTrace_679942 : CollatzResearch.WordTrace tailWord_679942 prefixEnd_679942 103448018719847098517929 := by
  unfold tailWord_679942
  simp only [CollatzResearch.WordTrace]
  refine ⟨774985065709179177923065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16533014735129155795692053 774985065709179177923065)
  ·
    refine ⟨581238799281884383442299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 774985065709179177923065 581238799281884383442299)
    ·
      refine ⟨871858198922826575163449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581238799281884383442299 871858198922826575163449)
      ·
        refine ⟨653893649192119931372587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871858198922826575163449 653893649192119931372587)
        ·
          refine ⟨980840473788179897058881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653893649192119931372587 980840473788179897058881)
          ·
            refine ⟨735630355341134922794161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980840473788179897058881 735630355341134922794161)
            ·
              refine ⟨551722766505851192095621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735630355341134922794161 551722766505851192095621)
              ·
                refine ⟨103448018719847098517929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551722766505851192095621 103448018719847098517929)
                ·
                  rfl

theorem cell20_679942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_679942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679942 prefixEnd_679942 := by exact prefixLift 679942
  have htrace : WordTrace (prefixWord ++ tailWord_679942) baseStart_679942 baseEnd_679942 := by
    simpa [prefixWord, tailWord_679942, baseEnd_679942] using wordTrace_append hprefix tailTrace_679942
  have hstable : (prefixWord ++ tailWord_679942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679942).length < 2 ^ (prefixWord ++ tailWord_679942).sum := by decide
  have hdescent : baseEnd_679942 < baseStart_679942 := by decide
  rcases family_descends (prefixWord ++ tailWord_679942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679947 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_679947 : Nat := 118140960795 + 679947 * 2 ^ 59
def prefixEnd_679947 : Nat := 4983230072969 + 3 ^ 40 * 679947 * 2
def baseEnd_679947 : Nat := 310346338295783500387099

theorem tailTrace_679947 : CollatzResearch.WordTrace tailWord_679947 prefixEnd_679947 310346338295783500387099 := by
  unfold tailWord_679947
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799704467675619547470095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16533136311783746364980063 24799704467675619547470095)
  ·
    refine ⟨37199556701513429321205143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24799704467675619547470095 37199556701513429321205143)
    ·
      refine ⟨55799335052270143981807715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37199556701513429321205143 55799335052270143981807715)
      ·
        refine ⟨83699002578405215972711573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55799335052270143981807715 83699002578405215972711573)
        ·
          refine ⟨3923390745862744498720855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83699002578405215972711573 3923390745862744498720855)
          ·
            refine ⟨5885086118794116748081283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923390745862744498720855 5885086118794116748081283)
            ·
              refine ⟨8827629178191175122121925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885086118794116748081283 8827629178191175122121925)
              ·
                refine ⟨1655180470910845335397861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8827629178191175122121925 1655180470910845335397861)
                ·
                  refine ⟨310346338295783500387099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655180470910845335397861 310346338295783500387099)
                  ·
                    rfl

theorem cell20_679947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_679947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679947 prefixEnd_679947 := by exact prefixLift 679947
  have htrace : WordTrace (prefixWord ++ tailWord_679947) baseStart_679947 baseEnd_679947 := by
    simpa [prefixWord, tailWord_679947, baseEnd_679947] using wordTrace_append hprefix tailTrace_679947
  have hstable : (prefixWord ++ tailWord_679947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679947).length < 2 ^ (prefixWord ++ tailWord_679947).sum := by decide
  have hdescent : baseEnd_679947 < baseStart_679947 := by decide
  rcases family_descends (prefixWord ++ tailWord_679947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679956 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_679956 : Nat := 118140960795 + 679956 * 2 ^ 59
def prefixEnd_679956 : Nat := 4983230072969 + 3 ^ 40 * 679956 * 2
def baseEnd_679956 : Nat := 310350446141019469087063

theorem tailTrace_679956 : CollatzResearch.WordTrace tailWord_679956 prefixEnd_679956 310350446141019469087063 := by
  unfold tailWord_679956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400016362321507042273861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16533355149762009389698481 12400016362321507042273861)
  ·
    refine ⟨2325003067935282570426349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12400016362321507042273861 2325003067935282570426349)
    ·
      refine ⟨871876150475730963909881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2325003067935282570426349 871876150475730963909881)
      ·
        refine ⟨653907112856798222932411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871876150475730963909881 653907112856798222932411)
        ·
          refine ⟨980860669285197334398617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653907112856798222932411 980860669285197334398617)
          ·
            refine ⟨735645501963898000798963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980860669285197334398617 735645501963898000798963)
            ·
              refine ⟨1103468252945847001198445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735645501963898000798963 1103468252945847001198445)
              ·
                refine ⟨413800594854692625449417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1103468252945847001198445 413800594854692625449417)
                ·
                  refine ⟨310350446141019469087063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413800594854692625449417 310350446141019469087063)
                  ·
                    rfl

theorem cell20_679956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_679956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_679956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_679956 prefixEnd_679956 := by exact prefixLift 679956
  have htrace : WordTrace (prefixWord ++ tailWord_679956) baseStart_679956 baseEnd_679956 := by
    simpa [prefixWord, tailWord_679956, baseEnd_679956] using wordTrace_append hprefix tailTrace_679956
  have hstable : (prefixWord ++ tailWord_679956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679956).length < 2 ^ (prefixWord ++ tailWord_679956).sum := by decide
  have hdescent : baseEnd_679956 < baseStart_679956 := by decide
  rcases family_descends (prefixWord ++ tailWord_679956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680047 : List Nat := [1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_680047 : Nat := 118140960795 + 680047 * 2 ^ 59
def prefixEnd_680047 : Nat := 4983230072969 + 3 ^ 40 * 680047 * 2
def baseEnd_680047 : Nat := 103463993673542532351119

theorem tailTrace_680047 : CollatzResearch.WordTrace tailWord_680047 prefixEnd_680047 103463993673542532351119 := by
  unfold tailWord_680047
  simp only [CollatzResearch.WordTrace]
  refine ⟨24803351767313336626110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16535567844875557750740263 24803351767313336626110395)
  ·
    refine ⟨37205027650970004939165593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24803351767313336626110395 37205027650970004939165593)
    ·
      refine ⟨27903770738227503704374195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37205027650970004939165593 27903770738227503704374195)
      ·
        refine ⟨41855656107341255556561293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27903770738227503704374195 41855656107341255556561293)
        ·
          refine ⟨15695871040252970833710485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41855656107341255556561293 15695871040252970833710485)
          ·
            refine ⟨735743955011858007830179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15695871040252970833710485 735743955011858007830179)
            ·
              refine ⟨1103615932517787011745269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735743955011858007830179 1103615932517787011745269)
              ·
                refine ⟨103463993673542532351119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1103615932517787011745269 103463993673542532351119)
                ·
                  rfl

theorem cell20_680047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_680047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680047 prefixEnd_680047 := by exact prefixLift 680047
  have htrace : WordTrace (prefixWord ++ tailWord_680047) baseStart_680047 baseEnd_680047 := by
    simpa [prefixWord, tailWord_680047, baseEnd_680047] using wordTrace_append hprefix tailTrace_680047
  have hstable : (prefixWord ++ tailWord_680047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680047).length < 2 ^ (prefixWord ++ tailWord_680047).sum := by decide
  have hdescent : baseEnd_680047 < baseStart_680047 := by decide
  rcases family_descends (prefixWord ++ tailWord_680047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680061 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_680061 : Nat := 118140960795 + 680061 * 2 ^ 59
def prefixEnd_680061 : Nat := 4983230072969 + 3 ^ 40 * 680061 * 2
def baseEnd_680061 : Nat := 310398371002105770586633

theorem tailTrace_680061 : CollatzResearch.WordTrace tailWord_680061 prefixEnd_680061 310398371002105770586633 := by
  unfold tailWord_680061
  simp only [CollatzResearch.WordTrace]
  refine ⟨24803862389262617017120037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16535908259508411344746691 24803862389262617017120037)
  ·
    refine ⟨4650724197986740690710007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24803862389262617017120037 4650724197986740690710007)
    ·
      refine ⟨6976086296980111036065011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4650724197986740690710007 6976086296980111036065011)
      ·
        refine ⟨10464129445470166554097517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976086296980111036065011 10464129445470166554097517)
        ·
          refine ⟨3924048542051312457786569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10464129445470166554097517 3924048542051312457786569)
          ·
            refine ⟨2943036406538484343339927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3924048542051312457786569 2943036406538484343339927)
            ·
              refine ⟨4414554609807726515009891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943036406538484343339927 4414554609807726515009891)
              ·
                refine ⟨6621831914711589772514837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414554609807726515009891 6621831914711589772514837)
                ·
                  refine ⟨310398371002105770586633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6621831914711589772514837 310398371002105770586633)
                  ·
                    rfl

theorem cell20_680061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_680061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680061 prefixEnd_680061 := by exact prefixLift 680061
  have htrace : WordTrace (prefixWord ++ tailWord_680061) baseStart_680061 baseEnd_680061 := by
    simpa [prefixWord, tailWord_680061, baseEnd_680061] using wordTrace_append hprefix tailTrace_680061
  have hstable : (prefixWord ++ tailWord_680061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680061).length < 2 ^ (prefixWord ++ tailWord_680061).sum := by decide
  have hdescent : baseEnd_680061 < baseStart_680061 := by decide
  rcases family_descends (prefixWord ++ tailWord_680061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680084 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_680084 : Nat := 118140960795 + 680084 * 2 ^ 59
def prefixEnd_680084 : Nat := 4983230072969 + 3 ^ 40 * 680084 * 2
def baseEnd_680084 : Nat := 310408868828819912819873

theorem tailTrace_680084 : CollatzResearch.WordTrace tailWord_680084 prefixEnd_680084 310408868828819912819873 := by
  unfold tailWord_680084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402350634089645972603653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16536467512119527963471537 12402350634089645972603653)
  ·
    refine ⟨2325440743891808619863185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12402350634089645972603653 2325440743891808619863185)
    ·
      refine ⟨1744080557918856464897389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2325440743891808619863185 1744080557918856464897389)
      ·
        refine ⟨654030209219571174336521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1744080557918856464897389 654030209219571174336521)
        ·
          refine ⟨490522656914678380752391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654030209219571174336521 490522656914678380752391)
          ·
            refine ⟨735783985372017571128587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490522656914678380752391 735783985372017571128587)
            ·
              refine ⟨1103675978058026356692881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735783985372017571128587 1103675978058026356692881)
              ·
                refine ⟨827756983543519767519661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103675978058026356692881 827756983543519767519661)
                ·
                  refine ⟨310408868828819912819873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827756983543519767519661 310408868828819912819873)
                  ·
                    rfl

theorem cell20_680084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_680084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680084 prefixEnd_680084 := by exact prefixLift 680084
  have htrace : WordTrace (prefixWord ++ tailWord_680084) baseStart_680084 baseEnd_680084 := by
    simpa [prefixWord, tailWord_680084, baseEnd_680084] using wordTrace_append hprefix tailTrace_680084
  have hstable : (prefixWord ++ tailWord_680084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680084).length < 2 ^ (prefixWord ++ tailWord_680084).sum := by decide
  have hdescent : baseEnd_680084 < baseStart_680084 := by decide
  rcases family_descends (prefixWord ++ tailWord_680084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680088 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_680088 : Nat := 118140960795 + 680088 * 2 ^ 59
def prefixEnd_680088 : Nat := 4983230072969 + 3 ^ 40 * 680088 * 2
def baseEnd_680088 : Nat := 310410694537813676686523

theorem tailTrace_680088 : CollatzResearch.WordTrace tailWord_680088 prefixEnd_680088 310410694537813676686523 := by
  unfold tailWord_680088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402423580082400314176459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16536564773443200418901945 12402423580082400314176459)
  ·
    refine ⟨18603635370123600471264689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12402423580082400314176459 18603635370123600471264689)
    ·
      refine ⟨13952726527592700353448517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18603635370123600471264689 13952726527592700353448517)
      ·
        refine ⟨2616136223923631316271597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13952726527592700353448517 2616136223923631316271597)
        ·
          refine ⟨981051083971361743601849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2616136223923631316271597 981051083971361743601849)
          ·
            refine ⟨735788312978521307701387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981051083971361743601849 735788312978521307701387)
            ·
              refine ⟨1103682469467781961552081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735788312978521307701387 1103682469467781961552081)
              ·
                refine ⟨827761852100836471164061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103682469467781961552081 827761852100836471164061)
                ·
                  refine ⟨310410694537813676686523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827761852100836471164061 310410694537813676686523)
                  ·
                    rfl

theorem cell20_680088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_680088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680088 prefixEnd_680088 := by exact prefixLift 680088
  have htrace : WordTrace (prefixWord ++ tailWord_680088) baseStart_680088 baseEnd_680088 := by
    simpa [prefixWord, tailWord_680088, baseEnd_680088] using wordTrace_append hprefix tailTrace_680088
  have hstable : (prefixWord ++ tailWord_680088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680088).length < 2 ^ (prefixWord ++ tailWord_680088).sum := by decide
  have hdescent : baseEnd_680088 < baseStart_680088 := by decide
  rcases family_descends (prefixWord ++ tailWord_680088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680092 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_680092 : Nat := 118140960795 + 680092 * 2 ^ 59
def prefixEnd_680092 : Nat := 4983230072969 + 3 ^ 40 * 680092 * 2
def baseEnd_680092 : Nat := 310412520246807440553173

theorem tailTrace_680092 : CollatzResearch.WordTrace tailWord_680092 prefixEnd_680092 310412520246807440553173 := by
  unfold tailWord_680092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402496526075154655749265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16536662034766872874332353 12402496526075154655749265)
  ·
    refine ⟨9301872394556365991811949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12402496526075154655749265 9301872394556365991811949)
    ·
      refine ⟨3488202147958637246929481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9301872394556365991811949 3488202147958637246929481)
      ·
        refine ⟨2616151610968977935197111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3488202147958637246929481 2616151610968977935197111)
        ·
          refine ⟨3924227416453466902795667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616151610968977935197111 3924227416453466902795667)
          ·
            refine ⟨5886341124680200354193501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924227416453466902795667 5886341124680200354193501)
            ·
              refine ⟨2207377921755075132822563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5886341124680200354193501 2207377921755075132822563)
              ·
                refine ⟨3311066882632612699233845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207377921755075132822563 3311066882632612699233845)
                ·
                  refine ⟨310412520246807440553173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311066882632612699233845 310412520246807440553173)
                  ·
                    rfl

theorem cell20_680092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_680092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680092 prefixEnd_680092 := by exact prefixLift 680092
  have htrace : WordTrace (prefixWord ++ tailWord_680092) baseStart_680092 baseEnd_680092 := by
    simpa [prefixWord, tailWord_680092, baseEnd_680092] using wordTrace_append hprefix tailTrace_680092
  have hstable : (prefixWord ++ tailWord_680092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680092).length < 2 ^ (prefixWord ++ tailWord_680092).sum := by decide
  have hdescent : baseEnd_680092 < baseStart_680092 := by decide
  rcases family_descends (prefixWord ++ tailWord_680092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680095 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 2]
def baseStart_680095 : Nat := 118140960795 + 680095 * 2 ^ 59
def prefixEnd_680095 : Nat := 4983230072969 + 3 ^ 40 * 680095 * 2
def baseEnd_680095 : Nat := 310413889528552763453161

theorem tailTrace_680095 : CollatzResearch.WordTrace tailWord_680095 prefixEnd_680095 310413889528552763453161 := by
  unfold tailWord_680095
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805102471139440823857739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16536734980759627215905159 24805102471139440823857739)
  ·
    refine ⟨37207653706709161235786609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24805102471139440823857739 37207653706709161235786609)
    ·
      refine ⟨27905740280031870926839957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37207653706709161235786609 27905740280031870926839957)
      ·
        refine ⟨1308081575626493949695623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27905740280031870926839957 1308081575626493949695623)
        ·
          refine ⟨1962122363439740924543435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308081575626493949695623 1962122363439740924543435)
          ·
            refine ⟨2943183545159611386815153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962122363439740924543435 2943183545159611386815153)
            ·
              refine ⟨2207387658869708540111365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2943183545159611386815153 2207387658869708540111365)
              ·
                refine ⟨413885186038070351270881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2207387658869708540111365 413885186038070351270881)
                ·
                  refine ⟨310413889528552763453161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413885186038070351270881 310413889528552763453161)
                  ·
                    rfl

theorem cell20_680095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 2].length) (baseStart_680095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680095 prefixEnd_680095 := by exact prefixLift 680095
  have htrace : WordTrace (prefixWord ++ tailWord_680095) baseStart_680095 baseEnd_680095 := by
    simpa [prefixWord, tailWord_680095, baseEnd_680095] using wordTrace_append hprefix tailTrace_680095
  have hstable : (prefixWord ++ tailWord_680095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680095).length < 2 ^ (prefixWord ++ tailWord_680095).sum := by decide
  have hdescent : baseEnd_680095 < baseStart_680095 := by decide
  rcases family_descends (prefixWord ++ tailWord_680095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680129 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 2]
def baseStart_680129 : Nat := 118140960795 + 680129 * 2 ^ 59
def prefixEnd_680129 : Nat := 4983230072969 + 3 ^ 40 * 680129 * 2
def baseEnd_680129 : Nat := 310429408054999756319689

theorem tailTrace_680129 : CollatzResearch.WordTrace tailWord_680129 prefixEnd_680129 310429408054999756319689 := by
  unfold tailWord_680129
  simp only [CollatzResearch.WordTrace]
  refine ⟨24806342553016264630595441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16537561702010843087063627 24806342553016264630595441)
  ·
    refine ⟨18604756914762198472946581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24806342553016264630595441 18604756914762198472946581)
    ·
      refine ⟨872097980379478053419371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18604756914762198472946581 872097980379478053419371)
      ·
        refine ⟨1308146970569217080129057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872097980379478053419371 1308146970569217080129057)
        ·
          refine ⟨981110227926912810096793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308146970569217080129057 981110227926912810096793)
          ·
            refine ⟨735832670945184607572595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981110227926912810096793 735832670945184607572595)
            ·
              refine ⟨1103749006417776911358893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735832670945184607572595 1103749006417776911358893)
              ·
                refine ⟨413905877406666341759585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1103749006417776911358893 413905877406666341759585)
                ·
                  refine ⟨310429408054999756319689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413905877406666341759585 310429408054999756319689)
                  ·
                    rfl

theorem cell20_680129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_680129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680129 prefixEnd_680129 := by exact prefixLift 680129
  have htrace : WordTrace (prefixWord ++ tailWord_680129) baseStart_680129 baseEnd_680129 := by
    simpa [prefixWord, tailWord_680129, baseEnd_680129] using wordTrace_append hprefix tailTrace_680129
  have hstable : (prefixWord ++ tailWord_680129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680129).length < 2 ^ (prefixWord ++ tailWord_680129).sum := by decide
  have hdescent : baseEnd_680129 < baseStart_680129 := by decide
  rcases family_descends (prefixWord ++ tailWord_680129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680140 : List Nat := [2, 2, 1, 6, 1, 2, 6]
def baseStart_680140 : Nat := 118140960795 + 680140 * 2 ^ 59
def prefixEnd_680140 : Nat := 4983230072969 + 3 ^ 40 * 680140 * 2
def baseEnd_680140 : Nat := 34492714306081400772553

theorem tailTrace_680140 : CollatzResearch.WordTrace tailWord_680140 prefixEnd_680140 34492714306081400772553 := by
  unfold tailWord_680140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403371877988206754622937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16537829170650942339497249 12403371877988206754622937)
  ·
    refine ⟨9302528908491155065967203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12403371877988206754622937 9302528908491155065967203)
    ·
      refine ⟨13953793362736732598950805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302528908491155065967203 13953793362736732598950805)
      ·
        refine ⟨654084063878284340575819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13953793362736732598950805 654084063878284340575819)
        ·
          refine ⟨981126095817426510863729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654084063878284340575819 981126095817426510863729)
          ·
            refine ⟨735844571863069883147797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981126095817426510863729 735844571863069883147797)
            ·
              refine ⟨34492714306081400772553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 735844571863069883147797 34492714306081400772553)
              ·
                rfl

theorem cell20_680140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_680140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680140 prefixEnd_680140 := by exact prefixLift 680140
  have htrace : WordTrace (prefixWord ++ tailWord_680140) baseStart_680140 baseEnd_680140 := by
    simpa [prefixWord, tailWord_680140, baseEnd_680140] using wordTrace_append hprefix tailTrace_680140
  have hstable : (prefixWord ++ tailWord_680140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680140).length < 2 ^ (prefixWord ++ tailWord_680140).sum := by decide
  have hdescent : baseEnd_680140 < baseStart_680140 := by decide
  rcases family_descends (prefixWord ++ tailWord_680140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680150 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_680150 : Nat := 118140960795 + 680150 * 2 ^ 59
def prefixEnd_680150 : Nat := 4983230072969 + 3 ^ 40 * 680150 * 2
def baseEnd_680150 : Nat := 310438993027217016619603

theorem tailTrace_680150 : CollatzResearch.WordTrace tailWord_680150 prefixEnd_680150 310438993027217016619603 := by
  unfold tailWord_680150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550444280371261576069369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16538072323960123478073269 1550444280371261576069369)
  ·
    refine ⟨1162833210278446182052027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1550444280371261576069369 1162833210278446182052027)
    ·
      refine ⟨1744249815417669273078041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162833210278446182052027 1744249815417669273078041)
      ·
        refine ⟨1308187361563251954808531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744249815417669273078041 1308187361563251954808531)
        ·
          refine ⟨1962281042344877932212797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308187361563251954808531 1962281042344877932212797)
          ·
            refine ⟨735855390879329224579799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1962281042344877932212797 735855390879329224579799)
            ·
              refine ⟨1103783086318993836869699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735855390879329224579799 1103783086318993836869699)
              ·
                refine ⟨1655674629478490755304549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103783086318993836869699 1655674629478490755304549)
                ·
                  refine ⟨310438993027217016619603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655674629478490755304549 310438993027217016619603)
                  ·
                    rfl

theorem cell20_680150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_680150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680150 prefixEnd_680150 := by exact prefixLift 680150
  have htrace : WordTrace (prefixWord ++ tailWord_680150) baseStart_680150 baseEnd_680150 := by
    simpa [prefixWord, tailWord_680150, baseEnd_680150] using wordTrace_append hprefix tailTrace_680150
  have hstable : (prefixWord ++ tailWord_680150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680150).length < 2 ^ (prefixWord ++ tailWord_680150).sum := by decide
  have hdescent : baseEnd_680150 < baseStart_680150 := by decide
  rcases family_descends (prefixWord ++ tailWord_680150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680154 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_680154 : Nat := 118140960795 + 680154 * 2 ^ 59
def prefixEnd_680154 : Nat := 4983230072969 + 3 ^ 40 * 680154 * 2
def baseEnd_680154 : Nat := 310440818736210780486253

theorem tailTrace_680154 : CollatzResearch.WordTrace tailWord_680154 prefixEnd_680154 310440818736210780486253 := by
  unfold tailWord_680154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201813594481423475063879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16538169585283795933503677 6201813594481423475063879)
  ·
    refine ⟨9302720391722135212595819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201813594481423475063879 9302720391722135212595819)
    ·
      refine ⟨13954080587583202818893729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302720391722135212595819 13954080587583202818893729)
      ·
        refine ⟨10465560440687402114170297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13954080587583202818893729 10465560440687402114170297)
        ·
          refine ⟨7849170330515551585627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10465560440687402114170297 7849170330515551585627723)
          ·
            refine ⟨11773755495773327378441585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849170330515551585627723 11773755495773327378441585)
            ·
              refine ⟨8830316621829995533831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11773755495773327378441585 8830316621829995533831189)
              ·
                refine ⟨413921091648281040648337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8830316621829995533831189 413921091648281040648337)
                ·
                  refine ⟨310440818736210780486253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413921091648281040648337 310440818736210780486253)
                  ·
                    rfl

theorem cell20_680154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_680154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680154 prefixEnd_680154 := by exact prefixLift 680154
  have htrace : WordTrace (prefixWord ++ tailWord_680154) baseStart_680154 baseEnd_680154 := by
    simpa [prefixWord, tailWord_680154, baseEnd_680154] using wordTrace_append hprefix tailTrace_680154
  have hstable : (prefixWord ++ tailWord_680154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680154).length < 2 ^ (prefixWord ++ tailWord_680154).sum := by decide
  have hdescent : baseEnd_680154 < baseStart_680154 := by decide
  rcases family_descends (prefixWord ++ tailWord_680154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680189 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_680189 : Nat := 118140960795 + 680189 * 2 ^ 59
def prefixEnd_680189 : Nat := 4983230072969 + 3 ^ 40 * 680189 * 2
def baseEnd_680189 : Nat := 310456793689906214319443

theorem tailTrace_680189 : CollatzResearch.WordTrace tailWord_680189 prefixEnd_680189 310456793689906214319443 := by
  unfold tailWord_680189
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808530932798894877779621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16539020621865929918519747 24808530932798894877779621)
  ·
    refine ⟨4651599549899792789583679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24808530932798894877779621 4651599549899792789583679)
    ·
      refine ⟨6977399324849689184375519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651599549899792789583679 6977399324849689184375519)
      ·
        refine ⟨10466098987274533776563279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6977399324849689184375519 10466098987274533776563279)
        ·
          refine ⟨15699148480911800664844919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10466098987274533776563279 15699148480911800664844919)
          ·
            refine ⟨23548722721367700997267379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15699148480911800664844919 23548722721367700997267379)
            ·
              refine ⟨35323084082051551495901069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23548722721367700997267379 35323084082051551495901069)
              ·
                refine ⟨13246156530769331810962901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35323084082051551495901069 13246156530769331810962901)
                ·
                  refine ⟨310456793689906214319443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13246156530769331810962901 310456793689906214319443)
                  ·
                    rfl

theorem cell20_680189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_680189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680189 prefixEnd_680189 := by exact prefixLift 680189
  have htrace : WordTrace (prefixWord ++ tailWord_680189) baseStart_680189 baseEnd_680189 := by
    simpa [prefixWord, tailWord_680189, baseEnd_680189] using wordTrace_append hprefix tailTrace_680189
  have hstable : (prefixWord ++ tailWord_680189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680189).length < 2 ^ (prefixWord ++ tailWord_680189).sum := by decide
  have hdescent : baseEnd_680189 < baseStart_680189 := by decide
  rcases family_descends (prefixWord ++ tailWord_680189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680199 : List Nat := [1, 1, 4, 5, 1, 8]
def baseStart_680199 : Nat := 118140960795 + 680199 * 2 ^ 59
def prefixEnd_680199 : Nat := 4983230072969 + 3 ^ 40 * 680199 * 2
def baseEnd_680199 : Nat := 11498568813421874962447

theorem tailTrace_680199 : CollatzResearch.WordTrace tailWord_680199 prefixEnd_680199 11498568813421874962447 := by
  unfold tailWord_680199
  simp only [CollatzResearch.WordTrace]
  refine ⟨24808895662762666585643651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16539263775175111057095767 24808895662762666585643651)
  ·
    refine ⟨37213343494143999878465477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24808895662762666585643651 37213343494143999878465477)
    ·
      refine ⟨6977501905151999977212277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37213343494143999878465477 6977501905151999977212277)
      ·
        refine ⟨654140803607999997863651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6977501905151999977212277 654140803607999997863651)
        ·
          refine ⟨981211205411999996795477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654140803607999997863651 981211205411999996795477)
          ·
            refine ⟨11498568813421874962447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 981211205411999996795477 11498568813421874962447)
            ·
              rfl

theorem cell20_680199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_680199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680199 prefixEnd_680199 := by exact prefixLift 680199
  have htrace : WordTrace (prefixWord ++ tailWord_680199) baseStart_680199 baseEnd_680199 := by
    simpa [prefixWord, tailWord_680199, baseEnd_680199] using wordTrace_append hprefix tailTrace_680199
  have hstable : (prefixWord ++ tailWord_680199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680199).length < 2 ^ (prefixWord ++ tailWord_680199).sum := by decide
  have hdescent : baseEnd_680199 < baseStart_680199 := by decide
  rcases family_descends (prefixWord ++ tailWord_680199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680209 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 2]
def baseStart_680209 : Nat := 118140960795 + 680209 * 2 ^ 59
def prefixEnd_680209 : Nat := 4983230072969 + 3 ^ 40 * 680209 * 2
def baseEnd_680209 : Nat := 310465922234875033652695

theorem tailTrace_680209 : CollatzResearch.WordTrace tailWord_680209 prefixEnd_680209 310465922234875033652695 := by
  unfold tailWord_680209
  simp only [CollatzResearch.WordTrace]
  refine ⟨24809260392726438293507681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16539506928484292195671787 24809260392726438293507681)
  ·
    refine ⟨18606945294544828720130761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24809260392726438293507681 18606945294544828720130761)
    ·
      refine ⟨13955208970908621540098071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18606945294544828720130761 13955208970908621540098071)
      ·
        refine ⟨20932813456362932310147107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13955208970908621540098071 20932813456362932310147107)
        ·
          refine ⟨31399220184544398465220661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20932813456362932310147107 31399220184544398465220661)
          ·
            refine ⟨2943676892301037356114437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31399220184544398465220661 2943676892301037356114437)
            ·
              refine ⟨551939417306444504271457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2943676892301037356114437 551939417306444504271457)
              ·
                refine ⟨413954562979833378203593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551939417306444504271457 413954562979833378203593)
                ·
                  refine ⟨310465922234875033652695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413954562979833378203593 310465922234875033652695)
                  ·
                    rfl

theorem cell20_680209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_680209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680209 prefixEnd_680209 := by exact prefixLift 680209
  have htrace : WordTrace (prefixWord ++ tailWord_680209) baseStart_680209 baseEnd_680209 := by
    simpa [prefixWord, tailWord_680209, baseEnd_680209] using wordTrace_append hprefix tailTrace_680209
  have hstable : (prefixWord ++ tailWord_680209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680209).length < 2 ^ (prefixWord ++ tailWord_680209).sum := by decide
  have hdescent : baseEnd_680209 < baseStart_680209 := by decide
  rcases family_descends (prefixWord ++ tailWord_680209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680257 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 3]
def baseStart_680257 : Nat := 118140960795 + 680257 * 2 ^ 59
def prefixEnd_680257 : Nat := 4983230072969 + 3 ^ 40 * 680257 * 2
def baseEnd_680257 : Nat := 310487830742800200052499

theorem tailTrace_680257 : CollatzResearch.WordTrace tailWord_680257 prefixEnd_680257 310487830742800200052499 := by
  unfold tailWord_680257
  simp only [CollatzResearch.WordTrace]
  refine ⟨24811011096552542491255025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16540674064368361660836683 24811011096552542491255025)
  ·
    refine ⟨18608258322414406868441269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24811011096552542491255025 18608258322414406868441269)
    ·
      refine ⟨1744524217726350643916369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18608258322414406868441269 1744524217726350643916369)
      ·
        refine ⟨1308393163294762982937277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1744524217726350643916369 1308393163294762982937277)
        ·
          refine ⟨490647436235536118601479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1308393163294762982937277 490647436235536118601479)
          ·
            refine ⟨735971154353304177902219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490647436235536118601479 735971154353304177902219)
            ·
              refine ⟨1103956731529956266853329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735971154353304177902219 1103956731529956266853329)
              ·
                refine ⟨827967548647467200139997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103956731529956266853329 827967548647467200139997)
                ·
                  refine ⟨310487830742800200052499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827967548647467200139997 310487830742800200052499)
                  ·
                    rfl

theorem cell20_680257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_680257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680257 prefixEnd_680257 := by exact prefixLift 680257
  have htrace : WordTrace (prefixWord ++ tailWord_680257) baseStart_680257 baseEnd_680257 := by
    simpa [prefixWord, tailWord_680257, baseEnd_680257] using wordTrace_append hprefix tailTrace_680257
  have hstable : (prefixWord ++ tailWord_680257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680257).length < 2 ^ (prefixWord ++ tailWord_680257).sum := by decide
  have hdescent : baseEnd_680257 < baseStart_680257 := by decide
  rcases family_descends (prefixWord ++ tailWord_680257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680268 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_680268 : Nat := 118140960795 + 680268 * 2 ^ 59
def prefixEnd_680268 : Nat := 4983230072969 + 3 ^ 40 * 680268 * 2
def baseEnd_680268 : Nat := 310492851442533050685787

theorem tailTrace_680268 : CollatzResearch.WordTrace tailWord_680268 prefixEnd_680268 310492851442533050685787 := by
  unfold tailWord_680268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405706149756345684952729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16540941533008460913270305 12405706149756345684952729)
  ·
    refine ⟨9304279612317259263714547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12405706149756345684952729 9304279612317259263714547)
    ·
      refine ⟨13956419418475888895571821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9304279612317259263714547 13956419418475888895571821)
      ·
        refine ⟨5233657281928458335839433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13956419418475888895571821 5233657281928458335839433)
        ·
          refine ⟨3925242961446343751879575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5233657281928458335839433 3925242961446343751879575)
          ·
            refine ⟨5887864442169515627819363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925242961446343751879575 5887864442169515627819363)
            ·
              refine ⟨8831796663254273441729045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5887864442169515627819363 8831796663254273441729045)
              ·
                refine ⟨413990468590044067581049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8831796663254273441729045 413990468590044067581049)
                ·
                  refine ⟨310492851442533050685787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413990468590044067581049 310492851442533050685787)
                  ·
                    rfl

theorem cell20_680268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_680268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680268 prefixEnd_680268 := by exact prefixLift 680268
  have htrace : WordTrace (prefixWord ++ tailWord_680268) baseStart_680268 baseEnd_680268 := by
    simpa [prefixWord, tailWord_680268, baseEnd_680268] using wordTrace_append hprefix tailTrace_680268
  have hstable : (prefixWord ++ tailWord_680268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680268).length < 2 ^ (prefixWord ++ tailWord_680268).sum := by decide
  have hdescent : baseEnd_680268 < baseStart_680268 := by decide
  rcases family_descends (prefixWord ++ tailWord_680268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680323 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 4]
def baseStart_680323 : Nat := 118140960795 + 680323 * 2 ^ 59
def prefixEnd_680323 : Nat := 4983230072969 + 3 ^ 40 * 680323 * 2
def baseEnd_680323 : Nat := 310517954941197303852229

theorem tailTrace_680323 : CollatzResearch.WordTrace tailWord_680323 prefixEnd_680323 310517954941197303852229 := by
  unfold tailWord_680323
  simp only [CollatzResearch.WordTrace]
  refine ⟨24813418314313435763157623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16542278876208957175438415 24813418314313435763157623)
  ·
    refine ⟨37220127471470153644736435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24813418314313435763157623 37220127471470153644736435)
    ·
      refine ⟨55830191207205230467104653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37220127471470153644736435 55830191207205230467104653)
      ·
        refine ⟨20936321702701961425164245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55830191207205230467104653 20936321702701961425164245)
        ·
          refine ⟨490695039907077220902287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20936321702701961425164245 490695039907077220902287)
          ·
            refine ⟨736042559860615831353431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490695039907077220902287 736042559860615831353431)
            ·
              refine ⟨1104063839790923747030147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736042559860615831353431 1104063839790923747030147)
              ·
                refine ⟨1656095759686385620545221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104063839790923747030147 1656095759686385620545221)
                ·
                  refine ⟨310517954941197303852229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656095759686385620545221 310517954941197303852229)
                  ·
                    rfl

theorem cell20_680323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 4].length) (baseStart_680323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680323 prefixEnd_680323 := by exact prefixLift 680323
  have htrace : WordTrace (prefixWord ++ tailWord_680323) baseStart_680323 baseEnd_680323 := by
    simpa [prefixWord, tailWord_680323, baseEnd_680323] using wordTrace_append hprefix tailTrace_680323
  have hstable : (prefixWord ++ tailWord_680323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680323).length < 2 ^ (prefixWord ++ tailWord_680323).sum := by decide
  have hdescent : baseEnd_680323 < baseStart_680323 := by decide
  rcases family_descends (prefixWord ++ tailWord_680323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680330 : List Nat := [3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_680330 : Nat := 118140960795 + 680330 * 2 ^ 59
def prefixEnd_680330 : Nat := 4983230072969 + 3 ^ 40 * 680330 * 2
def baseEnd_680330 : Nat := 103507049977312130206289

theorem tailTrace_680330 : CollatzResearch.WordTrace tailWord_680330 prefixEnd_680330 103507049977312130206289 := by
  unfold tailWord_680330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203418406322018989665611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16542449083525383972441629 6203418406322018989665611)
  ·
    refine ⟨9305127609483028484498417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6203418406322018989665611 9305127609483028484498417)
    ·
      refine ⟨6978845707112271363373813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9305127609483028484498417 6978845707112271363373813)
      ·
        refine ⟨654266785041775440316295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6978845707112271363373813 654266785041775440316295)
        ·
          refine ⟨981400177562663160474443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654266785041775440316295 981400177562663160474443)
          ·
            refine ⟨1472100266343994740711665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981400177562663160474443 1472100266343994740711665)
            ·
              refine ⟨1104075199757996055533749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472100266343994740711665 1104075199757996055533749)
              ·
                refine ⟨103507049977312130206289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104075199757996055533749 103507049977312130206289)
                ·
                  rfl

theorem cell20_680330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_680330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680330 prefixEnd_680330 := by exact prefixLift 680330
  have htrace : WordTrace (prefixWord ++ tailWord_680330) baseStart_680330 baseEnd_680330 := by
    simpa [prefixWord, tailWord_680330, baseEnd_680330] using wordTrace_append hprefix tailTrace_680330
  have hstable : (prefixWord ++ tailWord_680330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680330).length < 2 ^ (prefixWord ++ tailWord_680330).sum := by decide
  have hdescent : baseEnd_680330 < baseStart_680330 := by decide
  rcases family_descends (prefixWord ++ tailWord_680330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680406 : List Nat := [5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_680406 : Nat := 118140960795 + 680406 * 2 ^ 59
def prefixEnd_680406 : Nat := 4983230072969 + 3 ^ 40 * 680406 * 2
def baseEnd_680406 : Nat := 103518612800939301361741

theorem tailTrace_680406 : CollatzResearch.WordTrace tailWord_680406 prefixEnd_680406 103518612800939301361741 := by
  unfold tailWord_680406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551027848313296308651817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16544297048675160625619381 1551027848313296308651817)
  ·
    refine ⟨1163270886234972231488863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1551027848313296308651817 1163270886234972231488863)
    ·
      refine ⟨1744906329352458347233295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163270886234972231488863 1744906329352458347233295)
      ·
        refine ⟨2617359494028687520849943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744906329352458347233295 2617359494028687520849943)
        ·
          refine ⟨3926039241043031281274915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617359494028687520849943 3926039241043031281274915)
          ·
            refine ⟨5889058861564546921912373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926039241043031281274915 5889058861564546921912373)
            ·
              refine ⟨552099268271676273929285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5889058861564546921912373 552099268271676273929285)
              ·
                refine ⟨103518612800939301361741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552099268271676273929285 103518612800939301361741)
                ·
                  rfl

theorem cell20_680406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_680406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680406 prefixEnd_680406 := by exact prefixLift 680406
  have htrace : WordTrace (prefixWord ++ tailWord_680406) baseStart_680406 baseEnd_680406 := by
    simpa [prefixWord, tailWord_680406, baseEnd_680406] using wordTrace_append hprefix tailTrace_680406
  have hstable : (prefixWord ++ tailWord_680406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680406).length < 2 ^ (prefixWord ++ tailWord_680406).sum := by decide
  have hdescent : baseEnd_680406 < baseStart_680406 := by decide
  rcases family_descends (prefixWord ++ tailWord_680406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
