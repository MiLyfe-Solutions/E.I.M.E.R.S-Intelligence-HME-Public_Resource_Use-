import V185TrunkScan23Chunk1333

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7901179 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 4, 4]
def baseStart_7901179 : Nat := 118140960795 + 7901179 * 2 ^ 59
def prefixEnd_7901179 : Nat := 4983230072969 + 3 ^ 40 * 7901179 * 2
def baseEnd_7901179 : Nat := 1352367521403615778175215

theorem tailTrace_7901179 : CollatzResearch.WordTrace tailWord_7901179 prefixEnd_7901179 1352367521403615778175215 := by
  unfold tailWord_7901179
  simp only [CollatzResearch.WordTrace]
  refine ⟨288179673042385371785978591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192119782028256914523985727 288179673042385371785978591)
  ·
    refine ⟨432269509563578057678967887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288179673042385371785978591 432269509563578057678967887)
    ·
      refine ⟨648404264345367086518451831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432269509563578057678967887 648404264345367086518451831)
      ·
        refine ⟨972606396518050629777677747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648404264345367086518451831 972606396518050629777677747)
        ·
          refine ⟨1458909594777075944666516621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972606396518050629777677747 1458909594777075944666516621)
          ·
            refine ⟨547091098041403479249943733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458909594777075944666516621 547091098041403479249943733)
            ·
              refine ⟨51289790441381576179682225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 547091098041403479249943733 51289790441381576179682225)
              ·
                refine ⟨38467342831036182134761669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51289790441381576179682225 38467342831036182134761669)
                ·
                  refine ⟨7212626780819284150267813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38467342831036182134761669 7212626780819284150267813)
                  ·
                    refine ⟨1352367521403615778175215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212626780819284150267813 1352367521403615778175215)
                    ·
                      rfl

theorem cell23_7901179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 4].length) (baseStart_7901179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901179 prefixEnd_7901179 := by exact prefixLift 7901179
  have htrace : WordTrace (prefixWord ++ tailWord_7901179) baseStart_7901179 baseEnd_7901179 := by
    simpa [prefixWord, tailWord_7901179, baseEnd_7901179] using wordTrace_append hprefix tailTrace_7901179
  have hstable : (prefixWord ++ tailWord_7901179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901179).length < 2 ^ (prefixWord ++ tailWord_7901179).sum := by decide
  have hdescent : baseEnd_7901179 < baseStart_7901179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901189 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_7901189 : Nat := 118140960795 + 7901189 * 2 ^ 59
def prefixEnd_7901189 : Nat := 4983230072969 + 3 ^ 40 * 7901189 * 2
def baseEnd_7901189 : Nat := 4057107699017392295400599

theorem tailTrace_7901189 : CollatzResearch.WordTrace tailWord_7901189 prefixEnd_7901189 4057107699017392295400599 := by
  unfold tailWord_7901189
  simp only [CollatzResearch.WordTrace]
  refine ⟨288180037772349143493842621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192120025181566095662561747 288180037772349143493842621)
  ·
    refine ⟨108067514164630928810190983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288180037772349143493842621 108067514164630928810190983)
    ·
      refine ⟨162101271246946393215286475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108067514164630928810190983 162101271246946393215286475)
      ·
        refine ⟨243151906870419589822929713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162101271246946393215286475 243151906870419589822929713)
        ·
          refine ⟨182363930152814692367197285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243151906870419589822929713 182363930152814692367197285)
          ·
            refine ⟨34193236903652754818849491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182363930152814692367197285 34193236903652754818849491)
            ·
              refine ⟨51289855355479132228274237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34193236903652754818849491 51289855355479132228274237)
              ·
                refine ⟨19233695758304674585602839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51289855355479132228274237 19233695758304674585602839)
                ·
                  refine ⟨28850543637457011878404259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19233695758304674585602839 28850543637457011878404259)
                  ·
                    refine ⟨43275815456185517817606389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28850543637457011878404259 43275815456185517817606389)
                    ·
                      refine ⟨4057107699017392295400599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43275815456185517817606389 4057107699017392295400599)
                      ·
                        rfl

theorem cell23_7901189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_7901189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901189 prefixEnd_7901189 := by exact prefixLift 7901189
  have htrace : WordTrace (prefixWord ++ tailWord_7901189) baseStart_7901189 baseEnd_7901189 := by
    simpa [prefixWord, tailWord_7901189, baseEnd_7901189] using wordTrace_append hprefix tailTrace_7901189
  have hstable : (prefixWord ++ tailWord_7901189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901189).length < 2 ^ (prefixWord ++ tailWord_7901189).sum := by decide
  have hdescent : baseEnd_7901189 < baseStart_7901189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901196 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_7901196 : Nat := 118140960795 + 7901196 * 2 ^ 59
def prefixEnd_7901196 : Nat := 4983230072969 + 3 ^ 40 * 7901196 * 2
def baseEnd_7901196 : Nat := 1352370431127324589337689

theorem tailTrace_7901196 : CollatzResearch.WordTrace tailWord_7901196 prefixEnd_7901196 1352370431127324589337689 := by
  unfold tailWord_7901196
  simp only [CollatzResearch.WordTrace]
  refine ⟨144090146541661891844673721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192120195388882522459564961 144090146541661891844673721)
  ·
    refine ⟨108067609906246418883505291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144090146541661891844673721 108067609906246418883505291)
    ·
      refine ⟨162101414859369628325257937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108067609906246418883505291 162101414859369628325257937)
      ·
        refine ⟨121576061144527221243943453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162101414859369628325257937 121576061144527221243943453)
        ·
          refine ⟨45591022929197707966478795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121576061144527221243943453 45591022929197707966478795)
          ·
            refine ⟨68386534393796561949718193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45591022929197707966478795 68386534393796561949718193)
            ·
              refine ⟨51289900795347421462288645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68386534393796561949718193 51289900795347421462288645)
              ·
                refine ⟨9616856399127641524179121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51289900795347421462288645 9616856399127641524179121)
                ·
                  refine ⟨7212642299345731143134341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616856399127641524179121 7212642299345731143134341)
                  ·
                    refine ⟨1352370431127324589337689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212642299345731143134341 1352370431127324589337689)
                    ·
                      rfl

theorem cell23_7901196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_7901196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901196 prefixEnd_7901196 := by exact prefixLift 7901196
  have htrace : WordTrace (prefixWord ++ tailWord_7901196) baseStart_7901196 baseEnd_7901196 := by
    simpa [prefixWord, tailWord_7901196, baseEnd_7901196] using wordTrace_append hprefix tailTrace_7901196
  have hstable : (prefixWord ++ tailWord_7901196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901196).length < 2 ^ (prefixWord ++ tailWord_7901196).sum := by decide
  have hdescent : baseEnd_7901196 < baseStart_7901196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901203 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 3, 2, 2]
def baseStart_7901203 : Nat := 118140960795 + 7901203 * 2 ^ 59
def prefixEnd_7901203 : Nat := 4983230072969 + 3 ^ 40 * 7901203 * 2
def baseEnd_7901203 : Nat := 4057114887746555240625535

theorem tailTrace_7901203 : CollatzResearch.WordTrace tailWord_7901203 prefixEnd_7901203 4057114887746555240625535 := by
  unfold tailWord_7901203
  simp only [CollatzResearch.WordTrace]
  refine ⟨288180548394298423884852263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192120365596198949256568175 288180548394298423884852263)
  ·
    refine ⟨432270822591447635827278395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288180548394298423884852263 432270822591447635827278395)
    ·
      refine ⟨648406233887171453740917593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432270822591447635827278395 648406233887171453740917593)
      ·
        refine ⟨486304675415378590305688195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648406233887171453740917593 486304675415378590305688195)
        ·
          refine ⟨729457013123067885458532293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486304675415378590305688195 729457013123067885458532293)
          ·
            refine ⟨136773189960575228523474805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729457013123067885458532293 136773189960575228523474805)
            ·
              refine ⟨12822486558803927674075763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136773189960575228523474805 12822486558803927674075763)
              ·
                refine ⟨19233729838205891511113645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12822486558803927674075763 19233729838205891511113645)
                ·
                  refine ⟨7212648689327209316667617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19233729838205891511113645 7212648689327209316667617)
                  ·
                    refine ⟨5409486516995406987500713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212648689327209316667617 5409486516995406987500713)
                    ·
                      refine ⟨4057114887746555240625535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409486516995406987500713 4057114887746555240625535)
                      ·
                        rfl

theorem cell23_7901203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 2, 2].length) (baseStart_7901203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901203 prefixEnd_7901203 := by exact prefixLift 7901203
  have htrace : WordTrace (prefixWord ++ tailWord_7901203) baseStart_7901203 baseEnd_7901203 := by
    simpa [prefixWord, tailWord_7901203, baseEnd_7901203] using wordTrace_append hprefix tailTrace_7901203
  have hstable : (prefixWord ++ tailWord_7901203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901203).length < 2 ^ (prefixWord ++ tailWord_7901203).sum := by decide
  have hdescent : baseEnd_7901203 < baseStart_7901203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901213 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7901213 : Nat := 118140960795 + 7901213 * 2 ^ 59
def prefixEnd_7901213 : Nat := 4983230072969 + 3 ^ 40 * 7901213 * 2
def baseEnd_7901213 : Nat := 1352373340851033400500163

theorem tailTrace_7901213 : CollatzResearch.WordTrace tailWord_7901213 prefixEnd_7901213 1352373340851033400500163 := by
  unfold tailWord_7901213
  simp only [CollatzResearch.WordTrace]
  refine ⟨288180913124262195592716293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192120608749508130395144195 288180913124262195592716293)
  ·
    refine ⟨54033921210799161673634305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288180913124262195592716293 54033921210799161673634305)
    ·
      refine ⟨40525440908099371255225729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54033921210799161673634305 40525440908099371255225729)
      ·
        refine ⟨30394080681074528441419297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40525440908099371255225729 30394080681074528441419297)
        ·
          refine ⟨22795560510805896331064473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30394080681074528441419297 22795560510805896331064473)
          ·
            refine ⟨17096670383104422248298355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22795560510805896331064473 17096670383104422248298355)
            ·
              refine ⟨25645005574656633372447533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17096670383104422248298355 25645005574656633372447533)
              ·
                refine ⟨9616877090496237514667825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25645005574656633372447533 9616877090496237514667825)
                ·
                  refine ⟨7212657817872178136000869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616877090496237514667825 7212657817872178136000869)
                  ·
                    refine ⟨1352373340851033400500163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212657817872178136000869 1352373340851033400500163)
                    ·
                      rfl

theorem cell23_7901213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7901213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901213 prefixEnd_7901213 := by exact prefixLift 7901213
  have htrace : WordTrace (prefixWord ++ tailWord_7901213) baseStart_7901213 baseEnd_7901213 := by
    simpa [prefixWord, tailWord_7901213, baseEnd_7901213] using wordTrace_append hprefix tailTrace_7901213
  have hstable : (prefixWord ++ tailWord_7901213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901213).length < 2 ^ (prefixWord ++ tailWord_7901213).sum := by decide
  have hdescent : baseEnd_7901213 < baseStart_7901213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901220 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7901220 : Nat := 118140960795 + 7901220 * 2 ^ 59
def prefixEnd_7901220 : Nat := 4983230072969 + 3 ^ 40 * 7901220 * 2
def baseEnd_7901220 : Nat := 4057123616917681674112957

theorem tailTrace_7901220 : CollatzResearch.WordTrace tailWord_7901220 prefixEnd_7901220 4057123616917681674112957 := by
  unfold tailWord_7901220
  simp only [CollatzResearch.WordTrace]
  refine ⟨144090584217618417894110557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192120778956824557192147409 144090584217618417894110557)
  ·
    refine ⟨54033969081606906710291459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144090584217618417894110557 54033969081606906710291459)
    ·
      refine ⟨81050953622410360065437189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54033969081606906710291459 81050953622410360065437189)
      ·
        refine ⟨15197053804201942512269473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81050953622410360065437189 15197053804201942512269473)
        ·
          refine ⟨11397790353151456884202105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15197053804201942512269473 11397790353151456884202105)
          ·
            refine ⟨8548342764863592663151579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11397790353151456884202105 8548342764863592663151579)
            ·
              refine ⟨12822514147295388994727369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548342764863592663151579 12822514147295388994727369)
              ·
                refine ⟨9616885610471541746045527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12822514147295388994727369 9616885610471541746045527)
                ·
                  refine ⟨14425328415707312619068291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616885610471541746045527 14425328415707312619068291)
                  ·
                    refine ⟨21637992623560968928602437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14425328415707312619068291 21637992623560968928602437)
                    ·
                      refine ⟨4057123616917681674112957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21637992623560968928602437 4057123616917681674112957)
                      ·
                        rfl

theorem cell23_7901220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7901220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901220 prefixEnd_7901220 := by exact prefixLift 7901220
  have htrace : WordTrace (prefixWord ++ tailWord_7901220) baseStart_7901220 baseEnd_7901220 := by
    simpa [prefixWord, tailWord_7901220, baseEnd_7901220] using wordTrace_append hprefix tailTrace_7901220
  have hstable : (prefixWord ++ tailWord_7901220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901220).length < 2 ^ (prefixWord ++ tailWord_7901220).sum := by decide
  have hdescent : baseEnd_7901220 < baseStart_7901220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901240 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_7901240 : Nat := 118140960795 + 7901240 * 2 ^ 59
def prefixEnd_7901240 : Nat := 4983230072969 + 3 ^ 40 * 7901240 * 2
def baseEnd_7901240 : Nat := 4057133886530771595862865

theorem tailTrace_7901240 : CollatzResearch.WordTrace tailWord_7901240 prefixEnd_7901240 4057133886530771595862865 := by
  unfold tailWord_7901240
  simp only [CollatzResearch.WordTrace]
  refine ⟨144090948947582189601974587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192121265263442919469299449 144090948947582189601974587)
  ·
    refine ⟨216136423421373284402961881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144090948947582189601974587 216136423421373284402961881)
    ·
      refine ⟨162102317566029963302221411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216136423421373284402961881 162102317566029963302221411)
      ·
        refine ⟨243153476349044944953332117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162102317566029963302221411 243153476349044944953332117)
        ·
          refine ⟨11397819203861481794687443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243153476349044944953332117 11397819203861481794687443)
          ·
            refine ⟨17096728805792222692031165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397819203861481794687443 17096728805792222692031165)
            ·
              refine ⟨6411273302172083509511687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17096728805792222692031165 6411273302172083509511687)
              ·
                refine ⟨9616909953258125264267531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411273302172083509511687 9616909953258125264267531)
                ·
                  refine ⟨14425364929887187896401297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616909953258125264267531 14425364929887187896401297)
                  ·
                    refine ⟨10819023697415390922300973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14425364929887187896401297 10819023697415390922300973)
                    ·
                      refine ⟨4057133886530771595862865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10819023697415390922300973 4057133886530771595862865)
                      ·
                        rfl

theorem cell23_7901240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_7901240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901240 prefixEnd_7901240 := by exact prefixLift 7901240
  have htrace : WordTrace (prefixWord ++ tailWord_7901240) baseStart_7901240 baseEnd_7901240 := by
    simpa [prefixWord, tailWord_7901240, baseEnd_7901240] using wordTrace_append hprefix tailTrace_7901240
  have hstable : (prefixWord ++ tailWord_7901240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901240).length < 2 ^ (prefixWord ++ tailWord_7901240).sum := by decide
  have hdescent : baseEnd_7901240 < baseStart_7901240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901254 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7901254 : Nat := 118140960795 + 7901254 * 2 ^ 59
def prefixEnd_7901254 : Nat := 4983230072969 + 3 ^ 40 * 7901254 * 2
def baseEnd_7901254 : Nat := 4057141075259934541087801

theorem tailTrace_7901254 : CollatzResearch.WordTrace tailWord_7901254 prefixEnd_7901254 4057141075259934541087801 := by
  unfold tailWord_7901254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005700266159801862342463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192121605678075773063305877 9005700266159801862342463)
  ·
    refine ⟨13508550399239702793513695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005700266159801862342463 13508550399239702793513695)
    ·
      refine ⟨20262825598859554190270543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13508550399239702793513695 20262825598859554190270543)
      ·
        refine ⟨30394238398289331285405815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20262825598859554190270543 30394238398289331285405815)
        ·
          refine ⟨45591357597433996928108723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30394238398289331285405815 45591357597433996928108723)
          ·
            refine ⟨68387036396150995392163085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45591357597433996928108723 68387036396150995392163085)
            ·
              refine ⟨25645138648556623272061157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68387036396150995392163085 25645138648556623272061157)
              ·
                refine ⟨4808463496604366863511467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25645138648556623272061157 4808463496604366863511467)
                ·
                  refine ⟨7212695244906550295267201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808463496604366863511467 7212695244906550295267201)
                  ·
                    refine ⟨5409521433679912721450401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212695244906550295267201 5409521433679912721450401)
                    ·
                      refine ⟨4057141075259934541087801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409521433679912721450401 4057141075259934541087801)
                      ·
                        rfl

theorem cell23_7901254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7901254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901254 prefixEnd_7901254 := by exact prefixLift 7901254
  have htrace : WordTrace (prefixWord ++ tailWord_7901254) baseStart_7901254 baseEnd_7901254 := by
    simpa [prefixWord, tailWord_7901254, baseEnd_7901254] using wordTrace_append hprefix tailTrace_7901254
  have hstable : (prefixWord ++ tailWord_7901254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901254).length < 2 ^ (prefixWord ++ tailWord_7901254).sum := by decide
  have hdescent : baseEnd_7901254 < baseStart_7901254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901269 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7901269 : Nat := 118140960795 + 7901269 * 2 ^ 59
def prefixEnd_7901269 : Nat := 4983230072969 + 3 ^ 40 * 7901269 * 2
def baseEnd_7901269 : Nat := 1352382925823250660800077

theorem tailTrace_7901269 : CollatzResearch.WordTrace tailWord_7901269 prefixEnd_7901269 1352382925823250660800077 := by
  unfold tailWord_7901269
  simp only [CollatzResearch.WordTrace]
  refine ⟨288182955612059317156754861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192121970408039544771169907 288182955612059317156754861)
  ·
    refine ⟨108068608354522243933783073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288182955612059317156754861 108068608354522243933783073)
    ·
      refine ⟨81051456265891682950337305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108068608354522243933783073 81051456265891682950337305)
      ·
        refine ⟨60788592199418762212752979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81051456265891682950337305 60788592199418762212752979)
        ·
          refine ⟨91182888299128143319129469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60788592199418762212752979 91182888299128143319129469)
          ·
            refine ⟨34193583112173053744673551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91182888299128143319129469 34193583112173053744673551)
            ·
              refine ⟨51290374668259580617010327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34193583112173053744673551 51290374668259580617010327)
              ·
                refine ⟨76935562002389370925515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51290374668259580617010327 76935562002389370925515491)
                ·
                  refine ⟨115403343003584056388273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76935562002389370925515491 115403343003584056388273237)
                  ·
                    refine ⟨1352382925823250660800077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115403343003584056388273237 1352382925823250660800077)
                    ·
                      rfl

theorem cell23_7901269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7901269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901269 prefixEnd_7901269 := by exact prefixLift 7901269
  have htrace : WordTrace (prefixWord ++ tailWord_7901269) baseStart_7901269 baseEnd_7901269 := by
    simpa [prefixWord, tailWord_7901269, baseEnd_7901269] using wordTrace_append hprefix tailTrace_7901269
  have hstable : (prefixWord ++ tailWord_7901269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901269).length < 2 ^ (prefixWord ++ tailWord_7901269).sum := by decide
  have hdescent : baseEnd_7901269 < baseStart_7901269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901270 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7901270 : Nat := 118140960795 + 7901270 * 2 ^ 59
def prefixEnd_7901270 : Nat := 4983230072969 + 3 ^ 40 * 7901270 * 2
def baseEnd_7901270 : Nat := 4057149290950406478487727

theorem tailTrace_7901270 : CollatzResearch.WordTrace tailWord_7901270 prefixEnd_7901270 4057149290950406478487727 := by
  unfold tailWord_7901270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011437005315980895471329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192121994723370462885027509 18011437005315980895471329)
  ·
    refine ⟨13508577753986985671603497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18011437005315980895471329 13508577753986985671603497)
    ·
      refine ⟨10131433315490239253702623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13508577753986985671603497 10131433315490239253702623)
      ·
        refine ⟨15197149973235358880553935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131433315490239253702623 15197149973235358880553935)
        ·
          refine ⟨22795724959853038320830903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197149973235358880553935 22795724959853038320830903)
          ·
            refine ⟨34193587439779557481246355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22795724959853038320830903 34193587439779557481246355)
            ·
              refine ⟨51290381159669336221869533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34193587439779557481246355 51290381159669336221869533)
              ·
                refine ⟨19233892934876001083201075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51290381159669336221869533 19233892934876001083201075)
                ·
                  refine ⟨28850839402314001624801613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19233892934876001083201075 28850839402314001624801613)
                  ·
                    refine ⟨10819064775867750609300605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28850839402314001624801613 10819064775867750609300605)
                    ·
                      refine ⟨4057149290950406478487727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10819064775867750609300605 4057149290950406478487727)
                      ·
                        rfl

theorem cell23_7901270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7901270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901270 prefixEnd_7901270 := by exact prefixLift 7901270
  have htrace : WordTrace (prefixWord ++ tailWord_7901270) baseStart_7901270 baseEnd_7901270 := by
    simpa [prefixWord, tailWord_7901270, baseEnd_7901270] using wordTrace_append hprefix tailTrace_7901270
  have hstable : (prefixWord ++ tailWord_7901270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901270).length < 2 ^ (prefixWord ++ tailWord_7901270).sum := by decide
  have hdescent : baseEnd_7901270 < baseStart_7901270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901279 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_7901279 : Nat := 118140960795 + 7901279 * 2 ^ 59
def prefixEnd_7901279 : Nat := 4983230072969 + 3 ^ 40 * 7901279 * 2
def baseEnd_7901279 : Nat := 4057153912276296943275185

theorem tailTrace_7901279 : CollatzResearch.WordTrace tailWord_7901279 prefixEnd_7901279 4057153912276296943275185 := by
  unfold tailWord_7901279
  simp only [CollatzResearch.WordTrace]
  refine ⟨288183320342023088864618891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192122213561348725909745927 288183320342023088864618891)
  ·
    refine ⟨432274980513034633296928337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288183320342023088864618891 432274980513034633296928337)
    ·
      refine ⟨324206235384775974972696253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432274980513034633296928337 324206235384775974972696253)
      ·
        refine ⟨121577338269290990614761095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324206235384775974972696253 121577338269290990614761095)
        ·
          refine ⟨182366007403936485922141643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121577338269290990614761095 182366007403936485922141643)
          ·
            refine ⟨273549011105904728883212465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182366007403936485922141643 273549011105904728883212465)
            ·
              refine ⟨205161758329428546662409349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273549011105904728883212465 205161758329428546662409349)
              ·
                refine ⟨38467829686767852499201753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205161758329428546662409349 38467829686767852499201753)
                ·
                  refine ⟨28850872265075889374401315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38467829686767852499201753 28850872265075889374401315)
                  ·
                    refine ⟨43276308397613834061601973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28850872265075889374401315 43276308397613834061601973)
                    ·
                      refine ⟨4057153912276296943275185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43276308397613834061601973 4057153912276296943275185)
                      ·
                        rfl

theorem cell23_7901279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_7901279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901279 prefixEnd_7901279 := by exact prefixLift 7901279
  have htrace : WordTrace (prefixWord ++ tailWord_7901279) baseStart_7901279 baseEnd_7901279 := by
    simpa [prefixWord, tailWord_7901279, baseEnd_7901279] using wordTrace_append hprefix tailTrace_7901279
  have hstable : (prefixWord ++ tailWord_7901279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901279).length < 2 ^ (prefixWord ++ tailWord_7901279).sum := by decide
  have hdescent : baseEnd_7901279 < baseStart_7901279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901289 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_7901289 : Nat := 118140960795 + 7901289 * 2 ^ 59
def prefixEnd_7901289 : Nat := 4983230072969 + 3 ^ 40 * 7901289 * 2
def baseEnd_7901289 : Nat := 4057159047082841904150139

theorem tailTrace_7901289 : CollatzResearch.WordTrace tailWord_7901289 prefixEnd_7901289 4057159047082841904150139 := by
  unfold tailWord_7901289
  simp only [CollatzResearch.WordTrace]
  refine ⟨288183685071986860572482921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192122456714657907048321947 288183685071986860572482921)
  ·
    refine ⟨216137763803990145429362191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288183685071986860572482921 216137763803990145429362191)
    ·
      refine ⟨324206645705985218144043287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216137763803990145429362191 324206645705985218144043287)
      ·
        refine ⟨486309968558977827216064931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324206645705985218144043287 486309968558977827216064931)
        ·
          refine ⟨729464952838466740824097397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486309968558977827216064931 729464952838466740824097397)
          ·
            refine ⟨68387339328606256952259131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 729464952838466740824097397 68387339328606256952259131)
            ·
              refine ⟨102581008992909385428388697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68387339328606256952259131 102581008992909385428388697)
              ·
                refine ⟨76935756744682039071291523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102581008992909385428388697 76935756744682039071291523)
                ·
                  refine ⟨115403635117023058606937285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76935756744682039071291523 115403635117023058606937285)
                  ·
                    refine ⟨21638181584441823488800741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115403635117023058606937285 21638181584441823488800741)
                    ·
                      refine ⟨4057159047082841904150139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21638181584441823488800741 4057159047082841904150139)
                      ·
                        rfl

theorem cell23_7901289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_7901289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901289 prefixEnd_7901289 := by exact prefixLift 7901289
  have htrace : WordTrace (prefixWord ++ tailWord_7901289) baseStart_7901289 baseEnd_7901289 := by
    simpa [prefixWord, tailWord_7901289, baseEnd_7901289] using wordTrace_append hprefix tailTrace_7901289
  have hstable : (prefixWord ++ tailWord_7901289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901289).length < 2 ^ (prefixWord ++ tailWord_7901289).sum := by decide
  have hdescent : baseEnd_7901289 < baseStart_7901289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901293 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_7901293 : Nat := 118140960795 + 7901293 * 2 ^ 59
def prefixEnd_7901293 : Nat := 4983230072969 + 3 ^ 40 * 7901293 * 2
def baseEnd_7901293 : Nat := 4057161101005459888500121

theorem tailTrace_7901293 : CollatzResearch.WordTrace tailWord_7901293 prefixEnd_7901293 4057161101005459888500121 := by
  unfold tailWord_7901293
  simp only [CollatzResearch.WordTrace]
  refine ⟨288183830963972369255628533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192122553975981579503752355 288183830963972369255628533)
  ·
    refine ⟨27017234152872409617715175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288183830963972369255628533 27017234152872409617715175)
    ·
      refine ⟨40525851229308614426572763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27017234152872409617715175 40525851229308614426572763)
      ·
        refine ⟨60788776843962921639859145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40525851229308614426572763 60788776843962921639859145)
        ·
          refine ⟨45591582632972191229894359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60788776843962921639859145 45591582632972191229894359)
          ·
            refine ⟨68387373949458286844841539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45591582632972191229894359 68387373949458286844841539)
            ·
              refine ⟨102581060924187430267262309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68387373949458286844841539 102581060924187430267262309)
              ·
                refine ⟨19233948923285143175111683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102581060924187430267262309 19233948923285143175111683)
                ·
                  refine ⟨28850923384927714762667525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19233948923285143175111683 28850923384927714762667525)
                  ·
                    refine ⟨5409548134673946518000161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28850923384927714762667525 5409548134673946518000161)
                    ·
                      refine ⟨4057161101005459888500121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409548134673946518000161 4057161101005459888500121)
                      ·
                        rfl

theorem cell23_7901293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_7901293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901293 prefixEnd_7901293 := by exact prefixLift 7901293
  have htrace : WordTrace (prefixWord ++ tailWord_7901293) baseStart_7901293 baseEnd_7901293 := by
    simpa [prefixWord, tailWord_7901293, baseEnd_7901293] using wordTrace_append hprefix tailTrace_7901293
  have hstable : (prefixWord ++ tailWord_7901293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901293).length < 2 ^ (prefixWord ++ tailWord_7901293).sum := by decide
  have hdescent : baseEnd_7901293 < baseStart_7901293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901316 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 7]
def baseStart_7901316 : Nat := 118140960795 + 7901316 * 2 ^ 59
def prefixEnd_7901316 : Nat := 4983230072969 + 3 ^ 40 * 7901316 * 2
def baseEnd_7901316 : Nat := 450796990117834810945835

theorem tailTrace_7901316 : CollatzResearch.WordTrace tailWord_7901316 prefixEnd_7901316 450796990117834810945835 := by
  unfold tailWord_7901316
  simp only [CollatzResearch.WordTrace]
  refine ⟨144092334921444522091857901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192123113228592696122477201 144092334921444522091857901)
  ·
    refine ⟨54034625595541695784446713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144092334921444522091857901 54034625595541695784446713)
    ·
      refine ⟨40525969196656271838335035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54034625595541695784446713 40525969196656271838335035)
      ·
        refine ⟨60788953794984407757502553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40525969196656271838335035 60788953794984407757502553)
        ·
          refine ⟨45591715346238305818126915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60788953794984407757502553 45591715346238305818126915)
          ·
            refine ⟨68387573019357458727190373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45591715346238305818126915 68387573019357458727190373)
            ·
              refine ⟨12822669941129523511348195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68387573019357458727190373 12822669941129523511348195)
              ·
                refine ⟨19234004911694285267022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12822669941129523511348195 19234004911694285267022293)
                ·
                  refine ⟨450796990117834810945835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19234004911694285267022293 450796990117834810945835)
                  ·
                    rfl

theorem cell23_7901316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_7901316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901316 prefixEnd_7901316 := by exact prefixLift 7901316
  have htrace : WordTrace (prefixWord ++ tailWord_7901316) baseStart_7901316 baseEnd_7901316 := by
    simpa [prefixWord, tailWord_7901316, baseEnd_7901316] using wordTrace_append hprefix tailTrace_7901316
  have hstable : (prefixWord ++ tailWord_7901316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901316).length < 2 ^ (prefixWord ++ tailWord_7901316).sum := by decide
  have hdescent : baseEnd_7901316 < baseStart_7901316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901378 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7901378 : Nat := 118140960795 + 7901378 * 2 ^ 59
def prefixEnd_7901378 : Nat := 4983230072969 + 3 ^ 40 * 7901378 * 2
def baseEnd_7901378 : Nat := 4057204746861092055937231

theorem tailTrace_7901378 : CollatzResearch.WordTrace tailWord_7901378 prefixEnd_7901378 4057204746861092055937231 := by
  unfold tailWord_7901378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72046732792166107193118197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192124620779109619181648525 72046732792166107193118197)
  ·
    refine ⟨6754381199265572549354831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72046732792166107193118197 6754381199265572549354831)
    ·
      refine ⟨10131571798898358824032247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6754381199265572549354831 10131571798898358824032247)
      ·
        refine ⟨15197357698347538236048371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131571798898358824032247 15197357698347538236048371)
        ·
          refine ⟨22796036547521307354072557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197357698347538236048371 22796036547521307354072557)
          ·
            refine ⟨8548513705320490257777209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22796036547521307354072557 8548513705320490257777209)
            ·
              refine ⟨6411385278990367693332907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548513705320490257777209 6411385278990367693332907)
              ·
                refine ⟨9617077918485551539999361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411385278990367693332907 9617077918485551539999361)
                ·
                  refine ⟨7212808438864163654999521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617077918485551539999361 7212808438864163654999521)
                  ·
                    refine ⟨5409606329148122741249641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212808438864163654999521 5409606329148122741249641)
                    ·
                      refine ⟨4057204746861092055937231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409606329148122741249641 4057204746861092055937231)
                      ·
                        rfl

theorem cell23_7901378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7901378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901378 prefixEnd_7901378 := by exact prefixLift 7901378
  have htrace : WordTrace (prefixWord ++ tailWord_7901378) baseStart_7901378 baseEnd_7901378 := by
    simpa [prefixWord, tailWord_7901378, baseEnd_7901378] using wordTrace_append hprefix tailTrace_7901378
  have hstable : (prefixWord ++ tailWord_7901378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901378).length < 2 ^ (prefixWord ++ tailWord_7901378).sum := by decide
  have hdescent : baseEnd_7901378 < baseStart_7901378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_7901379 : Nat := 118140960795 + 7901379 * 2 ^ 59
def prefixEnd_7901379 : Nat := 4983230072969 + 3 ^ 40 * 7901379 * 2
def baseEnd_7901379 : Nat := 4057205260341746552024725

theorem tailTrace_7901379 : CollatzResearch.WordTrace tailWord_7901379 prefixEnd_7901379 4057205260341746552024725 := by
  unfold tailWord_7901379
  simp only [CollatzResearch.WordTrace]
  refine ⟨288186967641660805943259191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192124645094440537295506127 288186967641660805943259191)
  ·
    refine ⟨432280451462491208914888787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288186967641660805943259191 432280451462491208914888787)
    ·
      refine ⟨648420677193736813372333181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432280451462491208914888787 648420677193736813372333181)
      ·
        refine ⟨243157753947651305014624943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648420677193736813372333181 243157753947651305014624943)
        ·
          refine ⟨364736630921476957521937415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243157753947651305014624943 364736630921476957521937415)
          ·
            refine ⟨547104946382215436282906123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364736630921476957521937415 547104946382215436282906123)
            ·
              refine ⟨820657419573323154424359185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547104946382215436282906123 820657419573323154424359185)
              ·
                refine ⟨615493064679992365818269389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820657419573323154424359185 615493064679992365818269389)
                ·
                  refine ⟨230809899254997137181851021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615493064679992365818269389 230809899254997137181851021)
                  ·
                    refine ⟨86553712220623926443194133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230809899254997137181851021 86553712220623926443194133)
                    ·
                      refine ⟨4057205260341746552024725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86553712220623926443194133 4057205260341746552024725)
                      ·
                        rfl

theorem cell23_7901379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_7901379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901379 prefixEnd_7901379 := by exact prefixLift 7901379
  have htrace : WordTrace (prefixWord ++ tailWord_7901379) baseStart_7901379 baseEnd_7901379 := by
    simpa [prefixWord, tailWord_7901379, baseEnd_7901379] using wordTrace_append hprefix tailTrace_7901379
  have hstable : (prefixWord ++ tailWord_7901379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901379).length < 2 ^ (prefixWord ++ tailWord_7901379).sum := by decide
  have hdescent : baseEnd_7901379 < baseStart_7901379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901423 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 6]
def baseStart_7901423 : Nat := 118140960795 + 7901423 * 2 ^ 59
def prefixEnd_7901423 : Nat := 4983230072969 + 3 ^ 40 * 7901423 * 2
def baseEnd_7901423 : Nat := 450803094832282708874947

theorem tailTrace_7901423 : CollatzResearch.WordTrace tailWord_7901423 prefixEnd_7901423 450803094832282708874947 := by
  unfold tailWord_7901423
  simp only [CollatzResearch.WordTrace]
  refine ⟨288188572453501401457860923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192125714969000934305240615 288188572453501401457860923)
  ·
    refine ⟨432282858680252102186791385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288188572453501401457860923 432282858680252102186791385)
    ·
      refine ⟨324212144010189076640093539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432282858680252102186791385 324212144010189076640093539)
      ·
        refine ⟨486318216015283614960140309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324212144010189076640093539 486318216015283614960140309)
        ·
          refine ⟨22796166375716419451256577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 486318216015283614960140309 22796166375716419451256577)
          ·
            refine ⟨17097124781787314588442433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22796166375716419451256577 17097124781787314588442433)
            ·
              refine ⟨12822843586340485941331825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17097124781787314588442433 12822843586340485941331825)
              ·
                refine ⟨9617132689755364455998869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12822843586340485941331825 9617132689755364455998869)
                ·
                  refine ⟨450803094832282708874947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9617132689755364455998869 450803094832282708874947)
                  ·
                    rfl

theorem cell23_7901423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 6].length) (baseStart_7901423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901423 prefixEnd_7901423 := by exact prefixLift 7901423
  have htrace : WordTrace (prefixWord ++ tailWord_7901423) baseStart_7901423 baseEnd_7901423 := by
    simpa [prefixWord, tailWord_7901423, baseEnd_7901423] using wordTrace_append hprefix tailTrace_7901423
  have hstable : (prefixWord ++ tailWord_7901423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901423).length < 2 ^ (prefixWord ++ tailWord_7901423).sum := by decide
  have hdescent : baseEnd_7901423 < baseStart_7901423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901443 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 5, 2]
def baseStart_7901443 : Nat := 118140960795 + 7901443 * 2 ^ 59
def prefixEnd_7901443 : Nat := 4983230072969 + 3 ^ 40 * 7901443 * 2
def baseEnd_7901443 : Nat := 4057238123103634301624431

theorem tailTrace_7901443 : CollatzResearch.WordTrace tailWord_7901443 prefixEnd_7901443 4057238123103634301624431 := by
  unfold tailWord_7901443
  simp only [CollatzResearch.WordTrace]
  refine ⟨288189301913428944873588983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192126201275619296582392655 288189301913428944873588983)
  ·
    refine ⟨432283952870143417310383475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288189301913428944873588983 432283952870143417310383475)
    ·
      refine ⟨648425929305215125965575213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432283952870143417310383475 648425929305215125965575213)
      ·
        refine ⟨243159723489455672237090705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648425929305215125965575213 243159723489455672237090705)
        ·
          refine ⟨182369792617091754177818029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243159723489455672237090705 182369792617091754177818029)
          ·
            refine ⟨68388672231409407816681761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182369792617091754177818029 68388672231409407816681761)
            ·
              refine ⟨51291504173557055862511321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68388672231409407816681761 51291504173557055862511321)
              ·
                refine ⟨38468628130167791896883491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51291504173557055862511321 38468628130167791896883491)
                ·
                  refine ⟨57702942195251687845325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38468628130167791896883491 57702942195251687845325237)
                  ·
                    refine ⟨5409650830804845735499241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57702942195251687845325237 5409650830804845735499241)
                    ·
                      refine ⟨4057238123103634301624431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409650830804845735499241 4057238123103634301624431)
                      ·
                        rfl

theorem cell23_7901443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_7901443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901443 prefixEnd_7901443 := by exact prefixLift 7901443
  have htrace : WordTrace (prefixWord ++ tailWord_7901443) baseStart_7901443 baseEnd_7901443 := by
    simpa [prefixWord, tailWord_7901443, baseEnd_7901443] using wordTrace_append hprefix tailTrace_7901443
  have hstable : (prefixWord ++ tailWord_7901443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901443).length < 2 ^ (prefixWord ++ tailWord_7901443).sum := by decide
  have hdescent : baseEnd_7901443 < baseStart_7901443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901493 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7901493 : Nat := 118140960795 + 7901493 * 2 ^ 59
def prefixEnd_7901493 : Nat := 4983230072969 + 3 ^ 40 * 7901493 * 2
def baseEnd_7901493 : Nat := 4057263797136359105999201

theorem tailTrace_7901493 : CollatzResearch.WordTrace tailWord_7901493 prefixEnd_7901493 4057263797136359105999201 := by
  unfold tailWord_7901493
  simp only [CollatzResearch.WordTrace]
  refine ⟨288191125563247803412909133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192127417042165202275272755 288191125563247803412909133)
  ·
    refine ⟨108071672086217926279840925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288191125563247803412909133 108071672086217926279840925)
    ·
      refine ⟨40526877032331722354940347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108071672086217926279840925 40526877032331722354940347)
      ·
        refine ⟨60790315548497583532410521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40526877032331722354940347 60790315548497583532410521)
        ·
          refine ⟨45592736661373187649307891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60790315548497583532410521 45592736661373187649307891)
          ·
            refine ⟨68389104992059781473961837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45592736661373187649307891 68389104992059781473961837)
            ·
              refine ⟨25645914372022418052735689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68389104992059781473961837 25645914372022418052735689)
              ·
                refine ⟨19234435779016813539551767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25645914372022418052735689 19234435779016813539551767)
                ·
                  refine ⟨28851653668525220309327651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19234435779016813539551767 28851653668525220309327651)
                  ·
                    refine ⟨43277480502787830463991477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28851653668525220309327651 43277480502787830463991477)
                    ·
                      refine ⟨4057263797136359105999201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43277480502787830463991477 4057263797136359105999201)
                      ·
                        rfl

theorem cell23_7901493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7901493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901493 prefixEnd_7901493 := by exact prefixLift 7901493
  have htrace : WordTrace (prefixWord ++ tailWord_7901493) baseStart_7901493 baseEnd_7901493 := by
    simpa [prefixWord, tailWord_7901493, baseEnd_7901493] using wordTrace_append hprefix tailTrace_7901493
  have hstable : (prefixWord ++ tailWord_7901493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901493).length < 2 ^ (prefixWord ++ tailWord_7901493).sum := by decide
  have hdescent : baseEnd_7901493 < baseStart_7901493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901540 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_7901540 : Nat := 118140960795 + 7901540 * 2 ^ 59
def prefixEnd_7901540 : Nat := 4983230072969 + 3 ^ 40 * 7901540 * 2
def baseEnd_7901540 : Nat := 4057287930727120422111485

theorem tailTrace_7901540 : CollatzResearch.WordTrace tailWord_7901540 prefixEnd_7901540 4057287930727120422111485 := by
  unfold tailWord_7901540
  simp only [CollatzResearch.WordTrace]
  refine ⟨144096419897038765219935037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192128559862718353626580049 144096419897038765219935037)
  ·
    refine ⟨54036157461389536957475639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144096419897038765219935037 54036157461389536957475639)
    ·
      refine ⟨81054236192084305436213459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54036157461389536957475639 81054236192084305436213459)
      ·
        refine ⟨121581354288126458154320189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81054236192084305436213459 121581354288126458154320189)
        ·
          refine ⟨45593007858047421807870071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121581354288126458154320189 45593007858047421807870071)
          ·
            refine ⟨68389511787071132711805107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45593007858047421807870071 68389511787071132711805107)
            ·
              refine ⟨102584267680606699067707661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68389511787071132711805107 102584267680606699067707661)
              ·
                refine ⟨38469100380227512150390373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102584267680606699067707661 38469100380227512150390373)
                ·
                  refine ⟨7212956321292658528198195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38469100380227512150390373 7212956321292658528198195)
                  ·
                    refine ⟨10819434481938987792297293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7212956321292658528198195 10819434481938987792297293)
                    ·
                      refine ⟨4057287930727120422111485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10819434481938987792297293 4057287930727120422111485)
                      ·
                        rfl

theorem cell23_7901540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_7901540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901540 prefixEnd_7901540 := by exact prefixLift 7901540
  have htrace : WordTrace (prefixWord ++ tailWord_7901540) baseStart_7901540 baseEnd_7901540 := by
    simpa [prefixWord, tailWord_7901540, baseEnd_7901540] using wordTrace_append hprefix tailTrace_7901540
  have hstable : (prefixWord ++ tailWord_7901540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901540).length < 2 ^ (prefixWord ++ tailWord_7901540).sum := by decide
  have hdescent : baseEnd_7901540 < baseStart_7901540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901541 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_7901541 : Nat := 118140960795 + 7901541 * 2 ^ 59
def prefixEnd_7901541 : Nat := 4983230072969 + 3 ^ 40 * 7901541 * 2
def baseEnd_7901541 : Nat := 4057288444207774918198981

theorem tailTrace_7901541 : CollatzResearch.WordTrace tailWord_7901541 prefixEnd_7901541 4057288444207774918198981 := by
  unfold tailWord_7901541
  simp only [CollatzResearch.WordTrace]
  refine ⟨288192876267073907610656477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192128584178049271740437651 288192876267073907610656477)
  ·
    refine ⟨108072328600152715353996179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288192876267073907610656477 108072328600152715353996179)
    ·
      refine ⟨162108492900229073030994269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108072328600152715353996179 162108492900229073030994269)
      ·
        refine ⟨60790684837585902386622851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162108492900229073030994269 60790684837585902386622851)
        ·
          refine ⟨91186027256378853579934277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60790684837585902386622851 91186027256378853579934277)
          ·
            refine ⟨17097380110571035046237677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91186027256378853579934277 17097380110571035046237677)
            ·
              refine ⟨6411517541464138142339129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17097380110571035046237677 6411517541464138142339129)
              ·
                refine ⟨4808638156098103606754347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411517541464138142339129 4808638156098103606754347)
                ·
                  refine ⟨7212957234147155410131521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808638156098103606754347 7212957234147155410131521)
                  ·
                    refine ⟨5409717925610366557598641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7212957234147155410131521 5409717925610366557598641)
                    ·
                      refine ⟨4057288444207774918198981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409717925610366557598641 4057288444207774918198981)
                      ·
                        rfl

theorem cell23_7901541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_7901541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901541 prefixEnd_7901541 := by exact prefixLift 7901541
  have htrace : WordTrace (prefixWord ++ tailWord_7901541) baseStart_7901541 baseEnd_7901541 := by
    simpa [prefixWord, tailWord_7901541, baseEnd_7901541] using wordTrace_append hprefix tailTrace_7901541
  have hstable : (prefixWord ++ tailWord_7901541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901541).length < 2 ^ (prefixWord ++ tailWord_7901541).sum := by decide
  have hdescent : baseEnd_7901541 < baseStart_7901541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901580 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_7901580 : Nat := 118140960795 + 7901580 * 2 ^ 59
def prefixEnd_7901580 : Nat := 4983230072969 + 3 ^ 40 * 7901580 * 2
def baseEnd_7901580 : Nat := 4057308469953300265611301

theorem tailTrace_7901580 : CollatzResearch.WordTrace tailWord_7901580 prefixEnd_7901580 4057308469953300265611301 := by
  unfold tailWord_7901580
  simp only [CollatzResearch.WordTrace]
  refine ⟨144097149356966308635663097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192129532475955078180884129 144097149356966308635663097)
  ·
    refine ⟨108072862017724731476747323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144097149356966308635663097 108072862017724731476747323)
    ·
      refine ⟨162109293026587097215120985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108072862017724731476747323 162109293026587097215120985)
      ·
        refine ⟨121581969769940322911340739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162109293026587097215120985 121581969769940322911340739)
        ·
          refine ⟨182372954654910484367011109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121581969769940322911340739 182372954654910484367011109)
          ·
            refine ⟨34194928997795715818814583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182372954654910484367011109 34194928997795715818814583)
            ·
              refine ⟨51292393496693573728221875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34194928997795715818814583 51292393496693573728221875)
              ·
                refine ⟨76938590245040360592332813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51292393496693573728221875 76938590245040360592332813)
                ·
                  refine ⟨28851971341890135222124805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76938590245040360592332813 28851971341890135222124805)
                  ·
                    refine ⟨5409744626604400354148401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28851971341890135222124805 5409744626604400354148401)
                    ·
                      refine ⟨4057308469953300265611301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409744626604400354148401 4057308469953300265611301)
                      ·
                        rfl

theorem cell23_7901580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_7901580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901580 prefixEnd_7901580 := by exact prefixLift 7901580
  have htrace : WordTrace (prefixWord ++ tailWord_7901580) baseStart_7901580 baseEnd_7901580 := by
    simpa [prefixWord, tailWord_7901580, baseEnd_7901580] using wordTrace_append hprefix tailTrace_7901580
  have hstable : (prefixWord ++ tailWord_7901580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901580).length < 2 ^ (prefixWord ++ tailWord_7901580).sum := by decide
  have hdescent : baseEnd_7901580 < baseStart_7901580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901593 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_7901593 : Nat := 118140960795 + 7901593 * 2 ^ 59
def prefixEnd_7901593 : Nat := 4983230072969 + 3 ^ 40 * 7901593 * 2
def baseEnd_7901593 : Nat := 4057315145201808714748741

theorem tailTrace_7901593 : CollatzResearch.WordTrace tailWord_7901593 prefixEnd_7901593 4057315145201808714748741 := by
  unfold tailWord_7901593
  simp only [CollatzResearch.WordTrace]
  refine ⟨288194772862885520491549433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192129848575257013661032955 288194772862885520491549433)
  ·
    refine ⟨216146079647164140368662075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288194772862885520491549433 216146079647164140368662075)
    ·
      refine ⟨324219119470746210552993113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216146079647164140368662075 324219119470746210552993113)
      ·
        refine ⟨243164339603059657914744835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324219119470746210552993113 243164339603059657914744835)
        ·
          refine ⟨364746509404589486872117253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243164339603059657914744835 364746509404589486872117253)
          ·
            refine ⟨68389970513360528788521985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364746509404589486872117253 68389970513360528788521985)
            ·
              refine ⟨51292477885020396591391489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68389970513360528788521985 51292477885020396591391489)
              ·
                refine ⟨38469358413765297443543617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51292477885020396591391489 38469358413765297443543617)
                ·
                  refine ⟨28852018810323973082657713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38469358413765297443543617 28852018810323973082657713)
                  ·
                    refine ⟨21639014107742979811993285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28852018810323973082657713 21639014107742979811993285)
                    ·
                      refine ⟨4057315145201808714748741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21639014107742979811993285 4057315145201808714748741)
                      ·
                        rfl

theorem cell23_7901593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_7901593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901593 prefixEnd_7901593 := by exact prefixLift 7901593
  have htrace : WordTrace (prefixWord ++ tailWord_7901593) baseStart_7901593 baseEnd_7901593 := by
    simpa [prefixWord, tailWord_7901593, baseEnd_7901593] using wordTrace_append hprefix tailTrace_7901593
  have hstable : (prefixWord ++ tailWord_7901593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901593).length < 2 ^ (prefixWord ++ tailWord_7901593).sum := by decide
  have hdescent : baseEnd_7901593 < baseStart_7901593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901680 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_7901680 : Nat := 118140960795 + 7901680 * 2 ^ 59
def prefixEnd_7901680 : Nat := 4983230072969 + 3 ^ 40 * 7901680 * 2
def baseEnd_7901680 : Nat := 1352453272672916624786947

theorem tailTrace_7901680 : CollatzResearch.WordTrace tailWord_7901680 prefixEnd_7901680 1352453272672916624786947 := by
  unfold tailWord_7901680
  simp only [CollatzResearch.WordTrace]
  refine ⟨144098973006785167174983247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192131964009046889566644329 144098973006785167174983247)
  ·
    refine ⟨216148459510177750762474871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144098973006785167174983247 216148459510177750762474871)
    ·
      refine ⟨324222689265266626143712307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216148459510177750762474871 324222689265266626143712307)
      ·
        refine ⟨486334033897899939215568461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324222689265266626143712307 486334033897899939215568461)
        ·
          refine ⟨182375262711712477205838173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486334033897899939215568461 182375262711712477205838173)
          ·
            refine ⟨68390723516892178952189315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182375262711712477205838173 68390723516892178952189315)
            ·
              refine ⟨102586085275338268428283973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68390723516892178952189315 102586085275338268428283973)
              ·
                refine ⟨19234890989125925330303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102586085275338268428283973 19234890989125925330303245)
                ·
                  refine ⟨7213084120922221998863717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19234890989125925330303245 7213084120922221998863717)
                  ·
                    refine ⟨1352453272672916624786947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213084120922221998863717 1352453272672916624786947)
                    ·
                      rfl

theorem cell23_7901680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_7901680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901680 prefixEnd_7901680 := by exact prefixLift 7901680
  have htrace : WordTrace (prefixWord ++ tailWord_7901680) baseStart_7901680 baseEnd_7901680 := by
    simpa [prefixWord, tailWord_7901680, baseEnd_7901680] using wordTrace_append hprefix tailTrace_7901680
  have hstable : (prefixWord ++ tailWord_7901680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901680).length < 2 ^ (prefixWord ++ tailWord_7901680).sum := by decide
  have hdescent : baseEnd_7901680 < baseStart_7901680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901683 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_7901683 : Nat := 118140960795 + 7901683 * 2 ^ 59
def prefixEnd_7901683 : Nat := 4983230072969 + 3 ^ 40 * 7901683 * 2
def baseEnd_7901683 : Nat := 4057361358460713362623327

theorem tailTrace_7901683 : CollatzResearch.WordTrace tailWord_7901683 prefixEnd_7901683 4057361358460713362623327 := by
  unfold tailWord_7901683
  simp only [CollatzResearch.WordTrace]
  refine ⟨288198055432559465862325703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192132036955039643908217135 288198055432559465862325703)
  ·
    refine ⟨432297083148839198793488555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288198055432559465862325703 432297083148839198793488555)
    ·
      refine ⟨648445624723258798190232833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432297083148839198793488555 648445624723258798190232833)
      ·
        refine ⟨486334218542444098642674625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648445624723258798190232833 486334218542444098642674625)
        ·
          refine ⟨364750663906833073982005969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486334218542444098642674625 364750663906833073982005969)
          ·
            refine ⟨273562997930124805486504477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364750663906833073982005969 273562997930124805486504477)
            ·
              refine ⟨102586124223796802057439179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273562997930124805486504477 102586124223796802057439179)
              ·
                refine ⟨153879186335695203086158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102586124223796802057439179 153879186335695203086158769)
                ·
                  refine ⟨115409389751771402314619077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153879186335695203086158769 115409389751771402314619077)
                  ·
                    refine ⟨21639260578457137933991077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115409389751771402314619077 21639260578457137933991077)
                    ·
                      refine ⟨4057361358460713362623327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21639260578457137933991077 4057361358460713362623327)
                      ·
                        rfl

theorem cell23_7901683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_7901683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901683 prefixEnd_7901683 := by exact prefixLift 7901683
  have htrace : WordTrace (prefixWord ++ tailWord_7901683) baseStart_7901683 baseEnd_7901683 := by
    simpa [prefixWord, tailWord_7901683, baseEnd_7901683] using wordTrace_append hprefix tailTrace_7901683
  have hstable : (prefixWord ++ tailWord_7901683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901683).length < 2 ^ (prefixWord ++ tailWord_7901683).sum := by decide
  have hdescent : baseEnd_7901683 < baseStart_7901683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901693 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 10]
def baseStart_7901693 : Nat := 118140960795 + 7901693 * 2 ^ 59
def prefixEnd_7901693 : Nat := 4983230072969 + 3 ^ 40 * 7901693 * 2
def baseEnd_7901693 : Nat := 450818499251917591499809

theorem tailTrace_7901693 : CollatzResearch.WordTrace tailWord_7901693 prefixEnd_7901693 450818499251917591499809 := by
  unfold tailWord_7901693
  simp only [CollatzResearch.WordTrace]
  refine ⟨288198420162523237570189733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192132280108348825046793155 288198420162523237570189733)
  ·
    refine ⟨54037203780473107044410575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288198420162523237570189733 54037203780473107044410575)
    ·
      refine ⟨81055805670709660566615863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54037203780473107044410575 81055805670709660566615863)
      ·
        refine ⟨121583708506064490849923795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81055805670709660566615863 121583708506064490849923795)
        ·
          refine ⟨182375562759096736274885693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121583708506064490849923795 182375562759096736274885693)
          ·
            refine ⟨68390836034661276103082135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182375562759096736274885693 68390836034661276103082135)
            ·
              refine ⟨102586254051991914154623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68390836034661276103082135 102586254051991914154623203)
              ·
                refine ⟨153879381077987871231934805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102586254051991914154623203 153879381077987871231934805)
                ·
                  refine ⟨450818499251917591499809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153879381077987871231934805 450818499251917591499809)
                  ·
                    rfl

theorem cell23_7901693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_7901693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901693 prefixEnd_7901693 := by exact prefixLift 7901693
  have htrace : WordTrace (prefixWord ++ tailWord_7901693) baseStart_7901693 baseEnd_7901693 := by
    simpa [prefixWord, tailWord_7901693, baseEnd_7901693] using wordTrace_append hprefix tailTrace_7901693
  have hstable : (prefixWord ++ tailWord_7901693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901693).length < 2 ^ (prefixWord ++ tailWord_7901693).sum := by decide
  have hdescent : baseEnd_7901693 < baseStart_7901693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901707 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3]
def baseStart_7901707 : Nat := 118140960795 + 7901707 * 2 ^ 59
def prefixEnd_7901707 : Nat := 4983230072969 + 3 ^ 40 * 7901707 * 2
def baseEnd_7901707 : Nat := 4057373681996421268723217

theorem tailTrace_7901707 : CollatzResearch.WordTrace tailWord_7901707 prefixEnd_7901707 4057373681996421268723217 := by
  unfold tailWord_7901707
  simp only [CollatzResearch.WordTrace]
  refine ⟨288198930784472517961199375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192132620522981678640799583 288198930784472517961199375)
  ·
    refine ⟨432298396176708776941799063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288198930784472517961199375 432298396176708776941799063)
    ·
      refine ⟨648447594265063165412698595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432298396176708776941799063 648447594265063165412698595)
      ·
        refine ⟨972671391397594748119047893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648447594265063165412698595 972671391397594748119047893)
        ·
          refine ⟨22796985735881126909040185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 972671391397594748119047893 22796985735881126909040185)
          ·
            refine ⟨17097739301910845181780139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22796985735881126909040185 17097739301910845181780139)
            ·
              refine ⟨25646608952866267772670209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17097739301910845181780139 25646608952866267772670209)
              ·
                refine ⟨19234956714649700829502657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25646608952866267772670209 19234956714649700829502657)
                ·
                  refine ⟨14426217535987275622126993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19234956714649700829502657 14426217535987275622126993)
                  ·
                    refine ⟨10819663151990456716595245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14426217535987275622126993 10819663151990456716595245)
                    ·
                      refine ⟨4057373681996421268723217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10819663151990456716595245 4057373681996421268723217)
                      ·
                        rfl

theorem cell23_7901707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 3].length) (baseStart_7901707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901707 prefixEnd_7901707 := by exact prefixLift 7901707
  have htrace : WordTrace (prefixWord ++ tailWord_7901707) baseStart_7901707 baseEnd_7901707 := by
    simpa [prefixWord, tailWord_7901707, baseEnd_7901707] using wordTrace_append hprefix tailTrace_7901707
  have hstable : (prefixWord ++ tailWord_7901707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901707).length < 2 ^ (prefixWord ++ tailWord_7901707).sum := by decide
  have hdescent : baseEnd_7901707 < baseStart_7901707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901710 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_7901710 : Nat := 118140960795 + 7901710 * 2 ^ 59
def prefixEnd_7901710 : Nat := 4983230072969 + 3 ^ 40 * 7901710 * 2
def baseEnd_7901710 : Nat := 450819469159820528553967

theorem tailTrace_7901710 : CollatzResearch.WordTrace tailWord_7901710 prefixEnd_7901710 450819469159820528553967 := by
  unfold tailWord_7901710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024880025432706184194823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192132693468974432982372389 36024880025432706184194823)
  ·
    refine ⟨54037320038149059276292235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024880025432706184194823 54037320038149059276292235)
    ·
      refine ⟨81055980057223588914438353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54037320038149059276292235 81055980057223588914438353)
      ·
        refine ⟨60791985042917691685828765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81055980057223588914438353 60791985042917691685828765)
        ·
          refine ⟨22796994391094134382185787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60791985042917691685828765 22796994391094134382185787)
          ·
            refine ⟨34195491586641201573278681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22796994391094134382185787 34195491586641201573278681)
            ·
              refine ⟨25646618689980901179959011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34195491586641201573278681 25646618689980901179959011)
              ·
                refine ⟨38469928034971351769938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25646618689980901179959011 38469928034971351769938517)
                ·
                  refine ⟨450819469159820528553967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38469928034971351769938517 450819469159820528553967)
                  ·
                    rfl

theorem cell23_7901710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_7901710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901710 prefixEnd_7901710 := by exact prefixLift 7901710
  have htrace : WordTrace (prefixWord ++ tailWord_7901710) baseStart_7901710 baseEnd_7901710 := by
    simpa [prefixWord, tailWord_7901710, baseEnd_7901710] using wordTrace_append hprefix tailTrace_7901710
  have hstable : (prefixWord ++ tailWord_7901710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901710).length < 2 ^ (prefixWord ++ tailWord_7901710).sum := by decide
  have hdescent : baseEnd_7901710 < baseStart_7901710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901713 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_7901713 : Nat := 118140960795 + 7901713 * 2 ^ 59
def prefixEnd_7901713 : Nat := 4983230072969 + 3 ^ 40 * 7901713 * 2
def baseEnd_7901713 : Nat := 4057376762880348245248189

theorem tailTrace_7901713 : CollatzResearch.WordTrace tailWord_7901713 prefixEnd_7901713 4057376762880348245248189 := by
  unfold tailWord_7901713
  simp only [CollatzResearch.WordTrace]
  refine ⟨288199149622450780985917793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192132766414967187323945195 288199149622450780985917793)
  ·
    refine ⟨216149362216838085739438345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288199149622450780985917793 216149362216838085739438345)
    ·
      refine ⟨162112021662628564304578759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216149362216838085739438345 162112021662628564304578759)
      ·
        refine ⟨243168032493942846456868139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162112021662628564304578759 243168032493942846456868139)
        ·
          refine ⟨364752048740914269685302209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243168032493942846456868139 364752048740914269685302209)
          ·
            refine ⟨273564036555685702263976657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364752048740914269685302209 273564036555685702263976657)
            ·
              refine ⟨205173027416764276697982493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273564036555685702263976657 205173027416764276697982493)
              ·
                refine ⟨76939885281286603761743435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205173027416764276697982493 76939885281286603761743435)
                ·
                  refine ⟨115409827921929905642615153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76939885281286603761743435 115409827921929905642615153)
                  ·
                    refine ⟨86557370941447429231961365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115409827921929905642615153 86557370941447429231961365)
                    ·
                      refine ⟨4057376762880348245248189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86557370941447429231961365 4057376762880348245248189)
                      ·
                        rfl

theorem cell23_7901713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_7901713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901713 prefixEnd_7901713 := by exact prefixLift 7901713
  have htrace : WordTrace (prefixWord ++ tailWord_7901713) baseStart_7901713 baseEnd_7901713 := by
    simpa [prefixWord, tailWord_7901713, baseEnd_7901713] using wordTrace_append hprefix tailTrace_7901713
  have hstable : (prefixWord ++ tailWord_7901713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901713).length < 2 ^ (prefixWord ++ tailWord_7901713).sum := by decide
  have hdescent : baseEnd_7901713 < baseStart_7901713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901771 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 1, 1, 3]
def baseStart_7901771 : Nat := 118140960795 + 7901771 * 2 ^ 59
def prefixEnd_7901771 : Nat := 4983230072969 + 3 ^ 40 * 7901771 * 2
def baseEnd_7901771 : Nat := 4057406544758309018322923

theorem tailTrace_7901771 : CollatzResearch.WordTrace tailWord_7901771 prefixEnd_7901771 4057406544758309018322923 := by
  unfold tailWord_7901771
  simp only [CollatzResearch.WordTrace]
  refine ⟨288201265056240656891529167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192134176704160437927686111 288201265056240656891529167)
  ·
    refine ⟨432301897584360985337293751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288201265056240656891529167 432301897584360985337293751)
    ·
      refine ⟨648452846376541478005940627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432301897584360985337293751 648452846376541478005940627)
      ·
        refine ⟨972679269564812217008910941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648452846376541478005940627 972679269564812217008910941)
        ·
          refine ⟨364754726086804581378341603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972679269564812217008910941 364754726086804581378341603)
          ·
            refine ⟨547132089130206872067512405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364754726086804581378341603 547132089130206872067512405)
            ·
              refine ⟨6411704169494611782041161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 547132089130206872067512405 6411704169494611782041161)
              ·
                refine ⟨4808778127120958836530871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411704169494611782041161 4808778127120958836530871)
                ·
                  refine ⟨7213167190681438254796307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808778127120958836530871 7213167190681438254796307)
                  ·
                    refine ⟨10819750786022157382194461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213167190681438254796307 10819750786022157382194461)
                    ·
                      refine ⟨4057406544758309018322923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10819750786022157382194461 4057406544758309018322923)
                      ·
                        rfl

theorem cell23_7901771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 1, 3].length) (baseStart_7901771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901771 prefixEnd_7901771 := by exact prefixLift 7901771
  have htrace : WordTrace (prefixWord ++ tailWord_7901771) baseStart_7901771 baseEnd_7901771 := by
    simpa [prefixWord, tailWord_7901771, baseEnd_7901771] using wordTrace_append hprefix tailTrace_7901771
  have hstable : (prefixWord ++ tailWord_7901771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901771).length < 2 ^ (prefixWord ++ tailWord_7901771).sum := by decide
  have hdescent : baseEnd_7901771 < baseStart_7901771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901821 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_7901821 : Nat := 118140960795 + 7901821 * 2 ^ 59
def prefixEnd_7901821 : Nat := 4983230072969 + 3 ^ 40 * 7901821 * 2
def baseEnd_7901821 : Nat := 1352477406263677940899231

theorem tailTrace_7901821 : CollatzResearch.WordTrace tailWord_7901821 prefixEnd_7901821 1352477406263677940899231 := by
  unfold tailWord_7901821
  simp only [CollatzResearch.WordTrace]
  refine ⟨288203088706059515430849317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192135392470706343620566211 288203088706059515430849317)
  ·
    refine ⟨54038079132386159143284247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288203088706059515430849317 54038079132386159143284247)
    ·
      refine ⟨81057118698579238714926371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54038079132386159143284247 81057118698579238714926371)
      ·
        refine ⟨121585678047868858072389557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81057118698579238714926371 121585678047868858072389557)
        ·
          refine ⟨11398657316987705444286521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121585678047868858072389557 11398657316987705444286521)
          ·
            refine ⟨8548992987740779083214891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398657316987705444286521 8548992987740779083214891)
            ·
              refine ⟨12823489481611168624822337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548992987740779083214891 12823489481611168624822337)
              ·
                refine ⟨9617617111208376468616753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12823489481611168624822337 9617617111208376468616753)
                ·
                  refine ⟨7213212833406282351462565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617617111208376468616753 7213212833406282351462565)
                  ·
                    refine ⟨1352477406263677940899231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213212833406282351462565 1352477406263677940899231)
                    ·
                      rfl

theorem cell23_7901821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_7901821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901821 prefixEnd_7901821 := by exact prefixLift 7901821
  have htrace : WordTrace (prefixWord ++ tailWord_7901821) baseStart_7901821 baseEnd_7901821 := by
    simpa [prefixWord, tailWord_7901821, baseEnd_7901821] using wordTrace_append hprefix tailTrace_7901821
  have hstable : (prefixWord ++ tailWord_7901821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901821).length < 2 ^ (prefixWord ++ tailWord_7901821).sum := by decide
  have hdescent : baseEnd_7901821 < baseStart_7901821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901828 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7901828 : Nat := 118140960795 + 7901828 * 2 ^ 59
def prefixEnd_7901828 : Nat := 4983230072969 + 3 ^ 40 * 7901828 * 2
def baseEnd_7901828 : Nat := 4057435813155615295310161

theorem tailTrace_7901828 : CollatzResearch.WordTrace tailWord_7901828 prefixEnd_7901828 4057435813155615295310161 := by
  unfold tailWord_7901828
  simp only [CollatzResearch.WordTrace]
  refine ⟨144101672008517077813177069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192135562678022770417569425 144101672008517077813177069)
  ·
    refine ⟨54038127003193904179941401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144101672008517077813177069 54038127003193904179941401)
    ·
      refine ⟨40528595252395428134956051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54038127003193904179941401 40528595252395428134956051)
      ·
        refine ⟨60792892878593142202434077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40528595252395428134956051 60792892878593142202434077)
        ·
          refine ⟨22797334829472428325912779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60792892878593142202434077 22797334829472428325912779)
          ·
            refine ⟨34196002244208642488869169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22797334829472428325912779 34196002244208642488869169)
            ·
              refine ⟨25647001683156481866651877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34196002244208642488869169 25647001683156481866651877)
              ·
                refine ⟨4808812815591840349997227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25647001683156481866651877 4808812815591840349997227)
                ·
                  refine ⟨7213219223387760524995841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808812815591840349997227 7213219223387760524995841)
                  ·
                    refine ⟨5409914417540820393746881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7213219223387760524995841 5409914417540820393746881)
                    ·
                      refine ⟨4057435813155615295310161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5409914417540820393746881 4057435813155615295310161)
                      ·
                        rfl

theorem cell23_7901828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7901828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901828 prefixEnd_7901828 := by exact prefixLift 7901828
  have htrace : WordTrace (prefixWord ++ tailWord_7901828) baseStart_7901828 baseEnd_7901828 := by
    simpa [prefixWord, tailWord_7901828, baseEnd_7901828] using wordTrace_append hprefix tailTrace_7901828
  have hstable : (prefixWord ++ tailWord_7901828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901828).length < 2 ^ (prefixWord ++ tailWord_7901828).sum := by decide
  have hdescent : baseEnd_7901828 < baseStart_7901828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901937 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_7901937 : Nat := 118140960795 + 7901937 * 2 ^ 59
def prefixEnd_7901937 : Nat := 4983230072969 + 3 ^ 40 * 7901937 * 2
def baseEnd_7901937 : Nat := 1352497260848985122949053

theorem tailTrace_7901937 : CollatzResearch.WordTrace tailWord_7901937 prefixEnd_7901937 1352497260848985122949053 := by
  unfold tailWord_7901937
  simp only [CollatzResearch.WordTrace]
  refine ⟨288207319573639267242072065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192138213049092844828048043 288207319573639267242072065)
  ·
    refine ⟨216155489680229450431554049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288207319573639267242072065 216155489680229450431554049)
    ·
      refine ⟨162116617260172087823665537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216155489680229450431554049 162116617260172087823665537)
      ·
        refine ⟨121587462945129065867749153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162116617260172087823665537 121587462945129065867749153)
        ·
          refine ⟨91190597208846799400811865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121587462945129065867749153 91190597208846799400811865)
          ·
            refine ⟨68392947906635099550608899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91190597208846799400811865 68392947906635099550608899)
            ·
              refine ⟨102589421859952649325913349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68392947906635099550608899 102589421859952649325913349)
              ·
                refine ⟨19235516598741121748608753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102589421859952649325913349 19235516598741121748608753)
                ·
                  refine ⟨14426637449055841311456565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19235516598741121748608753 14426637449055841311456565)
                  ·
                    refine ⟨1352497260848985122949053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14426637449055841311456565 1352497260848985122949053)
                    ·
                      rfl

theorem cell23_7901937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_7901937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901937 prefixEnd_7901937 := by exact prefixLift 7901937
  have htrace : WordTrace (prefixWord ++ tailWord_7901937) baseStart_7901937 baseEnd_7901937 := by
    simpa [prefixWord, tailWord_7901937, baseEnd_7901937] using wordTrace_append hprefix tailTrace_7901937
  have hstable : (prefixWord ++ tailWord_7901937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901937).length < 2 ^ (prefixWord ++ tailWord_7901937).sum := by decide
  have hdescent : baseEnd_7901937 < baseStart_7901937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901957 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_7901957 : Nat := 118140960795 + 7901957 * 2 ^ 59
def prefixEnd_7901957 : Nat := 4983230072969 + 3 ^ 40 * 7901957 * 2
def baseEnd_7901957 : Nat := 4057502052160045290597067

theorem tailTrace_7901957 : CollatzResearch.WordTrace tailWord_7901957 prefixEnd_7901957 4057502052160045290597067 := by
  unfold tailWord_7901957
  simp only [CollatzResearch.WordTrace]
  refine ⟨288208049033566810657800125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192138699355711207105200083 288208049033566810657800125)
  ·
    refine ⟨108078018387587553996675047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288208049033566810657800125 108078018387587553996675047)
    ·
      refine ⟨162117027581381330995012571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108078018387587553996675047 162117027581381330995012571)
      ·
        refine ⟨243175541372071996492518857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162117027581381330995012571 243175541372071996492518857)
        ·
          refine ⟨182381656029053997369389143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243175541372071996492518857 182381656029053997369389143)
          ·
            refine ⟨273572484043580996054083715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182381656029053997369389143 273572484043580996054083715)
            ·
              refine ⟨410358726065371494081125573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273572484043580996054083715 410358726065371494081125573)
              ·
                refine ⟨76942261137257155140211045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410358726065371494081125573 76942261137257155140211045)
                ·
                  refine ⟨14426673963235716588789571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76942261137257155140211045 14426673963235716588789571)
                  ·
                    refine ⟨21640010944853574883184357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14426673963235716588789571 21640010944853574883184357)
                    ·
                      refine ⟨4057502052160045290597067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21640010944853574883184357 4057502052160045290597067)
                      ·
                        rfl

theorem cell23_7901957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_7901957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7901957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7901957 prefixEnd_7901957 := by exact prefixLift 7901957
  have htrace : WordTrace (prefixWord ++ tailWord_7901957) baseStart_7901957 baseEnd_7901957 := by
    simpa [prefixWord, tailWord_7901957, baseEnd_7901957] using wordTrace_append hprefix tailTrace_7901957
  have hstable : (prefixWord ++ tailWord_7901957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901957).length < 2 ^ (prefixWord ++ tailWord_7901957).sum := by decide
  have hdescent : baseEnd_7901957 < baseStart_7901957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902001 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 1, 4]
def baseStart_7902001 : Nat := 118140960795 + 7902001 * 2 ^ 59
def prefixEnd_7902001 : Nat := 4983230072969 + 3 ^ 40 * 7902001 * 2
def baseEnd_7902001 : Nat := 1352508215102947706148955

theorem tailTrace_7902001 : CollatzResearch.WordTrace tailWord_7902001 prefixEnd_7902001 1352508215102947706148955 := by
  unfold tailWord_7902001
  simp only [CollatzResearch.WordTrace]
  refine ⟨288209653845407406172401857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192139769230271604114934571 288209653845407406172401857)
  ·
    refine ⟨216157240384055554629301393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288209653845407406172401857 216157240384055554629301393)
    ·
      refine ⟨162117930288041665971976045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216157240384055554629301393 162117930288041665971976045)
      ·
        refine ⟨60794223858015624739491017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162117930288041665971976045 60794223858015624739491017)
        ·
          refine ⟨45595667893511718554618263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60794223858015624739491017 45595667893511718554618263)
          ·
            refine ⟨68393501840267577831927395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45595667893511718554618263 68393501840267577831927395)
            ·
              refine ⟨102590252760401366747891093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68393501840267577831927395 102590252760401366747891093)
              ·
                refine ⟨4808918098143814066307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102590252760401366747891093 4808918098143814066307395)
                ·
                  refine ⟨7213377147215721099461093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808918098143814066307395 7213377147215721099461093)
                  ·
                    refine ⟨1352508215102947706148955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213377147215721099461093 1352508215102947706148955)
                    ·
                      rfl

theorem cell23_7902001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_7902001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902001 prefixEnd_7902001 := by exact prefixLift 7902001
  have htrace : WordTrace (prefixWord ++ tailWord_7902001) baseStart_7902001 baseEnd_7902001 := by
    simpa [prefixWord, tailWord_7902001, baseEnd_7902001] using wordTrace_append hprefix tailTrace_7902001
  have hstable : (prefixWord ++ tailWord_7902001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902001).length < 2 ^ (prefixWord ++ tailWord_7902001).sum := by decide
  have hdescent : baseEnd_7902001 < baseStart_7902001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902051 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7902051 : Nat := 118140960795 + 7902051 * 2 ^ 59
def prefixEnd_7902051 : Nat := 4983230072969 + 3 ^ 40 * 7902051 * 2
def baseEnd_7902051 : Nat := 4057550319341567922821635

theorem tailTrace_7902051 : CollatzResearch.WordTrace tailWord_7902051 prefixEnd_7902051 4057550319341567922821635 := by
  unfold tailWord_7902051
  simp only [CollatzResearch.WordTrace]
  refine ⟨288211477495226264711722007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192140984996817509807814671 288211477495226264711722007)
  ·
    refine ⟨432317216242839397067583011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288211477495226264711722007 432317216242839397067583011)
    ·
      refine ⟨648475824364259095601374517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432317216242839397067583011 648475824364259095601374517)
      ·
        refine ⟨60794608534149290212628861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 648475824364259095601374517 60794608534149290212628861)
        ·
          refine ⟨22797978200305983829735823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60794608534149290212628861 22797978200305983829735823)
          ·
            refine ⟨34196967300458975744603735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22797978200305983829735823 34196967300458975744603735)
            ·
              refine ⟨51295450950688463616905603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34196967300458975744603735 51295450950688463616905603)
              ·
                refine ⟨76943176426032695425358405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51295450950688463616905603 76943176426032695425358405)
                ·
                  refine ⟨14426845579881130392254701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76943176426032695425358405 14426845579881130392254701)
                  ·
                    refine ⟨5410067092455423897095513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14426845579881130392254701 5410067092455423897095513)
                    ·
                      refine ⟨4057550319341567922821635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410067092455423897095513 4057550319341567922821635)
                      ·
                        rfl

theorem cell23_7902051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7902051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902051 prefixEnd_7902051 := by exact prefixLift 7902051
  have htrace : WordTrace (prefixWord ++ tailWord_7902051) baseStart_7902051 baseEnd_7902051 := by
    simpa [prefixWord, tailWord_7902051, baseEnd_7902051] using wordTrace_append hprefix tailTrace_7902051
  have hstable : (prefixWord ++ tailWord_7902051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902051).length < 2 ^ (prefixWord ++ tailWord_7902051).sum := by decide
  have hdescent : baseEnd_7902051 < baseStart_7902051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902078 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7902078 : Nat := 118140960795 + 7902078 * 2 ^ 59
def prefixEnd_7902078 : Nat := 4983230072969 + 3 ^ 40 * 7902078 * 2
def baseEnd_7902078 : Nat := 1352521394439746439061337

theorem tailTrace_7902078 : CollatzResearch.WordTrace tailWord_7902078 prefixEnd_7902078 1352521394439746439061337 := by
  unfold tailWord_7902078
  simp only [CollatzResearch.WordTrace]
  refine ⟨36026557783266056040369361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192141641510752298881969925 36026557783266056040369361)
  ·
    refine ⟨27019918337449542030277021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36026557783266056040369361 27019918337449542030277021)
    ·
      refine ⟨10132469376543578261353883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27019918337449542030277021 10132469376543578261353883)
      ·
        refine ⟨15198704064815367392030825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132469376543578261353883 15198704064815367392030825)
        ·
          refine ⟨11399028048611525544023119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15198704064815367392030825 11399028048611525544023119)
          ·
            refine ⟨17098542072917288316034679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399028048611525544023119 17098542072917288316034679)
            ·
              refine ⟨25647813109375932474052019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17098542072917288316034679 25647813109375932474052019)
              ·
                refine ⟨38471719664063898711078029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25647813109375932474052019 38471719664063898711078029)
                ·
                  refine ⟨14426894874023962016654261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38471719664063898711078029 14426894874023962016654261)
                  ·
                    refine ⟨1352521394439746439061337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14426894874023962016654261 1352521394439746439061337)
                    ·
                      rfl

theorem cell23_7902078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7902078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902078 prefixEnd_7902078 := by exact prefixLift 7902078
  have htrace : WordTrace (prefixWord ++ tailWord_7902078) baseStart_7902078 baseEnd_7902078 := by
    simpa [prefixWord, tailWord_7902078, baseEnd_7902078] using wordTrace_append hprefix tailTrace_7902078
  have hstable : (prefixWord ++ tailWord_7902078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902078).length < 2 ^ (prefixWord ++ tailWord_7902078).sum := by decide
  have hdescent : baseEnd_7902078 < baseStart_7902078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902101 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_7902101 : Nat := 118140960795 + 7902101 * 2 ^ 59
def prefixEnd_7902101 : Nat := 4983230072969 + 3 ^ 40 * 7902101 * 2
def baseEnd_7902101 : Nat := 4057575993374292727196405

theorem tailTrace_7902101 : CollatzResearch.WordTrace tailWord_7902101 prefixEnd_7902101 4057575993374292727196405 := by
  unfold tailWord_7902101
  simp only [CollatzResearch.WordTrace]
  refine ⟨288213301145045123251042157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192142200763363415500694771 288213301145045123251042157)
  ·
    refine ⟨108079987929391921219140809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288213301145045123251042157 108079987929391921219140809)
    ·
      refine ⟨81059990947043940914355607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108079987929391921219140809 81059990947043940914355607)
      ·
        refine ⟨121589986420565911371533411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81059990947043940914355607 121589986420565911371533411)
        ·
          refine ⟨182384979630848867057300117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121589986420565911371533411 182384979630848867057300117)
          ·
            refine ⟨8549295920196040643310943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182384979630848867057300117 8549295920196040643310943)
            ·
              refine ⟨12823943880294060964966415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549295920196040643310943 12823943880294060964966415)
              ·
                refine ⟨19235915820441091447449623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12823943880294060964966415 19235915820441091447449623)
                ·
                  refine ⟨28853873730661637171174435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19235915820441091447449623 28853873730661637171174435)
                  ·
                    refine ⟨43280810595992455756761653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28853873730661637171174435 43280810595992455756761653)
                    ·
                      refine ⟨4057575993374292727196405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43280810595992455756761653 4057575993374292727196405)
                      ·
                        rfl

theorem cell23_7902101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_7902101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902101 prefixEnd_7902101 := by exact prefixLift 7902101
  have htrace : WordTrace (prefixWord ++ tailWord_7902101) baseStart_7902101 baseEnd_7902101 := by
    simpa [prefixWord, tailWord_7902101, baseEnd_7902101] using wordTrace_append hprefix tailTrace_7902101
  have hstable : (prefixWord ++ tailWord_7902101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902101).length < 2 ^ (prefixWord ++ tailWord_7902101).sum := by decide
  have hdescent : baseEnd_7902101 < baseStart_7902101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902102 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7902102 : Nat := 118140960795 + 7902102 * 2 ^ 59
def prefixEnd_7902102 : Nat := 4983230072969 + 3 ^ 40 * 7902102 * 2
def baseEnd_7902102 : Nat := 4057576506854947223283901

theorem tailTrace_7902102 : CollatzResearch.WordTrace tailWord_7902102 prefixEnd_7902102 4057576506854947223283901 := by
  unfold tailWord_7902102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013333601127593776364285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192142225078694333614552373 18013333601127593776364285)
  ·
    refine ⟨6755000100422847666136607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18013333601127593776364285 6755000100422847666136607)
    ·
      refine ⟨10132500150634271499204911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755000100422847666136607 10132500150634271499204911)
      ·
        refine ⟨15198750225951407248807367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132500150634271499204911 15198750225951407248807367)
        ·
          refine ⟨22798125338927110873211051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198750225951407248807367 22798125338927110873211051)
          ·
            refine ⟨34197188008390666309816577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22798125338927110873211051 34197188008390666309816577)
            ·
              refine ⟨25647891006292999732362433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34197188008390666309816577 25647891006292999732362433)
              ·
                refine ⟨19235918254719749799271825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25647891006292999732362433 19235918254719749799271825)
                ·
                  refine ⟨14426938691039812349453869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19235918254719749799271825 14426938691039812349453869)
                  ·
                    refine ⟨5410102009139929631045201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14426938691039812349453869 5410102009139929631045201)
                    ·
                      refine ⟨4057576506854947223283901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410102009139929631045201 4057576506854947223283901)
                      ·
                        rfl

theorem cell23_7902102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7902102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902102 prefixEnd_7902102 := by exact prefixLift 7902102
  have htrace : WordTrace (prefixWord ++ tailWord_7902102) baseStart_7902102 baseEnd_7902102 := by
    simpa [prefixWord, tailWord_7902102, baseEnd_7902102] using wordTrace_append hprefix tailTrace_7902102
  have hstable : (prefixWord ++ tailWord_7902102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902102).length < 2 ^ (prefixWord ++ tailWord_7902102).sum := by decide
  have hdescent : baseEnd_7902102 < baseStart_7902102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902132 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7902132 : Nat := 118140960795 + 7902132 * 2 ^ 59
def prefixEnd_7902132 : Nat := 4983230072969 + 3 ^ 40 * 7902132 * 2
def baseEnd_7902132 : Nat := 4057591911274582105908763

theorem tailTrace_7902132 : CollatzResearch.WordTrace tailWord_7902132 prefixEnd_7902132 4057591911274582105908763 := by
  unfold tailWord_7902132
  simp only [CollatzResearch.WordTrace]
  refine ⟨144107215903966407772710325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192142954538621877030280433 144107215903966407772710325)
  ·
    refine ⟨13510051490996850728691593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144107215903966407772710325 13510051490996850728691593)
    ·
      refine ⟨10132538618247638046518695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13510051490996850728691593 10132538618247638046518695)
      ·
        refine ⟨15198807927371457069778043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132538618247638046518695 15198807927371457069778043)
        ·
          refine ⟨22798211891057185604667065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198807927371457069778043 22798211891057185604667065)
          ·
            refine ⟨17098658918292889203500299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22798211891057185604667065 17098658918292889203500299)
            ·
              refine ⟨25647988377439333805250449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17098658918292889203500299 25647988377439333805250449)
              ·
                refine ⟨19235991283079500353937837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25647988377439333805250449 19235991283079500353937837)
                ·
                  refine ⟨7213496731154812632726689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19235991283079500353937837 7213496731154812632726689)
                  ·
                    refine ⟨5410122548366109474545017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7213496731154812632726689 5410122548366109474545017)
                    ·
                      refine ⟨4057591911274582105908763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410122548366109474545017 4057591911274582105908763)
                      ·
                        rfl

theorem cell23_7902132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7902132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902132 prefixEnd_7902132 := by exact prefixLift 7902132
  have htrace : WordTrace (prefixWord ++ tailWord_7902132) baseStart_7902132 baseEnd_7902132 := by
    simpa [prefixWord, tailWord_7902132, baseEnd_7902132] using wordTrace_append hprefix tailTrace_7902132
  have hstable : (prefixWord ++ tailWord_7902132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902132).length < 2 ^ (prefixWord ++ tailWord_7902132).sum := by decide
  have hdescent : baseEnd_7902132 < baseStart_7902132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902152 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_7902152 : Nat := 118140960795 + 7902152 * 2 ^ 59
def prefixEnd_7902152 : Nat := 4983230072969 + 3 ^ 40 * 7902152 * 2
def baseEnd_7902152 : Nat := 4057602180887672027658671

theorem tailTrace_7902152 : CollatzResearch.WordTrace tailWord_7902152 prefixEnd_7902152 4057602180887672027658671 := by
  unfold tailWord_7902152
  simp only [CollatzResearch.WordTrace]
  refine ⟨144107580633930179480574355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192143440845240239307432473 144107580633930179480574355)
  ·
    refine ⟨216161370950895269220861533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144107580633930179480574355 216161370950895269220861533)
    ·
      refine ⟨81060514106585725957823075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216161370950895269220861533 81060514106585725957823075)
      ·
        refine ⟨121590771159878588936734613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81060514106585725957823075 121590771159878588936734613)
        ·
          refine ⟨5699567398119308856409435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121590771159878588936734613 5699567398119308856409435)
          ·
            refine ⟨8549351097178963284614153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699567398119308856409435 8549351097178963284614153)
            ·
              refine ⟨6412013322884222463460615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549351097178963284614153 6412013322884222463460615)
              ·
                refine ⟨9618019984326333695190923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412013322884222463460615 9618019984326333695190923)
                ·
                  refine ⟨14427029976489500542786385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618019984326333695190923 14427029976489500542786385)
                  ·
                    refine ⟨10820272482367125407089789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14427029976489500542786385 10820272482367125407089789)
                    ·
                      refine ⟨4057602180887672027658671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820272482367125407089789 4057602180887672027658671)
                      ·
                        rfl

theorem cell23_7902152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_7902152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902152 prefixEnd_7902152 := by exact prefixLift 7902152
  have htrace : WordTrace (prefixWord ++ tailWord_7902152) baseStart_7902152 baseEnd_7902152 := by
    simpa [prefixWord, tailWord_7902152, baseEnd_7902152] using wordTrace_append hprefix tailTrace_7902152
  have hstable : (prefixWord ++ tailWord_7902152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902152).length < 2 ^ (prefixWord ++ tailWord_7902152).sum := by decide
  have hdescent : baseEnd_7902152 < baseStart_7902152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902281 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_7902281 : Nat := 118140960795 + 7902281 * 2 ^ 59
def prefixEnd_7902281 : Nat := 4983230072969 + 3 ^ 40 * 7902281 * 2
def baseEnd_7902281 : Nat := 4057668419892102022945577

theorem tailTrace_7902281 : CollatzResearch.WordTrace tailWord_7902281 prefixEnd_7902281 4057668419892102022945577 := by
  unfold tailWord_7902281
  simp only [CollatzResearch.WordTrace]
  refine ⟨288219866284393013992594697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192146577522928675995063131 288219866284393013992594697)
  ·
    refine ⟨216164899713294760494446023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288219866284393013992594697 216164899713294760494446023)
    ·
      refine ⟨324247349569942140741669035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216164899713294760494446023 324247349569942140741669035)
      ·
        refine ⟨486371024354913211112503553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324247349569942140741669035 486371024354913211112503553)
        ·
          refine ⟨364778268266184908334377665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486371024354913211112503553 364778268266184908334377665)
          ·
            refine ⟨273583701199638681250783249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364778268266184908334377665 273583701199638681250783249)
            ·
              refine ⟨205187775899729010938087437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273583701199638681250783249 205187775899729010938087437)
              ·
                refine ⟨76945415962398379101782789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205187775899729010938087437 76945415962398379101782789)
                ·
                  refine ⟨14427265492949696081584273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76945415962398379101782789 14427265492949696081584273)
                  ·
                    refine ⟨10820449119712272061188205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14427265492949696081584273 10820449119712272061188205)
                    ·
                      refine ⟨4057668419892102022945577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820449119712272061188205 4057668419892102022945577)
                      ·
                        rfl

theorem cell23_7902281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_7902281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902281 prefixEnd_7902281 := by exact prefixLift 7902281
  have htrace : WordTrace (prefixWord ++ tailWord_7902281) baseStart_7902281 baseEnd_7902281 := by
    simpa [prefixWord, tailWord_7902281, baseEnd_7902281] using wordTrace_append hprefix tailTrace_7902281
  have hstable : (prefixWord ++ tailWord_7902281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902281).length < 2 ^ (prefixWord ++ tailWord_7902281).sum := by decide
  have hdescent : baseEnd_7902281 < baseStart_7902281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902312 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7902312 : Nat := 118140960795 + 7902312 * 2 ^ 59
def prefixEnd_7902312 : Nat := 4983230072969 + 3 ^ 40 * 7902312 * 2
def baseEnd_7902312 : Nat := 4057684337792391401657935

theorem tailTrace_7902312 : CollatzResearch.WordTrace tailWord_7902312 prefixEnd_7902312 4057684337792391401657935 := by
  unfold tailWord_7902312
  simp only [CollatzResearch.WordTrace]
  refine ⟨144110498473640353143486595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192147331298187137524648793 144110498473640353143486595)
  ·
    refine ⟨216165747710460529715229893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144110498473640353143486595 216165747710460529715229893)
    ·
      refine ⟨40531077695711349321605605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216165747710460529715229893 40531077695711349321605605)
      ·
        refine ⟨7599577067945877997801051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40531077695711349321605605 7599577067945877997801051)
        ·
          refine ⟨11399365601918816996701577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599577067945877997801051 11399365601918816996701577)
          ·
            refine ⟨8549524201439112747526183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399365601918816996701577 8549524201439112747526183)
            ·
              refine ⟨12824286302158669121289275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549524201439112747526183 12824286302158669121289275)
              ·
                refine ⟨19236429453238003681933913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824286302158669121289275 19236429453238003681933913)
                ·
                  refine ⟨14427322089928502761450435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19236429453238003681933913 14427322089928502761450435)
                  ·
                    refine ⟨21640983134892754142175653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14427322089928502761450435 21640983134892754142175653)
                    ·
                      refine ⟨4057684337792391401657935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21640983134892754142175653 4057684337792391401657935)
                      ·
                        rfl

theorem cell23_7902312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7902312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902312 prefixEnd_7902312 := by exact prefixLift 7902312
  have htrace : WordTrace (prefixWord ++ tailWord_7902312) baseStart_7902312 baseEnd_7902312 := by
    simpa [prefixWord, tailWord_7902312, baseEnd_7902312] using wordTrace_append hprefix tailTrace_7902312
  have hstable : (prefixWord ++ tailWord_7902312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902312).length < 2 ^ (prefixWord ++ tailWord_7902312).sum := by decide
  have hdescent : baseEnd_7902312 < baseStart_7902312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902345 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 3]
def baseStart_7902345 : Nat := 118140960795 + 7902345 * 2 ^ 59
def prefixEnd_7902345 : Nat := 4983230072969 + 3 ^ 40 * 7902345 * 2
def baseEnd_7902345 : Nat := 4057701282653989772545283

theorem tailTrace_7902345 : CollatzResearch.WordTrace tailWord_7902345 prefixEnd_7902345 4057701282653989772545283 := by
  unfold tailWord_7902345
  simp only [CollatzResearch.WordTrace]
  refine ⟨288222200556161152922924489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192148133704107435281949659 288222200556161152922924489)
  ·
    refine ⟨216166650417120864692193367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288222200556161152922924489 216166650417120864692193367)
    ·
      refine ⟨324249975625681297038290051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216166650417120864692193367 324249975625681297038290051)
      ·
        refine ⟨486374963438521945557435077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324249975625681297038290051 486374963438521945557435077)
        ·
          refine ⟨91195305644722864792019077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 486374963438521945557435077 91195305644722864792019077)
          ·
            refine ⟨17099119808385537148503577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91195305644722864792019077 17099119808385537148503577)
            ·
              refine ⟨12824339856289152861377683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17099119808385537148503577 12824339856289152861377683)
              ·
                refine ⟨19236509784433729292066525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824339856289152861377683 19236509784433729292066525)
                ·
                  refine ⟨7213691169162648484524947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19236509784433729292066525 7213691169162648484524947)
                  ·
                    refine ⟨10820536753743972726787421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213691169162648484524947 10820536753743972726787421)
                    ·
                      refine ⟨4057701282653989772545283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820536753743972726787421 4057701282653989772545283)
                      ·
                        rfl

theorem cell23_7902345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 3].length) (baseStart_7902345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902345 prefixEnd_7902345 := by exact prefixLift 7902345
  have htrace : WordTrace (prefixWord ++ tailWord_7902345) baseStart_7902345 baseEnd_7902345 := by
    simpa [prefixWord, tailWord_7902345, baseEnd_7902345] using wordTrace_append hprefix tailTrace_7902345
  have hstable : (prefixWord ++ tailWord_7902345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902345).length < 2 ^ (prefixWord ++ tailWord_7902345).sum := by decide
  have hdescent : baseEnd_7902345 < baseStart_7902345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902368 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2]
def baseStart_7902368 : Nat := 118140960795 + 7902368 * 2 ^ 59
def prefixEnd_7902368 : Nat := 4983230072969 + 3 ^ 40 * 7902368 * 2
def baseEnd_7902368 : Nat := 4057713092709043182557677

theorem tailTrace_7902368 : CollatzResearch.WordTrace tailWord_7902368 prefixEnd_7902368 4057713092709043182557677 := by
  unfold tailWord_7902368
  simp only [CollatzResearch.WordTrace]
  refine ⟨144111519717538913925505879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192148692956718551900674505 144111519717538913925505879)
  ·
    refine ⟨216167279576308370888258819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144111519717538913925505879 216167279576308370888258819)
    ·
      refine ⟨324250919364462556332388229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216167279576308370888258819 324250919364462556332388229)
      ·
        refine ⟨60797047380836729312322793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324250919364462556332388229 60797047380836729312322793)
        ·
          refine ⟨45597785535627546984242095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60797047380836729312322793 45597785535627546984242095)
          ·
            refine ⟨68396678303441320476363143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45597785535627546984242095 68396678303441320476363143)
            ·
              refine ⟨102595017455161980714544715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68396678303441320476363143 102595017455161980714544715)
              ·
                refine ⟨153892526182742971071817073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102595017455161980714544715 153892526182742971071817073)
                ·
                  refine ⟨115419394637057228303862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153892526182742971071817073 115419394637057228303862805)
                  ·
                    refine ⟨5410284123612057576743569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115419394637057228303862805 5410284123612057576743569)
                    ·
                      refine ⟨4057713092709043182557677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410284123612057576743569 4057713092709043182557677)
                      ·
                        rfl

theorem cell23_7902368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_7902368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902368 prefixEnd_7902368 := by exact prefixLift 7902368
  have htrace : WordTrace (prefixWord ++ tailWord_7902368) baseStart_7902368 baseEnd_7902368 := by
    simpa [prefixWord, tailWord_7902368, baseEnd_7902368] using wordTrace_append hprefix tailTrace_7902368
  have hstable : (prefixWord ++ tailWord_7902368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902368).length < 2 ^ (prefixWord ++ tailWord_7902368).sum := by decide
  have hdescent : baseEnd_7902368 < baseStart_7902368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3]
def baseStart_7902371 : Nat := 118140960795 + 7902371 * 2 ^ 59
def prefixEnd_7902371 : Nat := 4983230072969 + 3 ^ 40 * 7902371 * 2
def baseEnd_7902371 : Nat := 4057714633151006670820163

theorem tailTrace_7902371 : CollatzResearch.WordTrace tailWord_7902371 prefixEnd_7902371 4057714633151006670820163 := by
  unfold tailWord_7902371
  simp only [CollatzResearch.WordTrace]
  refine ⟨288223148854066959363370967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192148765902711306242247311 288223148854066959363370967)
  ·
    refine ⟨432334723281100439045056451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288223148854066959363370967 432334723281100439045056451)
    ·
      refine ⟨648502084921650658567584677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432334723281100439045056451 648502084921650658567584677)
      ·
        refine ⟨121594140922809498481422127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 648502084921650658567584677 121594140922809498481422127)
        ·
          refine ⟨182391211384214247722133191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121594140922809498481422127 182391211384214247722133191)
          ·
            refine ⟨273586817076321371583199787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182391211384214247722133191 273586817076321371583199787)
            ·
              refine ⟨410380225614482057374799681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273586817076321371583199787 410380225614482057374799681)
              ·
                refine ⟨307785169210861543031099761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410380225614482057374799681 307785169210861543031099761)
                ·
                  refine ⟨230838876908146157273324821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307785169210861543031099761 230838876908146157273324821)
                  ·
                    refine ⟨10820572355069351122187101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 230838876908146157273324821 10820572355069351122187101)
                    ·
                      refine ⟨4057714633151006670820163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820572355069351122187101 4057714633151006670820163)
                      ·
                        rfl

theorem cell23_7902371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_7902371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902371 prefixEnd_7902371 := by exact prefixLift 7902371
  have htrace : WordTrace (prefixWord ++ tailWord_7902371) baseStart_7902371 baseEnd_7902371 := by
    simpa [prefixWord, tailWord_7902371, baseEnd_7902371] using wordTrace_append hprefix tailTrace_7902371
  have hstable : (prefixWord ++ tailWord_7902371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902371).length < 2 ^ (prefixWord ++ tailWord_7902371).sum := by decide
  have hdescent : baseEnd_7902371 < baseStart_7902371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902385 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7902385 : Nat := 118140960795 + 7902385 * 2 ^ 59
def prefixEnd_7902385 : Nat := 4983230072969 + 3 ^ 40 * 7902385 * 2
def baseEnd_7902385 : Nat := 4057721821880169616045099

theorem tailTrace_7902385 : CollatzResearch.WordTrace tailWord_7902385 prefixEnd_7902385 4057721821880169616045099 := by
  unfold tailWord_7902385
  simp only [CollatzResearch.WordTrace]
  refine ⟨288223659476016239754380609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192149106317344159836253739 288223659476016239754380609)
  ·
    refine ⟨216167744607012179815785457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288223659476016239754380609 216167744607012179815785457)
    ·
      refine ⟨162125808455259134861839093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216167744607012179815785457 162125808455259134861839093)
      ·
        refine ⟨15199294542680543893297415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162125808455259134861839093 15199294542680543893297415)
        ·
          refine ⟨22798941814020815839946123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15199294542680543893297415 22798941814020815839946123)
          ·
            refine ⟨34198412721031223759919185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22798941814020815839946123 34198412721031223759919185)
            ·
              refine ⟨25648809540773417819939389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34198412721031223759919185 25648809540773417819939389)
              ·
                refine ⟨9618303577790031682477271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25648809540773417819939389 9618303577790031682477271)
                ·
                  refine ⟨14427455366685047523715907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618303577790031682477271 14427455366685047523715907)
                  ·
                    refine ⟨21641183050027571285573861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14427455366685047523715907 21641183050027571285573861)
                    ·
                      refine ⟨4057721821880169616045099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21641183050027571285573861 4057721821880169616045099)
                      ·
                        rfl

theorem cell23_7902385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7902385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902385 prefixEnd_7902385 := by exact prefixLift 7902385
  have htrace : WordTrace (prefixWord ++ tailWord_7902385) baseStart_7902385 baseEnd_7902385 := by
    simpa [prefixWord, tailWord_7902385, baseEnd_7902385] using wordTrace_append hprefix tailTrace_7902385
  have hstable : (prefixWord ++ tailWord_7902385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902385).length < 2 ^ (prefixWord ++ tailWord_7902385).sum := by decide
  have hdescent : baseEnd_7902385 < baseStart_7902385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902398 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7902398 : Nat := 118140960795 + 7902398 * 2 ^ 59
def prefixEnd_7902398 : Nat := 4983230072969 + 3 ^ 40 * 7902398 * 2
def baseEnd_7902398 : Nat := 4057728497128678065182539

theorem tailTrace_7902398 : CollatzResearch.WordTrace tailWord_7902398 prefixEnd_7902398 4057728497128678065182539 := by
  unfold tailWord_7902398
  simp only [CollatzResearch.WordTrace]
  refine ⟨36028016703121142871825481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192149422416646095316402565 36028016703121142871825481)
  ·
    refine ⟨27021012527340857153869111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36028016703121142871825481 27021012527340857153869111)
    ·
      refine ⟨40531518791011285730803667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021012527340857153869111 40531518791011285730803667)
      ·
        refine ⟨60797278186516928596205501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40531518791011285730803667 60797278186516928596205501)
        ·
          refine ⟨22798979319943848223577063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60797278186516928596205501 22798979319943848223577063)
          ·
            refine ⟨34198468979915772335365595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22798979319943848223577063 34198468979915772335365595)
            ·
              refine ⟨51297703469873658503048393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34198468979915772335365595 51297703469873658503048393)
              ·
                refine ⟨38473277602405243877286295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51297703469873658503048393 38473277602405243877286295)
                ·
                  refine ⟨57709916403607865815929443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38473277602405243877286295 57709916403607865815929443)
                  ·
                    refine ⟨86564874605411798723894165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57709916403607865815929443 86564874605411798723894165)
                    ·
                      refine ⟨4057728497128678065182539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86564874605411798723894165 4057728497128678065182539)
                      ·
                        rfl

theorem cell23_7902398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7902398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902398 prefixEnd_7902398 := by exact prefixLift 7902398
  have htrace : WordTrace (prefixWord ++ tailWord_7902398) baseStart_7902398 baseEnd_7902398 := by
    simpa [prefixWord, tailWord_7902398, baseEnd_7902398] using wordTrace_append hprefix tailTrace_7902398
  have hstable : (prefixWord ++ tailWord_7902398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902398).length < 2 ^ (prefixWord ++ tailWord_7902398).sum := by decide
  have hdescent : baseEnd_7902398 < baseStart_7902398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902431 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_7902431 : Nat := 118140960795 + 7902431 * 2 ^ 59
def prefixEnd_7902431 : Nat := 4983230072969 + 3 ^ 40 * 7902431 * 2
def baseEnd_7902431 : Nat := 4057745441990276436069887

theorem tailTrace_7902431 : CollatzResearch.WordTrace tailWord_7902431 prefixEnd_7902431 4057745441990276436069887 := by
  unfold tailWord_7902431
  simp only [CollatzResearch.WordTrace]
  refine ⟨288225337233849589610555147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192150224822566393073703431 288225337233849589610555147)
  ·
    refine ⟨432338005850774384415832721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288225337233849589610555147 432338005850774384415832721)
    ·
      refine ⟨324253504388080788311874541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432338005850774384415832721 324253504388080788311874541)
      ·
        refine ⟨121595064145530295616952953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324253504388080788311874541 121595064145530295616952953)
        ·
          refine ⟨91196298109147721712714715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121595064145530295616952953 91196298109147721712714715)
          ·
            refine ⟨136794447163721582569072073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91196298109147721712714715 136794447163721582569072073)
            ·
              refine ⟨102595835372791186926804055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136794447163721582569072073 102595835372791186926804055)
              ·
                refine ⟨153893753059186780390206083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102595835372791186926804055 153893753059186780390206083)
                ·
                  refine ⟨230840629588780170585309125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153893753059186780390206083 230840629588780170585309125)
                  ·
                    refine ⟨43282618047896281984745461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230840629588780170585309125 43282618047896281984745461)
                    ·
                      refine ⟨4057745441990276436069887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43282618047896281984745461 4057745441990276436069887)
                      ·
                        rfl

theorem cell23_7902431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_7902431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902431 prefixEnd_7902431 := by exact prefixLift 7902431
  have htrace : WordTrace (prefixWord ++ tailWord_7902431) baseStart_7902431 baseEnd_7902431 := by
    simpa [prefixWord, tailWord_7902431, baseEnd_7902431] using wordTrace_append hprefix tailTrace_7902431
  have hstable : (prefixWord ++ tailWord_7902431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902431).length < 2 ^ (prefixWord ++ tailWord_7902431).sum := by decide
  have hdescent : baseEnd_7902431 < baseStart_7902431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902439 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7902439 : Nat := 118140960795 + 7902439 * 2 ^ 59
def prefixEnd_7902439 : Nat := 4983230072969 + 3 ^ 40 * 7902439 * 2
def baseEnd_7902439 : Nat := 4057749549835512404769851

theorem tailTrace_7902439 : CollatzResearch.WordTrace tailWord_7902439 prefixEnd_7902439 4057749549835512404769851 := by
  unfold tailWord_7902439
  simp only [CollatzResearch.WordTrace]
  refine ⟨288225629017820606976846371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192150419345213737984564247 288225629017820606976846371)
  ·
    refine ⟨432338443526730910465269557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288225629017820606976846371 432338443526730910465269557)
    ·
      refine ⟨40531729080631022856119021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432338443526730910465269557 40531729080631022856119021)
      ·
        refine ⟨15199398405236633571044633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40531729080631022856119021 15199398405236633571044633)
        ·
          refine ⟨11399548803927475178283475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15199398405236633571044633 11399548803927475178283475)
          ·
            refine ⟨17099323205891212767425213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399548803927475178283475 17099323205891212767425213)
            ·
              refine ⟨6412246202209204787784455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17099323205891212767425213 6412246202209204787784455)
              ·
                refine ⟨9618369303313807181676683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412246202209204787784455 9618369303313807181676683)
                ·
                  refine ⟨14427553954970710772515025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618369303313807181676683 14427553954970710772515025)
                  ·
                    refine ⟨10820665466228033079386269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14427553954970710772515025 10820665466228033079386269)
                    ·
                      refine ⟨4057749549835512404769851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820665466228033079386269 4057749549835512404769851)
                      ·
                        rfl

theorem cell23_7902439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7902439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902439 prefixEnd_7902439 := by exact prefixLift 7902439
  have htrace : WordTrace (prefixWord ++ tailWord_7902439) baseStart_7902439 baseEnd_7902439 := by
    simpa [prefixWord, tailWord_7902439, baseEnd_7902439] using wordTrace_append hprefix tailTrace_7902439
  have hstable : (prefixWord ++ tailWord_7902439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902439).length < 2 ^ (prefixWord ++ tailWord_7902439).sum := by decide
  have hdescent : baseEnd_7902439 < baseStart_7902439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902441 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_7902441 : Nat := 118140960795 + 7902441 * 2 ^ 59
def prefixEnd_7902441 : Nat := 4983230072969 + 3 ^ 40 * 7902441 * 2
def baseEnd_7902441 : Nat := 4057750576796821396944841

theorem tailTrace_7902441 : CollatzResearch.WordTrace tailWord_7902441 prefixEnd_7902441 4057750576796821396944841 := by
  unfold tailWord_7902441
  simp only [CollatzResearch.WordTrace]
  refine ⟨288225701963813361318419177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192150467975875574212279451 288225701963813361318419177)
  ·
    refine ⟨216169276472860020988814383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288225701963813361318419177 216169276472860020988814383)
    ·
      refine ⟨324253914709290031483221575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216169276472860020988814383 324253914709290031483221575)
      ·
        refine ⟨486380872063935047224832363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324253914709290031483221575 486380872063935047224832363)
        ·
          refine ⟨729571308095902570837248545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486380872063935047224832363 729571308095902570837248545)
          ·
            refine ⟨547178481071926928127936409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729571308095902570837248545 547178481071926928127936409)
            ·
              refine ⟨410383860803945196095952307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547178481071926928127936409 410383860803945196095952307)
              ·
                refine ⟨615575791205917794143928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410383860803945196095952307 615575791205917794143928461)
                ·
                  refine ⟨230840921702219172803973173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615575791205917794143928461 230840921702219172803973173)
                  ·
                    refine ⟨21641336409583047450372485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230840921702219172803973173 21641336409583047450372485)
                    ·
                      refine ⟨4057750576796821396944841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21641336409583047450372485 4057750576796821396944841)
                      ·
                        rfl

theorem cell23_7902441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_7902441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902441 prefixEnd_7902441 := by exact prefixLift 7902441
  have htrace : WordTrace (prefixWord ++ tailWord_7902441) baseStart_7902441 baseEnd_7902441 := by
    simpa [prefixWord, tailWord_7902441, baseEnd_7902441] using wordTrace_append hprefix tailTrace_7902441
  have hstable : (prefixWord ++ tailWord_7902441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902441).length < 2 ^ (prefixWord ++ tailWord_7902441).sum := by decide
  have hdescent : baseEnd_7902441 < baseStart_7902441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902462 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7902462 : Nat := 118140960795 + 7902462 * 2 ^ 59
def prefixEnd_7902462 : Nat := 4983230072969 + 3 ^ 40 * 7902462 * 2
def baseEnd_7902462 : Nat := 4057761359890565814782245

theorem tailTrace_7902462 : CollatzResearch.WordTrace tailWord_7902462 prefixEnd_7902462 4057761359890565814782245 := by
  unfold tailWord_7902462
  simp only [CollatzResearch.WordTrace]
  refine ⟨36028308487092160238116705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192150978597824854603289093 36028308487092160238116705)
  ·
    refine ⟨27021231365319120178587529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36028308487092160238116705 27021231365319120178587529)
    ·
      refine ⟨20265923523989340133940647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27021231365319120178587529 20265923523989340133940647)
      ·
        refine ⟨30398885285984010200910971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20265923523989340133940647 30398885285984010200910971)
        ·
          refine ⟨45598327928976015301366457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30398885285984010200910971 45598327928976015301366457)
          ·
            refine ⟨34198745946732011476024843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45598327928976015301366457 34198745946732011476024843)
            ·
              refine ⟨51298118920098017214037265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34198745946732011476024843 51298118920098017214037265)
              ·
                refine ⟨38473589190073512910527949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51298118920098017214037265 38473589190073512910527949)
                ·
                  refine ⟨14427595946277567341447981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38473589190073512910527949 14427595946277567341447981)
                  ·
                    refine ⟨5410348479854087753042993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14427595946277567341447981 5410348479854087753042993)
                    ·
                      refine ⟨4057761359890565814782245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410348479854087753042993 4057761359890565814782245)
                      ·
                        rfl

theorem cell23_7902462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7902462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902462 prefixEnd_7902462 := by exact prefixLift 7902462
  have htrace : WordTrace (prefixWord ++ tailWord_7902462) baseStart_7902462 baseEnd_7902462 := by
    simpa [prefixWord, tailWord_7902462, baseEnd_7902462] using wordTrace_append hprefix tailTrace_7902462
  have hstable : (prefixWord ++ tailWord_7902462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902462).length < 2 ^ (prefixWord ++ tailWord_7902462).sum := by decide
  have hdescent : baseEnd_7902462 < baseStart_7902462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902468 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_7902468 : Nat := 118140960795 + 7902468 * 2 ^ 59
def prefixEnd_7902468 : Nat := 4983230072969 + 3 ^ 40 * 7902468 * 2
def baseEnd_7902468 : Nat := 1352588146924830930435739

theorem tailTrace_7902468 : CollatzResearch.WordTrace tailWord_7902468 prefixEnd_7902468 1352588146924830930435739 := by
  unfold tailWord_7902468
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113343367357772464826029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192151124489810363286434705 144113343367357772464826029)
  ·
    refine ⟨54042503762759164674309761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144113343367357772464826029 54042503762759164674309761)
    ·
      refine ⟨40531877822069373505732321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54042503762759164674309761 40531877822069373505732321)
      ·
        refine ⟨30398908366552030129299241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40531877822069373505732321 30398908366552030129299241)
        ·
          refine ⟨22799181274914022596974431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30398908366552030129299241 22799181274914022596974431)
          ·
            refine ⟨34198771912371033895461647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22799181274914022596974431 34198771912371033895461647)
            ·
              refine ⟨51298157868556550843192471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34198771912371033895461647 51298157868556550843192471)
              ·
                refine ⟨76947236802834826264788707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51298157868556550843192471 76947236802834826264788707)
                ·
                  refine ⟨115420855204252239397183061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76947236802834826264788707 115420855204252239397183061)
                  ·
                    refine ⟨1352588146924830930435739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115420855204252239397183061 1352588146924830930435739)
                    ·
                      rfl

theorem cell23_7902468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_7902468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902468 prefixEnd_7902468 := by exact prefixLift 7902468
  have htrace : WordTrace (prefixWord ++ tailWord_7902468) baseStart_7902468 baseEnd_7902468 := by
    simpa [prefixWord, tailWord_7902468, baseEnd_7902468] using wordTrace_append hprefix tailTrace_7902468
  have hstable : (prefixWord ++ tailWord_7902468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902468).length < 2 ^ (prefixWord ++ tailWord_7902468).sum := by decide
  have hdescent : baseEnd_7902468 < baseStart_7902468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902475 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 4, 2]
def baseStart_7902475 : Nat := 118140960795 + 7902475 * 2 ^ 59
def prefixEnd_7902475 : Nat := 4983230072969 + 3 ^ 40 * 7902475 * 2
def baseEnd_7902475 : Nat := 4057768035139074263919685

theorem tailTrace_7902475 : CollatzResearch.WordTrace tailWord_7902475 prefixEnd_7902475 4057768035139074263919685 := by
  unfold tailWord_7902475
  simp only [CollatzResearch.WordTrace]
  refine ⟨288226942045690185125156879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192151294697126790083437919 288226942045690185125156879)
  ·
    refine ⟨432340413068535277687735319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288226942045690185125156879 432340413068535277687735319)
    ·
      refine ⟨648510619602802916531602979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432340413068535277687735319 648510619602802916531602979)
      ·
        refine ⟨972765929404204374797404469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648510619602802916531602979 972765929404204374797404469)
        ·
          refine ⟨91196805881644160137256669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 972765929404204374797404469 91196805881644160137256669)
          ·
            refine ⟨34198802205616560051471251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91196805881644160137256669 34198802205616560051471251)
            ·
              refine ⟨51298203308424840077206877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34198802205616560051471251 51298203308424840077206877)
              ·
                refine ⟨19236826240659315028952579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51298203308424840077206877 19236826240659315028952579)
                ·
                  refine ⟨28855239360988972543428869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19236826240659315028952579 28855239360988972543428869)
                  ·
                    refine ⟨5410357380185432351892913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28855239360988972543428869 5410357380185432351892913)
                    ·
                      refine ⟨4057768035139074263919685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410357380185432351892913 4057768035139074263919685)
                      ·
                        rfl

theorem cell23_7902475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 4, 2].length) (baseStart_7902475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902475 prefixEnd_7902475 := by exact prefixLift 7902475
  have htrace : WordTrace (prefixWord ++ tailWord_7902475) baseStart_7902475 baseEnd_7902475 := by
    simpa [prefixWord, tailWord_7902475, baseEnd_7902475] using wordTrace_append hprefix tailTrace_7902475
  have hstable : (prefixWord ++ tailWord_7902475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902475).length < 2 ^ (prefixWord ++ tailWord_7902475).sum := by decide
  have hdescent : baseEnd_7902475 < baseStart_7902475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902491 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_7902491 : Nat := 118140960795 + 7902491 * 2 ^ 59
def prefixEnd_7902491 : Nat := 4983230072969 + 3 ^ 40 * 7902491 * 2
def baseEnd_7902491 : Nat := 4057776250829546201319611

theorem tailTrace_7902491 : CollatzResearch.WordTrace tailWord_7902491 prefixEnd_7902491 4057776250829546201319611 := by
  unfold tailWord_7902491
  simp only [CollatzResearch.WordTrace]
  refine ⟨288227525613632219857739327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192151683742421479905159551 288227525613632219857739327)
  ·
    refine ⟨432341288420448329786608991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288227525613632219857739327 432341288420448329786608991)
    ·
      refine ⟨648511932630672494679913487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432341288420448329786608991 648511932630672494679913487)
      ·
        refine ⟨972767898946008742019870231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648511932630672494679913487 972767898946008742019870231)
        ·
          refine ⟨1459151848419013113029805347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972767898946008742019870231 1459151848419013113029805347)
          ·
            refine ⟨2188727772628519669544708021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459151848419013113029805347 2188727772628519669544708021)
            ·
              refine ⟨205193228683923719019816377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2188727772628519669544708021 205193228683923719019816377)
              ·
                refine ⟨153894921512942789264862283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205193228683923719019816377 153894921512942789264862283)
                ·
                  refine ⟨230842382269414183897293425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153894921512942789264862283 230842382269414183897293425)
                  ·
                    refine ⟨173131786702060637922970069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230842382269414183897293425 173131786702060637922970069)
                    ·
                      refine ⟨4057776250829546201319611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173131786702060637922970069 4057776250829546201319611)
                      ·
                        rfl

theorem cell23_7902491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_7902491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902491 prefixEnd_7902491 := by exact prefixLift 7902491
  have htrace : WordTrace (prefixWord ++ tailWord_7902491) baseStart_7902491 baseEnd_7902491 := by
    simpa [prefixWord, tailWord_7902491, baseEnd_7902491] using wordTrace_append hprefix tailTrace_7902491
  have hstable : (prefixWord ++ tailWord_7902491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902491).length < 2 ^ (prefixWord ++ tailWord_7902491).sum := by decide
  have hdescent : baseEnd_7902491 < baseStart_7902491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902496 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7902496 : Nat := 118140960795 + 7902496 * 2 ^ 59
def prefixEnd_7902496 : Nat := 4983230072969 + 3 ^ 40 * 7902496 * 2
def baseEnd_7902496 : Nat := 4057778818232818681757089

theorem tailTrace_7902496 : CollatzResearch.WordTrace tailWord_7902496 prefixEnd_7902496 4057778818232818681757089 := by
  unfold tailWord_7902496
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113853989307052855835671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192151805319076070474447561 144113853989307052855835671)
  ·
    refine ⟨216170780983960579283753507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144113853989307052855835671 216170780983960579283753507)
    ·
      refine ⟨324256171475940868925630261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216170780983960579283753507 324256171475940868925630261)
      ·
        refine ⟨30399016075869456461777837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 324256171475940868925630261 30399016075869456461777837)
        ·
          refine ⟨11399631028451046173166689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30399016075869456461777837 11399631028451046173166689)
          ·
            refine ⟨8549723271338284629875017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399631028451046173166689 8549723271338284629875017)
            ·
              refine ⟨6412292453503713472406263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549723271338284629875017 6412292453503713472406263)
              ·
                refine ⟨9618438680255570208609395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412292453503713472406263 9618438680255570208609395)
                ·
                  refine ⟨14427658020383355312914093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618438680255570208609395 14427658020383355312914093)
                  ·
                    refine ⟨5410371757643758242342785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14427658020383355312914093 5410371757643758242342785)
                    ·
                      refine ⟨4057778818232818681757089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410371757643758242342785 4057778818232818681757089)
                      ·
                        rfl

theorem cell23_7902496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7902496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902496 prefixEnd_7902496 := by exact prefixLift 7902496
  have htrace : WordTrace (prefixWord ++ tailWord_7902496) baseStart_7902496 baseEnd_7902496 := by
    simpa [prefixWord, tailWord_7902496, baseEnd_7902496] using wordTrace_append hprefix tailTrace_7902496
  have hstable : (prefixWord ++ tailWord_7902496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902496).length < 2 ^ (prefixWord ++ tailWord_7902496).sum := by decide
  have hdescent : baseEnd_7902496 < baseStart_7902496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902515 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 5]
def baseStart_7902515 : Nat := 118140960795 + 7902515 * 2 ^ 59
def prefixEnd_7902515 : Nat := 4983230072969 + 3 ^ 40 * 7902515 * 2
def baseEnd_7902515 : Nat := 450865397151694900824389

theorem tailTrace_7902515 : CollatzResearch.WordTrace tailWord_7902515 prefixEnd_7902515 450865397151694900824389 := by
  unfold tailWord_7902515
  simp only [CollatzResearch.WordTrace]
  refine ⟨288228400965545271956612999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192152267310363514637741999 288228400965545271956612999)
  ·
    refine ⟨432342601448317907934919499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288228400965545271956612999 432342601448317907934919499)
    ·
      refine ⟨648513902172476861902379249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432342601448317907934919499 648513902172476861902379249)
      ·
        refine ⟨486385426629357646426784437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648513902172476861902379249 486385426629357646426784437)
        ·
          refine ⟨45598633746502279352511041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 486385426629357646426784437 45598633746502279352511041)
          ·
            refine ⟨34198975309876709514383281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45598633746502279352511041 34198975309876709514383281)
            ·
              refine ⟨25649231482407532135787461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34198975309876709514383281 25649231482407532135787461)
              ·
                refine ⟨4809230902951412275460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25649231482407532135787461 4809230902951412275460149)
                ·
                  refine ⟨450865397151694900824389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809230902951412275460149 450865397151694900824389)
                  ·
                    rfl

theorem cell23_7902515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 5].length) (baseStart_7902515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902515 prefixEnd_7902515 := by exact prefixLift 7902515
  have htrace : WordTrace (prefixWord ++ tailWord_7902515) baseStart_7902515 baseEnd_7902515 := by
    simpa [prefixWord, tailWord_7902515, baseEnd_7902515] using wordTrace_append hprefix tailTrace_7902515
  have hstable : (prefixWord ++ tailWord_7902515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902515).length < 2 ^ (prefixWord ++ tailWord_7902515).sum := by decide
  have hdescent : baseEnd_7902515 < baseStart_7902515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902526 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7902526 : Nat := 118140960795 + 7902526 * 2 ^ 59
def prefixEnd_7902526 : Nat := 4983230072969 + 3 ^ 40 * 7902526 * 2
def baseEnd_7902526 : Nat := 4057794222652453564381951

theorem tailTrace_7902526 : CollatzResearch.WordTrace tailWord_7902526 prefixEnd_7902526 4057794222652453564381951 := by
  unfold tailWord_7902526
  simp only [CollatzResearch.WordTrace]
  refine ⟨36028600271063177604407929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192152534779003613890175621 36028600271063177604407929)
  ·
    refine ⟨27021450203297383203305947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36028600271063177604407929 27021450203297383203305947)
    ·
      refine ⟨40532175304946074804958921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021450203297383203305947 40532175304946074804958921)
      ·
        refine ⟨30399131478709556103719191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40532175304946074804958921 30399131478709556103719191)
        ·
          refine ⟨45598697218064334155578787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30399131478709556103719191 45598697218064334155578787)
          ·
            refine ⟨68398045827096501233368181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45598697218064334155578787 68398045827096501233368181)
            ·
              refine ⟨6412316796290296990628267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68398045827096501233368181 6412316796290296990628267)
              ·
                refine ⟨9618475194435445485942401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412316796290296990628267 9618475194435445485942401)
                ·
                  refine ⟨7213856395826584114456801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618475194435445485942401 7213856395826584114456801)
                  ·
                    refine ⟨5410392296869938085842601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7213856395826584114456801 5410392296869938085842601)
                    ·
                      refine ⟨4057794222652453564381951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410392296869938085842601 4057794222652453564381951)
                      ·
                        rfl

theorem cell23_7902526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7902526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902526 prefixEnd_7902526 := by exact prefixLift 7902526
  have htrace : WordTrace (prefixWord ++ tailWord_7902526) baseStart_7902526 baseEnd_7902526 := by
    simpa [prefixWord, tailWord_7902526, baseEnd_7902526] using wordTrace_append hprefix tailTrace_7902526
  have hstable : (prefixWord ++ tailWord_7902526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902526).length < 2 ^ (prefixWord ++ tailWord_7902526).sum := by decide
  have hdescent : baseEnd_7902526 < baseStart_7902526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902565 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7902565 : Nat := 118140960795 + 7902565 * 2 ^ 59
def prefixEnd_7902565 : Nat := 4983230072969 + 3 ^ 40 * 7902565 * 2
def baseEnd_7902565 : Nat := 4057814248397978911794271

theorem tailTrace_7902565 : CollatzResearch.WordTrace tailWord_7902565 prefixEnd_7902565 4057814248397978911794271 := by
  unfold tailWord_7902565
  simp only [CollatzResearch.WordTrace]
  refine ⟨288230224615364130495933149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192153483076909420330622099 288230224615364130495933149)
  ·
    refine ⟨108086334230761548935974931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288230224615364130495933149 108086334230761548935974931)
    ·
      refine ⟨162129501346142323403962397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108086334230761548935974931 162129501346142323403962397)
      ·
        refine ⟨60798563004803371276485899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162129501346142323403962397 60798563004803371276485899)
        ·
          refine ⟨91197844507205056914728849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60798563004803371276485899 91197844507205056914728849)
          ·
            refine ⟨68398383380403792686046637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91197844507205056914728849 68398383380403792686046637)
            ·
              refine ⟨25649393767651422257267489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68398383380403792686046637 25649393767651422257267489)
              ·
                refine ⟨19237045325738566692950617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25649393767651422257267489 19237045325738566692950617)
                ·
                  refine ⟨14427783994303925019712963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19237045325738566692950617 14427783994303925019712963)
                  ·
                    refine ⟨21641675991455887529569445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14427783994303925019712963 21641675991455887529569445)
                    ·
                      refine ⟨4057814248397978911794271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21641675991455887529569445 4057814248397978911794271)
                      ·
                        rfl

theorem cell23_7902565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7902565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902565 prefixEnd_7902565 := by exact prefixLift 7902565
  have htrace : WordTrace (prefixWord ++ tailWord_7902565) baseStart_7902565 baseEnd_7902565 := by
    simpa [prefixWord, tailWord_7902565, baseEnd_7902565] using wordTrace_append hprefix tailTrace_7902565
  have hstable : (prefixWord ++ tailWord_7902565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902565).length < 2 ^ (prefixWord ++ tailWord_7902565).sum := by decide
  have hdescent : baseEnd_7902565 < baseStart_7902565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902626 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7902626 : Nat := 118140960795 + 7902626 * 2 ^ 59
def prefixEnd_7902626 : Nat := 4983230072969 + 3 ^ 40 * 7902626 * 2
def baseEnd_7902626 : Nat := 1352615190239301057710497

theorem tailTrace_7902626 : CollatzResearch.WordTrace tailWord_7902626 prefixEnd_7902626 1352615190239301057710497 := by
  unfold tailWord_7902626
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058112367035784478475933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192154966312095425275935821 72058112367035784478475933)
  ·
    refine ⟨27021792137638419179428475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72058112367035784478475933 27021792137638419179428475)
    ·
      refine ⟨40532688206457628769142713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021792137638419179428475 40532688206457628769142713)
      ·
        refine ⟨30399516154843221576857035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40532688206457628769142713 30399516154843221576857035)
        ·
          refine ⟨45599274232264832365285553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30399516154843221576857035 45599274232264832365285553)
          ·
            refine ⟨34199455674198624273964165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45599274232264832365285553 34199455674198624273964165)
            ·
              refine ⟨6412397938912242051368281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34199455674198624273964165 6412397938912242051368281)
              ·
                refine ⟨4809298454184181538526211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412397938912242051368281 4809298454184181538526211)
                ·
                  refine ⟨7213947681276272307789317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809298454184181538526211 7213947681276272307789317)
                  ·
                    refine ⟨1352615190239301057710497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213947681276272307789317 1352615190239301057710497)
                    ·
                      rfl

theorem cell23_7902626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7902626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902626 prefixEnd_7902626 := by exact prefixLift 7902626
  have htrace : WordTrace (prefixWord ++ tailWord_7902626) baseStart_7902626 baseEnd_7902626 := by
    simpa [prefixWord, tailWord_7902626, baseEnd_7902626] using wordTrace_append hprefix tailTrace_7902626
  have hstable : (prefixWord ++ tailWord_7902626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902626).length < 2 ^ (prefixWord ++ tailWord_7902626).sum := by decide
  have hdescent : baseEnd_7902626 < baseStart_7902626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902649 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7902649 : Nat := 118140960795 + 7902649 * 2 ^ 59
def prefixEnd_7902649 : Nat := 4983230072969 + 3 ^ 40 * 7902649 * 2
def baseEnd_7902649 : Nat := 4057857380772956583143885

theorem tailTrace_7902649 : CollatzResearch.WordTrace tailWord_7902649 prefixEnd_7902649 4057857380772956583143885 := by
  unfold tailWord_7902649
  simp only [CollatzResearch.WordTrace]
  refine ⟨288233288347059812841991001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192155525564706541894660667 288233288347059812841991001)
  ·
    refine ⟨216174966260294859631493251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288233288347059812841991001 216174966260294859631493251)
    ·
      refine ⟨324262449390442289447239877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216174966260294859631493251 324262449390442289447239877)
      ·
        refine ⟨60799209260707929271357477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324262449390442289447239877 60799209260707929271357477)
        ·
          refine ⟨11399851736382736738379527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60799209260707929271357477 11399851736382736738379527)
          ·
            refine ⟨17099777604574105107569291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399851736382736738379527 17099777604574105107569291)
            ·
              refine ⟨25649666406861157661353937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17099777604574105107569291 25649666406861157661353937)
              ·
                refine ⟨19237249805145868246015453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25649666406861157661353937 19237249805145868246015453)
                ·
                  refine ⟨7213968676929700592255795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19237249805145868246015453 7213968676929700592255795)
                  ·
                    refine ⟨10820953015394550888383693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213968676929700592255795 10820953015394550888383693)
                    ·
                      refine ⟨4057857380772956583143885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820953015394550888383693 4057857380772956583143885)
                      ·
                        rfl

theorem cell23_7902649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7902649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902649 prefixEnd_7902649 := by exact prefixLift 7902649
  have htrace : WordTrace (prefixWord ++ tailWord_7902649) baseStart_7902649 baseEnd_7902649 := by
    simpa [prefixWord, tailWord_7902649, baseEnd_7902649] using wordTrace_append hprefix tailTrace_7902649
  have hstable : (prefixWord ++ tailWord_7902649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902649).length < 2 ^ (prefixWord ++ tailWord_7902649).sum := by decide
  have hdescent : baseEnd_7902649 < baseStart_7902649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902665 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_7902665 : Nat := 118140960795 + 7902665 * 2 ^ 59
def prefixEnd_7902665 : Nat := 4983230072969 + 3 ^ 40 * 7902665 * 2
def baseEnd_7902665 : Nat := 1352621865487809506847937

theorem tailTrace_7902665 : CollatzResearch.WordTrace tailWord_7902665 prefixEnd_7902665 1352621865487809506847937 := by
  unfold tailWord_7902665
  simp only [CollatzResearch.WordTrace]
  refine ⟨288233871915001847574573449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192155914610001231716382299 288233871915001847574573449)
  ·
    refine ⟨216175403936251385680930087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288233871915001847574573449 216175403936251385680930087)
    ·
      refine ⟨324263105904377078521395131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216175403936251385680930087 324263105904377078521395131)
      ·
        refine ⟨486394658856565617782092697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324263105904377078521395131 486394658856565617782092697)
        ·
          refine ⟨364795994142424213336569523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486394658856565617782092697 364795994142424213336569523)
          ·
            refine ⟨547193991213636320004854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364795994142424213336569523 547193991213636320004854285)
            ·
              refine ⟨205197746705113620001820357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547193991213636320004854285 205197746705113620001820357)
              ·
                refine ⟨38474577507208803750341317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205197746705113620001820357 38474577507208803750341317)
                ·
                  refine ⟨7213983282601650703188997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38474577507208803750341317 7213983282601650703188997)
                  ·
                    refine ⟨1352621865487809506847937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213983282601650703188997 1352621865487809506847937)
                    ·
                      rfl

theorem cell23_7902665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_7902665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902665 prefixEnd_7902665 := by exact prefixLift 7902665
  have htrace : WordTrace (prefixWord ++ tailWord_7902665) baseStart_7902665 baseEnd_7902665 := by
    simpa [prefixWord, tailWord_7902665, baseEnd_7902665] using wordTrace_append hprefix tailTrace_7902665
  have hstable : (prefixWord ++ tailWord_7902665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902665).length < 2 ^ (prefixWord ++ tailWord_7902665).sum := by decide
  have hdescent : baseEnd_7902665 < baseStart_7902665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902666 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_7902666 : Nat := 118140960795 + 7902666 * 2 ^ 59
def prefixEnd_7902666 : Nat := 4983230072969 + 3 ^ 40 * 7902666 * 2
def baseEnd_7902666 : Nat := 4057866109944083016631307

theorem tailTrace_7902666 : CollatzResearch.WordTrace tailWord_7902666 prefixEnd_7902666 4057866109944083016631307 := by
  unfold tailWord_7902666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058477096999556186339963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192155938925332149830239901 72058477096999556186339963)
  ·
    refine ⟨108087715645499334279509945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72058477096999556186339963 108087715645499334279509945)
    ·
      refine ⟨81065786734124500709632459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108087715645499334279509945 81065786734124500709632459)
      ·
        refine ⟨121598680101186751064448689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81065786734124500709632459 121598680101186751064448689)
        ·
          refine ⟨91199010075890063298336517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121598680101186751064448689 91199010075890063298336517)
          ·
            refine ⟨17099814389229386868438097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91199010075890063298336517 17099814389229386868438097)
            ·
              refine ⟨12824860791922040151328573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17099814389229386868438097 12824860791922040151328573)
              ·
                refine ⟨4809322796970765056748215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12824860791922040151328573 4809322796970765056748215)
                ·
                  refine ⟨7213984195456147585122323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809322796970765056748215 7213984195456147585122323)
                  ·
                    refine ⟨10820976293184221377683485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213984195456147585122323 10820976293184221377683485)
                    ·
                      refine ⟨4057866109944083016631307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10820976293184221377683485 4057866109944083016631307)
                      ·
                        rfl

theorem cell23_7902666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_7902666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902666 prefixEnd_7902666 := by exact prefixLift 7902666
  have htrace : WordTrace (prefixWord ++ tailWord_7902666) baseStart_7902666 baseEnd_7902666 := by
    simpa [prefixWord, tailWord_7902666, baseEnd_7902666] using wordTrace_append hprefix tailTrace_7902666
  have hstable : (prefixWord ++ tailWord_7902666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902666).length < 2 ^ (prefixWord ++ tailWord_7902666).sum := by decide
  have hdescent : baseEnd_7902666 < baseStart_7902666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902682 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_7902682 : Nat := 118140960795 + 7902682 * 2 ^ 59
def prefixEnd_7902682 : Nat := 4983230072969 + 3 ^ 40 * 7902682 * 2
def baseEnd_7902682 : Nat := 1352624775211518318010411

theorem tailTrace_7902682 : CollatzResearch.WordTrace tailWord_7902682 prefixEnd_7902682 1352624775211518318010411 := by
  unfold tailWord_7902682
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058622988985064869485575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192156327970626839651961533 72058622988985064869485575)
  ·
    refine ⟨108087934483477597304228363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72058622988985064869485575 108087934483477597304228363)
    ·
      refine ⟨162131901725216395956342545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108087934483477597304228363 162131901725216395956342545)
      ·
        refine ⟨121598926293912296967256909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162131901725216395956342545 121598926293912296967256909)
        ·
          refine ⟨45599597360217111362721341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121598926293912296967256909 45599597360217111362721341)
          ·
            refine ⟨17099849010081416761020503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45599597360217111362721341 17099849010081416761020503)
            ·
              refine ⟨25649773515122125141530755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17099849010081416761020503 25649773515122125141530755)
              ·
                refine ⟨38474660272683187712296133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25649773515122125141530755 38474660272683187712296133)
                ·
                  refine ⟨7213998801128097696055525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38474660272683187712296133 7213998801128097696055525)
                  ·
                    refine ⟨1352624775211518318010411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213998801128097696055525 1352624775211518318010411)
                    ·
                      rfl

theorem cell23_7902682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_7902682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902682 prefixEnd_7902682 := by exact prefixLift 7902682
  have htrace : WordTrace (prefixWord ++ tailWord_7902682) baseStart_7902682 baseEnd_7902682 := by
    simpa [prefixWord, tailWord_7902682, baseEnd_7902682] using wordTrace_append hprefix tailTrace_7902682
  have hstable : (prefixWord ++ tailWord_7902682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902682).length < 2 ^ (prefixWord ++ tailWord_7902682).sum := by decide
  have hdescent : baseEnd_7902682 < baseStart_7902682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902689 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_7902689 : Nat := 118140960795 + 7902689 * 2 ^ 59
def prefixEnd_7902689 : Nat := 4983230072969 + 3 ^ 40 * 7902689 * 2
def baseEnd_7902689 : Nat := 4057877919999136426643701

theorem tailTrace_7902689 : CollatzResearch.WordTrace tailWord_7902689 prefixEnd_7902689 4057877919999136426643701 := by
  unfold tailWord_7902689
  simp only [CollatzResearch.WordTrace]
  refine ⟨288234747266914899673447121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192156498177943266448964747 288234747266914899673447121)
  ·
    refine ⟨216176060450186174755085341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288234747266914899673447121 216176060450186174755085341)
    ·
      refine ⟨81066022668819815533157003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216176060450186174755085341 81066022668819815533157003)
      ·
        refine ⟨121599034003229723299735505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81066022668819815533157003 121599034003229723299735505)
        ·
          refine ⟨91199275502422292474801629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121599034003229723299735505 91199275502422292474801629)
          ·
            refine ⟨34199728313408359678050611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91199275502422292474801629 34199728313408359678050611)
            ·
              refine ⟨51299592470112539517075917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34199728313408359678050611 51299592470112539517075917)
              ·
                refine ⟨19237347176292202318903469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51299592470112539517075917 19237347176292202318903469)
                ·
                  refine ⟨7214005191109575869588801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19237347176292202318903469 7214005191109575869588801)
                  ·
                    refine ⟨5410503893332181902191601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214005191109575869588801 5410503893332181902191601)
                    ·
                      refine ⟨4057877919999136426643701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410503893332181902191601 4057877919999136426643701)
                      ·
                        rfl

theorem cell23_7902689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_7902689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902689 prefixEnd_7902689 := by exact prefixLift 7902689
  have htrace : WordTrace (prefixWord ++ tailWord_7902689) baseStart_7902689 baseEnd_7902689 := by
    simpa [prefixWord, tailWord_7902689, baseEnd_7902689] using wordTrace_append hprefix tailTrace_7902689
  have hstable : (prefixWord ++ tailWord_7902689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902689).length < 2 ^ (prefixWord ++ tailWord_7902689).sum := by decide
  have hdescent : baseEnd_7902689 < baseStart_7902689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902706 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7902706 : Nat := 118140960795 + 7902706 * 2 ^ 59
def prefixEnd_7902706 : Nat := 4983230072969 + 3 ^ 40 * 7902706 * 2
def baseEnd_7902706 : Nat := 4057886649170262860131123

theorem tailTrace_7902706 : CollatzResearch.WordTrace tailWord_7902706 prefixEnd_7902706 4057886649170262860131123 := by
  unfold tailWord_7902706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058841826963327894203993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192156911538568874384543981 72058841826963327894203993)
  ·
    refine ⟨54044131370222495920652995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72058841826963327894203993 54044131370222495920652995)
    ·
      refine ⟨81066197055333743880979493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54044131370222495920652995 81066197055333743880979493)
      ·
        refine ⟨15199911947875076977683655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81066197055333743880979493 15199911947875076977683655)
        ·
          refine ⟨22799867921812615466525483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15199911947875076977683655 22799867921812615466525483)
          ·
            refine ⟨34199801882718923199788225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22799867921812615466525483 34199801882718923199788225)
            ·
              refine ⟨25649851412039192399841169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34199801882718923199788225 25649851412039192399841169)
              ·
                refine ⟨19237388559029394299880877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25649851412039192399841169 19237388559029394299880877)
                ·
                  refine ⟨7214020709636022862455329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19237388559029394299880877 7214020709636022862455329)
                  ·
                    refine ⟨5410515532227017146841497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214020709636022862455329 5410515532227017146841497)
                    ·
                      refine ⟨4057886649170262860131123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410515532227017146841497 4057886649170262860131123)
                      ·
                        rfl

theorem cell23_7902706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7902706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902706 prefixEnd_7902706 := by exact prefixLift 7902706
  have htrace : WordTrace (prefixWord ++ tailWord_7902706) baseStart_7902706 baseEnd_7902706 := by
    simpa [prefixWord, tailWord_7902706, baseEnd_7902706] using wordTrace_append hprefix tailTrace_7902706
  have hstable : (prefixWord ++ tailWord_7902706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902706).length < 2 ^ (prefixWord ++ tailWord_7902706).sum := by decide
  have hdescent : baseEnd_7902706 < baseStart_7902706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902712 : List Nat := [2, 1, 2, 1, 1, 7, 2, 7]
def baseStart_7902712 : Nat := 118140960795 + 7902712 * 2 ^ 59
def prefixEnd_7902712 : Nat := 4983230072969 + 3 ^ 40 * 7902712 * 2
def baseEnd_7902712 : Nat := 150292212224229253209485

theorem tailTrace_7902712 : CollatzResearch.WordTrace tailWord_7902712 prefixEnd_7902712 150292212224229253209485 := by
  unfold tailWord_7902712
  simp only [CollatzResearch.WordTrace]
  refine ⟨144117793072915787300767195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192157057430554383067689593 144117793072915787300767195)
  ·
    refine ⟨216176689609373680951150793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144117793072915787300767195 216176689609373680951150793)
    ·
      refine ⟨162132517207030260713363095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216176689609373680951150793 162132517207030260713363095)
      ·
        refine ⟨243198775810545391070044643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162132517207030260713363095 243198775810545391070044643)
        ·
          refine ⟨364798163715818086605066965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243198775810545391070044643 364798163715818086605066965)
          ·
            refine ⟨8549956962089486404806257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364798163715818086605066965 8549956962089486404806257)
            ·
              refine ⟨6412467721567114803604693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549956962089486404806257 6412467721567114803604693)
              ·
                refine ⟨150292212224229253209485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6412467721567114803604693 150292212224229253209485)
                ·
                  rfl

theorem cell23_7902712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 7].length) (baseStart_7902712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902712 prefixEnd_7902712 := by exact prefixLift 7902712
  have htrace : WordTrace (prefixWord ++ tailWord_7902712) baseStart_7902712 baseEnd_7902712 := by
    simpa [prefixWord, tailWord_7902712, baseEnd_7902712] using wordTrace_append hprefix tailTrace_7902712
  have hstable : (prefixWord ++ tailWord_7902712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902712).length < 2 ^ (prefixWord ++ tailWord_7902712).sum := by decide
  have hdescent : baseEnd_7902712 < baseStart_7902712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902740 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7902740 : Nat := 118140960795 + 7902740 * 2 ^ 59
def prefixEnd_7902740 : Nat := 4983230072969 + 3 ^ 40 * 7902740 * 2
def baseEnd_7902740 : Nat := 4057904107512515727105967

theorem tailTrace_7902740 : CollatzResearch.WordTrace tailWord_7902740 prefixEnd_7902740 4057904107512515727105967 := by
  unfold tailWord_7902740
  simp only [CollatzResearch.WordTrace]
  refine ⟨144118303694865067691776837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192157738259820090255702449 144118303694865067691776837)
  ·
    refine ⟨27022181942787200192208157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144118303694865067691776837 27022181942787200192208157)
    ·
      refine ⟨10133318228545200072078059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27022181942787200192208157 10133318228545200072078059)
      ·
        refine ⟨15199977342817800108117089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133318228545200072078059 15199977342817800108117089)
        ·
          refine ⟨11399983007113350081087817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15199977342817800108117089 11399983007113350081087817)
          ·
            refine ⟨8549987255335012560815863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399983007113350081087817 8549987255335012560815863)
            ·
              refine ⟨12824980883002518841223795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549987255335012560815863 12824980883002518841223795)
              ·
                refine ⟨19237471324503778261835693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824980883002518841223795 19237471324503778261835693)
                ·
                  refine ⟨7214051746688916848188385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19237471324503778261835693 7214051746688916848188385)
                  ·
                    refine ⟨5410538810016687636141289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214051746688916848188385 5410538810016687636141289)
                    ·
                      refine ⟨4057904107512515727105967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410538810016687636141289 4057904107512515727105967)
                      ·
                        rfl

theorem cell23_7902740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7902740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902740 prefixEnd_7902740 := by exact prefixLift 7902740
  have htrace : WordTrace (prefixWord ++ tailWord_7902740) baseStart_7902740 baseEnd_7902740 := by
    simpa [prefixWord, tailWord_7902740, baseEnd_7902740] using wordTrace_append hprefix tailTrace_7902740
  have hstable : (prefixWord ++ tailWord_7902740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902740).length < 2 ^ (prefixWord ++ tailWord_7902740).sum := by decide
  have hdescent : baseEnd_7902740 < baseStart_7902740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902749 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_7902749 : Nat := 118140960795 + 7902749 * 2 ^ 59
def prefixEnd_7902749 : Nat := 4983230072969 + 3 ^ 40 * 7902749 * 2
def baseEnd_7902749 : Nat := 4057908728838406191893425

theorem tailTrace_7902749 : CollatzResearch.WordTrace tailWord_7902749 prefixEnd_7902749 4057908728838406191893425 := by
  unfold tailWord_7902749
  simp only [CollatzResearch.WordTrace]
  refine ⟨288236935646697529920631301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192157957097798353280420867 288236935646697529920631301)
  ·
    refine ⟨54044425433755786860118369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288236935646697529920631301 54044425433755786860118369)
    ·
      refine ⟨40533319075316840145088777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54044425433755786860118369 40533319075316840145088777)
      ·
        refine ⟨30399989306487630108816583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40533319075316840145088777 30399989306487630108816583)
        ·
          refine ⟨45599983959731445163224875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30399989306487630108816583 45599983959731445163224875)
          ·
            refine ⟨68399975939597167744837313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45599983959731445163224875 68399975939597167744837313)
            ·
              refine ⟨51299981954697875808627985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68399975939597167744837313 51299981954697875808627985)
              ·
                refine ⟨38474986466023406856470989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51299981954697875808627985 38474986466023406856470989)
                ·
                  refine ⟨14428119924758777571176621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38474986466023406856470989 14428119924758777571176621)
                  ·
                    refine ⟨5410544971784541589191233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14428119924758777571176621 5410544971784541589191233)
                    ·
                      refine ⟨4057908728838406191893425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410544971784541589191233 4057908728838406191893425)
                      ·
                        rfl

theorem cell23_7902749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_7902749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902749 prefixEnd_7902749 := by exact prefixLift 7902749
  have htrace : WordTrace (prefixWord ++ tailWord_7902749) baseStart_7902749 baseEnd_7902749 := by
    simpa [prefixWord, tailWord_7902749, baseEnd_7902749] using wordTrace_append hprefix tailTrace_7902749
  have hstable : (prefixWord ++ tailWord_7902749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902749).length < 2 ^ (prefixWord ++ tailWord_7902749).sum := by decide
  have hdescent : baseEnd_7902749 < baseStart_7902749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902750 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7902750 : Nat := 118140960795 + 7902750 * 2 ^ 59
def prefixEnd_7902750 : Nat := 4983230072969 + 3 ^ 40 * 7902750 * 2
def baseEnd_7902750 : Nat := 1352636414106353562660307

theorem tailTrace_7902750 : CollatzResearch.WordTrace tailWord_7902750 prefixEnd_7902750 1352636414106353562660307 := by
  unfold tailWord_7902750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36029621514961738386427213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192157981413129271394278469 36029621514961738386427213)
  ·
    refine ⟨13511108068110651894910205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36029621514961738386427213 13511108068110651894910205)
    ·
      refine ⟨5066665525541494460591327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13511108068110651894910205 5066665525541494460591327)
      ·
        refine ⟨7599998288312241690886991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066665525541494460591327 7599998288312241690886991)
        ·
          refine ⟨11399997432468362536330487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599998288312241690886991 11399997432468362536330487)
          ·
            refine ⟨17099996148702543804495731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399997432468362536330487 17099996148702543804495731)
            ·
              refine ⟨25649994223053815706743597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17099996148702543804495731 25649994223053815706743597)
              ·
                refine ⟨9618747833645180890028849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25649994223053815706743597 9618747833645180890028849)
                ·
                  refine ⟨7214060875233885667521637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618747833645180890028849 7214060875233885667521637)
                  ·
                    refine ⟨1352636414106353562660307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214060875233885667521637 1352636414106353562660307)
                    ·
                      rfl

theorem cell23_7902750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7902750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902750 prefixEnd_7902750 := by exact prefixLift 7902750
  have htrace : WordTrace (prefixWord ++ tailWord_7902750) baseStart_7902750 baseEnd_7902750 := by
    simpa [prefixWord, tailWord_7902750, baseEnd_7902750] using wordTrace_append hprefix tailTrace_7902750
  have hstable : (prefixWord ++ tailWord_7902750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902750).length < 2 ^ (prefixWord ++ tailWord_7902750).sum := by decide
  have hdescent : baseEnd_7902750 < baseStart_7902750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902766 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7902766 : Nat := 118140960795 + 7902766 * 2 ^ 59
def prefixEnd_7902766 : Nat := 4983230072969 + 3 ^ 40 * 7902766 * 2
def baseEnd_7902766 : Nat := 4057917458009532625380847

theorem tailTrace_7902766 : CollatzResearch.WordTrace tailWord_7902766 prefixEnd_7902766 4057917458009532625380847 := by
  unfold tailWord_7902766
  simp only [CollatzResearch.WordTrace]
  refine ⟨36029694460954492728000019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192158370458423961216000101 36029694460954492728000019)
  ·
    refine ⟨54044541691431739092000029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36029694460954492728000019 54044541691431739092000029)
    ·
      refine ⟨20266703134286902159500011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54044541691431739092000029 20266703134286902159500011)
      ·
        refine ⟨30400054701430353239250017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20266703134286902159500011 30400054701430353239250017)
        ·
          refine ⟨22800041026072764929437513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30400054701430353239250017 22800041026072764929437513)
          ·
            refine ⟨17100030769554573697078135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22800041026072764929437513 17100030769554573697078135)
            ·
              refine ⟨25650046154331860545617203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17100030769554573697078135 25650046154331860545617203)
              ·
                refine ⟨38475069231497790818425805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25650046154331860545617203 38475069231497790818425805)
                ·
                  refine ⟨14428150961811671556909677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38475069231497790818425805 14428150961811671556909677)
                  ·
                    refine ⟨5410556610679376833841129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14428150961811671556909677 5410556610679376833841129)
                    ·
                      refine ⟨4057917458009532625380847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410556610679376833841129 4057917458009532625380847)
                      ·
                        rfl

theorem cell23_7902766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7902766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902766 prefixEnd_7902766 := by exact prefixLift 7902766
  have htrace : WordTrace (prefixWord ++ tailWord_7902766) baseStart_7902766 baseEnd_7902766 := by
    simpa [prefixWord, tailWord_7902766, baseEnd_7902766] using wordTrace_append hprefix tailTrace_7902766
  have hstable : (prefixWord ++ tailWord_7902766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902766).length < 2 ^ (prefixWord ++ tailWord_7902766).sum := by decide
  have hdescent : baseEnd_7902766 < baseStart_7902766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902790 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7902790 : Nat := 118140960795 + 7902790 * 2 ^ 59
def prefixEnd_7902790 : Nat := 4983230072969 + 3 ^ 40 * 7902790 * 2
def baseEnd_7902790 : Nat := 4057929781545240531480737

theorem tailTrace_7902790 : CollatzResearch.WordTrace tailWord_7902790 prefixEnd_7902790 4057929781545240531480737 := by
  unfold tailWord_7902790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007450969985906060089807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 192158954026365995948582549 9007450969985906060089807)
  ·
    refine ⟨13511176454978859090134711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007450969985906060089807 13511176454978859090134711)
    ·
      refine ⟨20266764682468288635202067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511176454978859090134711 20266764682468288635202067)
      ·
        refine ⟨30400147023702432952803101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20266764682468288635202067 30400147023702432952803101)
        ·
          refine ⟨11400055133888412357301163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30400147023702432952803101 11400055133888412357301163)
          ·
            refine ⟨17100082700832618535951745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400055133888412357301163 17100082700832618535951745)
            ·
              refine ⟨12825062025624463901963809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17100082700832618535951745 12825062025624463901963809)
              ·
                refine ⟨9618796519218347926472857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825062025624463901963809 9618796519218347926472857)
                ·
                  refine ⟨7214097389413760944854643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618796519218347926472857 7214097389413760944854643)
                  ·
                    refine ⟨10821146084120641417281965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214097389413760944854643 10821146084120641417281965)
                    ·
                      refine ⟨4057929781545240531480737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10821146084120641417281965 4057929781545240531480737)
                      ·
                        rfl

theorem cell23_7902790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7902790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902790 prefixEnd_7902790 := by exact prefixLift 7902790
  have htrace : WordTrace (prefixWord ++ tailWord_7902790) baseStart_7902790 baseEnd_7902790 := by
    simpa [prefixWord, tailWord_7902790, baseEnd_7902790] using wordTrace_append hprefix tailTrace_7902790
  have hstable : (prefixWord ++ tailWord_7902790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902790).length < 2 ^ (prefixWord ++ tailWord_7902790).sum := by decide
  have hdescent : baseEnd_7902790 < baseStart_7902790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902796 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_7902796 : Nat := 118140960795 + 7902796 * 2 ^ 59
def prefixEnd_7902796 : Nat := 4983230072969 + 3 ^ 40 * 7902796 * 2
def baseEnd_7902796 : Nat := 4057932862429167508005709

theorem tailTrace_7902796 : CollatzResearch.WordTrace tailWord_7902796 prefixEnd_7902796 4057932862429167508005709 := by
  unfold tailWord_7902796
  simp only [CollatzResearch.WordTrace]
  refine ⟨144119324938763628473796121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192159099918351504631728161 144119324938763628473796121)
  ·
    refine ⟨108089493704072721355347091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144119324938763628473796121 108089493704072721355347091)
    ·
      refine ⟨162134240556109082033020637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108089493704072721355347091 162134240556109082033020637)
      ·
        refine ⟨60800340208540905762382739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162134240556109082033020637 60800340208540905762382739)
        ·
          refine ⟨91200510312811358643574109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60800340208540905762382739 91200510312811358643574109)
          ·
            refine ⟨34200191367304259491340291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91200510312811358643574109 34200191367304259491340291)
            ·
              refine ⟨51300287050956389237010437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34200191367304259491340291 51300287050956389237010437)
              ·
                refine ⟨9618803822054322981939457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51300287050956389237010437 9618803822054322981939457)
                ·
                  refine ⟨7214102866540742236454593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618803822054322981939457 7214102866540742236454593)
                  ·
                    refine ⟨5410577149905556677340945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214102866540742236454593 5410577149905556677340945)
                    ·
                      refine ⟨4057932862429167508005709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410577149905556677340945 4057932862429167508005709)
                      ·
                        rfl

theorem cell23_7902796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_7902796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902796 prefixEnd_7902796 := by exact prefixLift 7902796
  have htrace : WordTrace (prefixWord ++ tailWord_7902796) baseStart_7902796 baseEnd_7902796 := by
    simpa [prefixWord, tailWord_7902796, baseEnd_7902796] using wordTrace_append hprefix tailTrace_7902796
  have hstable : (prefixWord ++ tailWord_7902796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902796).length < 2 ^ (prefixWord ++ tailWord_7902796).sum := by decide
  have hdescent : baseEnd_7902796 < baseStart_7902796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7902805 : Nat := 118140960795 + 7902805 * 2 ^ 59
def prefixEnd_7902805 : Nat := 4983230072969 + 3 ^ 40 * 7902805 * 2
def baseEnd_7902805 : Nat := 4057937483755057972793167

theorem tailTrace_7902805 : CollatzResearch.WordTrace tailWord_7902805 prefixEnd_7902805 4057937483755057972793167 := by
  unfold tailWord_7902805
  simp only [CollatzResearch.WordTrace]
  refine ⟨288238978134494651484669869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192159318756329767656446579 288238978134494651484669869)
  ·
    refine ⟨108089616800435494306751201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288238978134494651484669869 108089616800435494306751201)
    ·
      refine ⟨81067212600326620730063401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108089616800435494306751201 81067212600326620730063401)
      ·
        refine ⟨60800409450244965547547551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81067212600326620730063401 60800409450244965547547551)
        ·
          refine ⟨91200614175367448321321327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60800409450244965547547551 91200614175367448321321327)
          ·
            refine ⟨136800921263051172481981991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91200614175367448321321327 136800921263051172481981991)
            ·
              refine ⟨205201381894576758722972987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136800921263051172481981991 205201381894576758722972987)
              ·
                refine ⟨307802072841865138084459481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205201381894576758722972987 307802072841865138084459481)
                ·
                  refine ⟨230851554631398853563344611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307802072841865138084459481 230851554631398853563344611)
                  ·
                    refine ⟨346277331947098280345016917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230851554631398853563344611 346277331947098280345016917)
                    ·
                      refine ⟨4057937483755057972793167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346277331947098280345016917 4057937483755057972793167)
                      ·
                        rfl

theorem cell23_7902805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7902805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902805 prefixEnd_7902805 := by exact prefixLift 7902805
  have htrace : WordTrace (prefixWord ++ tailWord_7902805) baseStart_7902805 baseEnd_7902805 := by
    simpa [prefixWord, tailWord_7902805, baseEnd_7902805] using wordTrace_append hprefix tailTrace_7902805
  have hstable : (prefixWord ++ tailWord_7902805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902805).length < 2 ^ (prefixWord ++ tailWord_7902805).sum := by decide
  have hdescent : baseEnd_7902805 < baseStart_7902805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902825 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_7902825 : Nat := 118140960795 + 7902825 * 2 ^ 59
def prefixEnd_7902825 : Nat := 4983230072969 + 3 ^ 40 * 7902825 * 2
def baseEnd_7902825 : Nat := 4057947753368147894543075

theorem tailTrace_7902825 : CollatzResearch.WordTrace tailWord_7902825 prefixEnd_7902825 4057947753368147894543075 := by
  unfold tailWord_7902825
  simp only [CollatzResearch.WordTrace]
  refine ⟨288239707594422194900397929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192159805062948129933598619 288239707594422194900397929)
  ·
    refine ⟨216179780695816646175298447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288239707594422194900397929 216179780695816646175298447)
    ·
      refine ⟨324269671043724969262947671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216179780695816646175298447 324269671043724969262947671)
      ·
        refine ⟨486404506565587453894421507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324269671043724969262947671 486404506565587453894421507)
        ·
          refine ⟨729606759848381180841632261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486404506565587453894421507 729606759848381180841632261)
          ·
            refine ⟨136801267471571471407806049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729606759848381180841632261 136801267471571471407806049)
            ·
              refine ⟨102600950603678603555854537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136801267471571471407806049 102600950603678603555854537)
              ·
                refine ⟨76950712952758952666890903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102600950603678603555854537 76950712952758952666890903)
                ·
                  refine ⟨115426069429138429000336355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76950712952758952666890903 115426069429138429000336355)
                  ·
                    refine ⟨173139104143707643500504533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115426069429138429000336355 173139104143707643500504533)
                    ·
                      refine ⟨4057947753368147894543075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173139104143707643500504533 4057947753368147894543075)
                      ·
                        rfl

theorem cell23_7902825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_7902825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902825 prefixEnd_7902825 := by exact prefixLift 7902825
  have htrace : WordTrace (prefixWord ++ tailWord_7902825) baseStart_7902825 baseEnd_7902825 := by
    simpa [prefixWord, tailWord_7902825, baseEnd_7902825] using wordTrace_append hprefix tailTrace_7902825
  have hstable : (prefixWord ++ tailWord_7902825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902825).length < 2 ^ (prefixWord ++ tailWord_7902825).sum := by decide
  have hdescent : baseEnd_7902825 < baseStart_7902825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902832 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_7902832 : Nat := 118140960795 + 7902832 * 2 ^ 59
def prefixEnd_7902832 : Nat := 4983230072969 + 3 ^ 40 * 7902832 * 2
def baseEnd_7902832 : Nat := 1352650449244243122385181

theorem tailTrace_7902832 : CollatzResearch.WordTrace tailWord_7902832 prefixEnd_7902832 1352650449244243122385181 := by
  unfold tailWord_7902832
  simp only [CollatzResearch.WordTrace]
  refine ⟨144119981452698417547951375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192159975270264556730601833 144119981452698417547951375)
  ·
    refine ⟨216179972179047626321927063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144119981452698417547951375 216179972179047626321927063)
    ·
      refine ⟨324269958268571439482890595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216179972179047626321927063 324269958268571439482890595)
      ·
        refine ⟨486404937402857159224335893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324269958268571439482890595 486404937402857159224335893)
        ·
          refine ⟨22800231440758929338640745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 486404937402857159224335893 22800231440758929338640745)
          ·
            refine ⟨17100173580569197003980559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22800231440758929338640745 17100173580569197003980559)
            ·
              refine ⟨25650260370853795505970839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17100173580569197003980559 25650260370853795505970839)
              ·
                refine ⟨38475390556280693258956259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25650260370853795505970839 38475390556280693258956259)
                ·
                  refine ⟨57713085834421039888434389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38475390556280693258956259 57713085834421039888434389)
                  ·
                    refine ⟨1352650449244243122385181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57713085834421039888434389 1352650449244243122385181)
                    ·
                      rfl

theorem cell23_7902832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_7902832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902832 prefixEnd_7902832 := by exact prefixLift 7902832
  have htrace : WordTrace (prefixWord ++ tailWord_7902832) baseStart_7902832 baseEnd_7902832 := by
    simpa [prefixWord, tailWord_7902832, baseEnd_7902832] using wordTrace_append hprefix tailTrace_7902832
  have hstable : (prefixWord ++ tailWord_7902832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902832).length < 2 ^ (prefixWord ++ tailWord_7902832).sum := by decide
  have hdescent : baseEnd_7902832 < baseStart_7902832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902896 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 1, 4]
def baseStart_7902896 : Nat := 118140960795 + 7902896 * 2 ^ 59
def prefixEnd_7902896 : Nat := 4983230072969 + 3 ^ 40 * 7902896 * 2
def baseEnd_7902896 : Nat := 1352661403498205705585083

theorem tailTrace_7902896 : CollatzResearch.WordTrace tailWord_7902896 prefixEnd_7902896 1352661403498205705585083 := by
  unfold tailWord_7902896
  simp only [CollatzResearch.WordTrace]
  refine ⟨144121148588582487013116271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192161531451443316017488361 144121148588582487013116271)
  ·
    refine ⟨216181722882873730519674407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144121148588582487013116271 216181722882873730519674407)
    ·
      refine ⟨324272584324310595779511611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216181722882873730519674407 324272584324310595779511611)
      ·
        refine ⟨486408876486465893669267417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324272584324310595779511611 486408876486465893669267417)
        ·
          refine ⟨364806657364849420251950563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486408876486465893669267417 364806657364849420251950563)
          ·
            refine ⟨547209986047274130377925845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364806657364849420251950563 547209986047274130377925845)
            ·
              refine ⟨12825234047982987430732637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 547209986047274130377925845 12825234047982987430732637)
              ·
                refine ⟨4809462767993620286524739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12825234047982987430732637 4809462767993620286524739)
                ·
                  refine ⟨7214194151990430429787109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809462767993620286524739 7214194151990430429787109)
                  ·
                    refine ⟨1352661403498205705585083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214194151990430429787109 1352661403498205705585083)
                    ·
                      rfl

theorem cell23_7902896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_7902896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902896 prefixEnd_7902896 := by exact prefixLift 7902896
  have htrace : WordTrace (prefixWord ++ tailWord_7902896) baseStart_7902896 baseEnd_7902896 := by
    simpa [prefixWord, tailWord_7902896, baseEnd_7902896] using wordTrace_append hprefix tailTrace_7902896
  have hstable : (prefixWord ++ tailWord_7902896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902896).length < 2 ^ (prefixWord ++ tailWord_7902896).sum := by decide
  have hdescent : baseEnd_7902896 < baseStart_7902896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902964 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7902964 : Nat := 118140960795 + 7902964 * 2 ^ 59
def prefixEnd_7902964 : Nat := 4983230072969 + 3 ^ 40 * 7902964 * 2
def baseEnd_7902964 : Nat := 1352673042393040950234979

theorem tailTrace_7902964 : CollatzResearch.WordTrace tailWord_7902964 prefixEnd_7902964 1352673042393040950234979 := by
  unfold tailWord_7902964
  simp only [CollatzResearch.WordTrace]
  refine ⟨144122388670459310819853973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192163184893945747759805297 144122388670459310819853973)
  ·
    refine ⟨6755736968927780194680655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144122388670459310819853973 6755736968927780194680655)
    ·
      refine ⟨10133605453391670292020983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755736968927780194680655 10133605453391670292020983)
      ·
        refine ⟨15200408180087505438031475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133605453391670292020983 15200408180087505438031475)
        ·
          refine ⟨22800612270131258157047213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15200408180087505438031475 22800612270131258157047213)
          ·
            refine ⟨8550229601299221808892705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22800612270131258157047213 8550229601299221808892705)
            ·
              refine ⟨6412672200974416356669529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550229601299221808892705 6412672200974416356669529)
              ·
                refine ⟨4809504150730812267502147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412672200974416356669529 4809504150730812267502147)
                ·
                  refine ⟨7214256226096218401253221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809504150730812267502147 7214256226096218401253221)
                  ·
                    refine ⟨1352673042393040950234979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214256226096218401253221 1352673042393040950234979)
                    ·
                      rfl

theorem cell23_7902964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7902964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902964 prefixEnd_7902964 := by exact prefixLift 7902964
  have htrace : WordTrace (prefixWord ++ tailWord_7902964) baseStart_7902964 baseEnd_7902964 := by
    simpa [prefixWord, tailWord_7902964, baseEnd_7902964] using wordTrace_append hprefix tailTrace_7902964
  have hstable : (prefixWord ++ tailWord_7902964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902964).length < 2 ^ (prefixWord ++ tailWord_7902964).sum := by decide
  have hdescent : baseEnd_7902964 < baseStart_7902964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902979 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3]
def baseStart_7902979 : Nat := 118140960795 + 7902979 * 2 ^ 59
def prefixEnd_7902979 : Nat := 4983230072969 + 3 ^ 40 * 7902979 * 2
def baseEnd_7902979 : Nat := 4058026829388940292017367

theorem tailTrace_7902979 : CollatzResearch.WordTrace tailWord_7902979 prefixEnd_7902979 4058026829388940292017367 := by
  unfold tailWord_7902979
  simp only [CollatzResearch.WordTrace]
  refine ⟨288245324435864279201503991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192163549623909519467669327 288245324435864279201503991)
  ·
    refine ⟨432367986653796418802255987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288245324435864279201503991 432367986653796418802255987)
    ·
      refine ⟨648551979980694628203383981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432367986653796418802255987 648551979980694628203383981)
      ·
        refine ⟨243206992492760485576268993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648551979980694628203383981 243206992492760485576268993)
        ·
          refine ⟨182405244369570364182201745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243206992492760485576268993 182405244369570364182201745)
          ·
            refine ⟨136803933277177773136651309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182405244369570364182201745 136803933277177773136651309)
            ·
              refine ⟨51301474978941664926244241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136803933277177773136651309 51301474978941664926244241)
              ·
                refine ⟨38476106234206248694683181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51301474978941664926244241 38476106234206248694683181)
                ·
                  refine ⟨14428539837827343260506193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38476106234206248694683181 14428539837827343260506193)
                  ·
                    refine ⟨10821404878370507445379645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14428539837827343260506193 10821404878370507445379645)
                    ·
                      refine ⟨4058026829388940292017367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10821404878370507445379645 4058026829388940292017367)
                      ·
                        rfl

theorem cell23_7902979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_7902979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902979 prefixEnd_7902979 := by exact prefixLift 7902979
  have htrace : WordTrace (prefixWord ++ tailWord_7902979) baseStart_7902979 baseEnd_7902979 := by
    simpa [prefixWord, tailWord_7902979, baseEnd_7902979] using wordTrace_append hprefix tailTrace_7902979
  have hstable : (prefixWord ++ tailWord_7902979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902979).length < 2 ^ (prefixWord ++ tailWord_7902979).sum := by decide
  have hdescent : baseEnd_7902979 < baseStart_7902979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7902986 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_7902986 : Nat := 118140960795 + 7902986 * 2 ^ 59
def prefixEnd_7902986 : Nat := 4983230072969 + 3 ^ 40 * 7902986 * 2
def baseEnd_7902986 : Nat := 1352676807917840588209945

theorem tailTrace_7902986 : CollatzResearch.WordTrace tailWord_7902986 prefixEnd_7902986 1352676807917840588209945 := by
  unfold tailWord_7902986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72061394936709729849252203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192163719831225946264672541 72061394936709729849252203)
  ·
    refine ⟨108092092405064594773878305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72061394936709729849252203 108092092405064594773878305)
    ·
      refine ⟨81069069303798446080408729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108092092405064594773878305 81069069303798446080408729)
      ·
        refine ⟨60801801977848834560306547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81069069303798446080408729 60801801977848834560306547)
        ·
          refine ⟨91202702966773251840459821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60801801977848834560306547 91202702966773251840459821)
          ·
            refine ⟨34201013612539969440172433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91202702966773251840459821 34201013612539969440172433)
            ·
              refine ⟨25650760209404977080129325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34201013612539969440172433 25650760209404977080129325)
              ·
                refine ⟨9619035078526866405048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25650760209404977080129325 9619035078526866405048497)
                ·
                  refine ⟨7214276308895149803786373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619035078526866405048497 7214276308895149803786373)
                  ·
                    refine ⟨1352676807917840588209945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214276308895149803786373 1352676807917840588209945)
                    ·
                      rfl

theorem cell23_7902986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_7902986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7902986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7902986 prefixEnd_7902986 := by exact prefixLift 7902986
  have htrace : WordTrace (prefixWord ++ tailWord_7902986) baseStart_7902986 baseEnd_7902986 := by
    simpa [prefixWord, tailWord_7902986, baseEnd_7902986] using wordTrace_append hprefix tailTrace_7902986
  have hstable : (prefixWord ++ tailWord_7902986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7902986).length < 2 ^ (prefixWord ++ tailWord_7902986).sum := by decide
  have hdescent : baseEnd_7902986 < baseStart_7902986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7902986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903013 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_7903013 : Nat := 118140960795 + 7903013 * 2 ^ 59
def prefixEnd_7903013 : Nat := 4983230072969 + 3 ^ 40 * 7903013 * 2
def baseEnd_7903013 : Nat := 4058044287731193158992211

theorem tailTrace_7903013 : CollatzResearch.WordTrace tailWord_7903013 prefixEnd_7903013 4058044287731193158992211 := by
  unfold tailWord_7903013
  simp only [CollatzResearch.WordTrace]
  refine ⟨288246564517741103008241693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192164376345160735338827795 288246564517741103008241693)
  ·
    refine ⟨108092461694152913628090635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288246564517741103008241693 108092461694152913628090635)
    ·
      refine ⟨162138692541229370442135953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108092461694152913628090635 162138692541229370442135953)
      ·
        refine ⟨121604019405922027831601965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162138692541229370442135953 121604019405922027831601965)
        ·
          refine ⟨45601507277220760436850737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121604019405922027831601965 45601507277220760436850737)
          ·
            refine ⟨34201130457915570327638053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45601507277220760436850737 34201130457915570327638053)
            ·
              refine ⟨6412711960859169436432135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34201130457915570327638053 6412711960859169436432135)
              ·
                refine ⟨9619067941288754154648203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412711960859169436432135 9619067941288754154648203)
                ·
                  refine ⟨14428601911933131231972305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619067941288754154648203 14428601911933131231972305)
                  ·
                    refine ⟨10821451433949848423979229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14428601911933131231972305 10821451433949848423979229)
                    ·
                      refine ⟨4058044287731193158992211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10821451433949848423979229 4058044287731193158992211)
                      ·
                        rfl

theorem cell23_7903013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_7903013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903013 prefixEnd_7903013 := by exact prefixLift 7903013
  have htrace : WordTrace (prefixWord ++ tailWord_7903013) baseStart_7903013 baseEnd_7903013 := by
    simpa [prefixWord, tailWord_7903013, baseEnd_7903013] using wordTrace_append hprefix tailTrace_7903013
  have hstable : (prefixWord ++ tailWord_7903013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903013).length < 2 ^ (prefixWord ++ tailWord_7903013).sum := by decide
  have hdescent : baseEnd_7903013 < baseStart_7903013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903019 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 9, 2]
def baseStart_7903019 : Nat := 118140960795 + 7903019 * 2 ^ 59
def prefixEnd_7903019 : Nat := 4983230072969 + 3 ^ 40 * 7903019 * 2
def baseEnd_7903019 : Nat := 4058047368615120135517183

theorem tailTrace_7903019 : CollatzResearch.WordTrace tailWord_7903019 prefixEnd_7903019 4058047368615120135517183 := by
  unfold tailWord_7903019
  simp only [CollatzResearch.WordTrace]
  refine ⟨288246783355719366032960111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192164522237146244021973407 288246783355719366032960111)
  ·
    refine ⟨432370175033579049049440167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288246783355719366032960111 432370175033579049049440167)
    ·
      refine ⟨648555262550368573574160251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432370175033579049049440167 648555262550368573574160251)
      ·
        refine ⟨972832893825552860361240377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648555262550368573574160251 972832893825552860361240377)
        ·
          refine ⟨729624670369164645270930283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972832893825552860361240377 729624670369164645270930283)
          ·
            refine ⟨1094437005553746967906395425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729624670369164645270930283 1094437005553746967906395425)
            ·
              refine ⟨820827754165310225929796569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094437005553746967906395425 820827754165310225929796569)
              ·
                refine ⟨615620815623982669447347427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820827754165310225929796569 615620815623982669447347427)
                ·
                  refine ⟨923431223435974004171021141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615620815623982669447347427 923431223435974004171021141)
                  ·
                    refine ⟨5410729824820160180689577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 923431223435974004171021141 5410729824820160180689577)
                    ·
                      refine ⟨4058047368615120135517183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410729824820160180689577 4058047368615120135517183)
                      ·
                        rfl

theorem cell23_7903019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 9, 2].length) (baseStart_7903019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903019 prefixEnd_7903019 := by exact prefixLift 7903019
  have htrace : WordTrace (prefixWord ++ tailWord_7903019) baseStart_7903019 baseEnd_7903019 := by
    simpa [prefixWord, tailWord_7903019, baseEnd_7903019] using wordTrace_append hprefix tailTrace_7903019
  have hstable : (prefixWord ++ tailWord_7903019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903019).length < 2 ^ (prefixWord ++ tailWord_7903019).sum := by decide
  have hdescent : baseEnd_7903019 < baseStart_7903019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903036 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_7903036 : Nat := 118140960795 + 7903036 * 2 ^ 59
def prefixEnd_7903036 : Nat := 4983230072969 + 3 ^ 40 * 7903036 * 2
def baseEnd_7903036 : Nat := 4058056097786246569004605

theorem tailTrace_7903036 : CollatzResearch.WordTrace tailWord_7903036 prefixEnd_7903036 4058056097786246569004605 := by
  unfold tailWord_7903036
  simp only [CollatzResearch.WordTrace]
  refine ⟨144123701698328888968164481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192164935597771851957552641 144123701698328888968164481)
  ·
    refine ⟨108092776273746666726123361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144123701698328888968164481 108092776273746666726123361)
    ·
      refine ⟨81069582205310000044592521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108092776273746666726123361 81069582205310000044592521)
      ·
        refine ⟨60802186653982500033444391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81069582205310000044592521 60802186653982500033444391)
        ·
          refine ⟨91203279980973750050166587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60802186653982500033444391 91203279980973750050166587)
          ·
            refine ⟨136804919971460625075249881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91203279980973750050166587 136804919971460625075249881)
            ·
              refine ⟨102603689978595468806437411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136804919971460625075249881 102603689978595468806437411)
              ·
                refine ⟨153905534967893203209656117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102603689978595468806437411 153905534967893203209656117)
                ·
                  refine ⟨14428643903239987800905261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153905534967893203209656117 14428643903239987800905261)
                  ·
                    refine ⟨5410741463714995425339473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14428643903239987800905261 5410741463714995425339473)
                    ·
                      refine ⟨4058056097786246569004605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410741463714995425339473 4058056097786246569004605)
                      ·
                        rfl

theorem cell23_7903036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_7903036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903036 prefixEnd_7903036 := by exact prefixLift 7903036
  have htrace : WordTrace (prefixWord ++ tailWord_7903036) baseStart_7903036 baseEnd_7903036 := by
    simpa [prefixWord, tailWord_7903036, baseEnd_7903036] using wordTrace_append hprefix tailTrace_7903036
  have hstable : (prefixWord ++ tailWord_7903036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903036).length < 2 ^ (prefixWord ++ tailWord_7903036).sum := by decide
  have hdescent : baseEnd_7903036 < baseStart_7903036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903066 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_7903066 : Nat := 118140960795 + 7903066 * 2 ^ 59
def prefixEnd_7903066 : Nat := 4983230072969 + 3 ^ 40 * 7903066 * 2
def baseEnd_7903066 : Nat := 4058071502205881451629467

theorem tailTrace_7903066 : CollatzResearch.WordTrace tailWord_7903066 prefixEnd_7903066 4058071502205881451629467 := by
  unfold tailWord_7903066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72062124396637273264980263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192165665057699395373280701 72062124396637273264980263)
  ·
    refine ⟨108093186594955909897470395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72062124396637273264980263 108093186594955909897470395)
    ·
      refine ⟨162139779892433864846205593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108093186594955909897470395 162139779892433864846205593)
      ·
        refine ⟨121604834919325398634654195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162139779892433864846205593 121604834919325398634654195)
        ·
          refine ⟨182407252378988097951981293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121604834919325398634654195 182407252378988097951981293)
          ·
            refine ⟨68402719642120536731992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182407252378988097951981293 68402719642120536731992985)
            ·
              refine ⟨51302039731590402548994739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68402719642120536731992985 51302039731590402548994739)
              ·
                refine ⟨76953059597385603823492109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51302039731590402548994739 76953059597385603823492109)
                ·
                  refine ⟨28857397349019601433809541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76953059597385603823492109 28857397349019601433809541)
                  ·
                    refine ⟨5410762002941175268839289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28857397349019601433809541 5410762002941175268839289)
                    ·
                      refine ⟨4058071502205881451629467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410762002941175268839289 4058071502205881451629467)
                      ·
                        rfl

theorem cell23_7903066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_7903066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903066 prefixEnd_7903066 := by exact prefixLift 7903066
  have htrace : WordTrace (prefixWord ++ tailWord_7903066) baseStart_7903066 baseEnd_7903066 := by
    simpa [prefixWord, tailWord_7903066, baseEnd_7903066] using wordTrace_append hprefix tailTrace_7903066
  have hstable : (prefixWord ++ tailWord_7903066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903066).length < 2 ^ (prefixWord ++ tailWord_7903066).sum := by decide
  have hdescent : baseEnd_7903066 < baseStart_7903066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903083 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 2, 2, 2]
def baseStart_7903083 : Nat := 118140960795 + 7903083 * 2 ^ 59
def prefixEnd_7903083 : Nat := 4983230072969 + 3 ^ 40 * 7903083 * 2
def baseEnd_7903083 : Nat := 4058080231377007885116889

theorem tailTrace_7903083 : CollatzResearch.WordTrace tailWord_7903083 prefixEnd_7903083 4058080231377007885116889 := by
  unfold tailWord_7903083
  simp only [CollatzResearch.WordTrace]
  refine ⟨288249117627487504963289903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192166078418325003308859935 288249117627487504963289903)
  ·
    refine ⟨432373676441231257444934855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288249117627487504963289903 432373676441231257444934855)
    ·
      refine ⟨648560514661846886167402283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432373676441231257444934855 648560514661846886167402283)
      ·
        refine ⟨972840771992770329251103425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648560514661846886167402283 972840771992770329251103425)
        ·
          refine ⟨729630578994577746938327569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 972840771992770329251103425 729630578994577746938327569)
          ·
            refine ⟨547222934245933310203745677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729630578994577746938327569 547222934245933310203745677)
            ·
              refine ⟨205208600342224991326404629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547222934245933310203745677 205208600342224991326404629)
              ·
                refine ⟨9619153141041796468425217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205208600342224991326404629 9619153141041796468425217)
                ·
                  refine ⟨7214364855781347351318913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619153141041796468425217 7214364855781347351318913)
                  ·
                    refine ⟨5410773641836010513489185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214364855781347351318913 5410773641836010513489185)
                    ·
                      refine ⟨4058080231377007885116889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410773641836010513489185 4058080231377007885116889)
                      ·
                        rfl

theorem cell23_7903083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2, 2].length) (baseStart_7903083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903083 prefixEnd_7903083 := by exact prefixLift 7903083
  have htrace : WordTrace (prefixWord ++ tailWord_7903083) baseStart_7903083 baseEnd_7903083 := by
    simpa [prefixWord, tailWord_7903083, baseEnd_7903083] using wordTrace_append hprefix tailTrace_7903083
  have hstable : (prefixWord ++ tailWord_7903083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903083).length < 2 ^ (prefixWord ++ tailWord_7903083).sum := by decide
  have hdescent : baseEnd_7903083 < baseStart_7903083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903094 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7903094 : Nat := 118140960795 + 7903094 * 2 ^ 59
def prefixEnd_7903094 : Nat := 4983230072969 + 3 ^ 40 * 7903094 * 2
def baseEnd_7903094 : Nat := 4058085879664207342079339

theorem tailTrace_7903094 : CollatzResearch.WordTrace tailWord_7903094 prefixEnd_7903094 4058085879664207342079339 := by
  unfold tailWord_7903094
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015594926902978365121271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192166345886965102561293557 18015594926902978365121271)
  ·
    refine ⟨27023392390354467547681907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015594926902978365121271 27023392390354467547681907)
    ·
      refine ⟨40535088585531701321522861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023392390354467547681907 40535088585531701321522861)
      ·
        refine ⟨15200658219574387995571073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40535088585531701321522861 15200658219574387995571073)
        ·
          refine ⟨11400493664680790996678305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15200658219574387995571073 11400493664680790996678305)
          ·
            refine ⟨8550370248510593247508729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11400493664680790996678305 8550370248510593247508729)
            ·
              refine ⟨6412777686382944935631547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550370248510593247508729 6412777686382944935631547)
              ·
                refine ⟨9619166529574417403447321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412777686382944935631547 9619166529574417403447321)
                ·
                  refine ⟨7214374897180813052585491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619166529574417403447321 7214374897180813052585491)
                  ·
                    refine ⟨10821562345771219578878237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214374897180813052585491 10821562345771219578878237)
                    ·
                      refine ⟨4058085879664207342079339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10821562345771219578878237 4058085879664207342079339)
                      ·
                        rfl

theorem cell23_7903094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7903094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903094 prefixEnd_7903094 := by exact prefixLift 7903094
  have htrace : WordTrace (prefixWord ++ tailWord_7903094) baseStart_7903094 baseEnd_7903094 := by
    simpa [prefixWord, tailWord_7903094, baseEnd_7903094] using wordTrace_append hprefix tailTrace_7903094
  have hstable : (prefixWord ++ tailWord_7903094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903094).length < 2 ^ (prefixWord ++ tailWord_7903094).sum := by decide
  have hdescent : baseEnd_7903094 < baseStart_7903094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903099 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3]
def baseStart_7903099 : Nat := 118140960795 + 7903099 * 2 ^ 59
def prefixEnd_7903099 : Nat := 4983230072969 + 3 ^ 40 * 7903099 * 2
def baseEnd_7903099 : Nat := 4058088447067479822516815

theorem tailTrace_7903099 : CollatzResearch.WordTrace tailWord_7903099 prefixEnd_7903099 4058088447067479822516815 := by
  unfold tailWord_7903099
  simp only [CollatzResearch.WordTrace]
  refine ⟨288249701195429539695872351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192166467463619693130581567 288249701195429539695872351)
  ·
    refine ⟨432374551793144309543808527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288249701195429539695872351 432374551793144309543808527)
    ·
      refine ⟨648561827689716464315712791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432374551793144309543808527 648561827689716464315712791)
      ·
        refine ⟨972842741534574696473569187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648561827689716464315712791 972842741534574696473569187)
        ·
          refine ⟨1459264112301862044710353781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972842741534574696473569187 1459264112301862044710353781)
          ·
            refine ⟨136806010528299566691595667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1459264112301862044710353781 136806010528299566691595667)
            ·
              refine ⟨205209015792449350037393501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136806010528299566691595667 205209015792449350037393501)
              ·
                refine ⟨76953380922168506264022563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205209015792449350037393501 76953380922168506264022563)
                ·
                  refine ⟨115430071383252759396033845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76953380922168506264022563 115430071383252759396033845)
                  ·
                    refine ⟨10821569192179946193378173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115430071383252759396033845 10821569192179946193378173)
                    ·
                      refine ⟨4058088447067479822516815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10821569192179946193378173 4058088447067479822516815)
                      ·
                        rfl

theorem cell23_7903099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 3].length) (baseStart_7903099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903099 prefixEnd_7903099 := by exact prefixLift 7903099
  have htrace : WordTrace (prefixWord ++ tailWord_7903099) baseStart_7903099 baseEnd_7903099 := by
    simpa [prefixWord, tailWord_7903099, baseEnd_7903099] using wordTrace_append hprefix tailTrace_7903099
  have hstable : (prefixWord ++ tailWord_7903099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903099).length < 2 ^ (prefixWord ++ tailWord_7903099).sum := by decide
  have hdescent : baseEnd_7903099 < baseStart_7903099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903129 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_7903129 : Nat := 118140960795 + 7903129 * 2 ^ 59
def prefixEnd_7903129 : Nat := 4983230072969 + 3 ^ 40 * 7903129 * 2
def baseEnd_7903129 : Nat := 4058103851487114705141677

theorem tailTrace_7903129 : CollatzResearch.WordTrace tailWord_7903129 prefixEnd_7903129 4058103851487114705141677 := by
  unfold tailWord_7903129
  simp only [CollatzResearch.WordTrace]
  refine ⟨288250795385320854819464441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192167196923547236546309627 288250795385320854819464441)
  ·
    refine ⟨216188096538990641114598331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288250795385320854819464441 216188096538990641114598331)
    ·
      refine ⟨324282144808485961671897497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216188096538990641114598331 324282144808485961671897497)
      ·
        refine ⟨243211608606364471253923123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324282144808485961671897497 243211608606364471253923123)
        ·
          refine ⟨364817412909546706880884685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243211608606364471253923123 364817412909546706880884685)
          ·
            refine ⟨136806529841080015080331757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364817412909546706880884685 136806529841080015080331757)
            ·
              refine ⟨51302448690405005655124409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136806529841080015080331757 51302448690405005655124409)
              ·
                refine ⟨38476836517803754241343307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51302448690405005655124409 38476836517803754241343307)
                ·
                  refine ⟨57715254776705631362014961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38476836517803754241343307 57715254776705631362014961)
                  ·
                    refine ⟨43286441082529223521511221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57715254776705631362014961 43286441082529223521511221)
                    ·
                      refine ⟨4058103851487114705141677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43286441082529223521511221 4058103851487114705141677)
                      ·
                        rfl

theorem cell23_7903129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_7903129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903129 prefixEnd_7903129 := by exact prefixLift 7903129
  have htrace : WordTrace (prefixWord ++ tailWord_7903129) baseStart_7903129 baseEnd_7903129 := by
    simpa [prefixWord, tailWord_7903129, baseEnd_7903129] using wordTrace_append hprefix tailTrace_7903129
  have hstable : (prefixWord ++ tailWord_7903129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903129).length < 2 ^ (prefixWord ++ tailWord_7903129).sum := by decide
  have hdescent : baseEnd_7903129 < baseStart_7903129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903139 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7903139 : Nat := 118140960795 + 7903139 * 2 ^ 59
def prefixEnd_7903139 : Nat := 4983230072969 + 3 ^ 40 * 7903139 * 2
def baseEnd_7903139 : Nat := 4058108986293659666016631

theorem tailTrace_7903139 : CollatzResearch.WordTrace tailWord_7903139 prefixEnd_7903139 4058108986293659666016631 := by
  unfold tailWord_7903139
  simp only [CollatzResearch.WordTrace]
  refine ⟨288251160115284626527328471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192167440076856417684885647 288251160115284626527328471)
  ·
    refine ⟨432376740172926939790992707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288251160115284626527328471 432376740172926939790992707)
    ·
      refine ⟨648565110259390409686489061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432376740172926939790992707 648565110259390409686489061)
      ·
        refine ⟨121605958173635701816216699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 648565110259390409686489061 121605958173635701816216699)
        ·
          refine ⟨182408937260453552724325049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121605958173635701816216699 182408937260453552724325049)
          ·
            refine ⟨136806702945340164543243787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182408937260453552724325049 136806702945340164543243787)
            ·
              refine ⟨205210054418010246814865681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136806702945340164543243787 205210054418010246814865681)
              ·
                refine ⟨153907540813507685111149261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205210054418010246814865681 153907540813507685111149261)
                ·
                  refine ⟨57715327805065381916680973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153907540813507685111149261 57715327805065381916680973)
                  ·
                    refine ⟨21643247926899518218755365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57715327805065381916680973 21643247926899518218755365)
                    ·
                      refine ⟨4058108986293659666016631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21643247926899518218755365 4058108986293659666016631)
                      ·
                        rfl

theorem cell23_7903139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7903139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903139 prefixEnd_7903139 := by exact prefixLift 7903139
  have htrace : WordTrace (prefixWord ++ tailWord_7903139) baseStart_7903139 baseEnd_7903139 := by
    simpa [prefixWord, tailWord_7903139, baseEnd_7903139] using wordTrace_append hprefix tailTrace_7903139
  have hstable : (prefixWord ++ tailWord_7903139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903139).length < 2 ^ (prefixWord ++ tailWord_7903139).sum := by decide
  have hdescent : baseEnd_7903139 < baseStart_7903139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903140 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 5]
def baseStart_7903140 : Nat := 118140960795 + 7903140 * 2 ^ 59
def prefixEnd_7903140 : Nat := 4983230072969 + 3 ^ 40 * 7903140 * 2
def baseEnd_7903140 : Nat := 450901055530479351344903

theorem tailTrace_7903140 : CollatzResearch.WordTrace tailWord_7903140 prefixEnd_7903140 450901055530479351344903 := by
  unfold tailWord_7903140
  simp only [CollatzResearch.WordTrace]
  refine ⟨144125598294140501849057437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192167464392187335798743249 144125598294140501849057437)
  ·
    refine ⟨54047099360302688193396539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144125598294140501849057437 54047099360302688193396539)
    ·
      refine ⟨81070649040454032290094809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54047099360302688193396539 81070649040454032290094809)
      ·
        refine ⟨60802986780340524217571107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81070649040454032290094809 60802986780340524217571107)
        ·
          refine ⟨91204480170510786326356661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60802986780340524217571107 91204480170510786326356661)
          ·
            refine ⟨8550420015985386218095937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91204480170510786326356661 8550420015985386218095937)
            ·
              refine ⟨6412815011989039663571953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550420015985386218095937 6412815011989039663571953)
              ·
                refine ⟨4809611258991779747678965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412815011989039663571953 4809611258991779747678965)
                ·
                  refine ⟨450901055530479351344903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809611258991779747678965 450901055530479351344903)
                  ·
                    rfl

theorem cell23_7903140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_7903140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903140 prefixEnd_7903140 := by exact prefixLift 7903140
  have htrace : WordTrace (prefixWord ++ tailWord_7903140) baseStart_7903140 baseEnd_7903140 := by
    simpa [prefixWord, tailWord_7903140, baseEnd_7903140] using wordTrace_append hprefix tailTrace_7903140
  have hstable : (prefixWord ++ tailWord_7903140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903140).length < 2 ^ (prefixWord ++ tailWord_7903140).sum := by decide
  have hdescent : baseEnd_7903140 < baseStart_7903140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903143 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7903143 : Nat := 118140960795 + 7903143 * 2 ^ 59
def prefixEnd_7903143 : Nat := 4983230072969 + 3 ^ 40 * 7903143 * 2
def baseEnd_7903143 : Nat := 4058111040216277650366613

theorem tailTrace_7903143 : CollatzResearch.WordTrace tailWord_7903143 prefixEnd_7903143 4058111040216277650366613 := by
  unfold tailWord_7903143
  simp only [CollatzResearch.WordTrace]
  refine ⟨288251306007270135210474083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192167537338180090140316055 288251306007270135210474083)
  ·
    refine ⟨432376959010905202815711125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288251306007270135210474083 432376959010905202815711125)
    ·
      refine ⟨20267669953636181381986459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432376959010905202815711125 20267669953636181381986459)
      ·
        refine ⟨30401504930454272072979689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267669953636181381986459 30401504930454272072979689)
        ·
          refine ⟨22801128697840704054734767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30401504930454272072979689 22801128697840704054734767)
          ·
            refine ⟨34201693046761056082102151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22801128697840704054734767 34201693046761056082102151)
            ·
              refine ⟨51302539570141584123153227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34201693046761056082102151 51302539570141584123153227)
              ·
                refine ⟨76953809355212376184729841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51302539570141584123153227 76953809355212376184729841)
                ·
                  refine ⟨57715357016409282138547381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76953809355212376184729841 57715357016409282138547381)
                  ·
                    refine ⟨5410814720288370200488817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57715357016409282138547381 5410814720288370200488817)
                    ·
                      refine ⟨4058111040216277650366613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410814720288370200488817 4058111040216277650366613)
                      ·
                        rfl

theorem cell23_7903143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7903143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903143 prefixEnd_7903143 := by exact prefixLift 7903143
  have htrace : WordTrace (prefixWord ++ tailWord_7903143) baseStart_7903143 baseEnd_7903143 := by
    simpa [prefixWord, tailWord_7903143, baseEnd_7903143] using wordTrace_append hprefix tailTrace_7903143
  have hstable : (prefixWord ++ tailWord_7903143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903143).length < 2 ^ (prefixWord ++ tailWord_7903143).sum := by decide
  have hdescent : baseEnd_7903143 < baseStart_7903143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903179 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 8]
def baseStart_7903179 : Nat := 118140960795 + 7903179 * 2 ^ 59
def prefixEnd_7903179 : Nat := 4983230072969 + 3 ^ 40 * 7903179 * 2
def baseEnd_7903179 : Nat := 450903280613315501057383

theorem tailTrace_7903179 : CollatzResearch.WordTrace tailWord_7903179 prefixEnd_7903179 450903280613315501057383 := by
  unfold tailWord_7903179
  simp only [CollatzResearch.WordTrace]
  refine ⟨288252619035139713358784591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192168412690093142239189727 288252619035139713358784591)
  ·
    refine ⟨432378928552709570038176887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288252619035139713358784591 432378928552709570038176887)
    ·
      refine ⟨648568392829064355057265331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432378928552709570038176887 648568392829064355057265331)
      ·
        refine ⟨972852589243596532585897997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648568392829064355057265331 972852589243596532585897997)
        ·
          refine ⟨364819720966348699719711749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972852589243596532585897997 364819720966348699719711749)
          ·
            refine ⟨68403697681190381197445953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364819720966348699719711749 68403697681190381197445953)
            ·
              refine ⟨51302773260892785898084465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68403697681190381197445953 51302773260892785898084465)
              ·
                refine ⟨38477079945669589423563349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51302773260892785898084465 38477079945669589423563349)
                ·
                  refine ⟨450903280613315501057383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38477079945669589423563349 450903280613315501057383)
                  ·
                    rfl

theorem cell23_7903179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_7903179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903179 prefixEnd_7903179 := by exact prefixLift 7903179
  have htrace : WordTrace (prefixWord ++ tailWord_7903179) baseStart_7903179 baseEnd_7903179 := by
    simpa [prefixWord, tailWord_7903179, baseEnd_7903179] using wordTrace_append hprefix tailTrace_7903179
  have hstable : (prefixWord ++ tailWord_7903179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903179).length < 2 ^ (prefixWord ++ tailWord_7903179).sum := by decide
  have hdescent : baseEnd_7903179 < baseStart_7903179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903219 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_7903219 : Nat := 118140960795 + 7903219 * 2 ^ 59
def prefixEnd_7903219 : Nat := 4983230072969 + 3 ^ 40 * 7903219 * 2
def baseEnd_7903219 : Nat := 4058150064746019353016263

theorem tailTrace_7903219 : CollatzResearch.WordTrace tailWord_7903219 prefixEnd_7903219 4058150064746019353016263 := by
  unfold tailWord_7903219
  simp only [CollatzResearch.WordTrace]
  refine ⟨288254077954994800190240711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192169385303329866793493807 288254077954994800190240711)
  ·
    refine ⟨432381116932492200285361067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288254077954994800190240711 432381116932492200285361067)
    ·
      refine ⟨648571675398738300428041601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432381116932492200285361067 648571675398738300428041601)
      ·
        refine ⟨486428756549053725321031201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648571675398738300428041601 486428756549053725321031201)
        ·
          refine ⟨364821567411790293990773401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486428756549053725321031201 364821567411790293990773401)
          ·
            refine ⟨273616175558842720493080051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364821567411790293990773401 273616175558842720493080051)
            ·
              refine ⟨410424263338264080739620077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273616175558842720493080051 410424263338264080739620077)
              ·
                refine ⟨153909098751849030277357529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410424263338264080739620077 153909098751849030277357529)
                ·
                  refine ⟨115431824063886772708018147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153909098751849030277357529 115431824063886772708018147)
                  ·
                    refine ⟨173147736095830159062027221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115431824063886772708018147 173147736095830159062027221)
                    ·
                      refine ⟨4058150064746019353016263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173147736095830159062027221 4058150064746019353016263)
                      ·
                        rfl

theorem cell23_7903219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_7903219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903219 prefixEnd_7903219 := by exact prefixLift 7903219
  have htrace : WordTrace (prefixWord ++ tailWord_7903219) baseStart_7903219 baseEnd_7903219 := by
    simpa [prefixWord, tailWord_7903219, baseEnd_7903219] using wordTrace_append hprefix tailTrace_7903219
  have hstable : (prefixWord ++ tailWord_7903219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903219).length < 2 ^ (prefixWord ++ tailWord_7903219).sum := by decide
  have hdescent : baseEnd_7903219 < baseStart_7903219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903233 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_7903233 : Nat := 118140960795 + 7903233 * 2 ^ 59
def prefixEnd_7903233 : Nat := 4983230072969 + 3 ^ 40 * 7903233 * 2
def baseEnd_7903233 : Nat := 4058157253475182298241199

theorem tailTrace_7903233 : CollatzResearch.WordTrace tailWord_7903233 prefixEnd_7903233 4058157253475182298241199 := by
  unfold tailWord_7903233
  simp only [CollatzResearch.WordTrace]
  refine ⟨288254588576944080581250353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192169725717962720387500235 288254588576944080581250353)
  ·
    refine ⟨216190941432708060435937765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288254588576944080581250353 216190941432708060435937765)
    ·
      refine ⟨40535801518632761331738331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216190941432708060435937765 40535801518632761331738331)
      ·
        refine ⟨60803702277949141997607497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40535801518632761331738331 60803702277949141997607497)
        ·
          refine ⟨45602776708461856498205623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60803702277949141997607497 45602776708461856498205623)
          ·
            refine ⟨68404165062692784747308435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45602776708461856498205623 68404165062692784747308435)
            ·
              refine ⟨102606247594039177120962653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68404165062692784747308435 102606247594039177120962653)
              ·
                refine ⟨38477342847764691420360995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102606247594039177120962653 38477342847764691420360995)
                ·
                  refine ⟨57716014271647037130541493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38477342847764691420360995 57716014271647037130541493)
                  ·
                    refine ⟨5410876337966909730988265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57716014271647037130541493 5410876337966909730988265)
                    ·
                      refine ⟨4058157253475182298241199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410876337966909730988265 4058157253475182298241199)
                      ·
                        rfl

theorem cell23_7903233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_7903233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903233 prefixEnd_7903233 := by exact prefixLift 7903233
  have htrace : WordTrace (prefixWord ++ tailWord_7903233) baseStart_7903233 baseEnd_7903233 := by
    simpa [prefixWord, tailWord_7903233, baseEnd_7903233] using wordTrace_append hprefix tailTrace_7903233
  have hstable : (prefixWord ++ tailWord_7903233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903233).length < 2 ^ (prefixWord ++ tailWord_7903233).sum := by decide
  have hdescent : baseEnd_7903233 < baseStart_7903233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903280 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_7903280 : Nat := 118140960795 + 7903280 * 2 ^ 59
def prefixEnd_7903280 : Nat := 4983230072969 + 3 ^ 40 * 7903280 * 2
def baseEnd_7903280 : Nat := 4058181387065943614353483

theorem tailTrace_7903280 : CollatzResearch.WordTrace tailWord_7903280 prefixEnd_7903280 4058181387065943614353483 := by
  unfold tailWord_7903280
  simp only [CollatzResearch.WordTrace]
  refine ⟨144128151403886903804105647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192170868538515871738807529 144128151403886903804105647)
  ·
    refine ⟨216192227105830355706158471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144128151403886903804105647 216192227105830355706158471)
    ·
      refine ⟨324288340658745533559237707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216192227105830355706158471 324288340658745533559237707)
      ·
        refine ⟨486432510988118300338856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324288340658745533559237707 486432510988118300338856561)
        ·
          refine ⟨364824383241088725254142421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486432510988118300338856561 364824383241088725254142421)
          ·
            refine ⟨8550571482213016998143963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364824383241088725254142421 8550571482213016998143963)
            ·
              refine ⟨12825857223319525497215945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550571482213016998143963 12825857223319525497215945)
              ·
                refine ⟨9619392917489644122911959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825857223319525497215945 9619392917489644122911959)
                ·
                  refine ⟨14429089376234466184367939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619392917489644122911959 14429089376234466184367939)
                  ·
                    refine ⟨21643634064351699276551909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14429089376234466184367939 21643634064351699276551909)
                    ·
                      refine ⟨4058181387065943614353483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21643634064351699276551909 4058181387065943614353483)
                      ·
                        rfl

theorem cell23_7903280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_7903280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903280 prefixEnd_7903280 := by exact prefixLift 7903280
  have htrace : WordTrace (prefixWord ++ tailWord_7903280) baseStart_7903280 baseEnd_7903280 := by
    simpa [prefixWord, tailWord_7903280, baseEnd_7903280] using wordTrace_append hprefix tailTrace_7903280
  have hstable : (prefixWord ++ tailWord_7903280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903280).length < 2 ^ (prefixWord ++ tailWord_7903280).sum := by decide
  have hdescent : baseEnd_7903280 < baseStart_7903280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903284 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7903284 : Nat := 118140960795 + 7903284 * 2 ^ 59
def prefixEnd_7903284 : Nat := 4983230072969 + 3 ^ 40 * 7903284 * 2
def baseEnd_7903284 : Nat := 4058183440988561598703465

theorem tailTrace_7903284 : CollatzResearch.WordTrace tailWord_7903284 prefixEnd_7903284 4058183440988561598703465 := by
  unfold tailWord_7903284
  simp only [CollatzResearch.WordTrace]
  refine ⟨144128224349879658145678453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192170965799839544194237937 144128224349879658145678453)
  ·
    refine ⟨13512021032801217951157355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144128224349879658145678453 13512021032801217951157355)
    ·
      refine ⟨20268031549201826926736033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512021032801217951157355 20268031549201826926736033)
      ·
        refine ⟨15201023661901370195052025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20268031549201826926736033 15201023661901370195052025)
        ·
          refine ⟨11400767746426027646289019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201023661901370195052025 11400767746426027646289019)
          ·
            refine ⟨17101151619639041469433529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400767746426027646289019 17101151619639041469433529)
            ·
              refine ⟨12825863714729281102075147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17101151619639041469433529 12825863714729281102075147)
              ·
                refine ⟨19238795572093921653112721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12825863714729281102075147 19238795572093921653112721)
                ·
                  refine ⟨14429096679070441239834541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19238795572093921653112721 14429096679070441239834541)
                  ·
                    refine ⟨5410911254651415464937953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14429096679070441239834541 5410911254651415464937953)
                    ·
                      refine ⟨4058183440988561598703465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410911254651415464937953 4058183440988561598703465)
                      ·
                        rfl

theorem cell23_7903284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7903284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903284 prefixEnd_7903284 := by exact prefixLift 7903284
  have htrace : WordTrace (prefixWord ++ tailWord_7903284) baseStart_7903284 baseEnd_7903284 := by
    simpa [prefixWord, tailWord_7903284, baseEnd_7903284] using wordTrace_append hprefix tailTrace_7903284
  have hstable : (prefixWord ++ tailWord_7903284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903284).length < 2 ^ (prefixWord ++ tailWord_7903284).sum := by decide
  have hdescent : baseEnd_7903284 < baseStart_7903284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903293 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7903293 : Nat := 118140960795 + 7903293 * 2 ^ 59
def prefixEnd_7903293 : Nat := 4983230072969 + 3 ^ 40 * 7903293 * 2
def baseEnd_7903293 : Nat := 4058188062314452063490923

theorem tailTrace_7903293 : CollatzResearch.WordTrace tailWord_7903293 prefixEnd_7903293 4058188062314452063490923 := by
  unfold tailWord_7903293
  simp only [CollatzResearch.WordTrace]
  refine ⟨288256776956726710828434533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192171184637817807218956355 288256776956726710828434533)
  ·
    refine ⟨54048145679386258280331475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288256776956726710828434533 54048145679386258280331475)
    ·
      refine ⟨81072218519079387420497213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048145679386258280331475 81072218519079387420497213)
      ·
        refine ⟨30402081944654770282686455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81072218519079387420497213 30402081944654770282686455)
        ·
          refine ⟨45603122916982155424029683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30402081944654770282686455 45603122916982155424029683)
          ·
            refine ⟨68404684375473233136044525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45603122916982155424029683 68404684375473233136044525)
            ·
              refine ⟨25651756640802462426016697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68404684375473233136044525 25651756640802462426016697)
              ·
                refine ⟨19238817480601846819512523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25651756640802462426016697 19238817480601846819512523)
                ·
                  refine ⟨28858226220902770229268785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19238817480601846819512523 28858226220902770229268785)
                  ·
                    refine ⟨21643669665677077671951589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28858226220902770229268785 21643669665677077671951589)
                    ·
                      refine ⟨4058188062314452063490923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21643669665677077671951589 4058188062314452063490923)
                      ·
                        rfl

theorem cell23_7903293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7903293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903293 prefixEnd_7903293 := by exact prefixLift 7903293
  have htrace : WordTrace (prefixWord ++ tailWord_7903293) baseStart_7903293 baseEnd_7903293 := by
    simpa [prefixWord, tailWord_7903293, baseEnd_7903293] using wordTrace_append hprefix tailTrace_7903293
  have hstable : (prefixWord ++ tailWord_7903293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903293).length < 2 ^ (prefixWord ++ tailWord_7903293).sum := by decide
  have hdescent : baseEnd_7903293 < baseStart_7903293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903297 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7903297 : Nat := 118140960795 + 7903297 * 2 ^ 59
def prefixEnd_7903297 : Nat := 4983230072969 + 3 ^ 40 * 7903297 * 2
def baseEnd_7903297 : Nat := 4058190116237070047840905

theorem tailTrace_7903297 : CollatzResearch.WordTrace tailWord_7903297 prefixEnd_7903297 4058190116237070047840905 := by
  unfold tailWord_7903297
  simp only [CollatzResearch.WordTrace]
  refine ⟨288256922848712219511580145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192171281899141479674386763 288256922848712219511580145)
  ·
    refine ⟨216192692136534164633685109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288256922848712219511580145 216192692136534164633685109)
    ·
      refine ⟨20268064887800077934407979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216192692136534164633685109 20268064887800077934407979)
      ·
        refine ⟨30402097331700116901611969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20268064887800077934407979 30402097331700116901611969)
        ·
          refine ⟨22801572998775087676208977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30402097331700116901611969 22801572998775087676208977)
          ·
            refine ⟨17101179749081315757156733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22801572998775087676208977 17101179749081315757156733)
            ·
              refine ⟨6412942405905493408933775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17101179749081315757156733 6412942405905493408933775)
              ·
                refine ⟨9619413608858240113400663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412942405905493408933775 9619413608858240113400663)
                ·
                  refine ⟨14429120413287360170100995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619413608858240113400663 14429120413287360170100995)
                  ·
                    refine ⟨21643680619931040255151493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14429120413287360170100995 21643680619931040255151493)
                    ·
                      refine ⟨4058190116237070047840905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21643680619931040255151493 4058190116237070047840905)
                      ·
                        rfl

theorem cell23_7903297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7903297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903297 prefixEnd_7903297 := by exact prefixLift 7903297
  have htrace : WordTrace (prefixWord ++ tailWord_7903297) baseStart_7903297 baseEnd_7903297 := by
    simpa [prefixWord, tailWord_7903297, baseEnd_7903297] using wordTrace_append hprefix tailTrace_7903297
  have hstable : (prefixWord ++ tailWord_7903297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903297).length < 2 ^ (prefixWord ++ tailWord_7903297).sum := by decide
  have hdescent : baseEnd_7903297 < baseStart_7903297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903340 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_7903340 : Nat := 118140960795 + 7903340 * 2 ^ 59
def prefixEnd_7903340 : Nat := 4983230072969 + 3 ^ 40 * 7903340 * 2
def baseEnd_7903340 : Nat := 4058212195905213379603207

theorem tailTrace_7903340 : CollatzResearch.WordTrace tailWord_7903340 prefixEnd_7903340 4058212195905213379603207 := by
  unfold tailWord_7903340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144129245593778218927697737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192172327458370958570263649 144129245593778218927697737)
  ·
    refine ⟨108096934195333664195773303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144129245593778218927697737 108096934195333664195773303)
    ·
      refine ⟨162145401293000496293659955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108096934195333664195773303 162145401293000496293659955)
      ·
        refine ⟨243218101939500744440489933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162145401293000496293659955 243218101939500744440489933)
        ·
          refine ⟨91206788227312779165183725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243218101939500744440489933 91206788227312779165183725)
          ·
            refine ⟨34202545585242292186943897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91206788227312779165183725 34202545585242292186943897)
            ·
              refine ⟨25651909188931719140207923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34202545585242292186943897 25651909188931719140207923)
              ·
                refine ⟨38477863783397578710311885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25651909188931719140207923 38477863783397578710311885)
                ·
                  refine ⟨14429198918774092016366957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38477863783397578710311885 14429198918774092016366957)
                  ·
                    refine ⟨5410949594540284506137609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14429198918774092016366957 5410949594540284506137609)
                    ·
                      refine ⟨4058212195905213379603207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410949594540284506137609 4058212195905213379603207)
                      ·
                        rfl

theorem cell23_7903340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_7903340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903340 prefixEnd_7903340 := by exact prefixLift 7903340
  have htrace : WordTrace (prefixWord ++ tailWord_7903340) baseStart_7903340 baseEnd_7903340 := by
    simpa [prefixWord, tailWord_7903340, baseEnd_7903340] using wordTrace_append hprefix tailTrace_7903340
  have hstable : (prefixWord ++ tailWord_7903340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903340).length < 2 ^ (prefixWord ++ tailWord_7903340).sum := by decide
  have hdescent : baseEnd_7903340 < baseStart_7903340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903357 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_7903357 : Nat := 118140960795 + 7903357 * 2 ^ 59
def prefixEnd_7903357 : Nat := 4983230072969 + 3 ^ 40 * 7903357 * 2
def baseEnd_7903357 : Nat := 4058220925076339813090629

theorem tailTrace_7903357 : CollatzResearch.WordTrace tailWord_7903357 prefixEnd_7903357 4058220925076339813090629 := by
  unfold tailWord_7903357
  simp only [CollatzResearch.WordTrace]
  refine ⟨288259111228494849758764325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192172740818996566505842883 288259111228494849758764325)
  ·
    refine ⟨54048583355342784329768311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288259111228494849758764325 54048583355342784329768311)
    ·
      refine ⟨81072875033014176494652467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048583355342784329768311 81072875033014176494652467)
      ·
        refine ⟨121609312549521264741978701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81072875033014176494652467 121609312549521264741978701)
        ·
          refine ⟨45603492206070474278242013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121609312549521264741978701 45603492206070474278242013)
          ·
            refine ⟨17101309577276427854340755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45603492206070474278242013 17101309577276427854340755)
            ·
              refine ⟨25651964365914641781511133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17101309577276427854340755 25651964365914641781511133)
              ·
                refine ⟨9619486637217990668066675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25651964365914641781511133 9619486637217990668066675)
                ·
                  refine ⟨14429229955826986002100013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619486637217990668066675 14429229955826986002100013)
                  ·
                    refine ⟨5410961233435119750787505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14429229955826986002100013 5410961233435119750787505)
                    ·
                      refine ⟨4058220925076339813090629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5410961233435119750787505 4058220925076339813090629)
                      ·
                        rfl

theorem cell23_7903357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_7903357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903357 prefixEnd_7903357 := by exact prefixLift 7903357
  have htrace : WordTrace (prefixWord ++ tailWord_7903357) baseStart_7903357 baseEnd_7903357 := by
    simpa [prefixWord, tailWord_7903357, baseEnd_7903357] using wordTrace_append hprefix tailTrace_7903357
  have hstable : (prefixWord ++ tailWord_7903357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903357).length < 2 ^ (prefixWord ++ tailWord_7903357).sum := by decide
  have hdescent : baseEnd_7903357 < baseStart_7903357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903393 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 7]
def baseStart_7903393 : Nat := 118140960795 + 7903393 * 2 ^ 59
def prefixEnd_7903393 : Nat := 4983230072969 + 3 ^ 40 * 7903393 * 2
def baseEnd_7903393 : Nat := 450915490042211296915607

theorem tailTrace_7903393 : CollatzResearch.WordTrace tailWord_7903393 prefixEnd_7903393 450915490042211296915607 := by
  unfold tailWord_7903393
  simp only [CollatzResearch.WordTrace]
  refine ⟨288260424256364427907074833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192173616170909618604716555 288260424256364427907074833)
  ·
    refine ⟨216195318192273320930306125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288260424256364427907074833 216195318192273320930306125)
    ·
      refine ⟨81073244322102495348864797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216195318192273320930306125 81073244322102495348864797)
      ·
        refine ⟨30402466620788435755824299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81073244322102495348864797 30402466620788435755824299)
        ·
          refine ⟨45603699931182653633736449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30402466620788435755824299 45603699931182653633736449)
          ·
            refine ⟨34202774948386990225302337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45603699931182653633736449 34202774948386990225302337)
            ·
              refine ⟨25652081211290242668976753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34202774948386990225302337 25652081211290242668976753)
              ·
                refine ⟨19239060908467682001732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25652081211290242668976753 19239060908467682001732565)
                ·
                  refine ⟨450915490042211296915607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19239060908467682001732565 450915490042211296915607)
                  ·
                    rfl

theorem cell23_7903393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_7903393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903393 prefixEnd_7903393 := by exact prefixLift 7903393
  have htrace : WordTrace (prefixWord ++ tailWord_7903393) baseStart_7903393 baseEnd_7903393 := by
    simpa [prefixWord, tailWord_7903393, baseEnd_7903393] using wordTrace_append hprefix tailTrace_7903393
  have hstable : (prefixWord ++ tailWord_7903393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903393).length < 2 ^ (prefixWord ++ tailWord_7903393).sum := by decide
  have hdescent : baseEnd_7903393 < baseStart_7903393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903460 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_7903460 : Nat := 118140960795 + 7903460 * 2 ^ 59
def prefixEnd_7903460 : Nat := 4983230072969 + 3 ^ 40 * 7903460 * 2
def baseEnd_7903460 : Nat := 4058273813583752910102655

theorem tailTrace_7903460 : CollatzResearch.WordTrace tailWord_7903460 prefixEnd_7903460 4058273813583752910102655 := by
  unfold tailWord_7903460
  simp only [CollatzResearch.WordTrace]
  refine ⟨144131433973560849174881917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192175245298081132233175889 144131433973560849174881917)
  ·
    refine ⟨54049287740085318440580719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144131433973560849174881917 54049287740085318440580719)
    ·
      refine ⟨81073931610127977660871079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54049287740085318440580719 81073931610127977660871079)
      ·
        refine ⟨121610897415191966491306619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81073931610127977660871079 121610897415191966491306619)
        ·
          refine ⟨182416346122787949736959929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121610897415191966491306619 182416346122787949736959929)
          ·
            refine ⟨136812259592090962302719947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182416346122787949736959929 136812259592090962302719947)
            ·
              refine ⟨205218389388136443454079921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136812259592090962302719947 205218389388136443454079921)
              ·
                refine ⟨153913792041102332590559941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205218389388136443454079921 153913792041102332590559941)
                ·
                  refine ⟨28858836007706687360729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153913792041102332590559941 28858836007706687360729989)
                  ·
                    refine ⟨5411031751445003880136873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28858836007706687360729989 5411031751445003880136873)
                    ·
                      refine ⟨4058273813583752910102655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411031751445003880136873 4058273813583752910102655)
                      ·
                        rfl

theorem cell23_7903460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_7903460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903460 prefixEnd_7903460 := by exact prefixLift 7903460
  have htrace : WordTrace (prefixWord ++ tailWord_7903460) baseStart_7903460 baseEnd_7903460 := by
    simpa [prefixWord, tailWord_7903460, baseEnd_7903460] using wordTrace_append hprefix tailTrace_7903460
  have hstable : (prefixWord ++ tailWord_7903460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903460).length < 2 ^ (prefixWord ++ tailWord_7903460).sum := by decide
  have hdescent : baseEnd_7903460 < baseStart_7903460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903487 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 1, 4]
def baseStart_7903487 : Nat := 118140960795 + 7903487 * 2 ^ 59
def prefixEnd_7903487 : Nat := 4983230072969 + 3 ^ 40 * 7903487 * 2
def baseEnd_7903487 : Nat := 1352762559187141434821677

theorem tailTrace_7903487 : CollatzResearch.WordTrace tailWord_7903487 prefixEnd_7903487 1352762559187141434821677 := by
  unfold tailWord_7903487
  simp only [CollatzResearch.WordTrace]
  refine ⟨288263852718023881960996715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192175901812015921307331143 288263852718023881960996715)
  ·
    refine ⟨432395779077035822941495073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288263852718023881960996715 432395779077035822941495073)
    ·
      refine ⟨324296834307776867206121305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432395779077035822941495073 324296834307776867206121305)
      ·
        refine ⟨243222625730832650404590979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324296834307776867206121305 243222625730832650404590979)
        ·
          refine ⟨364833938596248975606886469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243222625730832650404590979 364833938596248975606886469)
          ·
            refine ⟨68406363486796682926291213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364833938596248975606886469 68406363486796682926291213)
            ·
              refine ⟨25652386307548756097359205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68406363486796682926291213 25652386307548756097359205)
              ·
                refine ⟨4809822432665391768254851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25652386307548756097359205 4809822432665391768254851)
                ·
                  refine ⟨7214733648998087652382277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809822432665391768254851 7214733648998087652382277)
                  ·
                    refine ⟨1352762559187141434821677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214733648998087652382277 1352762559187141434821677)
                    ·
                      rfl

theorem cell23_7903487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_7903487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903487 prefixEnd_7903487 := by exact prefixLift 7903487
  have htrace : WordTrace (prefixWord ++ tailWord_7903487) baseStart_7903487 baseEnd_7903487 := by
    simpa [prefixWord, tailWord_7903487, baseEnd_7903487] using wordTrace_append hprefix tailTrace_7903487
  have hstable : (prefixWord ++ tailWord_7903487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903487).length < 2 ^ (prefixWord ++ tailWord_7903487).sum := by decide
  have hdescent : baseEnd_7903487 < baseStart_7903487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903514 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_7903514 : Nat := 118140960795 + 7903514 * 2 ^ 59
def prefixEnd_7903514 : Nat := 4983230072969 + 3 ^ 40 * 7903514 * 2
def baseEnd_7903514 : Nat := 4058301541539095698827407

theorem tailTrace_7903514 : CollatzResearch.WordTrace tailWord_7903514 prefixEnd_7903514 4058301541539095698827407 := by
  unfold tailWord_7903514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72066209372231516393057399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192176558325950710381486397 72066209372231516393057399)
  ·
    refine ⟨108099314058347274589586099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72066209372231516393057399 108099314058347274589586099)
    ·
      refine ⟨162148971087520911884379149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108099314058347274589586099 162148971087520911884379149)
      ·
        refine ⟨60805864157820341956642181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162148971087520911884379149 60805864157820341956642181)
        ·
          refine ⟨11401099529591314116870409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60805864157820341956642181 11401099529591314116870409)
          ·
            refine ⟨8550824647193485587652807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401099529591314116870409 8550824647193485587652807)
            ·
              refine ⟨12826236970790228381479211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550824647193485587652807 12826236970790228381479211)
              ·
                refine ⟨19239355456185342572218817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826236970790228381479211 19239355456185342572218817)
                ·
                  refine ⟨14429516592139006929164113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19239355456185342572218817 14429516592139006929164113)
                  ·
                    refine ⟨10822137444104255196873085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14429516592139006929164113 10822137444104255196873085)
                    ·
                      refine ⟨4058301541539095698827407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822137444104255196873085 4058301541539095698827407)
                      ·
                        rfl

theorem cell23_7903514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_7903514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903514 prefixEnd_7903514 := by exact prefixLift 7903514
  have htrace : WordTrace (prefixWord ++ tailWord_7903514) baseStart_7903514 baseEnd_7903514 := by
    simpa [prefixWord, tailWord_7903514, baseEnd_7903514] using wordTrace_append hprefix tailTrace_7903514
  have hstable : (prefixWord ++ tailWord_7903514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903514).length < 2 ^ (prefixWord ++ tailWord_7903514).sum := by decide
  have hdescent : baseEnd_7903514 < baseStart_7903514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903543 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 3, 6]
def baseStart_7903543 : Nat := 118140960795 + 7903543 * 2 ^ 59
def prefixEnd_7903543 : Nat := 4983230072969 + 3 ^ 40 * 7903543 * 2
def baseEnd_7903543 : Nat := 1352772144159358695121591

theorem tailTrace_7903543 : CollatzResearch.WordTrace tailWord_7903543 prefixEnd_7903543 1352772144159358695121591 := by
  unfold tailWord_7903543
  simp only [CollatzResearch.WordTrace]
  refine ⟨288265895205821003525035283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192177263470547335683356855 288265895205821003525035283)
  ·
    refine ⟨432398842808731505287552925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288265895205821003525035283 432398842808731505287552925)
    ·
      refine ⟨162149566053274314482832347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432398842808731505287552925 162149566053274314482832347)
      ·
        refine ⟨243224349079911471724248521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162149566053274314482832347 243224349079911471724248521)
        ·
          refine ⟨182418261809933603793186391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243224349079911471724248521 182418261809933603793186391)
          ·
            refine ⟨273627392714900405689779587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182418261809933603793186391 273627392714900405689779587)
            ·
              refine ⟨410441089072350608534669381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273627392714900405689779587 410441089072350608534669381)
              ·
                refine ⟨76957704201065739100250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410441089072350608534669381 76957704201065739100250509)
                ·
                  refine ⟨28859139075399652162593941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76957704201065739100250509 28859139075399652162593941)
                  ·
                    refine ⟨1352772144159358695121591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28859139075399652162593941 1352772144159358695121591)
                    ·
                      rfl

theorem cell23_7903543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_7903543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903543 prefixEnd_7903543 := by exact prefixLift 7903543
  have htrace : WordTrace (prefixWord ++ tailWord_7903543) baseStart_7903543 baseEnd_7903543 := by
    simpa [prefixWord, tailWord_7903543, baseEnd_7903543] using wordTrace_append hprefix tailTrace_7903543
  have hstable : (prefixWord ++ tailWord_7903543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903543).length < 2 ^ (prefixWord ++ tailWord_7903543).sum := by decide
  have hdescent : baseEnd_7903543 < baseStart_7903543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903544 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_7903544 : Nat := 118140960795 + 7903544 * 2 ^ 59
def prefixEnd_7903544 : Nat := 4983230072969 + 3 ^ 40 * 7903544 * 2
def baseEnd_7903544 : Nat := 4058316945958730581452269

theorem tailTrace_7903544 : CollatzResearch.WordTrace tailWord_7903544 prefixEnd_7903544 4058316945958730581452269 := by
  unfold tailWord_7903544
  simp only [CollatzResearch.WordTrace]
  refine ⟨144132965839408690347910843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192177287785878253797214457 144132965839408690347910843)
  ·
    refine ⟨216199448759113035521866265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144132965839408690347910843 216199448759113035521866265)
    ·
      refine ⟨162149586569334776641399699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216199448759113035521866265 162149586569334776641399699)
      ·
        refine ⟨243224379854002164962099549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162149586569334776641399699 243224379854002164962099549)
        ·
          refine ⟨91209142445250811860787331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243224379854002164962099549 91209142445250811860787331)
          ·
            refine ⟨136813713667876217791180997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91209142445250811860787331 136813713667876217791180997)
            ·
              refine ⟨25652571312726790835846437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136813713667876217791180997 25652571312726790835846437)
              ·
                refine ⟨4809857121136273281721207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25652571312726790835846437 4809857121136273281721207)
                ·
                  refine ⟨7214785681704409922581811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809857121136273281721207 7214785681704409922581811)
                  ·
                    refine ⟨10822178522556614883872717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214785681704409922581811 10822178522556614883872717)
                    ·
                      refine ⟨4058316945958730581452269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822178522556614883872717 4058316945958730581452269)
                      ·
                        rfl

theorem cell23_7903544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_7903544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903544 prefixEnd_7903544 := by exact prefixLift 7903544
  have htrace : WordTrace (prefixWord ++ tailWord_7903544) baseStart_7903544 baseEnd_7903544 := by
    simpa [prefixWord, tailWord_7903544, baseEnd_7903544] using wordTrace_append hprefix tailTrace_7903544
  have hstable : (prefixWord ++ tailWord_7903544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903544).length < 2 ^ (prefixWord ++ tailWord_7903544).sum := by decide
  have hdescent : baseEnd_7903544 < baseStart_7903544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903560 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_7903560 : Nat := 118140960795 + 7903560 * 2 ^ 59
def prefixEnd_7903560 : Nat := 4983230072969 + 3 ^ 40 * 7903560 * 2
def baseEnd_7903560 : Nat := 1352775053883067506284065

theorem tailTrace_7903560 : CollatzResearch.WordTrace tailWord_7903560 prefixEnd_7903560 1352775053883067506284065 := by
  unfold tailWord_7903560
  simp only [CollatzResearch.WordTrace]
  refine ⟨144133257623379707714202067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192177676831172943618936089 144133257623379707714202067)
  ·
    refine ⟨216199886435069561571303101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144133257623379707714202067 216199886435069561571303101)
    ·
      refine ⟨81074957413151085589238663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216199886435069561571303101 81074957413151085589238663)
      ·
        refine ⟨121612436119726628383857995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81074957413151085589238663 121612436119726628383857995)
        ·
          refine ⟨182418654179589942575786993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121612436119726628383857995 182418654179589942575786993)
          ·
            refine ⟨136813990634692456931840245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182418654179589942575786993 136813990634692456931840245)
            ·
              refine ⟨12826311622002417837360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136813990634692456931840245 12826311622002417837360023)
              ·
                refine ⟨19239467433003626756040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826311622002417837360023 19239467433003626756040035)
                ·
                  refine ⟨28859201149505440134060053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19239467433003626756040035 28859201149505440134060053)
                  ·
                    refine ⟨1352775053883067506284065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28859201149505440134060053 1352775053883067506284065)
                    ·
                      rfl

theorem cell23_7903560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_7903560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903560 prefixEnd_7903560 := by exact prefixLift 7903560
  have htrace : WordTrace (prefixWord ++ tailWord_7903560) baseStart_7903560 baseEnd_7903560 := by
    simpa [prefixWord, tailWord_7903560, baseEnd_7903560] using wordTrace_append hprefix tailTrace_7903560
  have hstable : (prefixWord ++ tailWord_7903560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903560).length < 2 ^ (prefixWord ++ tailWord_7903560).sum := by decide
  have hdescent : baseEnd_7903560 < baseStart_7903560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903567 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 5, 2, 2]
def baseStart_7903567 : Nat := 118140960795 + 7903567 * 2 ^ 59
def prefixEnd_7903567 : Nat := 4983230072969 + 3 ^ 40 * 7903567 * 2
def baseEnd_7903567 : Nat := 4058328756013783991464663

theorem tailTrace_7903567 : CollatzResearch.WordTrace tailWord_7903567 prefixEnd_7903567 4058328756013783991464663 := by
  unfold tailWord_7903567
  simp only [CollatzResearch.WordTrace]
  refine ⟨288266770557734055623908955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192177847038489370415939303 288266770557734055623908955)
  ·
    refine ⟨432400155836601083435863433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288266770557734055623908955 432400155836601083435863433)
    ·
      refine ⟨324300116877450812576897575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432400155836601083435863433 324300116877450812576897575)
      ·
        refine ⟨486450175316176218865346363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324300116877450812576897575 486450175316176218865346363)
        ·
          refine ⟨729675262974264328298019545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486450175316176218865346363 729675262974264328298019545)
          ·
            refine ⟨547256447230698246223514659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729675262974264328298019545 547256447230698246223514659)
            ·
              refine ⟨820884670846047369335271989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547256447230698246223514659 820884670846047369335271989)
              ·
                refine ⟨76957937891816940875181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820884670846047369335271989 76957937891816940875181749)
                ·
                  refine ⟨7214806677357838207048289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76957937891816940875181749 7214806677357838207048289)
                  ·
                    refine ⟨5411105008018378655286217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214806677357838207048289 5411105008018378655286217)
                    ·
                      refine ⟨4058328756013783991464663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411105008018378655286217 4058328756013783991464663)
                      ·
                        rfl

theorem cell23_7903567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 2, 2].length) (baseStart_7903567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903567 prefixEnd_7903567 := by exact prefixLift 7903567
  have htrace : WordTrace (prefixWord ++ tailWord_7903567) baseStart_7903567 baseEnd_7903567 := by
    simpa [prefixWord, tailWord_7903567, baseEnd_7903567] using wordTrace_append hprefix tailTrace_7903567
  have hstable : (prefixWord ++ tailWord_7903567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903567).length < 2 ^ (prefixWord ++ tailWord_7903567).sum := by decide
  have hdescent : baseEnd_7903567 < baseStart_7903567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903587 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7903587 : Nat := 118140960795 + 7903587 * 2 ^ 59
def prefixEnd_7903587 : Nat := 4983230072969 + 3 ^ 40 * 7903587 * 2
def baseEnd_7903587 : Nat := 4058339025626873913214571

theorem tailTrace_7903587 : CollatzResearch.WordTrace tailWord_7903587 prefixEnd_7903587 4058339025626873913214571 := by
  unfold tailWord_7903587
  simp only [CollatzResearch.WordTrace]
  refine ⟨288267500017661599039637015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192178333345107732693091343 288267500017661599039637015)
  ·
    refine ⟨432401250026492398559455523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288267500017661599039637015 432401250026492398559455523)
    ·
      refine ⟨648601875039738597839183285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432401250026492398559455523 648601875039738597839183285)
      ·
        refine ⟨60806425784975493547423433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 648601875039738597839183285 60806425784975493547423433)
        ·
          refine ⟨45604819338731620160567575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60806425784975493547423433 45604819338731620160567575)
          ·
            refine ⟨68407229008097430240851363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45604819338731620160567575 68407229008097430240851363)
            ·
              refine ⟨102610843512146145361277045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68407229008097430240851363 102610843512146145361277045)
              ·
                refine ⟨9619766579263701127619723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102610843512146145361277045 9619766579263701127619723)
                ·
                  refine ⟨14429649868895551691429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619766579263701127619723 14429649868895551691429585)
                  ·
                    refine ⟨10822237401671663768572189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14429649868895551691429585 10822237401671663768572189)
                    ·
                      refine ⟨4058339025626873913214571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822237401671663768572189 4058339025626873913214571)
                      ·
                        rfl

theorem cell23_7903587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7903587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903587 prefixEnd_7903587 := by exact prefixLift 7903587
  have htrace : WordTrace (prefixWord ++ tailWord_7903587) baseStart_7903587 baseEnd_7903587 := by
    simpa [prefixWord, tailWord_7903587, baseEnd_7903587] using wordTrace_append hprefix tailTrace_7903587
  have hstable : (prefixWord ++ tailWord_7903587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903587).length < 2 ^ (prefixWord ++ tailWord_7903587).sum := by decide
  have hdescent : baseEnd_7903587 < baseStart_7903587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903603 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 9]
def baseStart_7903603 : Nat := 118140960795 + 7903603 * 2 ^ 59
def prefixEnd_7903603 : Nat := 4983230072969 + 3 ^ 40 * 7903603 * 2
def baseEnd_7903603 : Nat := 1352782413772448616871499

theorem tailTrace_7903603 : CollatzResearch.WordTrace tailWord_7903603 prefixEnd_7903603 1352782413772448616871499 := by
  unfold tailWord_7903603
  simp only [CollatzResearch.WordTrace]
  refine ⟨288268083585603633772219463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192178722390402422514812975 288268083585603633772219463)
  ·
    refine ⟨432402125378405450658329195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288268083585603633772219463 432402125378405450658329195)
    ·
      refine ⟨648603188067608175987493793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432402125378405450658329195 648603188067608175987493793)
      ·
        refine ⟨486452391050706131990620345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648603188067608175987493793 486452391050706131990620345)
        ·
          refine ⟨364839293288029598992965259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486452391050706131990620345 364839293288029598992965259)
          ·
            refine ⟨547258939932044398489447889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364839293288029598992965259 547258939932044398489447889)
            ·
              refine ⟨410444204949033298867085917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547258939932044398489447889 410444204949033298867085917)
              ·
                refine ⟨153916576855887487075157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410444204949033298867085917 153916576855887487075157219)
                ·
                  refine ⟨230874865283831230612735829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153916576855887487075157219 230874865283831230612735829)
                  ·
                    refine ⟨1352782413772448616871499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 230874865283831230612735829 1352782413772448616871499)
                    ·
                      rfl

theorem cell23_7903603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_7903603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903603 prefixEnd_7903603 := by exact prefixLift 7903603
  have htrace : WordTrace (prefixWord ++ tailWord_7903603) baseStart_7903603 baseEnd_7903603 := by
    simpa [prefixWord, tailWord_7903603, baseEnd_7903603] using wordTrace_append hprefix tailTrace_7903603
  have hstable : (prefixWord ++ tailWord_7903603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903603).length < 2 ^ (prefixWord ++ tailWord_7903603).sum := by decide
  have hdescent : baseEnd_7903603 < baseStart_7903603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903618 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7903618 : Nat := 118140960795 + 7903618 * 2 ^ 59
def prefixEnd_7903618 : Nat := 4983230072969 + 3 ^ 40 * 7903618 * 2
def baseEnd_7903618 : Nat := 4058354943527163291926929

theorem tailTrace_7903618 : CollatzResearch.WordTrace tailWord_7903618 prefixEnd_7903618 4058354943527163291926929 := by
  unfold tailWord_7903618
  simp only [CollatzResearch.WordTrace]
  refine ⟨72067157670137322833503877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192179087120366194222677005 72067157670137322833503877)
  ·
    refine ⟨13512592063150748031281977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72067157670137322833503877 13512592063150748031281977)
    ·
      refine ⟨10134444047363061023461483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13512592063150748031281977 10134444047363061023461483)
      ·
        refine ⟨15201666071044591535192225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134444047363061023461483 15201666071044591535192225)
        ·
          refine ⟨11401249553283443651394169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201666071044591535192225 11401249553283443651394169)
          ·
            refine ⟨8550937164962582738545627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401249553283443651394169 8550937164962582738545627)
            ·
              refine ⟨12826405747443874107818441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550937164962582738545627 12826405747443874107818441)
              ·
                refine ⟨9619804310582905580863831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12826405747443874107818441 9619804310582905580863831)
                ·
                  refine ⟨14429706465874358371295747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619804310582905580863831 14429706465874358371295747)
                  ·
                    refine ⟨21644559698811537556943621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14429706465874358371295747 21644559698811537556943621)
                    ·
                      refine ⟨4058354943527163291926929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21644559698811537556943621 4058354943527163291926929)
                      ·
                        rfl

theorem cell23_7903618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7903618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903618 prefixEnd_7903618 := by exact prefixLift 7903618
  have htrace : WordTrace (prefixWord ++ tailWord_7903618) baseStart_7903618 baseEnd_7903618 := by
    simpa [prefixWord, tailWord_7903618, baseEnd_7903618] using wordTrace_append hprefix tailTrace_7903618
  have hstable : (prefixWord ++ tailWord_7903618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903618).length < 2 ^ (prefixWord ++ tailWord_7903618).sum := by decide
  have hdescent : baseEnd_7903618 < baseStart_7903618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903658 : List Nat := [3, 1, 6, 1, 2, 1, 1, 8]
def baseStart_7903658 : Nat := 118140960795 + 7903658 * 2 ^ 59
def prefixEnd_7903658 : Nat := 4983230072969 + 3 ^ 40 * 7903658 * 2
def baseEnd_7903658 : Nat := 150310203064938634645435

theorem tailTrace_7903658 : CollatzResearch.WordTrace tailWord_7903658 prefixEnd_7903658 150310203064938634645435 := by
  unfold tailWord_7903658
  simp only [CollatzResearch.WordTrace]
  refine ⟨72067522400101094541367907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192180059733602918776981085 72067522400101094541367907)
  ·
    refine ⟨108101283600151641812051861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72067522400101094541367907 108101283600151641812051861)
    ·
      refine ⟨5067247668757108209939931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108101283600151641812051861 5067247668757108209939931)
      ·
        refine ⟨7600871503135662314909897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067247668757108209939931 7600871503135662314909897)
        ·
          refine ⟨5700653627351746736182423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600871503135662314909897 5700653627351746736182423)
          ·
            refine ⟨8550980441027620104273635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700653627351746736182423 8550980441027620104273635)
            ·
              refine ⟨12826470661541430156410453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550980441027620104273635 12826470661541430156410453)
              ·
                refine ⟨150310203064938634645435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12826470661541430156410453 150310203064938634645435)
                ·
                  rfl

theorem cell23_7903658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_7903658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903658 prefixEnd_7903658 := by exact prefixLift 7903658
  have htrace : WordTrace (prefixWord ++ tailWord_7903658) baseStart_7903658 baseEnd_7903658 := by
    simpa [prefixWord, tailWord_7903658, baseEnd_7903658] using wordTrace_append hprefix tailTrace_7903658
  have hstable : (prefixWord ++ tailWord_7903658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903658).length < 2 ^ (prefixWord ++ tailWord_7903658).sum := by decide
  have hdescent : baseEnd_7903658 < baseStart_7903658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903668 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7903668 : Nat := 118140960795 + 7903668 * 2 ^ 59
def prefixEnd_7903668 : Nat := 4983230072969 + 3 ^ 40 * 7903668 * 2
def baseEnd_7903668 : Nat := 4058380617559888096301699

theorem tailTrace_7903668 : CollatzResearch.WordTrace tailWord_7903668 prefixEnd_7903668 4058380617559888096301699 := by
  unfold tailWord_7903668
  simp only [CollatzResearch.WordTrace]
  refine ⟨144135227165184074936667829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192180302886912099915557105 144135227165184074936667829)
  ·
    refine ⟨13512677546736007025312609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144135227165184074936667829 13512677546736007025312609)
    ·
      refine ⟨10134508160052005268984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13512677546736007025312609 10134508160052005268984457)
      ·
        refine ⟨7600881120039003951738343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134508160052005268984457 7600881120039003951738343)
        ·
          refine ⟨11401321680058505927607515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600881120039003951738343 11401321680058505927607515)
          ·
            refine ⟨17101982520087758891411273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401321680058505927607515 17101982520087758891411273)
            ·
              refine ⟨12826486890065819168558455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17101982520087758891411273 12826486890065819168558455)
              ·
                refine ⟨19239730335098728752837683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826486890065819168558455 19239730335098728752837683)
                ·
                  refine ⟨28859595502648093129256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19239730335098728752837683 28859595502648093129256525)
                  ·
                    refine ⟨10822348313493034923471197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28859595502648093129256525 10822348313493034923471197)
                    ·
                      refine ⟨4058380617559888096301699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822348313493034923471197 4058380617559888096301699)
                      ·
                        rfl

theorem cell23_7903668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7903668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903668 prefixEnd_7903668 := by exact prefixLift 7903668
  have htrace : WordTrace (prefixWord ++ tailWord_7903668) baseStart_7903668 baseEnd_7903668 := by
    simpa [prefixWord, tailWord_7903668, baseEnd_7903668] using wordTrace_append hprefix tailTrace_7903668
  have hstable : (prefixWord ++ tailWord_7903668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903668).length < 2 ^ (prefixWord ++ tailWord_7903668).sum := by decide
  have hdescent : baseEnd_7903668 < baseStart_7903668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903725 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7903725 : Nat := 118140960795 + 7903725 * 2 ^ 59
def prefixEnd_7903725 : Nat := 4983230072969 + 3 ^ 40 * 7903725 * 2
def baseEnd_7903725 : Nat := 4058409885957194373288937

theorem tailTrace_7903725 : CollatzResearch.WordTrace tailWord_7903725 prefixEnd_7903725 4058409885957194373288937 := by
  unfold tailWord_7903725
  simp only [CollatzResearch.WordTrace]
  refine ⟨288272533291161648608160629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192181688860774432405440419 288272533291161648608160629)
  ·
    refine ⟨27025549996046404557015059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288272533291161648608160629 27025549996046404557015059)
    ·
      refine ⟨40538324994069606835522589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27025549996046404557015059 40538324994069606835522589)
      ·
        refine ⟨15201871872776102563320971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40538324994069606835522589 15201871872776102563320971)
        ·
          refine ⟨22802807809164153844981457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201871872776102563320971 22802807809164153844981457)
          ·
            refine ⟨17102105856873115383736093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22802807809164153844981457 17102105856873115383736093)
            ·
              refine ⟨6413289696327418268901035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17102105856873115383736093 6413289696327418268901035)
              ·
                refine ⟨9619934544491127403351553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413289696327418268901035 9619934544491127403351553)
                ·
                  refine ⟨7214950908368345552513665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619934544491127403351553 7214950908368345552513665)
                  ·
                    refine ⟨5411213181276259164385249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7214950908368345552513665 5411213181276259164385249)
                    ·
                      refine ⟨4058409885957194373288937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411213181276259164385249 4058409885957194373288937)
                      ·
                        rfl

theorem cell23_7903725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7903725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903725 prefixEnd_7903725 := by exact prefixLift 7903725
  have htrace : WordTrace (prefixWord ++ tailWord_7903725) baseStart_7903725 baseEnd_7903725 := by
    simpa [prefixWord, tailWord_7903725, baseEnd_7903725] using wordTrace_append hprefix tailTrace_7903725
  have hstable : (prefixWord ++ tailWord_7903725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903725).length < 2 ^ (prefixWord ++ tailWord_7903725).sum := by decide
  have hdescent : baseEnd_7903725 < baseStart_7903725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903740 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_7903740 : Nat := 118140960795 + 7903740 * 2 ^ 59
def prefixEnd_7903740 : Nat := 4983230072969 + 3 ^ 40 * 7903740 * 2
def baseEnd_7903740 : Nat := 1352805862722337271533789

theorem tailTrace_7903740 : CollatzResearch.WordTrace tailWord_7903740 prefixEnd_7903740 1352805862722337271533789 := by
  unfold tailWord_7903740
  simp only [CollatzResearch.WordTrace]
  refine ⟨144136540193053653084978337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192182053590738204113304449 144136540193053653084978337)
  ·
    refine ⟨108102405144790239813733753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144136540193053653084978337 108102405144790239813733753)
    ·
      refine ⟨81076803858592679860300315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108102405144790239813733753 81076803858592679860300315)
      ·
        refine ⟨121615205787889019790450473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81076803858592679860300315 121615205787889019790450473)
        ·
          refine ⟨91211404340916764842837855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121615205787889019790450473 91211404340916764842837855)
          ·
            refine ⟨136817106511375147264256783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91211404340916764842837855 136817106511375147264256783)
            ·
              refine ⟨205225659767062720896385175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136817106511375147264256783 205225659767062720896385175)
              ·
                refine ⟨307838489650594081344577763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205225659767062720896385175 307838489650594081344577763)
                ·
                  refine ⟨461757734475891122016866645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307838489650594081344577763 461757734475891122016866645)
                  ·
                    refine ⟨1352805862722337271533789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 461757734475891122016866645 1352805862722337271533789)
                    ·
                      rfl

theorem cell23_7903740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_7903740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903740 prefixEnd_7903740 := by exact prefixLift 7903740
  have htrace : WordTrace (prefixWord ++ tailWord_7903740) baseStart_7903740 baseEnd_7903740 := by
    simpa [prefixWord, tailWord_7903740, baseEnd_7903740] using wordTrace_append hprefix tailTrace_7903740
  have hstable : (prefixWord ++ tailWord_7903740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903740).length < 2 ^ (prefixWord ++ tailWord_7903740).sum := by decide
  have hdescent : baseEnd_7903740 < baseStart_7903740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903747 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4]
def baseStart_7903747 : Nat := 118140960795 + 7903747 * 2 ^ 59
def prefixEnd_7903747 : Nat := 4983230072969 + 3 ^ 40 * 7903747 * 2
def baseEnd_7903747 : Nat := 4058421182531593287213835

theorem tailTrace_7903747 : CollatzResearch.WordTrace tailWord_7903747 prefixEnd_7903747 4058421182531593287213835 := by
  unfold tailWord_7903747
  simp only [CollatzResearch.WordTrace]
  refine ⟨288273335697081946365461495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192182223798054630910307663 288273335697081946365461495)
  ·
    refine ⟨432410003545622919548192243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288273335697081946365461495 432410003545622919548192243)
    ·
      refine ⟨648615005318434379322288365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432410003545622919548192243 648615005318434379322288365)
      ·
        refine ⟨243230626994412892245858137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648615005318434379322288365 243230626994412892245858137)
        ·
          refine ⟨182422970245809669184393603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243230626994412892245858137 182422970245809669184393603)
          ·
            refine ⟨273634455368714503776590405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182422970245809669184393603 273634455368714503776590405)
            ·
              refine ⟨51306460381633969458110701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273634455368714503776590405 51306460381633969458110701)
              ·
                refine ⟨19239922643112738546791513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51306460381633969458110701 19239922643112738546791513)
                ·
                  refine ⟨14429941982334553910093635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19239922643112738546791513 14429941982334553910093635)
                  ·
                    refine ⟨21644912973501830865140453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14429941982334553910093635 21644912973501830865140453)
                    ·
                      refine ⟨4058421182531593287213835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21644912973501830865140453 4058421182531593287213835)
                      ·
                        rfl

theorem cell23_7903747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_7903747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903747 prefixEnd_7903747 := by exact prefixLift 7903747
  have htrace : WordTrace (prefixWord ++ tailWord_7903747) baseStart_7903747 baseEnd_7903747 := by
    simpa [prefixWord, tailWord_7903747, baseEnd_7903747] using wordTrace_append hprefix tailTrace_7903747
  have hstable : (prefixWord ++ tailWord_7903747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903747).length < 2 ^ (prefixWord ++ tailWord_7903747).sum := by decide
  have hdescent : baseEnd_7903747 < baseStart_7903747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903760 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_7903760 : Nat := 118140960795 + 7903760 * 2 ^ 59
def prefixEnd_7903760 : Nat := 4983230072969 + 3 ^ 40 * 7903760 * 2
def baseEnd_7903760 : Nat := 4058427857780101736351275

theorem tailTrace_7903760 : CollatzResearch.WordTrace tailWord_7903760 prefixEnd_7903760 4058427857780101736351275 := by
  unfold tailWord_7903760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144136904923017424792842367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192182539897356566390456489 144136904923017424792842367)
  ·
    refine ⟨216205357384526137189263551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144136904923017424792842367 216205357384526137189263551)
    ·
      refine ⟨324308036076789205783895327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216205357384526137189263551 324308036076789205783895327)
      ·
        refine ⟨486462054115183808675842991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324308036076789205783895327 486462054115183808675842991)
        ·
          refine ⟨729693081172775713013764487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486462054115183808675842991 729693081172775713013764487)
          ·
            refine ⟨1094539621759163569520646731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729693081172775713013764487 1094539621759163569520646731)
            ·
              refine ⟨1641809432638745354280970097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094539621759163569520646731 1641809432638745354280970097)
              ·
                refine ⟨1231357074479059015710727573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641809432638745354280970097 1231357074479059015710727573)
                ·
                  refine ⟨57719862866205891361440355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1231357074479059015710727573 57719862866205891361440355)
                  ·
                    refine ⟨86579794299308837042160533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57719862866205891361440355 86579794299308837042160533)
                    ·
                      refine ⟨4058427857780101736351275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86579794299308837042160533 4058427857780101736351275)
                      ·
                        rfl

theorem cell23_7903760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_7903760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903760 prefixEnd_7903760 := by exact prefixLift 7903760
  have htrace : WordTrace (prefixWord ++ tailWord_7903760) baseStart_7903760 baseEnd_7903760 := by
    simpa [prefixWord, tailWord_7903760, baseEnd_7903760] using wordTrace_append hprefix tailTrace_7903760
  have hstable : (prefixWord ++ tailWord_7903760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903760).length < 2 ^ (prefixWord ++ tailWord_7903760).sum := by decide
  have hdescent : baseEnd_7903760 < baseStart_7903760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903821 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 6]
def baseStart_7903821 : Nat := 118140960795 + 7903821 * 2 ^ 59
def prefixEnd_7903821 : Nat := 4983230072969 + 3 ^ 40 * 7903821 * 2
def baseEnd_7903821 : Nat := 450939908900002888632055

theorem tailTrace_7903821 : CollatzResearch.WordTrace tailWord_7903821 prefixEnd_7903821 450939908900002888632055 := by
  unfold tailWord_7903821
  simp only [CollatzResearch.WordTrace]
  refine ⟨288276034698813857003655317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192184023132542571335770211 288276034698813857003655317)
  ·
    refine ⟨13512939126506899547046343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288276034698813857003655317 13512939126506899547046343)
    ·
      refine ⟨20269408689760349320569515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512939126506899547046343 20269408689760349320569515)
      ·
        refine ⟨30404113034640523980854273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269408689760349320569515 30404113034640523980854273)
        ·
          refine ⟨22803084775980392985640705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30404113034640523980854273 22803084775980392985640705)
          ·
            refine ⟨17102313581985294739230529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22803084775980392985640705 17102313581985294739230529)
            ·
              refine ⟨12826735186488971054422897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17102313581985294739230529 12826735186488971054422897)
              ·
                refine ⟨9620051389866728290817173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12826735186488971054422897 9620051389866728290817173)
                ·
                  refine ⟨450939908900002888632055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9620051389866728290817173 450939908900002888632055)
                  ·
                    rfl

theorem cell23_7903821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_7903821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903821 prefixEnd_7903821 := by exact prefixLift 7903821
  have htrace : WordTrace (prefixWord ++ tailWord_7903821) baseStart_7903821 baseEnd_7903821 := by
    simpa [prefixWord, tailWord_7903821, baseEnd_7903821] using wordTrace_append hprefix tailTrace_7903821
  have hstable : (prefixWord ++ tailWord_7903821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903821).length < 2 ^ (prefixWord ++ tailWord_7903821).sum := by decide
  have hdescent : baseEnd_7903821 < baseStart_7903821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2]
def baseStart_7903824 : Nat := 118140960795 + 7903824 * 2 ^ 59
def prefixEnd_7903824 : Nat := 4983230072969 + 3 ^ 40 * 7903824 * 2
def baseEnd_7903824 : Nat := 4058460720541989485950981

theorem tailTrace_7903824 : CollatzResearch.WordTrace tailWord_7903824 prefixEnd_7903824 4058460720541989485950981 := by
  unfold tailWord_7903824
  simp only [CollatzResearch.WordTrace]
  refine ⟨144138072058901494258007263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192184096078535325677343017 144138072058901494258007263)
  ·
    refine ⟨216207108088352241387010895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144138072058901494258007263 216207108088352241387010895)
    ·
      refine ⟨324310662132528362080516343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216207108088352241387010895 324310662132528362080516343)
      ·
        refine ⟨486465993198792543120774515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324310662132528362080516343 486465993198792543120774515)
        ·
          refine ⟨729698989798188814681161773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486465993198792543120774515 729698989798188814681161773)
          ·
            refine ⟨273637121174320805505435665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 729698989798188814681161773 273637121174320805505435665)
            ·
              refine ⟨205227840880740604129076749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273637121174320805505435665 205227840880740604129076749)
              ·
                refine ⟨76960440330277726548403781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205227840880740604129076749 76960440330277726548403781)
                ·
                  refine ⟨14430082561927073727825709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76960440330277726548403781 14430082561927073727825709)
                  ·
                    refine ⟨5411280960722652647934641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14430082561927073727825709 5411280960722652647934641)
                    ·
                      refine ⟨4058460720541989485950981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411280960722652647934641 4058460720541989485950981)
                      ·
                        rfl

theorem cell23_7903824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 3, 2].length) (baseStart_7903824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903824 prefixEnd_7903824 := by exact prefixLift 7903824
  have htrace : WordTrace (prefixWord ++ tailWord_7903824) baseStart_7903824 baseEnd_7903824 := by
    simpa [prefixWord, tailWord_7903824, baseEnd_7903824] using wordTrace_append hprefix tailTrace_7903824
  have hstable : (prefixWord ++ tailWord_7903824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903824).length < 2 ^ (prefixWord ++ tailWord_7903824).sum := by decide
  have hdescent : baseEnd_7903824 < baseStart_7903824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903848 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7903848 : Nat := 118140960795 + 7903848 * 2 ^ 59
def prefixEnd_7903848 : Nat := 4983230072969 + 3 ^ 40 * 7903848 * 2
def baseEnd_7903848 : Nat := 4058473044077697392050871

theorem tailTrace_7903848 : CollatzResearch.WordTrace tailWord_7903848 prefixEnd_7903848 4058473044077697392050871 := by
  unfold tailWord_7903848
  simp only [CollatzResearch.WordTrace]
  refine ⟨144138509734858020307444099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192184679646477360409925465 144138509734858020307444099)
  ·
    refine ⟨216207764602287030461166149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144138509734858020307444099 216207764602287030461166149)
    ·
      refine ⟨40538955862928818211468653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216207764602287030461166149 40538955862928818211468653)
      ·
        refine ⟨15202108448598306829300745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40538955862928818211468653 15202108448598306829300745)
        ·
          refine ⟨11401581336448730121975559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15202108448598306829300745 11401581336448730121975559)
          ·
            refine ⟨17102372004673095182963339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401581336448730121975559 17102372004673095182963339)
            ·
              refine ⟨25653558007009642774445009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17102372004673095182963339 25653558007009642774445009)
              ·
                refine ⟨19240168505257232080833757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25653558007009642774445009 19240168505257232080833757)
                ·
                  refine ⟨7215063189471462030312659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19240168505257232080833757 7215063189471462030312659)
                  ·
                    refine ⟨10822594784207193045468989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215063189471462030312659 10822594784207193045468989)
                    ·
                      refine ⟨4058473044077697392050871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822594784207193045468989 4058473044077697392050871)
                      ·
                        rfl

theorem cell23_7903848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7903848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903848 prefixEnd_7903848 := by exact prefixLift 7903848
  have htrace : WordTrace (prefixWord ++ tailWord_7903848) baseStart_7903848 baseEnd_7903848 := by
    simpa [prefixWord, tailWord_7903848, baseEnd_7903848] using wordTrace_append hprefix tailTrace_7903848
  have hstable : (prefixWord ++ tailWord_7903848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903848).length < 2 ^ (prefixWord ++ tailWord_7903848).sum := by decide
  have hdescent : baseEnd_7903848 < baseStart_7903848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903867 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_7903867 : Nat := 118140960795 + 7903867 * 2 ^ 59
def prefixEnd_7903867 : Nat := 4983230072969 + 3 ^ 40 * 7903867 * 2
def baseEnd_7903867 : Nat := 4058482800210132817713283

theorem tailTrace_7903867 : CollatzResearch.WordTrace tailWord_7903867 prefixEnd_7903867 4058482800210132817713283 := by
  unfold tailWord_7903867
  simp only [CollatzResearch.WordTrace]
  refine ⟨288277712456647206859829855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192185141637764804573219903 288277712456647206859829855)
  ·
    refine ⟨432416568684970810289744783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288277712456647206859829855 432416568684970810289744783)
    ·
      refine ⟨648624853027456215434617175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432416568684970810289744783 648624853027456215434617175)
      ·
        refine ⟨972937279541184323151925763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648624853027456215434617175 972937279541184323151925763)
        ·
          refine ⟨1459405919311776484727888645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972937279541184323151925763 1459405919311776484727888645)
          ·
            refine ⟨273638609870958090886479121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1459405919311776484727888645 273638609870958090886479121)
            ·
              refine ⟨205228957403218568164859341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273638609870958090886479121 205228957403218568164859341)
              ·
                refine ⟨76960859026206963061822253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205228957403218568164859341 76960859026206963061822253)
                ·
                  refine ⟨28860322134827611148183345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76960859026206963061822253 28860322134827611148183345)
                  ·
                    refine ⟨21645241601120708361137509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28860322134827611148183345 21645241601120708361137509)
                    ·
                      refine ⟨4058482800210132817713283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21645241601120708361137509 4058482800210132817713283)
                      ·
                        rfl

theorem cell23_7903867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_7903867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903867 prefixEnd_7903867 := by exact prefixLift 7903867
  have htrace : WordTrace (prefixWord ++ tailWord_7903867) baseStart_7903867 baseEnd_7903867 := by
    simpa [prefixWord, tailWord_7903867, baseEnd_7903867] using wordTrace_append hprefix tailTrace_7903867
  have hstable : (prefixWord ++ tailWord_7903867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903867).length < 2 ^ (prefixWord ++ tailWord_7903867).sum := by decide
  have hdescent : baseEnd_7903867 < baseStart_7903867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903877 : List Nat := [1, 3, 1, 1, 4, 3, 10]
def baseStart_7903877 : Nat := 118140960795 + 7903877 * 2 ^ 59
def prefixEnd_7903877 : Nat := 4983230072969 + 3 ^ 40 * 7903877 * 2
def baseEnd_7903877 : Nat := 50104789321193552822077

theorem tailTrace_7903877 : CollatzResearch.WordTrace tailWord_7903877 prefixEnd_7903877 50104789321193552822077 := by
  unfold tailWord_7903877
  simp only [CollatzResearch.WordTrace]
  refine ⟨288278077186610978567693885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192185384791073985711795923 288278077186610978567693885)
  ·
    refine ⟨108104278944979116962885207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288278077186610978567693885 108104278944979116962885207)
    ·
      refine ⟨162156418417468675444327811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108104278944979116962885207 162156418417468675444327811)
      ·
        refine ⟨243234627626203013166491717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162156418417468675444327811 243234627626203013166491717)
        ·
          refine ⟨45606492679913064968717197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243234627626203013166491717 45606492679913064968717197)
          ·
            refine ⟨17102434754967399363268949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45606492679913064968717197 17102434754967399363268949)
            ·
              refine ⟨50104789321193552822077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17102434754967399363268949 50104789321193552822077)
              ·
                rfl

theorem cell23_7903877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 10].length) (baseStart_7903877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903877 prefixEnd_7903877 := by exact prefixLift 7903877
  have htrace : WordTrace (prefixWord ++ tailWord_7903877) baseStart_7903877 baseEnd_7903877 := by
    simpa [prefixWord, tailWord_7903877, baseEnd_7903877] using wordTrace_append hprefix tailTrace_7903877
  have hstable : (prefixWord ++ tailWord_7903877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903877).length < 2 ^ (prefixWord ++ tailWord_7903877).sum := by decide
  have hdescent : baseEnd_7903877 < baseStart_7903877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903898 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_7903898 : Nat := 118140960795 + 7903898 * 2 ^ 59
def prefixEnd_7903898 : Nat := 4983230072969 + 3 ^ 40 * 7903898 * 2
def baseEnd_7903898 : Nat := 1352832906036807398808547

theorem tailTrace_7903898 : CollatzResearch.WordTrace tailWord_7903898 prefixEnd_7903898 1352832906036807398808547 := by
  unfold tailWord_7903898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72069710779883724788552087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192185895413023266102805565 72069710779883724788552087)
  ·
    refine ⟨108104566169825587182828131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72069710779883724788552087 108104566169825587182828131)
    ·
      refine ⟨162156849254738380774242197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108104566169825587182828131 162156849254738380774242197)
      ·
        refine ⟨7601102308815861598792603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162156849254738380774242197 7601102308815861598792603)
        ·
          refine ⟨11401653463223792398188905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601102308815861598792603 11401653463223792398188905)
          ·
            refine ⟨8551240097417844298641679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401653463223792398188905 8551240097417844298641679)
            ·
              refine ⟨12826860146126766447962519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551240097417844298641679 12826860146126766447962519)
              ·
                refine ⟨19240290219190149671943779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826860146126766447962519 19240290219190149671943779)
                ·
                  refine ⟨28860435328785224507915669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19240290219190149671943779 28860435328785224507915669)
                  ·
                    refine ⟨1352832906036807398808547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28860435328785224507915669 1352832906036807398808547)
                    ·
                      rfl

theorem cell23_7903898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_7903898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903898 prefixEnd_7903898 := by exact prefixLift 7903898
  have htrace : WordTrace (prefixWord ++ tailWord_7903898) baseStart_7903898 baseEnd_7903898 := by
    simpa [prefixWord, tailWord_7903898, baseEnd_7903898] using wordTrace_append hprefix tailTrace_7903898
  have hstable : (prefixWord ++ tailWord_7903898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903898).length < 2 ^ (prefixWord ++ tailWord_7903898).sum := by decide
  have hdescent : baseEnd_7903898 < baseStart_7903898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903911 : List Nat := [1, 1, 6, 3, 1, 1, 1, 9]
def baseStart_7903911 : Nat := 118140960795 + 7903911 * 2 ^ 59
def prefixEnd_7903911 : Nat := 4983230072969 + 3 ^ 40 * 7903911 * 2
def baseEnd_7903911 : Nat := 150315014568849283169003

theorem tailTrace_7903911 : CollatzResearch.WordTrace tailWord_7903911 prefixEnd_7903911 150315014568849283169003 := by
  unfold tailWord_7903911
  simp only [CollatzResearch.WordTrace]
  refine ⟨288279317268487802374431587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192186211512325201582954391 288279317268487802374431587)
  ·
    refine ⟨432418975902731703561647381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288279317268487802374431587 432418975902731703561647381)
    ·
      refine ⟨20269639495440548604452221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432418975902731703561647381 20269639495440548604452221)
      ·
        refine ⟨7601114810790205726669583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20269639495440548604452221 7601114810790205726669583)
        ·
          refine ⟨11401672216185308590004375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601114810790205726669583 11401672216185308590004375)
          ·
            refine ⟨17102508324277962885006563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401672216185308590004375 17102508324277962885006563)
            ·
              refine ⟨25653762486416944327509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17102508324277962885006563 25653762486416944327509845)
              ·
                refine ⟨150315014568849283169003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25653762486416944327509845 150315014568849283169003)
                ·
                  rfl

theorem cell23_7903911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 9].length) (baseStart_7903911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903911 prefixEnd_7903911 := by exact prefixLift 7903911
  have htrace : WordTrace (prefixWord ++ tailWord_7903911) baseStart_7903911 baseEnd_7903911 := by
    simpa [prefixWord, tailWord_7903911, baseEnd_7903911] using wordTrace_append hprefix tailTrace_7903911
  have hstable : (prefixWord ++ tailWord_7903911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903911).length < 2 ^ (prefixWord ++ tailWord_7903911).sum := by decide
  have hdescent : baseEnd_7903911 < baseStart_7903911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903934 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7903934 : Nat := 118140960795 + 7903934 * 2 ^ 59
def prefixEnd_7903934 : Nat := 4983230072969 + 3 ^ 40 * 7903934 * 2
def baseEnd_7903934 : Nat := 4058517203413984055575475

theorem tailTrace_7903934 : CollatzResearch.WordTrace tailWord_7903934 prefixEnd_7903934 4058517203413984055575475 := by
  unfold tailWord_7903934
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035019518425559662814857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192186770764936318201679237 36035019518425559662814857)
  ·
    refine ⟨27026264638819169747111143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36035019518425559662814857 27026264638819169747111143)
    ·
      refine ⟨40539396958228754620666715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27026264638819169747111143 40539396958228754620666715)
      ·
        refine ⟨60809095437343131931000073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40539396958228754620666715 60809095437343131931000073)
        ·
          refine ⟨45606821578007348948250055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60809095437343131931000073 45606821578007348948250055)
          ·
            refine ⟨68410232367011023422375083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45606821578007348948250055 68410232367011023422375083)
            ·
              refine ⟨102615348550516535133562625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68410232367011023422375083 102615348550516535133562625)
              ·
                refine ⟨76961511412887401350171969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102615348550516535133562625 76961511412887401350171969)
                ·
                  refine ⟨57721133559665551012628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76961511412887401350171969 57721133559665551012628977)
                  ·
                    refine ⟨43290850169749163259471733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57721133559665551012628977 43290850169749163259471733)
                    ·
                      refine ⟨4058517203413984055575475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43290850169749163259471733 4058517203413984055575475)
                      ·
                        rfl

theorem cell23_7903934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7903934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903934 prefixEnd_7903934 := by exact prefixLift 7903934
  have htrace : WordTrace (prefixWord ++ tailWord_7903934) baseStart_7903934 baseEnd_7903934 := by
    simpa [prefixWord, tailWord_7903934, baseEnd_7903934] using wordTrace_append hprefix tailTrace_7903934
  have hstable : (prefixWord ++ tailWord_7903934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903934).length < 2 ^ (prefixWord ++ tailWord_7903934).sum := by decide
  have hdescent : baseEnd_7903934 < baseStart_7903934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903949 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7903949 : Nat := 118140960795 + 7903949 * 2 ^ 59
def prefixEnd_7903949 : Nat := 4983230072969 + 3 ^ 40 * 7903949 * 2
def baseEnd_7903949 : Nat := 1352841635207933832295969

theorem tailTrace_7903949 : CollatzResearch.WordTrace tailWord_7903949 prefixEnd_7903949 1352841635207933832295969 := by
  unfold tailWord_7903949
  simp only [CollatzResearch.WordTrace]
  refine ⟨288280703242350134864314901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192187135494900089909543267 288280703242350134864314901)
  ·
    refine ⟨13513157964485162571764761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 288280703242350134864314901 13513157964485162571764761)
    ·
      refine ⟨10134868473363871928823571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13513157964485162571764761 10134868473363871928823571)
      ·
        refine ⟨15202302710045807893235357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134868473363871928823571 15202302710045807893235357)
        ·
          refine ⟨5700863516267177959963259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15202302710045807893235357 5700863516267177959963259)
          ·
            refine ⟨8551295274400766939944889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700863516267177959963259 8551295274400766939944889)
            ·
              refine ⟨6413471455800575204958667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8551295274400766939944889 6413471455800575204958667)
              ·
                refine ⟨9620207183700862807438001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413471455800575204958667 9620207183700862807438001)
                ·
                  refine ⟨7215155387775647105578501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9620207183700862807438001 7215155387775647105578501)
                  ·
                    refine ⟨1352841635207933832295969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215155387775647105578501 1352841635207933832295969)
                    ·
                      rfl

theorem cell23_7903949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7903949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903949 prefixEnd_7903949 := by exact prefixLift 7903949
  have htrace : WordTrace (prefixWord ++ tailWord_7903949) baseStart_7903949 baseEnd_7903949 := by
    simpa [prefixWord, tailWord_7903949, baseEnd_7903949] using wordTrace_append hprefix tailTrace_7903949
  have hstable : (prefixWord ++ tailWord_7903949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903949).length < 2 ^ (prefixWord ++ tailWord_7903949).sum := by decide
  have hdescent : baseEnd_7903949 < baseStart_7903949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903961 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 4, 2]
def baseStart_7903961 : Nat := 118140960795 + 7903961 * 2 ^ 59
def prefixEnd_7903961 : Nat := 4983230072969 + 3 ^ 40 * 7903961 * 2
def baseEnd_7903961 : Nat := 4058531067391655449937851

theorem tailTrace_7903961 : CollatzResearch.WordTrace tailWord_7903961 prefixEnd_7903961 4058531067391655449937851 := by
  unfold tailWord_7903961
  simp only [CollatzResearch.WordTrace]
  refine ⟨288281140918306660913751737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192187427278871107275834491 288281140918306660913751737)
  ·
    refine ⟨216210855688729995685313803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288281140918306660913751737 216210855688729995685313803)
    ·
      refine ⟨324316283533094993527970705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216210855688729995685313803 324316283533094993527970705)
      ·
        refine ⟨243237212649821245145978029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324316283533094993527970705 243237212649821245145978029)
        ·
          refine ⟨91213954743682966929741761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243237212649821245145978029 91213954743682966929741761)
          ·
            refine ⟨68410466057762225197306321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91213954743682966929741761 68410466057762225197306321)
            ·
              refine ⟨51307849543321668897979741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68410466057762225197306321 51307849543321668897979741)
              ·
                refine ⟨19240443578745625836742403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51307849543321668897979741 19240443578745625836742403)
                ·
                  refine ⟨28860665368118438755113605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19240443578745625836742403 28860665368118438755113605)
                  ·
                    refine ⟨5411374756522207266583801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28860665368118438755113605 5411374756522207266583801)
                    ·
                      refine ⟨4058531067391655449937851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411374756522207266583801 4058531067391655449937851)
                      ·
                        rfl

theorem cell23_7903961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_7903961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903961 prefixEnd_7903961 := by exact prefixLift 7903961
  have htrace : WordTrace (prefixWord ++ tailWord_7903961) baseStart_7903961 baseEnd_7903961 := by
    simpa [prefixWord, tailWord_7903961, baseEnd_7903961] using wordTrace_append hprefix tailTrace_7903961
  have hstable : (prefixWord ++ tailWord_7903961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903961).length < 2 ^ (prefixWord ++ tailWord_7903961).sum := by decide
  have hdescent : baseEnd_7903961 < baseStart_7903961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7903989 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7903989 : Nat := 118140960795 + 7903989 * 2 ^ 59
def prefixEnd_7903989 : Nat := 4983230072969 + 3 ^ 40 * 7903989 * 2
def baseEnd_7903989 : Nat := 4058545444849981340387723

theorem tailTrace_7903989 : CollatzResearch.WordTrace tailWord_7903989 prefixEnd_7903989 4058545444849981340387723 := by
  unfold tailWord_7903989
  simp only [CollatzResearch.WordTrace]
  refine ⟨288282162162205221695771021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192188108108136814463847347 288282162162205221695771021)
  ·
    refine ⟨108105810810826958135914133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288282162162205221695771021 108105810810826958135914133)
    ·
      refine ⟨5067459881757513662620975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108105810810826958135914133 5067459881757513662620975)
      ·
        refine ⟨7601189822636270493931463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067459881757513662620975 7601189822636270493931463)
        ·
          refine ⟨11401784733954405740897195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601189822636270493931463 11401784733954405740897195)
          ·
            refine ⟨17102677100931608611345793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401784733954405740897195 17102677100931608611345793)
            ·
              refine ⟨12827007825698706458509345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17102677100931608611345793 12827007825698706458509345)
              ·
                refine ⟨9620255869274029843882009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12827007825698706458509345 9620255869274029843882009)
                ·
                  refine ⟨7215191901955522382911507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9620255869274029843882009 7215191901955522382911507)
                  ·
                    refine ⟨10822787852933283574367261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215191901955522382911507 10822787852933283574367261)
                    ·
                      refine ⟨4058545444849981340387723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10822787852933283574367261 4058545444849981340387723)
                      ·
                        rfl

theorem cell23_7903989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7903989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7903989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7903989 prefixEnd_7903989 := by exact prefixLift 7903989
  have htrace : WordTrace (prefixWord ++ tailWord_7903989) baseStart_7903989 baseEnd_7903989 := by
    simpa [prefixWord, tailWord_7903989, baseEnd_7903989] using wordTrace_append hprefix tailTrace_7903989
  have hstable : (prefixWord ++ tailWord_7903989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7903989).length < 2 ^ (prefixWord ++ tailWord_7903989).sum := by decide
  have hdescent : baseEnd_7903989 < baseStart_7903989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7903989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904014 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_7904014 : Nat := 118140960795 + 7904014 * 2 ^ 59
def prefixEnd_7904014 : Nat := 4983230072969 + 3 ^ 40 * 7904014 * 2
def baseEnd_7904014 : Nat := 1352852760622114580858369

theorem tailTrace_7904014 : CollatzResearch.WordTrace tailWord_7904014 prefixEnd_7904014 1352852760622114580858369 := by
  unfold tailWord_7904014
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035384248389331370678887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192188715991409767310287397 36035384248389331370678887)
  ·
    refine ⟨54053076372583997056018331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36035384248389331370678887 54053076372583997056018331)
    ·
      refine ⟨81079614558875995584027497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54053076372583997056018331 81079614558875995584027497)
      ·
        refine ⟨60809710919156996688020623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81079614558875995584027497 60809710919156996688020623)
        ·
          refine ⟨91214566378735495032030935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60809710919156996688020623 91214566378735495032030935)
          ·
            refine ⟨136821849568103242548046403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91214566378735495032030935 136821849568103242548046403)
            ·
              refine ⟨205232774352154863822069605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136821849568103242548046403 205232774352154863822069605)
              ·
                refine ⟨38481145191029036966638051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205232774352154863822069605 38481145191029036966638051)
                ·
                  refine ⟨57721717786543555449957077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38481145191029036966638051 57721717786543555449957077)
                  ·
                    refine ⟨1352852760622114580858369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57721717786543555449957077 1352852760622114580858369)
                    ·
                      rfl

theorem cell23_7904014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_7904014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904014 prefixEnd_7904014 := by exact prefixLift 7904014
  have htrace : WordTrace (prefixWord ++ tailWord_7904014) baseStart_7904014 baseEnd_7904014 := by
    simpa [prefixWord, tailWord_7904014, baseEnd_7904014] using wordTrace_append hprefix tailTrace_7904014
  have hstable : (prefixWord ++ tailWord_7904014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904014).length < 2 ^ (prefixWord ++ tailWord_7904014).sum := by decide
  have hdescent : baseEnd_7904014 < baseStart_7904014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904018 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_7904018 : Nat := 118140960795 + 7904018 * 2 ^ 59
def prefixEnd_7904018 : Nat := 4983230072969 + 3 ^ 40 * 7904018 * 2
def baseEnd_7904018 : Nat := 450951148420995747436121

theorem tailTrace_7904018 : CollatzResearch.WordTrace tailWord_7904018 prefixEnd_7904018 450951148420995747436121 := by
  unfold tailWord_7904018
  simp only [CollatzResearch.WordTrace]
  refine ⟨72070804969775039912144177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192188813252733439765717805 72070804969775039912144177)
  ·
    refine ⟨54053103727331279934108133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72070804969775039912144177 54053103727331279934108133)
    ·
      refine ⟨10134956948874614987645275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54053103727331279934108133 10134956948874614987645275)
      ·
        refine ⟨15202435423311922481467913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134956948874614987645275 15202435423311922481467913)
        ·
          refine ⟨11401826567483941861100935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15202435423311922481467913 11401826567483941861100935)
          ·
            refine ⟨17102739851225912791651403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401826567483941861100935 17102739851225912791651403)
            ·
              refine ⟨25654109776838869187477105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17102739851225912791651403 25654109776838869187477105)
              ·
                refine ⟨19240582332629151890607829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25654109776838869187477105 19240582332629151890607829)
                ·
                  refine ⟨450951148420995747436121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19240582332629151890607829 450951148420995747436121)
                  ·
                    rfl

theorem cell23_7904018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_7904018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904018 prefixEnd_7904018 := by exact prefixLift 7904018
  have htrace : WordTrace (prefixWord ++ tailWord_7904018) baseStart_7904018 baseEnd_7904018 := by
    simpa [prefixWord, tailWord_7904018, baseEnd_7904018] using wordTrace_append hprefix tailTrace_7904018
  have hstable : (prefixWord ++ tailWord_7904018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904018).length < 2 ^ (prefixWord ++ tailWord_7904018).sum := by decide
  have hdescent : baseEnd_7904018 < baseStart_7904018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904021 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_7904021 : Nat := 118140960795 + 7904021 * 2 ^ 59
def prefixEnd_7904021 : Nat := 4983230072969 + 3 ^ 40 * 7904021 * 2
def baseEnd_7904021 : Nat := 4058561876230925215187575

theorem tailTrace_7904021 : CollatzResearch.WordTrace tailWord_7904021 prefixEnd_7904021 4058561876230925215187575 := by
  unfold tailWord_7904021
  simp only [CollatzResearch.WordTrace]
  refine ⟨288283329298089291160935917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192188886198726194107290611 288283329298089291160935917)
  ·
    refine ⟨108106248486783484185350969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288283329298089291160935917 108106248486783484185350969)
    ·
      refine ⟨81079686365087613139013227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108106248486783484185350969 81079686365087613139013227)
      ·
        refine ⟨121619529547631419708519841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81079686365087613139013227 121619529547631419708519841)
        ·
          refine ⟨91214647160723564781389881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121619529547631419708519841 91214647160723564781389881)
          ·
            refine ⟨68410985370542673586042411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91214647160723564781389881 68410985370542673586042411)
            ·
              refine ⟨102616478055814010379063617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68410985370542673586042411 102616478055814010379063617)
              ·
                refine ⟨76962358541860507784297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102616478055814010379063617 76962358541860507784297713)
                ·
                  refine ⟨57721768906395380838223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76962358541860507784297713 57721768906395380838223285)
                  ·
                    refine ⟨5411415834974566953583433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57721768906395380838223285 5411415834974566953583433)
                    ·
                      refine ⟨4058561876230925215187575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411415834974566953583433 4058561876230925215187575)
                      ·
                        rfl

theorem cell23_7904021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_7904021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904021 prefixEnd_7904021 := by exact prefixLift 7904021
  have htrace : WordTrace (prefixWord ++ tailWord_7904021) baseStart_7904021 baseEnd_7904021 := by
    simpa [prefixWord, tailWord_7904021, baseEnd_7904021] using wordTrace_append hprefix tailTrace_7904021
  have hstable : (prefixWord ++ tailWord_7904021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904021).length < 2 ^ (prefixWord ++ tailWord_7904021).sum := by decide
  have hdescent : baseEnd_7904021 < baseStart_7904021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904031 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 2, 5]
def baseStart_7904031 : Nat := 118140960795 + 7904031 * 2 ^ 59
def prefixEnd_7904031 : Nat := 4983230072969 + 3 ^ 40 * 7904031 * 2
def baseEnd_7904031 : Nat := 1352855670345823392020843

theorem tailTrace_7904031 : CollatzResearch.WordTrace tailWord_7904031 prefixEnd_7904031 1352855670345823392020843 := by
  unfold tailWord_7904031
  simp only [CollatzResearch.WordTrace]
  refine ⟨288283694028053062868799947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192189129352035375245866631 288283694028053062868799947)
  ·
    refine ⟨432425541042079594303199921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288283694028053062868799947 432425541042079594303199921)
    ·
      refine ⟨324319155781559695727399941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432425541042079594303199921 324319155781559695727399941)
      ·
        refine ⟨60809841709042442948887489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324319155781559695727399941 60809841709042442948887489)
        ·
          refine ⟨45607381281781832211665617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60809841709042442948887489 45607381281781832211665617)
          ·
            refine ⟨34205535961336374158749213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45607381281781832211665617 34205535961336374158749213)
            ·
              refine ⟨12827075985501140309530955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34205535961336374158749213 12827075985501140309530955)
              ·
                refine ⟨19240613978251710464296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12827075985501140309530955 19240613978251710464296433)
                ·
                  refine ⟨14430460483688782848222325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19240613978251710464296433 14430460483688782848222325)
                  ·
                    refine ⟨1352855670345823392020843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14430460483688782848222325 1352855670345823392020843)
                    ·
                      rfl

theorem cell23_7904031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_7904031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904031 prefixEnd_7904031 := by exact prefixLift 7904031
  have htrace : WordTrace (prefixWord ++ tailWord_7904031) baseStart_7904031 baseEnd_7904031 := by
    simpa [prefixWord, tailWord_7904031, baseEnd_7904031] using wordTrace_append hprefix tailTrace_7904031
  have hstable : (prefixWord ++ tailWord_7904031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904031).length < 2 ^ (prefixWord ++ tailWord_7904031).sum := by decide
  have hdescent : baseEnd_7904031 < baseStart_7904031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904138 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_7904138 : Nat := 118140960795 + 7904138 * 2 ^ 59
def prefixEnd_7904138 : Nat := 4983230072969 + 3 ^ 40 * 7904138 * 2
def baseEnd_7904138 : Nat := 1352873984489167085808179

theorem tailTrace_7904138 : CollatzResearch.WordTrace tailWord_7904138 prefixEnd_7904138 1352873984489167085808179 := by
  unfold tailWord_7904138
  simp only [CollatzResearch.WordTrace]
  refine ⟨72071899159666355035736267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192191731092443613428630045 72071899159666355035736267)
  ·
    refine ⟨108107848739499532553604401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72071899159666355035736267 108107848739499532553604401)
    ·
      refine ⟨81080886554624649415203301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108107848739499532553604401 81080886554624649415203301)
      ·
        refine ⟨15202666228992121765350619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81080886554624649415203301 15202666228992121765350619)
        ·
          refine ⟨22803999343488182648025929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202666228992121765350619 22803999343488182648025929)
          ·
            refine ⟨17102999507616136986019447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22803999343488182648025929 17102999507616136986019447)
            ·
              refine ⟨25654499261424205479029171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17102999507616136986019447 25654499261424205479029171)
              ·
                refine ⟨38481748892136308218543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25654499261424205479029171 38481748892136308218543757)
                ·
                  refine ⟨14430655834551115581953909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38481748892136308218543757 14430655834551115581953909)
                  ·
                    refine ⟨1352873984489167085808179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14430655834551115581953909 1352873984489167085808179)
                    ·
                      rfl

theorem cell23_7904138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_7904138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904138 prefixEnd_7904138 := by exact prefixLift 7904138
  have htrace : WordTrace (prefixWord ++ tailWord_7904138) baseStart_7904138 baseEnd_7904138 := by
    simpa [prefixWord, tailWord_7904138, baseEnd_7904138] using wordTrace_append hprefix tailTrace_7904138
  have hstable : (prefixWord ++ tailWord_7904138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904138).length < 2 ^ (prefixWord ++ tailWord_7904138).sum := by decide
  have hdescent : baseEnd_7904138 < baseStart_7904138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904151 : List Nat := [1, 1, 3, 3, 1, 2, 3, 2, 1, 6]
def baseStart_7904151 : Nat := 118140960795 + 7904151 * 2 ^ 59
def prefixEnd_7904151 : Nat := 4983230072969 + 3 ^ 40 * 7904151 * 2
def baseEnd_7904151 : Nat := 1352876209572003235520659

theorem tailTrace_7904151 : CollatzResearch.WordTrace tailWord_7904151 prefixEnd_7904151 1352876209572003235520659 := by
  unfold tailWord_7904151
  simp only [CollatzResearch.WordTrace]
  refine ⟨288288070787618323363168307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192192047191745548908778871 288288070787618323363168307)
  ·
    refine ⟨432432106181427485044752461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288288070787618323363168307 432432106181427485044752461)
    ·
      refine ⟨162162039818035306891782173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432432106181427485044752461 162162039818035306891782173)
      ·
        refine ⟨60810764931763240084418315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162162039818035306891782173 60810764931763240084418315)
        ·
          refine ⟨91216147397644860126627473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60810764931763240084418315 91216147397644860126627473)
          ·
            refine ⟨68412110548233645094970605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91216147397644860126627473 68412110548233645094970605)
            ·
              refine ⟨25654541455587616910613977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68412110548233645094970605 25654541455587616910613977)
              ·
                refine ⟨19240906091690712682960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25654541455587616910613977 19240906091690712682960483)
                ·
                  refine ⟨28861359137536069024440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19240906091690712682960483 28861359137536069024440725)
                  ·
                    refine ⟨1352876209572003235520659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28861359137536069024440725 1352876209572003235520659)
                    ·
                      rfl

theorem cell23_7904151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_7904151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904151 prefixEnd_7904151 := by exact prefixLift 7904151
  have htrace : WordTrace (prefixWord ++ tailWord_7904151) baseStart_7904151 baseEnd_7904151 := by
    simpa [prefixWord, tailWord_7904151, baseEnd_7904151] using wordTrace_append hprefix tailTrace_7904151
  have hstable : (prefixWord ++ tailWord_7904151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904151).length < 2 ^ (prefixWord ++ tailWord_7904151).sum := by decide
  have hdescent : baseEnd_7904151 < baseStart_7904151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904196 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7904196 : Nat := 118140960795 + 7904196 * 2 ^ 59
def prefixEnd_7904196 : Nat := 4983230072969 + 3 ^ 40 * 7904196 * 2
def baseEnd_7904196 : Nat := 4058651735345462030499271

theorem tailTrace_7904196 : CollatzResearch.WordTrace tailWord_7904196 prefixEnd_7904196 4058651735345462030499271 := by
  unfold tailWord_7904196
  simp only [CollatzResearch.WordTrace]
  refine ⟨144144856036227648024278221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192193141381636864032370961 144144856036227648024278221)
  ·
    refine ⟨54054321013585368009104333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144144856036227648024278221 54054321013585368009104333)
    ·
      refine ⟨20270370380094513003414125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54054321013585368009104333 20270370380094513003414125)
      ·
        refine ⟨7601388892535442376280297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20270370380094513003414125 7601388892535442376280297)
        ·
          refine ⟨5701041669401581782210223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7601388892535442376280297 5701041669401581782210223)
          ·
            refine ⟨8551562504102372673315335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701041669401581782210223 8551562504102372673315335)
            ·
              refine ⟨12827343756153559009973003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551562504102372673315335 12827343756153559009973003)
              ·
                refine ⟨19241015634230338514959505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12827343756153559009973003 19241015634230338514959505)
                ·
                  refine ⟨14430761725672753886219629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19241015634230338514959505 14430761725672753886219629)
                  ·
                    refine ⟨5411535647127282707332361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14430761725672753886219629 5411535647127282707332361)
                    ·
                      refine ⟨4058651735345462030499271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411535647127282707332361 4058651735345462030499271)
                      ·
                        rfl

theorem cell23_7904196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7904196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904196 prefixEnd_7904196 := by exact prefixLift 7904196
  have htrace : WordTrace (prefixWord ++ tailWord_7904196) baseStart_7904196 baseEnd_7904196 := by
    simpa [prefixWord, tailWord_7904196, baseEnd_7904196] using wordTrace_append hprefix tailTrace_7904196
  have hstable : (prefixWord ++ tailWord_7904196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904196).length < 2 ^ (prefixWord ++ tailWord_7904196).sum := by decide
  have hdescent : baseEnd_7904196 < baseStart_7904196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904208 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_7904208 : Nat := 118140960795 + 7904208 * 2 ^ 59
def prefixEnd_7904208 : Nat := 4983230072969 + 3 ^ 40 * 7904208 * 2
def baseEnd_7904208 : Nat := 4058657897113315983549215

theorem tailTrace_7904208 : CollatzResearch.WordTrace tailWord_7904208 prefixEnd_7904208 4058657897113315983549215 := by
  unfold tailWord_7904208
  simp only [CollatzResearch.WordTrace]
  refine ⟨144145074874205911048996639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192193433165607881398662185 144145074874205911048996639)
  ·
    refine ⟨216217612311308866573494959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144145074874205911048996639 216217612311308866573494959)
    ·
      refine ⟨324326418466963299860242439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216217612311308866573494959 324326418466963299860242439)
      ·
        refine ⟨486489627700444949790363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324326418466963299860242439 486489627700444949790363659)
        ·
          refine ⟨729734441550667424685545489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486489627700444949790363659 729734441550667424685545489)
          ·
            refine ⟨547300831163000568514159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729734441550667424685545489 547300831163000568514159117)
            ·
              refine ⟨205237811686125213192809669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547300831163000568514159117 205237811686125213192809669)
              ·
                refine ⟨38482089691148477473651813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205237811686125213192809669 38482089691148477473651813)
                ·
                  refine ⟨7215391817090339526309715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38482089691148477473651813 7215391817090339526309715)
                  ·
                    refine ⟨10823087725635509289464573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215391817090339526309715 10823087725635509289464573)
                    ·
                      refine ⟨4058657897113315983549215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823087725635509289464573 4058657897113315983549215)
                      ·
                        rfl

theorem cell23_7904208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_7904208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904208 prefixEnd_7904208 := by exact prefixLift 7904208
  have htrace : WordTrace (prefixWord ++ tailWord_7904208) baseStart_7904208 baseEnd_7904208 := by
    simpa [prefixWord, tailWord_7904208, baseEnd_7904208] using wordTrace_append hprefix tailTrace_7904208
  have hstable : (prefixWord ++ tailWord_7904208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904208).length < 2 ^ (prefixWord ++ tailWord_7904208).sum := by decide
  have hdescent : baseEnd_7904208 < baseStart_7904208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904212 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7904212 : Nat := 118140960795 + 7904212 * 2 ^ 59
def prefixEnd_7904212 : Nat := 4983230072969 + 3 ^ 40 * 7904212 * 2
def baseEnd_7904212 : Nat := 4058659951035933967899197

theorem tailTrace_7904212 : CollatzResearch.WordTrace tailWord_7904212 prefixEnd_7904212 4058659951035933967899197 := by
  unfold tailWord_7904212
  simp only [CollatzResearch.WordTrace]
  refine ⟨144145147820198665390569445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192193530426931553854092593 144145147820198665390569445)
  ·
    refine ⟨27027215216287249760731771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144145147820198665390569445 27027215216287249760731771)
    ·
      refine ⟨40540822824430874641097657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27027215216287249760731771 40540822824430874641097657)
      ·
        refine ⟨30405617118323155980823243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40540822824430874641097657 30405617118323155980823243)
        ·
          refine ⟨45608425677484733971234865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30405617118323155980823243 45608425677484733971234865)
          ·
            refine ⟨34206319258113550478426149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45608425677484733971234865 34206319258113550478426149)
            ·
              refine ⟨6413684860896290714704903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34206319258113550478426149 6413684860896290714704903)
              ·
                refine ⟨9620527291344436072057355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413684860896290714704903 9620527291344436072057355)
                ·
                  refine ⟨14430790937016654108086033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9620527291344436072057355 14430790937016654108086033)
                  ·
                    refine ⟨10823093202762490581064525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14430790937016654108086033 10823093202762490581064525)
                    ·
                      refine ⟨4058659951035933967899197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823093202762490581064525 4058659951035933967899197)
                      ·
                        rfl

theorem cell23_7904212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7904212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904212 prefixEnd_7904212 := by exact prefixLift 7904212
  have htrace : WordTrace (prefixWord ++ tailWord_7904212) baseStart_7904212 baseEnd_7904212 := by
    simpa [prefixWord, tailWord_7904212, baseEnd_7904212] using wordTrace_append hprefix tailTrace_7904212
  have hstable : (prefixWord ++ tailWord_7904212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904212).length < 2 ^ (prefixWord ++ tailWord_7904212).sum := by decide
  have hdescent : baseEnd_7904212 < baseStart_7904212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904226 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7904226 : Nat := 118140960795 + 7904226 * 2 ^ 59
def prefixEnd_7904226 : Nat := 4983230072969 + 3 ^ 40 * 7904226 * 2
def baseEnd_7904226 : Nat := 4058667139765096913124133

theorem tailTrace_7904226 : CollatzResearch.WordTrace tailWord_7904226 prefixEnd_7904226 4058667139765096913124133 := by
  unfold tailWord_7904226
  simp only [CollatzResearch.WordTrace]
  refine ⟨72072701565586652793037133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192193870841564407448099021 72072701565586652793037133)
  ·
    refine ⟨27027263087094994797388925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72072701565586652793037133 27027263087094994797388925)
    ·
      refine ⟨10135223657660623049020847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27027263087094994797388925 10135223657660623049020847)
      ·
        refine ⟨15202835486490934573531271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135223657660623049020847 15202835486490934573531271)
        ·
          refine ⟨22804253229736401860296907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202835486490934573531271 22804253229736401860296907)
          ·
            refine ⟨34206379844604602790445361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22804253229736401860296907 34206379844604602790445361)
            ·
              refine ⟨25654784883453452092834021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34206379844604602790445361 25654784883453452092834021)
              ·
                refine ⟨4810272165647522267406379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25654784883453452092834021 4810272165647522267406379)
                ·
                  refine ⟨7215408248471283401109569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810272165647522267406379 7215408248471283401109569)
                  ·
                    refine ⟨5411556186353462550832177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215408248471283401109569 5411556186353462550832177)
                    ·
                      refine ⟨4058667139765096913124133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411556186353462550832177 4058667139765096913124133)
                      ·
                        rfl

theorem cell23_7904226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7904226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904226 prefixEnd_7904226 := by exact prefixLift 7904226
  have htrace : WordTrace (prefixWord ++ tailWord_7904226) baseStart_7904226 baseEnd_7904226 := by
    simpa [prefixWord, tailWord_7904226, baseEnd_7904226] using wordTrace_append hprefix tailTrace_7904226
  have hstable : (prefixWord ++ tailWord_7904226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904226).length < 2 ^ (prefixWord ++ tailWord_7904226).sum := by decide
  have hdescent : baseEnd_7904226 < baseStart_7904226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904251 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5]
def baseStart_7904251 : Nat := 118140960795 + 7904251 * 2 ^ 59
def prefixEnd_7904251 : Nat := 4983230072969 + 3 ^ 40 * 7904251 * 2
def baseEnd_7904251 : Nat := 4058679976781459315311517

theorem tailTrace_7904251 : CollatzResearch.WordTrace tailWord_7904251 prefixEnd_7904251 4058679976781459315311517 := by
  unfold tailWord_7904251
  simp only [CollatzResearch.WordTrace]
  refine ⟨288291718087256040441808607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192194478724837360294539071 288291718087256040441808607)
  ·
    refine ⟨432437577130884060662712911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288291718087256040441808607 432437577130884060662712911)
    ·
      refine ⟨648656365696326090994069367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432437577130884060662712911 648656365696326090994069367)
      ·
        refine ⟨972984548544489136491104051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648656365696326090994069367 972984548544489136491104051)
        ·
          refine ⟨1459476822816733704736656077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972984548544489136491104051 1459476822816733704736656077)
          ·
            refine ⟨547303808556275139276246029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1459476822816733704736656077 547303808556275139276246029)
            ·
              refine ⟨205238928208603177228592261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 547303808556275139276246029 205238928208603177228592261)
              ·
                refine ⟨38482299039113095730361049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205238928208603177228592261 38482299039113095730361049)
                ·
                  refine ⟨28861724279334821797770787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38482299039113095730361049 28861724279334821797770787)
                  ·
                    refine ⟨43292586419002232696656181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28861724279334821797770787 43292586419002232696656181)
                    ·
                      refine ⟨4058679976781459315311517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43292586419002232696656181 4058679976781459315311517)
                      ·
                        rfl

theorem cell23_7904251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 5].length) (baseStart_7904251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904251 prefixEnd_7904251 := by exact prefixLift 7904251
  have htrace : WordTrace (prefixWord ++ tailWord_7904251) baseStart_7904251 baseEnd_7904251 := by
    simpa [prefixWord, tailWord_7904251, baseEnd_7904251] using wordTrace_append hprefix tailTrace_7904251
  have hstable : (prefixWord ++ tailWord_7904251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904251).length < 2 ^ (prefixWord ++ tailWord_7904251).sum := by decide
  have hdescent : baseEnd_7904251 < baseStart_7904251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904252 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_7904252 : Nat := 118140960795 + 7904252 * 2 ^ 59
def prefixEnd_7904252 : Nat := 4983230072969 + 3 ^ 40 * 7904252 * 2
def baseEnd_7904252 : Nat := 4058680490262113811399013

theorem tailTrace_7904252 : CollatzResearch.WordTrace tailWord_7904252 prefixEnd_7904252 4058680490262113811399013 := by
  unfold tailWord_7904252
  simp only [CollatzResearch.WordTrace]
  refine ⟨144145877280126208806297505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192194503040168278408396673 144145877280126208806297505)
  ·
    refine ⟨108109407960094656604723129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144145877280126208806297505 108109407960094656604723129)
    ·
      refine ⟨81082055970070992453542347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108109407960094656604723129 81082055970070992453542347)
      ·
        refine ⟨121623083955106488680313521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81082055970070992453542347 121623083955106488680313521)
        ·
          refine ⟨91217312966329866510235141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121623083955106488680313521 91217312966329866510235141)
          ·
            refine ⟨17103246181186849970669089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91217312966329866510235141 17103246181186849970669089)
            ·
              refine ⟨12827434635890137478001817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17103246181186849970669089 12827434635890137478001817)
              ·
                refine ⟨9620575976917603108501363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12827434635890137478001817 9620575976917603108501363)
                ·
                  refine ⟨14430863965376404662752045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9620575976917603108501363 14430863965376404662752045)
                  ·
                    refine ⟨5411573987016151748532017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14430863965376404662752045 5411573987016151748532017)
                    ·
                      refine ⟨4058680490262113811399013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411573987016151748532017 4058680490262113811399013)
                      ·
                        rfl

theorem cell23_7904252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_7904252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904252 prefixEnd_7904252 := by exact prefixLift 7904252
  have htrace : WordTrace (prefixWord ++ tailWord_7904252) baseStart_7904252 baseEnd_7904252 := by
    simpa [prefixWord, tailWord_7904252, baseEnd_7904252] using wordTrace_append hprefix tailTrace_7904252
  have hstable : (prefixWord ++ tailWord_7904252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904252).length < 2 ^ (prefixWord ++ tailWord_7904252).sum := by decide
  have hdescent : baseEnd_7904252 < baseStart_7904252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904268 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_7904268 : Nat := 118140960795 + 7904268 * 2 ^ 59
def prefixEnd_7904268 : Nat := 4983230072969 + 3 ^ 40 * 7904268 * 2
def baseEnd_7904268 : Nat := 4058688705952585748798939

theorem tailTrace_7904268 : CollatzResearch.WordTrace tailWord_7904268 prefixEnd_7904268 4058688705952585748798939 := by
  unfold tailWord_7904268
  simp only [CollatzResearch.WordTrace]
  refine ⟨144146169064097226172588729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192194892085462968230118305 144146169064097226172588729)
  ·
    refine ⟨108109626798072919629441547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144146169064097226172588729 108109626798072919629441547)
    ·
      refine ⟨162164440197109379444162321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108109626798072919629441547 162164440197109379444162321)
      ·
        refine ⟨121623330147832034583121741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162164440197109379444162321 121623330147832034583121741)
        ·
          refine ⟨45608748805437012968670653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121623330147832034583121741 45608748805437012968670653)
          ·
            refine ⟨17103280802038879863251495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45608748805437012968670653 17103280802038879863251495)
            ·
              refine ⟨25654921203058319794877243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17103280802038879863251495 25654921203058319794877243)
              ·
                refine ⟨38482381804587479692315865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25654921203058319794877243 38482381804587479692315865)
                ·
                  refine ⟨28861786353440609769236899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38482381804587479692315865 28861786353440609769236899)
                  ·
                    refine ⟨43292679530160914653855349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28861786353440609769236899 43292679530160914653855349)
                    ·
                      refine ⟨4058688705952585748798939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43292679530160914653855349 4058688705952585748798939)
                      ·
                        rfl

theorem cell23_7904268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_7904268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904268 prefixEnd_7904268 := by exact prefixLift 7904268
  have htrace : WordTrace (prefixWord ++ tailWord_7904268) baseStart_7904268 baseEnd_7904268 := by
    simpa [prefixWord, tailWord_7904268, baseEnd_7904268] using wordTrace_append hprefix tailTrace_7904268
  have hstable : (prefixWord ++ tailWord_7904268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904268).length < 2 ^ (prefixWord ++ tailWord_7904268).sum := by decide
  have hdescent : baseEnd_7904268 < baseStart_7904268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904282 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_7904282 : Nat := 118140960795 + 7904282 * 2 ^ 59
def prefixEnd_7904282 : Nat := 4983230072969 + 3 ^ 40 * 7904282 * 2
def baseEnd_7904282 : Nat := 4058695894681748694023875

theorem tailTrace_7904282 : CollatzResearch.WordTrace tailWord_7904282 prefixEnd_7904282 4058695894681748694023875 := by
  unfold tailWord_7904282
  simp only [CollatzResearch.WordTrace]
  refine ⟨72073212187535933184046775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192195232500095821824124733 72073212187535933184046775)
  ·
    refine ⟨108109818281303899776070163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72073212187535933184046775 108109818281303899776070163)
    ·
      refine ⟨162164727421955849664105245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108109818281303899776070163 162164727421955849664105245)
      ·
        refine ⟨60811772783233443624039467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162164727421955849664105245 60811772783233443624039467)
        ·
          refine ⟨91217659174850165436059201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60811772783233443624039467 91217659174850165436059201)
          ·
            refine ⟨68413244381137624077044401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91217659174850165436059201 68413244381137624077044401)
            ·
              refine ⟨51309933285853218057783301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68413244381137624077044401 51309933285853218057783301)
              ·
                refine ⟨9620612491097478385834369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51309933285853218057783301 9620612491097478385834369)
                ·
                  refine ⟨7215459368323108789375777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9620612491097478385834369 7215459368323108789375777)
                  ·
                    refine ⟨5411594526242331592031833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215459368323108789375777 5411594526242331592031833)
                    ·
                      refine ⟨4058695894681748694023875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411594526242331592031833 4058695894681748694023875)
                      ·
                        rfl

theorem cell23_7904282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_7904282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904282 prefixEnd_7904282 := by exact prefixLift 7904282
  have htrace : WordTrace (prefixWord ++ tailWord_7904282) baseStart_7904282 baseEnd_7904282 := by
    simpa [prefixWord, tailWord_7904282, baseEnd_7904282] using wordTrace_append hprefix tailTrace_7904282
  have hstable : (prefixWord ++ tailWord_7904282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904282).length < 2 ^ (prefixWord ++ tailWord_7904282).sum := by decide
  have hdescent : baseEnd_7904282 < baseStart_7904282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904311 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_7904311 : Nat := 118140960795 + 7904311 * 2 ^ 59
def prefixEnd_7904311 : Nat := 4983230072969 + 3 ^ 40 * 7904311 * 2
def baseEnd_7904311 : Nat := 4058710785620729080561241

theorem tailTrace_7904311 : CollatzResearch.WordTrace tailWord_7904311 prefixEnd_7904311 4058710785620729080561241 := by
  unfold tailWord_7904311
  simp only [CollatzResearch.WordTrace]
  refine ⟨288293906467038670688992787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192195937644692447125995191 288293906467038670688992787)
  ·
    refine ⟨432440859700558006033489181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288293906467038670688992787 432440859700558006033489181)
    ·
      refine ⟨162165322387709252262558443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432440859700558006033489181 162165322387709252262558443)
      ·
        refine ⟨243247983581563878393837665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162165322387709252262558443 243247983581563878393837665)
        ·
          refine ⟨182435987686172908795378249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243247983581563878393837665 182435987686172908795378249)
          ·
            refine ⟨136826990764629681596533687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182435987686172908795378249 136826990764629681596533687)
            ·
              refine ⟨205240486146944522394800531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136826990764629681596533687 205240486146944522394800531)
              ·
                refine ⟨307860729220416783592200797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205240486146944522394800531 307860729220416783592200797)
                ·
                  refine ⟨115447773457656293847075299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307860729220416783592200797 115447773457656293847075299)
                  ·
                    refine ⟨173171660186484440770612949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115447773457656293847075299 173171660186484440770612949)
                    ·
                      refine ⟨4058710785620729080561241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173171660186484440770612949 4058710785620729080561241)
                      ·
                        rfl

theorem cell23_7904311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_7904311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904311 prefixEnd_7904311 := by exact prefixLift 7904311
  have htrace : WordTrace (prefixWord ++ tailWord_7904311) baseStart_7904311 baseEnd_7904311 := by
    simpa [prefixWord, tailWord_7904311, baseEnd_7904311] using wordTrace_append hprefix tailTrace_7904311
  have hstable : (prefixWord ++ tailWord_7904311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904311).length < 2 ^ (prefixWord ++ tailWord_7904311).sum := by decide
  have hdescent : baseEnd_7904311 < baseStart_7904311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904365 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_7904365 : Nat := 118140960795 + 7904365 * 2 ^ 59
def prefixEnd_7904365 : Nat := 4983230072969 + 3 ^ 40 * 7904365 * 2
def baseEnd_7904365 : Nat := 1352912837858690623095331

theorem tailTrace_7904365 : CollatzResearch.WordTrace tailWord_7904365 prefixEnd_7904365 1352912837858690623095331 := by
  unfold tailWord_7904365
  simp only [CollatzResearch.WordTrace]
  refine ⟨288295876008843037911458549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192197250672562025274305699 288295876008843037911458549)
  ·
    refine ⟨27027738375829034804199239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288295876008843037911458549 27027738375829034804199239)
    ·
      refine ⟨40541607563743552206298859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27027738375829034804199239 40541607563743552206298859)
      ·
        refine ⟨60812411345615328309448289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40541607563743552206298859 60812411345615328309448289)
        ·
          refine ⟨45609308509211496232086217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60812411345615328309448289 45609308509211496232086217)
          ·
            refine ⟨34206981381908622174064663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45609308509211496232086217 34206981381908622174064663)
            ·
              refine ⟨51310472072862933261096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34206981381908622174064663 51310472072862933261096995)
              ·
                refine ⟨76965708109294399891645493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51310472072862933261096995 76965708109294399891645493)
                ·
                  refine ⟨7215535135246349989841765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76965708109294399891645493 7215535135246349989841765)
                  ·
                    refine ⟨1352912837858690623095331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215535135246349989841765 1352912837858690623095331)
                    ·
                      rfl

theorem cell23_7904365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_7904365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904365 prefixEnd_7904365 := by exact prefixLift 7904365
  have htrace : WordTrace (prefixWord ++ tailWord_7904365) baseStart_7904365 baseEnd_7904365 := by
    simpa [prefixWord, tailWord_7904365, baseEnd_7904365] using wordTrace_append hprefix tailTrace_7904365
  have hstable : (prefixWord ++ tailWord_7904365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904365).length < 2 ^ (prefixWord ++ tailWord_7904365).sum := by decide
  have hdescent : baseEnd_7904365 < baseStart_7904365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904412 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 6]
def baseStart_7904412 : Nat := 118140960795 + 7904412 * 2 ^ 59
def prefixEnd_7904412 : Nat := 4983230072969 + 3 ^ 40 * 7904412 * 2
def baseEnd_7904412 : Nat := 450973627462981465044253

theorem tailTrace_7904412 : CollatzResearch.WordTrace tailWord_7904412 prefixEnd_7904412 450973627462981465044253 := by
  unfold tailWord_7904412
  simp only [CollatzResearch.WordTrace]
  refine ⟨144148795119836382469209745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192198393493115176625612993 144148795119836382469209745)
  ·
    refine ⟨108111596339877286851907309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144148795119836382469209745 108111596339877286851907309)
    ·
      refine ⟨40541848627453982569465241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108111596339877286851907309 40541848627453982569465241)
      ·
        refine ⟨30406386470590486927098931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40541848627453982569465241 30406386470590486927098931)
        ·
          refine ⟨45609579705885730390648397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30406386470590486927098931 45609579705885730390648397)
          ·
            refine ⟨17103592389707148896493149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45609579705885730390648397 17103592389707148896493149)
            ·
              refine ⟨6413847146140180836184931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103592389707148896493149 6413847146140180836184931)
              ·
                refine ⟨9620770719210271254277397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413847146140180836184931 9620770719210271254277397)
                ·
                  refine ⟨450973627462981465044253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9620770719210271254277397 450973627462981465044253)
                  ·
                    rfl

theorem cell23_7904412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_7904412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904412 prefixEnd_7904412 := by exact prefixLift 7904412
  have htrace : WordTrace (prefixWord ++ tailWord_7904412) baseStart_7904412 baseEnd_7904412 := by
    simpa [prefixWord, tailWord_7904412, baseEnd_7904412] using wordTrace_append hprefix tailTrace_7904412
  have hstable : (prefixWord ++ tailWord_7904412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904412).length < 2 ^ (prefixWord ++ tailWord_7904412).sum := by decide
  have hdescent : baseEnd_7904412 < baseStart_7904412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904449 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7904449 : Nat := 118140960795 + 7904449 * 2 ^ 59
def prefixEnd_7904449 : Nat := 4983230072969 + 3 ^ 40 * 7904449 * 2
def baseEnd_7904449 : Nat := 4058781645951049540635607

theorem tailTrace_7904449 : CollatzResearch.WordTrace tailWord_7904449 prefixEnd_7904449 4058781645951049540635607 := by
  unfold tailWord_7904449
  simp only [CollatzResearch.WordTrace]
  refine ⟨288298939740538720257516401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192199293160359146838344267 288298939740538720257516401)
  ·
    refine ⟨216224204805404040193137301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288298939740538720257516401 216224204805404040193137301)
    ·
      refine ⟨10135509600253314384053311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216224204805404040193137301 10135509600253314384053311)
      ·
        refine ⟨15203264400379971576079967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135509600253314384053311 15203264400379971576079967)
        ·
          refine ⟨22804896600569957364119951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203264400379971576079967 22804896600569957364119951)
          ·
            refine ⟨34207344900854936046179927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22804896600569957364119951 34207344900854936046179927)
            ·
              refine ⟨51311017351282404069269891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34207344900854936046179927 51311017351282404069269891)
              ·
                refine ⟨76966526026923606103904837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51311017351282404069269891 76966526026923606103904837)
                ·
                  refine ⟨14431223630048176144482157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76966526026923606103904837 14431223630048176144482157)
                  ·
                    refine ⟨5411708861268066054180809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14431223630048176144482157 5411708861268066054180809)
                    ·
                      refine ⟨4058781645951049540635607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411708861268066054180809 4058781645951049540635607)
                      ·
                        rfl

theorem cell23_7904449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7904449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904449 prefixEnd_7904449 := by exact prefixLift 7904449
  have htrace : WordTrace (prefixWord ++ tailWord_7904449) baseStart_7904449 baseEnd_7904449 := by
    simpa [prefixWord, tailWord_7904449, baseEnd_7904449] using wordTrace_append hprefix tailTrace_7904449
  have hstable : (prefixWord ++ tailWord_7904449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904449).length < 2 ^ (prefixWord ++ tailWord_7904449).sum := by decide
  have hdescent : baseEnd_7904449 < baseStart_7904449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904450 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_7904450 : Nat := 118140960795 + 7904450 * 2 ^ 59
def prefixEnd_7904450 : Nat := 4983230072969 + 3 ^ 40 * 7904450 * 2
def baseEnd_7904450 : Nat := 1352927386477234678907701

theorem tailTrace_7904450 : CollatzResearch.WordTrace tailWord_7904450 prefixEnd_7904450 1352927386477234678907701 := by
  unfold tailWord_7904450
  simp only [CollatzResearch.WordTrace]
  refine ⟨72074744053383774357075701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192199317475690064952201869 72074744053383774357075701)
  ·
    refine ⟨6757007255004728845975847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72074744053383774357075701 6757007255004728845975847)
    ·
      refine ⟨10135510882507093268963771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6757007255004728845975847 10135510882507093268963771)
      ·
        refine ⟨15203266323760639903445657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135510882507093268963771 15203266323760639903445657)
        ·
          refine ⟨11402449742820479927584243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15203266323760639903445657 11402449742820479927584243)
          ·
            refine ⟨17103674614230719891376365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402449742820479927584243 17103674614230719891376365)
            ·
              refine ⟨6413877980336519959266137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103674614230719891376365 6413877980336519959266137)
              ·
                refine ⟨4810408485252389969449603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413877980336519959266137 4810408485252389969449603)
                ·
                  refine ⟨7215612727878584954174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810408485252389969449603 7215612727878584954174405)
                  ·
                    refine ⟨1352927386477234678907701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215612727878584954174405 1352927386477234678907701)
                    ·
                      rfl

theorem cell23_7904450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_7904450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904450 prefixEnd_7904450 := by exact prefixLift 7904450
  have htrace : WordTrace (prefixWord ++ tailWord_7904450) baseStart_7904450 baseEnd_7904450 := by
    simpa [prefixWord, tailWord_7904450, baseEnd_7904450] using wordTrace_append hprefix tailTrace_7904450
  have hstable : (prefixWord ++ tailWord_7904450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904450).length < 2 ^ (prefixWord ++ tailWord_7904450).sum := by decide
  have hdescent : baseEnd_7904450 < baseStart_7904450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904465 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_7904465 : Nat := 118140960795 + 7904465 * 2 ^ 59
def prefixEnd_7904465 : Nat := 4983230072969 + 3 ^ 40 * 7904465 * 2
def baseEnd_7904465 : Nat := 4058789861641521478035533

theorem tailTrace_7904465 : CollatzResearch.WordTrace tailWord_7904465 prefixEnd_7904465 4058789861641521478035533 := by
  unfold tailWord_7904465
  simp only [CollatzResearch.WordTrace]
  refine ⟨288299523308480754990098849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192199682205653836660065899 288299523308480754990098849)
  ·
    refine ⟨216224642481360566242574137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288299523308480754990098849 216224642481360566242574137)
    ·
      refine ⟨162168481861020424681930603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216224642481360566242574137 162168481861020424681930603)
      ·
        refine ⟨243252722791530637022895905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162168481861020424681930603 243252722791530637022895905)
        ·
          refine ⟨182439542093647977767171929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243252722791530637022895905 182439542093647977767171929)
          ·
            refine ⟨136829656570235983325378947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182439542093647977767171929 136829656570235983325378947)
            ·
              refine ⟨205244484855353974988068421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136829656570235983325378947 205244484855353974988068421)
              ·
                refine ⟨38483340910378870310262829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205244484855353974988068421 38483340910378870310262829)
                ·
                  refine ⟨14431252841392076366348561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38483340910378870310262829 14431252841392076366348561)
                  ·
                    refine ⟨10823439631044057274761421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14431252841392076366348561 10823439631044057274761421)
                    ·
                      refine ⟨4058789861641521478035533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823439631044057274761421 4058789861641521478035533)
                      ·
                        rfl

theorem cell23_7904465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_7904465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904465 prefixEnd_7904465 := by exact prefixLift 7904465
  have htrace : WordTrace (prefixWord ++ tailWord_7904465) baseStart_7904465 baseEnd_7904465 := by
    simpa [prefixWord, tailWord_7904465, baseEnd_7904465] using wordTrace_append hprefix tailTrace_7904465
  have hstable : (prefixWord ++ tailWord_7904465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904465).length < 2 ^ (prefixWord ++ tailWord_7904465).sum := by decide
  have hdescent : baseEnd_7904465 < baseStart_7904465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904499 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 1, 2, 3]
def baseStart_7904499 : Nat := 118140960795 + 7904499 * 2 ^ 59
def prefixEnd_7904499 : Nat := 4983230072969 + 3 ^ 40 * 7904499 * 2
def baseEnd_7904499 : Nat := 4058807319983774345010377

theorem tailTrace_7904499 : CollatzResearch.WordTrace tailWord_7904499 prefixEnd_7904499 4058807319983774345010377 := by
  unfold tailWord_7904499
  simp only [CollatzResearch.WordTrace]
  refine ⟨288300763390357578796836551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192200508926905052531224367 288300763390357578796836551)
  ·
    refine ⟨432451145085536368195254827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288300763390357578796836551 432451145085536368195254827)
    ·
      refine ⟨648676717628304552292882241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432451145085536368195254827 648676717628304552292882241)
      ·
        refine ⟨486507538221228414219661681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648676717628304552292882241 486507538221228414219661681)
        ·
          refine ⟨364880653665921310664746261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486507538221228414219661681 364880653665921310664746261)
          ·
            refine ⟨17103780640590061437409981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364880653665921310664746261 17103780640590061437409981)
            ·
              refine ⟨6413917740221273039028743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103780640590061437409981 6413917740221273039028743)
              ·
                refine ⟨9620876610331909558543115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413917740221273039028743 9620876610331909558543115)
                ·
                  refine ⟨14431314915497864337814673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9620876610331909558543115 14431314915497864337814673)
                  ·
                    refine ⟨10823486186623398253361005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14431314915497864337814673 10823486186623398253361005)
                    ·
                      refine ⟨4058807319983774345010377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823486186623398253361005 4058807319983774345010377)
                      ·
                        rfl

theorem cell23_7904499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 2, 3].length) (baseStart_7904499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904499 prefixEnd_7904499 := by exact prefixLift 7904499
  have htrace : WordTrace (prefixWord ++ tailWord_7904499) baseStart_7904499 baseEnd_7904499 := by
    simpa [prefixWord, tailWord_7904499, baseEnd_7904499] using wordTrace_append hprefix tailTrace_7904499
  have hstable : (prefixWord ++ tailWord_7904499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904499).length < 2 ^ (prefixWord ++ tailWord_7904499).sum := by decide
  have hdescent : baseEnd_7904499 < baseStart_7904499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904513 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_7904513 : Nat := 118140960795 + 7904513 * 2 ^ 59
def prefixEnd_7904513 : Nat := 4983230072969 + 3 ^ 40 * 7904513 * 2
def baseEnd_7904513 : Nat := 4058814508712937290235313

theorem tailTrace_7904513 : CollatzResearch.WordTrace tailWord_7904513 prefixEnd_7904513 4058814508712937290235313 := by
  unfold tailWord_7904513
  simp only [CollatzResearch.WordTrace]
  refine ⟨288301274012306859187846193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192200849341537906125230795 288301274012306859187846193)
  ·
    refine ⟨216225955509230144390884645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288301274012306859187846193 216225955509230144390884645)
    ·
      refine ⟨40542366657980652073290871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216225955509230144390884645 40542366657980652073290871)
      ·
        refine ⟨60813549986970978109936307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40542366657980652073290871 60813549986970978109936307)
        ·
          refine ⟨91220324980456467164904461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60813549986970978109936307 91220324980456467164904461)
          ·
            refine ⟨34207621867671175186839173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91220324980456467164904461 34207621867671175186839173)
            ·
              refine ⟨6413929100188345347532345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34207621867671175186839173 6413929100188345347532345)
              ·
                refine ⟨4810446825141259010649259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413929100188345347532345 4810446825141259010649259)
                ·
                  refine ⟨7215670237711888515973889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810446825141259010649259 7215670237711888515973889)
                  ·
                    refine ⟨5411752678283916386980417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215670237711888515973889 5411752678283916386980417)
                    ·
                      refine ⟨4058814508712937290235313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411752678283916386980417 4058814508712937290235313)
                      ·
                        rfl

theorem cell23_7904513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_7904513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904513 prefixEnd_7904513 := by exact prefixLift 7904513
  have htrace : WordTrace (prefixWord ++ tailWord_7904513) baseStart_7904513 baseEnd_7904513 := by
    simpa [prefixWord, tailWord_7904513, baseEnd_7904513] using wordTrace_append hprefix tailTrace_7904513
  have hstable : (prefixWord ++ tailWord_7904513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904513).length < 2 ^ (prefixWord ++ tailWord_7904513).sum := by decide
  have hdescent : baseEnd_7904513 < baseStart_7904513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904535 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7904535 : Nat := 118140960795 + 7904535 * 2 ^ 59
def prefixEnd_7904535 : Nat := 4983230072969 + 3 ^ 40 * 7904535 * 2
def baseEnd_7904535 : Nat := 4058825805287336204160211

theorem tailTrace_7904535 : CollatzResearch.WordTrace tailWord_7904535 prefixEnd_7904535 4058825805287336204160211 := by
  unfold tailWord_7904535
  simp only [CollatzResearch.WordTrace]
  refine ⟨288302076418227156945147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192201384278818104630098039 288302076418227156945147059)
  ·
    refine ⟨432453114627340735417720589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288302076418227156945147059 432453114627340735417720589)
    ·
      refine ⟨162169917985252775781645221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432453114627340735417720589 162169917985252775781645221)
      ·
        refine ⟨30406859622234895459058479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162169917985252775781645221 30406859622234895459058479)
        ·
          refine ⟨45610289433352343188587719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30406859622234895459058479 45610289433352343188587719)
          ·
            refine ⟨68415434150028514782881579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45610289433352343188587719 68415434150028514782881579)
            ·
              refine ⟨102623151225042772174322369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68415434150028514782881579 102623151225042772174322369)
              ·
                refine ⟨76967363418782079130741777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102623151225042772174322369 76967363418782079130741777)
                ·
                  refine ⟨57725522564086559348056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76967363418782079130741777 57725522564086559348056333)
                  ·
                    refine ⟨21647070961532459755521125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57725522564086559348056333 21647070961532459755521125)
                    ·
                      refine ⟨4058825805287336204160211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21647070961532459755521125 4058825805287336204160211)
                      ·
                        rfl

theorem cell23_7904535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7904535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904535 prefixEnd_7904535 := by exact prefixLift 7904535
  have htrace : WordTrace (prefixWord ++ tailWord_7904535) baseStart_7904535 baseEnd_7904535 := by
    simpa [prefixWord, tailWord_7904535, baseEnd_7904535] using wordTrace_append hprefix tailTrace_7904535
  have hstable : (prefixWord ++ tailWord_7904535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904535).length < 2 ^ (prefixWord ++ tailWord_7904535).sum := by decide
  have hdescent : baseEnd_7904535 < baseStart_7904535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904575 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 7]
def baseStart_7904575 : Nat := 118140960795 + 7904575 * 2 ^ 59
def prefixEnd_7904575 : Nat := 4983230072969 + 3 ^ 40 * 7904575 * 2
def baseEnd_7904575 : Nat := 450982927168168449740003

theorem tailTrace_7904575 : CollatzResearch.WordTrace tailWord_7904575 prefixEnd_7904575 450982927168168449740003 := by
  unfold tailWord_7904575
  simp only [CollatzResearch.WordTrace]
  refine ⟨288303535338082243776603179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192202356892054829184402119 288303535338082243776603179)
  ·
    refine ⟨432455303007123365664904769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288303535338082243776603179 432455303007123365664904769)
    ·
      refine ⟨324341477255342524248678577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432455303007123365664904769 324341477255342524248678577)
      ·
        refine ⟨243256107941506893186508933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324341477255342524248678577 243256107941506893186508933)
        ·
          refine ⟨45610520239032542472470425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243256107941506893186508933 45610520239032542472470425)
          ·
            refine ⟨34207890179274406854352819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45610520239032542472470425 34207890179274406854352819)
            ·
              refine ⟨51311835268911610281529229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34207890179274406854352819 51311835268911610281529229)
              ·
                refine ⟨19241938225841853855573461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51311835268911610281529229 19241938225841853855573461)
                ·
                  refine ⟨450982927168168449740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19241938225841853855573461 450982927168168449740003)
                  ·
                    rfl

theorem cell23_7904575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 7].length) (baseStart_7904575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904575 prefixEnd_7904575 := by exact prefixLift 7904575
  have htrace : WordTrace (prefixWord ++ tailWord_7904575) baseStart_7904575 baseEnd_7904575 := by
    simpa [prefixWord, tailWord_7904575, baseEnd_7904575] using wordTrace_append hprefix tailTrace_7904575
  have hstable : (prefixWord ++ tailWord_7904575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904575).length < 2 ^ (prefixWord ++ tailWord_7904575).sum := by decide
  have hdescent : baseEnd_7904575 < baseStart_7904575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904652 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_7904652 : Nat := 118140960795 + 7904652 * 2 ^ 59
def prefixEnd_7904652 : Nat := 4983230072969 + 3 ^ 40 * 7904652 * 2
def baseEnd_7904652 : Nat := 1352961960841304082132391

theorem tailTrace_7904652 : CollatzResearch.WordTrace tailWord_7904652 prefixEnd_7904652 1352961960841304082132391 := by
  unfold tailWord_7904652
  simp only [CollatzResearch.WordTrace]
  refine ⟨144153171879401642963578105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192204229172535523951437473 144153171879401642963578105)
  ·
    refine ⟨108114878909551232222683579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144153171879401642963578105 108114878909551232222683579)
    ·
      refine ⟨162172318364326848334025369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108114878909551232222683579 162172318364326848334025369)
      ·
        refine ⟨121629238773245136250519027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162172318364326848334025369 121629238773245136250519027)
        ·
          refine ⟨182443858159867704375778541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121629238773245136250519027 182443858159867704375778541)
          ·
            refine ⟨68416446809950389140916953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182443858159867704375778541 68416446809950389140916953)
            ·
              refine ⟨51312335107462791855687715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68416446809950389140916953 51312335107462791855687715)
              ·
                refine ⟨76968502661194187783531573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51312335107462791855687715 76968502661194187783531573)
                ·
                  refine ⟨7215797124486955104706085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76968502661194187783531573 7215797124486955104706085)
                  ·
                    refine ⟨1352961960841304082132391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215797124486955104706085 1352961960841304082132391)
                    ·
                      rfl

theorem cell23_7904652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_7904652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904652 prefixEnd_7904652 := by exact prefixLift 7904652
  have htrace : WordTrace (prefixWord ++ tailWord_7904652) baseStart_7904652 baseEnd_7904652 := by
    simpa [prefixWord, tailWord_7904652, baseEnd_7904652] using wordTrace_append hprefix tailTrace_7904652
  have hstable : (prefixWord ++ tailWord_7904652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904652).length < 2 ^ (prefixWord ++ tailWord_7904652).sum := by decide
  have hdescent : baseEnd_7904652 < baseStart_7904652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904679 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7904679 : Nat := 118140960795 + 7904679 * 2 ^ 59
def prefixEnd_7904679 : Nat := 4983230072969 + 3 ^ 40 * 7904679 * 2
def baseEnd_7904679 : Nat := 4058899746501583640759549

theorem tailTrace_7904679 : CollatzResearch.WordTrace tailWord_7904679 prefixEnd_7904679 4058899746501583640759549 := by
  unfold tailWord_7904679
  simp only [CollatzResearch.WordTrace]
  refine ⟨288307328529705469538389091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192204885686470313025592727 288307328529705469538389091)
  ·
    refine ⟨432460992794558204307583637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288307328529705469538389091 432460992794558204307583637)
    ·
      refine ⟨20271609037244915826917983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 432460992794558204307583637 20271609037244915826917983)
      ·
        refine ⟨30407413555867373740376975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271609037244915826917983 30407413555867373740376975)
        ·
          refine ⟨45611120333801060610565463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30407413555867373740376975 45611120333801060610565463)
          ·
            refine ⟨68416680500701590915848195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45611120333801060610565463 68416680500701590915848195)
            ·
              refine ⟨102625020751052386373772293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68416680500701590915848195 102625020751052386373772293)
              ·
                refine ⟨19242191390822322445082305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102625020751052386373772293 19242191390822322445082305)
                ·
                  refine ⟨14431643543116741833811729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19242191390822322445082305 14431643543116741833811729)
                  ·
                    refine ⟨10823732657337556375358797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14431643543116741833811729 10823732657337556375358797)
                    ·
                      refine ⟨4058899746501583640759549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823732657337556375358797 4058899746501583640759549)
                      ·
                        rfl

theorem cell23_7904679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7904679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904679 prefixEnd_7904679 := by exact prefixLift 7904679
  have htrace : WordTrace (prefixWord ++ tailWord_7904679) baseStart_7904679 baseEnd_7904679 := by
    simpa [prefixWord, tailWord_7904679, baseEnd_7904679] using wordTrace_append hprefix tailTrace_7904679
  have hstable : (prefixWord ++ tailWord_7904679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904679).length < 2 ^ (prefixWord ++ tailWord_7904679).sum := by decide
  have hdescent : baseEnd_7904679 < baseStart_7904679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904712 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_7904712 : Nat := 118140960795 + 7904712 * 2 ^ 59
def prefixEnd_7904712 : Nat := 4983230072969 + 3 ^ 40 * 7904712 * 2
def baseEnd_7904712 : Nat := 1352972230454394003882299

theorem tailTrace_7904712 : CollatzResearch.WordTrace tailWord_7904712 prefixEnd_7904712 1352972230454394003882299 := by
  unfold tailWord_7904712
  simp only [CollatzResearch.WordTrace]
  refine ⟨144154266069292958087170195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192205688092390610782893593 144154266069292958087170195)
  ·
    refine ⟨216231399103939437130755293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144154266069292958087170195 216231399103939437130755293)
    ·
      refine ⟨81086774663977288924033235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216231399103939437130755293 81086774663977288924033235)
      ·
        refine ⟨121630161995965933386049853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81086774663977288924033235 121630161995965933386049853)
        ·
          refine ⟨45611310748487225019768695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121630161995965933386049853 45611310748487225019768695)
          ·
            refine ⟨68416966122730837529653043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45611310748487225019768695 68416966122730837529653043)
            ·
              refine ⟨102625449184096256294479565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68416966122730837529653043 102625449184096256294479565)
              ·
                refine ⟨38484543444036096110429837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102625449184096256294479565 38484543444036096110429837)
                ·
                  refine ⟨14431703791513536041411189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38484543444036096110429837 14431703791513536041411189)
                  ·
                    refine ⟨1352972230454394003882299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14431703791513536041411189 1352972230454394003882299)
                    ·
                      rfl

theorem cell23_7904712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_7904712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904712 prefixEnd_7904712 := by exact prefixLift 7904712
  have htrace : WordTrace (prefixWord ++ tailWord_7904712) baseStart_7904712 baseEnd_7904712 := by
    simpa [prefixWord, tailWord_7904712, baseEnd_7904712] using wordTrace_append hprefix tailTrace_7904712
  have hstable : (prefixWord ++ tailWord_7904712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904712).length < 2 ^ (prefixWord ++ tailWord_7904712).sum := by decide
  have hdescent : baseEnd_7904712 < baseStart_7904712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904729 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_7904729 : Nat := 118140960795 + 7904729 * 2 ^ 59
def prefixEnd_7904729 : Nat := 4983230072969 + 3 ^ 40 * 7904729 * 2
def baseEnd_7904729 : Nat := 1352975140178102815044773

theorem tailTrace_7904729 : CollatzResearch.WordTrace tailWord_7904729 prefixEnd_7904729 1352975140178102815044773 := by
  unfold tailWord_7904729
  simp only [CollatzResearch.WordTrace]
  refine ⟨288309152179524328077709241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192206101453016218718472827 288309152179524328077709241)
  ·
    refine ⟨216231864134643246058281931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288309152179524328077709241 216231864134643246058281931)
    ·
      refine ⟨324347796201964869087422897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216231864134643246058281931 324347796201964869087422897)
      ·
        refine ⟨243260847151473651815567173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324347796201964869087422897 243260847151473651815567173)
        ·
          refine ⟨45611408840901309715418845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243260847151473651815567173 45611408840901309715418845)
          ·
            refine ⟨17104278315337991143282067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45611408840901309715418845 17104278315337991143282067)
            ·
              refine ⟨25656417473006986714923101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17104278315337991143282067 25656417473006986714923101)
              ·
                refine ⟨9621156552377620018096163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25656417473006986714923101 9621156552377620018096163)
                ·
                  refine ⟨14431734828566430027144245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9621156552377620018096163 14431734828566430027144245)
                  ·
                    refine ⟨1352975140178102815044773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14431734828566430027144245 1352975140178102815044773)
                    ·
                      rfl

theorem cell23_7904729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_7904729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904729 prefixEnd_7904729 := by exact prefixLift 7904729
  have htrace : WordTrace (prefixWord ++ tailWord_7904729) baseStart_7904729 baseEnd_7904729 := by
    simpa [prefixWord, tailWord_7904729, baseEnd_7904729] using wordTrace_append hprefix tailTrace_7904729
  have hstable : (prefixWord ++ tailWord_7904729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904729).length < 2 ^ (prefixWord ++ tailWord_7904729).sum := by decide
  have hdescent : baseEnd_7904729 < baseStart_7904729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904743 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7904743 : Nat := 118140960795 + 7904743 * 2 ^ 59
def prefixEnd_7904743 : Nat := 4983230072969 + 3 ^ 40 * 7904743 * 2
def baseEnd_7904743 : Nat := 4058932609263471390359255

theorem tailTrace_7904743 : CollatzResearch.WordTrace tailWord_7904743 prefixEnd_7904743 4058932609263471390359255 := by
  unfold tailWord_7904743
  simp only [CollatzResearch.WordTrace]
  refine ⟨288309662801473608468718883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192206441867649072312479255 288309662801473608468718883)
  ·
    refine ⟨432464494202210412703078325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288309662801473608468718883 432464494202210412703078325)
    ·
      refine ⟨40543546331457226190913593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432464494202210412703078325 40543546331457226190913593)
      ·
        refine ⟨30407659748592919643185195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40543546331457226190913593 30407659748592919643185195)
        ·
          refine ⟨45611489622889379464777793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30407659748592919643185195 45611489622889379464777793)
          ·
            refine ⟨34208617217167034598583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45611489622889379464777793 34208617217167034598583345)
            ·
              refine ⟨25656462912875275948937509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34208617217167034598583345 25656462912875275948937509)
              ·
                refine ⟨4810586796164114240425783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25656462912875275948937509 4810586796164114240425783)
                ·
                  refine ⟨7215880194246171360638675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810586796164114240425783 7215880194246171360638675)
                  ·
                    refine ⟨10823820291369257040958013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215880194246171360638675 10823820291369257040958013)
                    ·
                      refine ⟨4058932609263471390359255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10823820291369257040958013 4058932609263471390359255)
                      ·
                        rfl

theorem cell23_7904743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7904743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904743 prefixEnd_7904743 := by exact prefixLift 7904743
  have htrace : WordTrace (prefixWord ++ tailWord_7904743) baseStart_7904743 baseEnd_7904743 := by
    simpa [prefixWord, tailWord_7904743, baseEnd_7904743] using wordTrace_append hprefix tailTrace_7904743
  have hstable : (prefixWord ++ tailWord_7904743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904743).length < 2 ^ (prefixWord ++ tailWord_7904743).sum := by decide
  have hdescent : baseEnd_7904743 < baseStart_7904743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904752 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_7904752 : Nat := 118140960795 + 7904752 * 2 ^ 59
def prefixEnd_7904752 : Nat := 4983230072969 + 3 ^ 40 * 7904752 * 2
def baseEnd_7904752 : Nat := 4058937230589361855146713

theorem tailTrace_7904752 : CollatzResearch.WordTrace tailWord_7904752 prefixEnd_7904752 4058937230589361855146713 := by
  unfold tailWord_7904752
  simp only [CollatzResearch.WordTrace]
  refine ⟨144154995529220501502898255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192206660705627335337197673 144154995529220501502898255)
  ·
    refine ⟨216232493293830752254347383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144154995529220501502898255 216232493293830752254347383)
    ·
      refine ⟨324348739940746128381521075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216232493293830752254347383 324348739940746128381521075)
      ·
        refine ⟨486523109911119192572281613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324348739940746128381521075 486523109911119192572281613)
        ·
          refine ⟨182446166216669697214605605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486523109911119192572281613 182446166216669697214605605)
          ·
            refine ⟨34208656165625568227738551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182446166216669697214605605 34208656165625568227738551)
            ·
              refine ⟨51312984248438352341607827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34208656165625568227738551 51312984248438352341607827)
              ·
                refine ⟨76969476372657528512411741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51312984248438352341607827 76969476372657528512411741)
                ·
                  refine ⟨28863553639746573192154403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76969476372657528512411741 28863553639746573192154403)
                  ·
                    refine ⟨43295330459619859788231605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28863553639746573192154403 43295330459619859788231605)
                    ·
                      refine ⟨4058937230589361855146713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43295330459619859788231605 4058937230589361855146713)
                      ·
                        rfl

theorem cell23_7904752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_7904752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904752 prefixEnd_7904752 := by exact prefixLift 7904752
  have htrace : WordTrace (prefixWord ++ tailWord_7904752) baseStart_7904752 baseEnd_7904752 := by
    simpa [prefixWord, tailWord_7904752, baseEnd_7904752] using wordTrace_append hprefix tailTrace_7904752
  have hstable : (prefixWord ++ tailWord_7904752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904752).length < 2 ^ (prefixWord ++ tailWord_7904752).sum := by decide
  have hdescent : baseEnd_7904752 < baseStart_7904752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904762 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_7904762 : Nat := 118140960795 + 7904762 * 2 ^ 59
def prefixEnd_7904762 : Nat := 4983230072969 + 3 ^ 40 * 7904762 * 2
def baseEnd_7904762 : Nat := 4058942365395906816021667

theorem tailTrace_7904762 : CollatzResearch.WordTrace tailWord_7904762 prefixEnd_7904762 4058942365395906816021667 := by
  unfold tailWord_7904762
  simp only [CollatzResearch.WordTrace]
  refine ⟨72077588947101193678415135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192206903858936516475773693 72077588947101193678415135)
  ·
    refine ⟨108116383420651790517622703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72077588947101193678415135 108116383420651790517622703)
    ·
      refine ⟨162174575130977685776434055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108116383420651790517622703 162174575130977685776434055)
      ·
        refine ⟨243261862696466528664651083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162174575130977685776434055 243261862696466528664651083)
        ·
          refine ⟨364892794044699792996976625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243261862696466528664651083 364892794044699792996976625)
          ·
            refine ⟨273669595533524844747732469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364892794044699792996976625 273669595533524844747732469)
            ·
              refine ⟨25656524581267954195099919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273669595533524844747732469 25656524581267954195099919)
              ·
                refine ⟨38484786871901931292649879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25656524581267954195099919 38484786871901931292649879)
                ·
                  refine ⟨57727180307852896938974819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38484786871901931292649879 57727180307852896938974819)
                  ·
                    refine ⟨86590770461779345408462229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57727180307852896938974819 86590770461779345408462229)
                    ·
                      refine ⟨4058942365395906816021667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86590770461779345408462229 4058942365395906816021667)
                      ·
                        rfl

theorem cell23_7904762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_7904762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904762 prefixEnd_7904762 := by exact prefixLift 7904762
  have htrace : WordTrace (prefixWord ++ tailWord_7904762) baseStart_7904762 baseEnd_7904762 := by
    simpa [prefixWord, tailWord_7904762, baseEnd_7904762] using wordTrace_append hprefix tailTrace_7904762
  have hstable : (prefixWord ++ tailWord_7904762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904762).length < 2 ^ (prefixWord ++ tailWord_7904762).sum := by decide
  have hdescent : baseEnd_7904762 < baseStart_7904762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904800 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7904800 : Nat := 118140960795 + 7904800 * 2 ^ 59
def prefixEnd_7904800 : Nat := 4983230072969 + 3 ^ 40 * 7904800 * 2
def baseEnd_7904800 : Nat := 4058961877660777667346493

theorem tailTrace_7904800 : CollatzResearch.WordTrace tailWord_7904800 prefixEnd_7904800 4058961877660777667346493 := by
  unfold tailWord_7904800
  simp only [CollatzResearch.WordTrace]
  refine ⟨144155870881133553601771927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192207827841511404802362569 144155870881133553601771927)
  ·
    refine ⟨216233806321700330402657891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144155870881133553601771927 216233806321700330402657891)
    ·
      refine ⟨324350709482550495603986837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216233806321700330402657891 324350709482550495603986837)
      ·
        refine ⟨15203939506994554481436883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324350709482550495603986837 15203939506994554481436883)
        ·
          refine ⟨22805909260491831722155325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203939506994554481436883 22805909260491831722155325)
          ·
            refine ⟨8552215972684436895808247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22805909260491831722155325 8552215972684436895808247)
            ·
              refine ⟨12828323959026655343712371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552215972684436895808247 12828323959026655343712371)
              ·
                refine ⟨19242485938539983015568557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12828323959026655343712371 19242485938539983015568557)
                ·
                  refine ⟨7215932226952493630838209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19242485938539983015568557 7215932226952493630838209)
                  ·
                    refine ⟨5411949170214370223128657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215932226952493630838209 5411949170214370223128657)
                    ·
                      refine ⟨4058961877660777667346493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411949170214370223128657 4058961877660777667346493)
                      ·
                        rfl

theorem cell23_7904800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7904800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904800 prefixEnd_7904800 := by exact prefixLift 7904800
  have htrace : WordTrace (prefixWord ++ tailWord_7904800) baseStart_7904800 baseEnd_7904800 := by
    simpa [prefixWord, tailWord_7904800, baseEnd_7904800] using wordTrace_append hprefix tailTrace_7904800
  have hstable : (prefixWord ++ tailWord_7904800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904800).length < 2 ^ (prefixWord ++ tailWord_7904800).sum := by decide
  have hdescent : baseEnd_7904800 < baseStart_7904800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904826 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_7904826 : Nat := 118140960795 + 7904826 * 2 ^ 59
def prefixEnd_7904826 : Nat := 4983230072969 + 3 ^ 40 * 7904826 * 2
def baseEnd_7904826 : Nat := 4058975228157794565621373

theorem tailTrace_7904826 : CollatzResearch.WordTrace tailWord_7904826 prefixEnd_7904826 4058975228157794565621373 := by
  unfold tailWord_7904826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72078172515043228410997583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192208460040115275762660221 72078172515043228410997583)
  ·
    refine ⟨108117258772564842616496375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72078172515043228410997583 108117258772564842616496375)
    ·
      refine ⟨162175888158847263924744563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108117258772564842616496375 162175888158847263924744563)
      ·
        refine ⟨243263832238270895887116845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162175888158847263924744563 243263832238270895887116845)
        ·
          refine ⟨91223937089351585957668817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243263832238270895887116845 91223937089351585957668817)
          ·
            refine ⟨68417952817013689468251613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91223937089351585957668817 68417952817013689468251613)
            ·
              refine ⟨25656732306380133550594355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68417952817013689468251613 25656732306380133550594355)
              ·
                refine ⟨38485098459570200325891533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25656732306380133550594355 38485098459570200325891533)
                ·
                  refine ⟨14431911922338825122209325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38485098459570200325891533 14431911922338825122209325)
                  ·
                    refine ⟨5411966970877059420828497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14431911922338825122209325 5411966970877059420828497)
                    ·
                      refine ⟨4058975228157794565621373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411966970877059420828497 4058975228157794565621373)
                      ·
                        rfl

theorem cell23_7904826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_7904826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904826 prefixEnd_7904826 := by exact prefixLift 7904826
  have htrace : WordTrace (prefixWord ++ tailWord_7904826) baseStart_7904826 baseEnd_7904826 := by
    simpa [prefixWord, tailWord_7904826, baseEnd_7904826] using wordTrace_append hprefix tailTrace_7904826
  have hstable : (prefixWord ++ tailWord_7904826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904826).length < 2 ^ (prefixWord ++ tailWord_7904826).sum := by decide
  have hdescent : baseEnd_7904826 < baseStart_7904826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904832 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_7904832 : Nat := 118140960795 + 7904832 * 2 ^ 59
def prefixEnd_7904832 : Nat := 4983230072969 + 3 ^ 40 * 7904832 * 2
def baseEnd_7904832 : Nat := 1352992769680573847382115

theorem tailTrace_7904832 : CollatzResearch.WordTrace tailWord_7904832 prefixEnd_7904832 1352992769680573847382115 := by
  unfold tailWord_7904832
  simp only [CollatzResearch.WordTrace]
  refine ⟨144156454449075588334354375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192208605932100784445805833 144156454449075588334354375)
  ·
    refine ⟨216234681673613382501531563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144156454449075588334354375 216234681673613382501531563)
    ·
      refine ⟨324352022510420073752297345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216234681673613382501531563 324352022510420073752297345)
      ·
        refine ⟨243264016882815055314223009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324352022510420073752297345 243264016882815055314223009)
        ·
          refine ⟨182448012662111291485667257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243264016882815055314223009 182448012662111291485667257)
          ·
            refine ⟨136836009496583468614250443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182448012662111291485667257 136836009496583468614250443)
            ·
              refine ⟨205254014244875202921375665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136836009496583468614250443 205254014244875202921375665)
              ·
                refine ⟨153940510683656402191031749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205254014244875202921375665 153940510683656402191031749)
                ·
                  refine ⟨28863845753185575410818453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153940510683656402191031749 28863845753185575410818453)
                  ·
                    refine ⟨1352992769680573847382115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28863845753185575410818453 1352992769680573847382115)
                    ·
                      rfl

theorem cell23_7904832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_7904832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904832 prefixEnd_7904832 := by exact prefixLift 7904832
  have htrace : WordTrace (prefixWord ++ tailWord_7904832) baseStart_7904832 baseEnd_7904832 := by
    simpa [prefixWord, tailWord_7904832, baseEnd_7904832] using wordTrace_append hprefix tailTrace_7904832
  have hstable : (prefixWord ++ tailWord_7904832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904832).length < 2 ^ (prefixWord ++ tailWord_7904832).sum := by decide
  have hdescent : baseEnd_7904832 < baseStart_7904832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904869 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7904869 : Nat := 118140960795 + 7904869 * 2 ^ 59
def prefixEnd_7904869 : Nat := 4983230072969 + 3 ^ 40 * 7904869 * 2
def baseEnd_7904869 : Nat := 4058997307825937897383675

theorem tailTrace_7904869 : CollatzResearch.WordTrace tailWord_7904869 prefixEnd_7904869 4058997307825937897383675 := by
  unfold tailWord_7904869
  simp only [CollatzResearch.WordTrace]
  refine ⟨288314258399017131987805661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192209505599344754658537107 288314258399017131987805661)
  ·
    refine ⟨108117846899631424495427123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288314258399017131987805661 108117846899631424495427123)
    ·
      refine ⟨162176770349447136743140685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108117846899631424495427123 162176770349447136743140685)
      ·
        refine ⟨60816288881042676278677757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162176770349447136743140685 60816288881042676278677757)
        ·
          refine ⟨22806108330391003604504159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60816288881042676278677757 22806108330391003604504159)
          ·
            refine ⟨34209162495586505406756239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806108330391003604504159 34209162495586505406756239)
            ·
              refine ⟨51313743743379758110134359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34209162495586505406756239 51313743743379758110134359)
              ·
                refine ⟨76970615615069637165201539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51313743743379758110134359 76970615615069637165201539)
                ·
                  refine ⟨115455923422604455747802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76970615615069637165201539 115455923422604455747802309)
                  ·
                    refine ⟨21647985641738335452712933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115455923422604455747802309 21647985641738335452712933)
                    ·
                      refine ⟨4058997307825937897383675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21647985641738335452712933 4058997307825937897383675)
                      ·
                        rfl

theorem cell23_7904869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7904869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904869 prefixEnd_7904869 := by exact prefixLift 7904869
  have htrace : WordTrace (prefixWord ++ tailWord_7904869) baseStart_7904869 baseEnd_7904869 := by
    simpa [prefixWord, tailWord_7904869, baseEnd_7904869] using wordTrace_append hprefix tailTrace_7904869
  have hstable : (prefixWord ++ tailWord_7904869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904869).length < 2 ^ (prefixWord ++ tailWord_7904869).sum := by decide
  have hdescent : baseEnd_7904869 < baseStart_7904869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904873 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 2, 2, 2]
def baseStart_7904873 : Nat := 118140960795 + 7904873 * 2 ^ 59
def prefixEnd_7904873 : Nat := 4983230072969 + 3 ^ 40 * 7904873 * 2
def baseEnd_7904873 : Nat := 4058999361748555881733657

theorem tailTrace_7904873 : CollatzResearch.WordTrace tailWord_7904873 prefixEnd_7904873 4058999361748555881733657 := by
  unfold tailWord_7904873
  simp only [CollatzResearch.WordTrace]
  refine ⟨288314404291002640670951273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192209602860668427113967515 288314404291002640670951273)
  ·
    refine ⟨216235803218251980503213455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288314404291002640670951273 216235803218251980503213455)
    ·
      refine ⟨324353704827377970754820183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216235803218251980503213455 324353704827377970754820183)
      ·
        refine ⟨486530557241066956132230275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324353704827377970754820183 486530557241066956132230275)
        ·
          refine ⟨729795835861600434198345413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486530557241066956132230275 729795835861600434198345413)
          ·
            refine ⟨136836719224050081412189765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 729795835861600434198345413 136836719224050081412189765)
            ·
              refine ⟨25656884854509390264785581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136836719224050081412189765 25656884854509390264785581)
              ·
                refine ⟨9621331820441021349294593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25656884854509390264785581 9621331820441021349294593)
                ·
                  refine ⟨7215998865330766011970945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9621331820441021349294593 7215998865330766011970945)
                  ·
                    refine ⟨5411999148998074508978209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215998865330766011970945 5411999148998074508978209)
                    ·
                      refine ⟨4058999361748555881733657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5411999148998074508978209 4058999361748555881733657)
                      ·
                        rfl

theorem cell23_7904873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2, 2].length) (baseStart_7904873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904873 prefixEnd_7904873 := by exact prefixLift 7904873
  have htrace : WordTrace (prefixWord ++ tailWord_7904873) baseStart_7904873 baseEnd_7904873 := by
    simpa [prefixWord, tailWord_7904873, baseEnd_7904873] using wordTrace_append hprefix tailTrace_7904873
  have hstable : (prefixWord ++ tailWord_7904873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904873).length < 2 ^ (prefixWord ++ tailWord_7904873).sum := by decide
  have hdescent : baseEnd_7904873 < baseStart_7904873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904889 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_7904889 : Nat := 118140960795 + 7904889 * 2 ^ 59
def prefixEnd_7904889 : Nat := 4983230072969 + 3 ^ 40 * 7904889 * 2
def baseEnd_7904889 : Nat := 4059007577439027819133583

theorem tailTrace_7904889 : CollatzResearch.WordTrace tailWord_7904889 prefixEnd_7904889 4059007577439027819133583 := by
  unfold tailWord_7904889
  simp only [CollatzResearch.WordTrace]
  refine ⟨288314987858944675403533721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192209991905963116935689147 288314987858944675403533721)
  ·
    refine ⟨216236240894208506552650291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288314987858944675403533721 216236240894208506552650291)
    ·
      refine ⟨324354361341312759828975437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216236240894208506552650291 324354361341312759828975437)
      ·
        refine ⟨121632885502992284935865789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324354361341312759828975437 121632885502992284935865789)
        ·
          refine ⟨45612332063622106850949671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121632885502992284935865789 45612332063622106850949671)
          ·
            refine ⟨68418498095433160276424507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45612332063622106850949671 68418498095433160276424507)
            ·
              refine ⟨102627747143149740414636761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68418498095433160276424507 102627747143149740414636761)
              ·
                refine ⟨76970810357362305310977571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102627747143149740414636761 76970810357362305310977571)
                ·
                  refine ⟨115456215536043457966466357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76970810357362305310977571 115456215536043457966466357)
                  ·
                    refine ⟨10824020206504074184356221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115456215536043457966466357 10824020206504074184356221)
                    ·
                      refine ⟨4059007577439027819133583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824020206504074184356221 4059007577439027819133583)
                      ·
                        rfl

theorem cell23_7904889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_7904889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904889 prefixEnd_7904889 := by exact prefixLift 7904889
  have htrace : WordTrace (prefixWord ++ tailWord_7904889) baseStart_7904889 baseEnd_7904889 := by
    simpa [prefixWord, tailWord_7904889, baseEnd_7904889] using wordTrace_append hprefix tailTrace_7904889
  have hstable : (prefixWord ++ tailWord_7904889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904889).length < 2 ^ (prefixWord ++ tailWord_7904889).sum := by decide
  have hdescent : baseEnd_7904889 < baseStart_7904889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904896 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 5]
def baseStart_7904896 : Nat := 118140960795 + 7904896 * 2 ^ 59
def prefixEnd_7904896 : Nat := 4983230072969 + 3 ^ 40 * 7904896 * 2
def baseEnd_7904896 : Nat := 451001241311512143527339

theorem tailTrace_7904896 : CollatzResearch.WordTrace tailWord_7904896 prefixEnd_7904896 451001241311512143527339 := by
  unfold tailWord_7904896
  simp only [CollatzResearch.WordTrace]
  refine ⟨144157621584959657799519271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192210162113279543732692361 144157621584959657799519271)
  ·
    refine ⟨216236432377439486699278907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144157621584959657799519271 216236432377439486699278907)
    ·
      refine ⟨324354648566159230048918361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216236432377439486699278907 324354648566159230048918361)
      ·
        refine ⟨243265986424619422536688771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324354648566159230048918361 243265986424619422536688771)
        ·
          refine ⟨364898979636929133805033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243265986424619422536688771 364898979636929133805033157)
          ·
            refine ⟨68418558681924212588443717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364898979636929133805033157 68418558681924212588443717)
            ·
              refine ⟨12828479752860789860333197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68418558681924212588443717 12828479752860789860333197)
              ·
                refine ⟨4810679907322796197624949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12828479752860789860333197 4810679907322796197624949)
                ·
                  refine ⟨451001241311512143527339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810679907322796197624949 451001241311512143527339)
                  ·
                    rfl

theorem cell23_7904896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 5].length) (baseStart_7904896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904896 prefixEnd_7904896 := by exact prefixLift 7904896
  have htrace : WordTrace (prefixWord ++ tailWord_7904896) baseStart_7904896 baseEnd_7904896 := by
    simpa [prefixWord, tailWord_7904896, baseEnd_7904896] using wordTrace_append hprefix tailTrace_7904896
  have hstable : (prefixWord ++ tailWord_7904896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904896).length < 2 ^ (prefixWord ++ tailWord_7904896).sum := by decide
  have hdescent : baseEnd_7904896 < baseStart_7904896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904906 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_7904906 : Nat := 118140960795 + 7904906 * 2 ^ 59
def prefixEnd_7904906 : Nat := 4983230072969 + 3 ^ 40 * 7904906 * 2
def baseEnd_7904906 : Nat := 4059016306610154252621005

theorem tailTrace_7904906 : CollatzResearch.WordTrace tailWord_7904906 prefixEnd_7904906 4059016306610154252621005 := by
  unfold tailWord_7904906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72078901974970771826725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192210405266588724871268381 72078901974970771826725643)
  ·
    refine ⟨108118352962456157740088465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72078901974970771826725643 108118352962456157740088465)
    ·
      refine ⟨81088764721842118305066349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108118352962456157740088465 81088764721842118305066349)
      ·
        refine ⟨30408286770690794364399881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81088764721842118305066349 30408286770690794364399881)
        ·
          refine ⟨22806215078018095773299911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30408286770690794364399881 22806215078018095773299911)
          ·
            refine ⟨34209322617027143659949867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806215078018095773299911 34209322617027143659949867)
            ·
              refine ⟨51313983925540715489924801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34209322617027143659949867 51313983925540715489924801)
              ·
                refine ⟨38485487944155536617443601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51313983925540715489924801 38485487944155536617443601)
                ·
                  refine ⟨28864115958116652463082701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38485487944155536617443601 28864115958116652463082701)
                  ·
                    refine ⟨10824043484293744673656013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28864115958116652463082701 10824043484293744673656013)
                    ·
                      refine ⟨4059016306610154252621005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824043484293744673656013 4059016306610154252621005)
                      ·
                        rfl

theorem cell23_7904906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_7904906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904906 prefixEnd_7904906 := by exact prefixLift 7904906
  have htrace : WordTrace (prefixWord ++ tailWord_7904906) baseStart_7904906 baseEnd_7904906 := by
    simpa [prefixWord, tailWord_7904906, baseEnd_7904906] using wordTrace_append hprefix tailTrace_7904906
  have hstable : (prefixWord ++ tailWord_7904906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904906).length < 2 ^ (prefixWord ++ tailWord_7904906).sum := by decide
  have hdescent : baseEnd_7904906 < baseStart_7904906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904926 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7904926 : Nat := 118140960795 + 7904926 * 2 ^ 59
def prefixEnd_7904926 : Nat := 4983230072969 + 3 ^ 40 * 7904926 * 2
def baseEnd_7904926 : Nat := 1353008858741081391456971

theorem tailTrace_7904926 : CollatzResearch.WordTrace tailWord_7904926 prefixEnd_7904926 1353008858741081391456971 := by
  unfold tailWord_7904926
  simp only [CollatzResearch.WordTrace]
  refine ⟨36039542169976328840328829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192210891573207087148420421 36039542169976328840328829)
  ·
    refine ⟨13514828313741123315123311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36039542169976328840328829 13514828313741123315123311)
    ·
      refine ⟨20272242470611684972684967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13514828313741123315123311 20272242470611684972684967)
      ·
        refine ⟨30408363705917527459027451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20272242470611684972684967 30408363705917527459027451)
        ·
          refine ⟨45612545558876291188541177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30408363705917527459027451 45612545558876291188541177)
          ·
            refine ⟨34209409169157218391405883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45612545558876291188541177 34209409169157218391405883)
            ·
              refine ⟨51314113753735827587108825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34209409169157218391405883 51314113753735827587108825)
              ·
                refine ⟨38485585315301870690331619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51314113753735827587108825 38485585315301870690331619)
                ·
                  refine ⟨57728377972952806035497429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38485585315301870690331619 57728377972952806035497429)
                  ·
                    refine ⟨1353008858741081391456971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57728377972952806035497429 1353008858741081391456971)
                    ·
                      rfl

theorem cell23_7904926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7904926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904926 prefixEnd_7904926 := by exact prefixLift 7904926
  have htrace : WordTrace (prefixWord ++ tailWord_7904926) baseStart_7904926 baseEnd_7904926 := by
    simpa [prefixWord, tailWord_7904926, baseEnd_7904926] using wordTrace_append hprefix tailTrace_7904926
  have hstable : (prefixWord ++ tailWord_7904926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904926).length < 2 ^ (prefixWord ++ tailWord_7904926).sum := by decide
  have hdescent : baseEnd_7904926 < baseStart_7904926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904946 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_7904946 : Nat := 118140960795 + 7904946 * 2 ^ 59
def prefixEnd_7904946 : Nat := 4983230072969 + 3 ^ 40 * 7904946 * 2
def baseEnd_7904946 : Nat := 4059036845836334096120821

theorem tailTrace_7904946 : CollatzResearch.WordTrace tailWord_7904946 prefixEnd_7904946 4059036845836334096120821 := by
  unfold tailWord_7904946
  simp only [CollatzResearch.WordTrace]
  refine ⟨72079266704934543534589673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192211377879825449425572461 72079266704934543534589673)
  ·
    refine ⟨54059450028700907650942255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72079266704934543534589673 54059450028700907650942255)
    ·
      refine ⟨81089175043051361476413383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54059450028700907650942255 81089175043051361476413383)
      ·
        refine ⟨121633762564577042214620075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81089175043051361476413383 121633762564577042214620075)
        ·
          refine ⟨182450643846865563321930113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121633762564577042214620075 182450643846865563321930113)
          ·
            refine ⟨136837982885149172491447585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182450643846865563321930113 136837982885149172491447585)
            ·
              refine ⟨102628487163861879368585689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136837982885149172491447585 102628487163861879368585689)
              ·
                refine ⟨76971365372896409526439267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102628487163861879368585689 76971365372896409526439267)
                ·
                  refine ⟨115457048059344614289658901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76971365372896409526439267 115457048059344614289658901)
                  ·
                    refine ⟨5412049127781778794827761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115457048059344614289658901 5412049127781778794827761)
                    ·
                      refine ⟨4059036845836334096120821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412049127781778794827761 4059036845836334096120821)
                      ·
                        rfl

theorem cell23_7904946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_7904946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904946 prefixEnd_7904946 := by exact prefixLift 7904946
  have htrace : WordTrace (prefixWord ++ tailWord_7904946) baseStart_7904946 baseEnd_7904946 := by
    simpa [prefixWord, tailWord_7904946, baseEnd_7904946] using wordTrace_append hprefix tailTrace_7904946
  have hstable : (prefixWord ++ tailWord_7904946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904946).length < 2 ^ (prefixWord ++ tailWord_7904946).sum := by decide
  have hdescent : baseEnd_7904946 < baseStart_7904946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904979 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3]
def baseStart_7904979 : Nat := 118140960795 + 7904979 * 2 ^ 59
def prefixEnd_7904979 : Nat := 4983230072969 + 3 ^ 40 * 7904979 * 2
def baseEnd_7904979 : Nat := 4059053790697932467008169

theorem tailTrace_7904979 : CollatzResearch.WordTrace tailWord_7904979 prefixEnd_7904979 4059053790697932467008169 := by
  unfold tailWord_7904979
  simp only [CollatzResearch.WordTrace]
  refine ⟨288318270428618620774309991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192212180285745747182873327 288318270428618620774309991)
  ·
    refine ⟨432477405642927931161464987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288318270428618620774309991 432477405642927931161464987)
    ·
      refine ⟨648716108464391896742197481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432477405642927931161464987 648716108464391896742197481)
      ·
        refine ⟨486537081348293922556648111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648716108464391896742197481 486537081348293922556648111)
        ·
          refine ⟨729805622022440883834972167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486537081348293922556648111 729805622022440883834972167)
          ·
            refine ⟨1094708433033661325752458251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729805622022440883834972167 1094708433033661325752458251)
            ·
              refine ⟨1642062649550491988628687377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094708433033661325752458251 1642062649550491988628687377)
              ·
                refine ⟨1231546987162868991471515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642062649550491988628687377 1231546987162868991471515533)
                ·
                  refine ⟨461830120186075871801818325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231546987162868991471515533 461830120186075871801818325)
                  ·
                    refine ⟨10824143441861153245355117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 461830120186075871801818325 10824143441861153245355117)
                    ·
                      refine ⟨4059053790697932467008169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824143441861153245355117 4059053790697932467008169)
                      ·
                        rfl

theorem cell23_7904979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_7904979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904979 prefixEnd_7904979 := by exact prefixLift 7904979
  have htrace : WordTrace (prefixWord ++ tailWord_7904979) baseStart_7904979 baseEnd_7904979 := by
    simpa [prefixWord, tailWord_7904979, baseEnd_7904979] using wordTrace_append hprefix tailTrace_7904979
  have hstable : (prefixWord ++ tailWord_7904979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904979).length < 2 ^ (prefixWord ++ tailWord_7904979).sum := by decide
  have hdescent : baseEnd_7904979 < baseStart_7904979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7904986 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_7904986 : Nat := 118140960795 + 7904986 * 2 ^ 59
def prefixEnd_7904986 : Nat := 4983230072969 + 3 ^ 40 * 7904986 * 2
def baseEnd_7904986 : Nat := 451006376118057104402293

theorem tailTrace_7904986 : CollatzResearch.WordTrace tailWord_7904986 prefixEnd_7904986 451006376118057104402293 := by
  unfold tailWord_7904986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72079631434898315242453703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192212350493062173979876541 72079631434898315242453703)
  ·
    refine ⟨108119447152347472863680555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72079631434898315242453703 108119447152347472863680555)
    ·
      refine ⟨162179170728521209295520833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108119447152347472863680555 162179170728521209295520833)
      ·
        refine ⟨121634378046390906971640625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162179170728521209295520833 121634378046390906971640625)
        ·
          refine ⟨91225783534793180228730469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121634378046390906971640625 91225783534793180228730469)
          ·
            refine ⟨17104834412773721292886963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91225783534793180228730469 17104834412773721292886963)
            ·
              refine ⟨25657251619160581939330445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17104834412773721292886963 25657251619160581939330445)
              ·
                refine ⟨9621469357185218227248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25657251619160581939330445 9621469357185218227248917)
                ·
                  refine ⟨451006376118057104402293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9621469357185218227248917 451006376118057104402293)
                  ·
                    rfl

theorem cell23_7904986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_7904986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7904986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7904986 prefixEnd_7904986 := by exact prefixLift 7904986
  have htrace : WordTrace (prefixWord ++ tailWord_7904986) baseStart_7904986 baseEnd_7904986 := by
    simpa [prefixWord, tailWord_7904986, baseEnd_7904986] using wordTrace_append hprefix tailTrace_7904986
  have hstable : (prefixWord ++ tailWord_7904986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7904986).length < 2 ^ (prefixWord ++ tailWord_7904986).sum := by decide
  have hdescent : baseEnd_7904986 < baseStart_7904986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7904986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905023 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 2, 3, 2]
def baseStart_7905023 : Nat := 118140960795 + 7905023 * 2 ^ 59
def prefixEnd_7905023 : Nat := 4983230072969 + 3 ^ 40 * 7905023 * 2
def baseEnd_7905023 : Nat := 4059076383846730294857967

theorem tailTrace_7905023 : CollatzResearch.WordTrace tailWord_7905023 prefixEnd_7905023 4059076383846730294857967 := by
  unfold tailWord_7905023
  simp only [CollatzResearch.WordTrace]
  refine ⟨288319875240459216288911723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192213250160306144192607815 288319875240459216288911723)
  ·
    refine ⟨432479812860688824433367585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288319875240459216288911723 432479812860688824433367585)
    ·
      refine ⟨324359859645516618325025689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432479812860688824433367585 324359859645516618325025689)
      ·
        refine ⟨243269894734137463743769267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324359859645516618325025689 243269894734137463743769267)
        ·
          refine ⟨364904842101206195615653901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243269894734137463743769267 364904842101206195615653901)
          ·
            refine ⟨136839315787952323355870213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364904842101206195615653901 136839315787952323355870213)
            ·
              refine ⟨25657371710241060629225665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136839315787952323355870213 25657371710241060629225665)
              ·
                refine ⟨19243028782680795471919249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25657371710241060629225665 19243028782680795471919249)
                ·
                  refine ⟨14432271587010596603939437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19243028782680795471919249 14432271587010596603939437)
                  ·
                    refine ⟨5412101845128973726477289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14432271587010596603939437 5412101845128973726477289)
                    ·
                      refine ⟨4059076383846730294857967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412101845128973726477289 4059076383846730294857967)
                      ·
                        rfl

theorem cell23_7905023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_7905023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905023 prefixEnd_7905023 := by exact prefixLift 7905023
  have htrace : WordTrace (prefixWord ++ tailWord_7905023) baseStart_7905023 baseEnd_7905023 := by
    simpa [prefixWord, tailWord_7905023, baseEnd_7905023] using wordTrace_append hprefix tailTrace_7905023
  have hstable : (prefixWord ++ tailWord_7905023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905023).length < 2 ^ (prefixWord ++ tailWord_7905023).sum := by decide
  have hdescent : baseEnd_7905023 < baseStart_7905023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905036 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_7905036 : Nat := 118140960795 + 7905036 * 2 ^ 59
def prefixEnd_7905036 : Nat := 4983230072969 + 3 ^ 40 * 7905036 * 2
def baseEnd_7905036 : Nat := 4059083059095238743995407

theorem tailTrace_7905036 : CollatzResearch.WordTrace tailWord_7905036 prefixEnd_7905036 4059083059095238743995407 := by
  unfold tailWord_7905036
  simp only [CollatzResearch.WordTrace]
  refine ⟨144160174694706059754567481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192213566259608079672756641 144160174694706059754567481)
  ·
    refine ⟨108120131021029544815925611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144160174694706059754567481 108120131021029544815925611)
    ·
      refine ⟨162180196531544317223888417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108120131021029544815925611 162180196531544317223888417)
      ·
        refine ⟨121635147398658237917916313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162180196531544317223888417 121635147398658237917916313)
        ·
          refine ⟨91226360548993678438437235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121635147398658237917916313 91226360548993678438437235)
          ·
            refine ⟨136839540823490517657655853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91226360548993678438437235 136839540823490517657655853)
            ·
              refine ⟨51314827808808944121620945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136839540823490517657655853 51314827808808944121620945)
              ·
                refine ⟨38486120856606708091215709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51314827808808944121620945 38486120856606708091215709)
                ·
                  refine ⟨14432295321227515534205891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38486120856606708091215709 14432295321227515534205891)
                  ·
                    refine ⟨21648442981841273301308837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14432295321227515534205891 21648442981841273301308837)
                    ·
                      refine ⟨4059083059095238743995407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21648442981841273301308837 4059083059095238743995407)
                      ·
                        rfl

theorem cell23_7905036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_7905036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905036 prefixEnd_7905036 := by exact prefixLift 7905036
  have htrace : WordTrace (prefixWord ++ tailWord_7905036) baseStart_7905036 baseEnd_7905036 := by
    simpa [prefixWord, tailWord_7905036, baseEnd_7905036] using wordTrace_append hprefix tailTrace_7905036
  have hstable : (prefixWord ++ tailWord_7905036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905036).length < 2 ^ (prefixWord ++ tailWord_7905036).sum := by decide
  have hdescent : baseEnd_7905036 < baseStart_7905036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905049 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_7905049 : Nat := 118140960795 + 7905049 * 2 ^ 59
def prefixEnd_7905049 : Nat := 4983230072969 + 3 ^ 40 * 7905049 * 2
def baseEnd_7905049 : Nat := 4059089734343747193132847

theorem tailTrace_7905049 : CollatzResearch.WordTrace tailWord_7905049 prefixEnd_7905049 4059089734343747193132847 := by
  unfold tailWord_7905049
  simp only [CollatzResearch.WordTrace]
  refine ⟨288320823538365022729358201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192213882358910015152905467 288320823538365022729358201)
  ·
    refine ⟨216240617653773767047018651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288320823538365022729358201 216240617653773767047018651)
    ·
      refine ⟨324360926480660650570527977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216240617653773767047018651 324360926480660650570527977)
      ·
        refine ⟨243270694860495487927895983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324360926480660650570527977 243270694860495487927895983)
        ·
          refine ⟨364906042290743231891843975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243270694860495487927895983 364906042290743231891843975)
          ·
            refine ⟨547359063436114847837765963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364906042290743231891843975 547359063436114847837765963)
            ·
              refine ⟨821038595154172271756648945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547359063436114847837765963 821038595154172271756648945)
              ·
                refine ⟨615778946365629203817486709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821038595154172271756648945 615778946365629203817486709)
                ·
                  refine ⟨57729276221777737857889379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 615778946365629203817486709 57729276221777737857889379)
                  ·
                    refine ⟨86593914332666606786834069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57729276221777737857889379 86593914332666606786834069)
                    ·
                      refine ⟨4059089734343747193132847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86593914332666606786834069 4059089734343747193132847)
                      ·
                        rfl

theorem cell23_7905049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_7905049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905049 prefixEnd_7905049 := by exact prefixLift 7905049
  have htrace : WordTrace (prefixWord ++ tailWord_7905049) baseStart_7905049 baseEnd_7905049 := by
    simpa [prefixWord, tailWord_7905049, baseEnd_7905049] using wordTrace_append hprefix tailTrace_7905049
  have hstable : (prefixWord ++ tailWord_7905049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905049).length < 2 ^ (prefixWord ++ tailWord_7905049).sum := by decide
  have hdescent : baseEnd_7905049 < baseStart_7905049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905059 : List Nat := [1, 1, 1, 4, 2, 1, 2, 11]
def baseStart_7905059 : Nat := 118140960795 + 7905059 * 2 ^ 59
def prefixEnd_7905059 : Nat := 4983230072969 + 3 ^ 40 * 7905059 * 2
def baseEnd_7905059 : Nat := 150336847005566376074363

theorem tailTrace_7905059 : CollatzResearch.WordTrace tailWord_7905059 prefixEnd_7905059 150336847005566376074363 := by
  unfold tailWord_7905059
  simp only [CollatzResearch.WordTrace]
  refine ⟨288321188268328794437222231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192214125512219196291481487 288321188268328794437222231)
  ·
    refine ⟨432481782402493191655833347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288321188268328794437222231 432481782402493191655833347)
    ·
      refine ⟨648722673603739787483750021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432481782402493191655833347 648722673603739787483750021)
      ·
        refine ⟨121635501300701210153203129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 648722673603739787483750021 121635501300701210153203129)
        ·
          refine ⟨91226625975525907614902347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121635501300701210153203129 91226625975525907614902347)
          ·
            refine ⟨136839938963288861422353521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91226625975525907614902347 136839938963288861422353521)
            ·
              refine ⟨102629954222466646066765141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136839938963288861422353521 102629954222466646066765141)
              ·
                refine ⟨150336847005566376074363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102629954222466646066765141 150336847005566376074363)
                ·
                  rfl

theorem cell23_7905059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 11].length) (baseStart_7905059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905059 prefixEnd_7905059 := by exact prefixLift 7905059
  have htrace : WordTrace (prefixWord ++ tailWord_7905059) baseStart_7905059 baseEnd_7905059 := by
    simpa [prefixWord, tailWord_7905059, baseEnd_7905059] using wordTrace_append hprefix tailTrace_7905059
  have hstable : (prefixWord ++ tailWord_7905059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905059).length < 2 ^ (prefixWord ++ tailWord_7905059).sum := by decide
  have hdescent : baseEnd_7905059 < baseStart_7905059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905080 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_7905080 : Nat := 118140960795 + 7905080 * 2 ^ 59
def prefixEnd_7905080 : Nat := 4983230072969 + 3 ^ 40 * 7905080 * 2
def baseEnd_7905080 : Nat := 1353035217414678857281735

theorem tailTrace_7905080 : CollatzResearch.WordTrace tailWord_7905080 prefixEnd_7905080 1353035217414678857281735 := by
  unfold tailWord_7905080
  simp only [CollatzResearch.WordTrace]
  refine ⟨144160977100626357511868347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192214636134168476682491129 144160977100626357511868347)
  ·
    refine ⟨216241465650939536267802521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144160977100626357511868347 216241465650939536267802521)
    ·
      refine ⟨162181099238204652200851891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216241465650939536267802521 162181099238204652200851891)
      ·
        refine ⟨243271648857306978301277837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162181099238204652200851891 243271648857306978301277837)
        ·
          refine ⟨91226868321490116862979189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243271648857306978301277837 91226868321490116862979189)
          ·
            refine ⟨8552518905139698455904299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91226868321490116862979189 8552518905139698455904299)
            ·
              refine ⟨12828778357709547683856449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552518905139698455904299 12828778357709547683856449)
              ·
                refine ⟨9621583768282160762892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12828778357709547683856449 9621583768282160762892337)
                ·
                  refine ⟨7216187826211620572169253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9621583768282160762892337 7216187826211620572169253)
                  ·
                    refine ⟨1353035217414678857281735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216187826211620572169253 1353035217414678857281735)
                    ·
                      rfl

theorem cell23_7905080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_7905080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905080 prefixEnd_7905080 := by exact prefixLift 7905080
  have htrace : WordTrace (prefixWord ++ tailWord_7905080) baseStart_7905080 baseEnd_7905080 := by
    simpa [prefixWord, tailWord_7905080, baseEnd_7905080] using wordTrace_append hprefix tailTrace_7905080
  have hstable : (prefixWord ++ tailWord_7905080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905080).length < 2 ^ (prefixWord ++ tailWord_7905080).sum := by decide
  have hdescent : baseEnd_7905080 < baseStart_7905080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905087 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 3, 2, 2]
def baseStart_7905087 : Nat := 118140960795 + 7905087 * 2 ^ 59
def prefixEnd_7905087 : Nat := 4983230072969 + 3 ^ 40 * 7905087 * 2
def baseEnd_7905087 : Nat := 4059109246608618044457673

theorem tailTrace_7905087 : CollatzResearch.WordTrace tailWord_7905087 prefixEnd_7905087 4059109246608618044457673 := by
  unfold tailWord_7905087
  simp only [CollatzResearch.WordTrace]
  refine ⟨288322209512227355219241515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192214806341484903479494343 288322209512227355219241515)
  ·
    refine ⟨432483314268341032828862273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288322209512227355219241515 432483314268341032828862273)
    ·
      refine ⟨324362485701255774621646705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432483314268341032828862273 324362485701255774621646705)
      ·
        refine ⟨243271864275941830966235029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324362485701255774621646705 243271864275941830966235029)
        ·
          refine ⟨11403368637934773326542267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 243271864275941830966235029 11403368637934773326542267)
          ·
            refine ⟨17105052956902159989813401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11403368637934773326542267 17105052956902159989813401)
            ·
              refine ⟨12828789717676619992360051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17105052956902159989813401 12828789717676619992360051)
              ·
                refine ⟨19243184576514929988540077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12828789717676619992360051 19243184576514929988540077)
                ·
                  refine ⟨7216194216193098745702529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19243184576514929988540077 7216194216193098745702529)
                  ·
                    refine ⟨5412145662144824059276897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216194216193098745702529 5412145662144824059276897)
                    ·
                      refine ⟨4059109246608618044457673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412145662144824059276897 4059109246608618044457673)
                      ·
                        rfl

theorem cell23_7905087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_7905087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905087 prefixEnd_7905087 := by exact prefixLift 7905087
  have htrace : WordTrace (prefixWord ++ tailWord_7905087) baseStart_7905087 baseEnd_7905087 := by
    simpa [prefixWord, tailWord_7905087, baseEnd_7905087] using wordTrace_append hprefix tailTrace_7905087
  have hstable : (prefixWord ++ tailWord_7905087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905087).length < 2 ^ (prefixWord ++ tailWord_7905087).sum := by decide
  have hdescent : baseEnd_7905087 < baseStart_7905087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905100 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_7905100 : Nat := 118140960795 + 7905100 * 2 ^ 59
def prefixEnd_7905100 : Nat := 4983230072969 + 3 ^ 40 * 7905100 * 2
def baseEnd_7905100 : Nat := 4059115921857126493595113

theorem tailTrace_7905100 : CollatzResearch.WordTrace tailWord_7905100 prefixEnd_7905100 4059115921857126493595113 := by
  unfold tailWord_7905100
  simp only [CollatzResearch.WordTrace]
  refine ⟨144161341830590129219732377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192215122440786838959643169 144161341830590129219732377)
  ·
    refine ⟨108121006372942596914799283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144161341830590129219732377 108121006372942596914799283)
    ·
      refine ⟨162181509559413895372198925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108121006372942596914799283 162181509559413895372198925)
      ·
        refine ⟨60818066084780210764574597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162181509559413895372198925 60818066084780210764574597)
        ·
          refine ⟨11403387390896289518357737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60818066084780210764574597 11403387390896289518357737)
          ·
            refine ⟨8552540543172217138768303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11403387390896289518357737 8552540543172217138768303)
            ·
              refine ⟨12828810814758325708152455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552540543172217138768303 12828810814758325708152455)
              ·
                refine ⟨19243216222137488562228683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12828810814758325708152455 19243216222137488562228683)
                ·
                  refine ⟨28864824333206232843343025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19243216222137488562228683 28864824333206232843343025)
                  ·
                    refine ⟨21648618249904674632507269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28864824333206232843343025 21648618249904674632507269)
                    ·
                      refine ⟨4059115921857126493595113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21648618249904674632507269 4059115921857126493595113)
                      ·
                        rfl

theorem cell23_7905100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_7905100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905100 prefixEnd_7905100 := by exact prefixLift 7905100
  have htrace : WordTrace (prefixWord ++ tailWord_7905100) baseStart_7905100 baseEnd_7905100 := by
    simpa [prefixWord, tailWord_7905100, baseEnd_7905100] using wordTrace_append hprefix tailTrace_7905100
  have hstable : (prefixWord ++ tailWord_7905100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905100).length < 2 ^ (prefixWord ++ tailWord_7905100).sum := by decide
  have hdescent : baseEnd_7905100 < baseStart_7905100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905203 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 7, 2]
def baseStart_7905203 : Nat := 118140960795 + 7905203 * 2 ^ 59
def prefixEnd_7905203 : Nat := 4983230072969 + 3 ^ 40 * 7905203 * 2
def baseEnd_7905203 : Nat := 4059168810364539590607139

theorem tailTrace_7905203 : CollatzResearch.WordTrace tailWord_7905203 prefixEnd_7905203 4059168810364539590607139 := by
  unfold tailWord_7905203
  simp only [CollatzResearch.WordTrace]
  refine ⟨288326440379807107030464263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192217626919871404686976175 288326440379807107030464263)
  ·
    refine ⟨432489660569710660545696395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288326440379807107030464263 432489660569710660545696395)
    ·
      refine ⟨648734490854565990818544593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432489660569710660545696395 648734490854565990818544593)
      ·
        refine ⟨486550868140924493113908445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648734490854565990818544593 486550868140924493113908445)
        ·
          refine ⟨182456575552846684917715667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486550868140924493113908445 182456575552846684917715667)
          ·
            refine ⟨273684863329270027376573501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182456575552846684917715667 273684863329270027376573501)
            ·
              refine ⟨102631823748476260266215063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273684863329270027376573501 102631823748476260266215063)
              ·
                refine ⟨153947735622714390399322595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102631823748476260266215063 153947735622714390399322595)
                ·
                  refine ⟨230921603434071585598983893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153947735622714390399322595 230921603434071585598983893)
                  ·
                    refine ⟨5412225080486052787476185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230921603434071585598983893 5412225080486052787476185)
                    ·
                      refine ⟨4059168810364539590607139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412225080486052787476185 4059168810364539590607139)
                      ·
                        rfl

theorem cell23_7905203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7, 2].length) (baseStart_7905203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905203 prefixEnd_7905203 := by exact prefixLift 7905203
  have htrace : WordTrace (prefixWord ++ tailWord_7905203) baseStart_7905203 baseEnd_7905203 := by
    simpa [prefixWord, tailWord_7905203, baseEnd_7905203] using wordTrace_append hprefix tailTrace_7905203
  have hstable : (prefixWord ++ tailWord_7905203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905203).length < 2 ^ (prefixWord ++ tailWord_7905203).sum := by decide
  have hdescent : baseEnd_7905203 < baseStart_7905203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905233 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_7905233 : Nat := 118140960795 + 7905233 * 2 ^ 59
def prefixEnd_7905233 : Nat := 4983230072969 + 3 ^ 40 * 7905233 * 2
def baseEnd_7905233 : Nat := 4059184214784174473232001

theorem tailTrace_7905233 : CollatzResearch.WordTrace tailWord_7905233 prefixEnd_7905233 4059184214784174473232001 := by
  unfold tailWord_7905233
  simp only [CollatzResearch.WordTrace]
  refine ⟨288327534569698422154056353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192218356379798948102704235 288327534569698422154056353)
  ·
    refine ⟨216245650927273816615542265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288327534569698422154056353 216245650927273816615542265)
    ·
      refine ⟨162184238195455362461656699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216245650927273816615542265 162184238195455362461656699)
      ·
        refine ⟨243276357293183043692485049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162184238195455362461656699 243276357293183043692485049)
        ·
          refine ⟨182457267969887282769363787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243276357293183043692485049 182457267969887282769363787)
          ·
            refine ⟨273685901954830924154045681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182457267969887282769363787 273685901954830924154045681)
            ·
              refine ⟨205264426466123193115534261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273685901954830924154045681 205264426466123193115534261)
              ·
                refine ⟨19243539981199049354581337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205264426466123193115534261 19243539981199049354581337)
                ·
                  refine ⟨14432654985899287015936003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19243539981199049354581337 14432654985899287015936003)
                  ·
                    refine ⟨21648982478848930523904005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14432654985899287015936003 21648982478848930523904005)
                    ·
                      refine ⟨4059184214784174473232001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21648982478848930523904005 4059184214784174473232001)
                      ·
                        rfl

theorem cell23_7905233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_7905233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905233 prefixEnd_7905233 := by exact prefixLift 7905233
  have htrace : WordTrace (prefixWord ++ tailWord_7905233) baseStart_7905233 baseEnd_7905233 := by
    simpa [prefixWord, tailWord_7905233, baseEnd_7905233] using wordTrace_append hprefix tailTrace_7905233
  have hstable : (prefixWord ++ tailWord_7905233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905233).length < 2 ^ (prefixWord ++ tailWord_7905233).sum := by decide
  have hdescent : baseEnd_7905233 < baseStart_7905233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905317 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_7905317 : Nat := 118140960795 + 7905317 * 2 ^ 59
def prefixEnd_7905317 : Nat := 4983230072969 + 3 ^ 40 * 7905317 * 2
def baseEnd_7905317 : Nat := 4059227347159152144581615

theorem tailTrace_7905317 : CollatzResearch.WordTrace tailWord_7905317 prefixEnd_7905317 4059227347159152144581615 := by
  unfold tailWord_7905317
  simp only [CollatzResearch.WordTrace]
  refine ⟨288330598301394104500114205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192220398867596069666742803 288330598301394104500114205)
  ·
    refine ⟨108123974363022789187542827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288330598301394104500114205 108123974363022789187542827)
    ·
      refine ⟨162185961544534183781314241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108123974363022789187542827 162185961544534183781314241)
      ·
        refine ⟨121639471158400637835985681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162185961544534183781314241 121639471158400637835985681)
        ·
          refine ⟨91229603368800478376989261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121639471158400637835985681 91229603368800478376989261)
          ·
            refine ⟨34211101263300179391370973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91229603368800478376989261 34211101263300179391370973)
            ·
              refine ⟨12829162973737567271764115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34211101263300179391370973 12829162973737567271764115)
              ·
                refine ⟨19243744460606350907646173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12829162973737567271764115 19243744460606350907646173)
                ·
                  refine ⟨7216404172727381590367315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19243744460606350907646173 7216404172727381590367315)
                  ·
                    refine ⟨10824606259091072385550973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216404172727381590367315 10824606259091072385550973)
                    ·
                      refine ⟨4059227347159152144581615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824606259091072385550973 4059227347159152144581615)
                      ·
                        rfl

theorem cell23_7905317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_7905317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905317 prefixEnd_7905317 := by exact prefixLift 7905317
  have htrace : WordTrace (prefixWord ++ tailWord_7905317) baseStart_7905317 baseEnd_7905317 := by
    simpa [prefixWord, tailWord_7905317, baseEnd_7905317] using wordTrace_append hprefix tailTrace_7905317
  have hstable : (prefixWord ++ tailWord_7905317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905317).length < 2 ^ (prefixWord ++ tailWord_7905317).sum := by decide
  have hdescent : baseEnd_7905317 < baseStart_7905317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905340 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_7905340 : Nat := 118140960795 + 7905340 * 2 ^ 59
def prefixEnd_7905340 : Nat := 4983230072969 + 3 ^ 40 * 7905340 * 2
def baseEnd_7905340 : Nat := 4059239157214205554594009

theorem tailTrace_7905340 : CollatzResearch.WordTrace tailWord_7905340 prefixEnd_7905340 4059239157214205554594009 := by
  unfold tailWord_7905340
  simp only [CollatzResearch.WordTrace]
  refine ⟨144165718590155389714100737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192220958120207186285467649 144165718590155389714100737)
  ·
    refine ⟨108124288942616542285575553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144165718590155389714100737 108124288942616542285575553)
    ·
      refine ⟨81093216706962406714181665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108124288942616542285575553 81093216706962406714181665)
      ·
        refine ⟨60819912530221805035636249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81093216706962406714181665 60819912530221805035636249)
        ·
          refine ⟨45614934397666353776727187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60819912530221805035636249 45614934397666353776727187)
          ·
            refine ⟨68422401596499530665090781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45614934397666353776727187 68422401596499530665090781)
            ·
              refine ⟨25658400598687323999409043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68422401596499530665090781 25658400598687323999409043)
              ·
                refine ⟨38487600898030985999113565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25658400598687323999409043 38487600898030985999113565)
                ·
                  refine ⟨14432850336761619749667587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38487600898030985999113565 14432850336761619749667587)
                  ·
                    refine ⟨21649275505142429624501381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14432850336761619749667587 21649275505142429624501381)
                    ·
                      refine ⟨4059239157214205554594009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21649275505142429624501381 4059239157214205554594009)
                      ·
                        rfl

theorem cell23_7905340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_7905340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905340 prefixEnd_7905340 := by exact prefixLift 7905340
  have htrace : WordTrace (prefixWord ++ tailWord_7905340) baseStart_7905340 baseEnd_7905340 := by
    simpa [prefixWord, tailWord_7905340, baseEnd_7905340] using wordTrace_append hprefix tailTrace_7905340
  have hstable : (prefixWord ++ tailWord_7905340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905340).length < 2 ^ (prefixWord ++ tailWord_7905340).sum := by decide
  have hdescent : baseEnd_7905340 < baseStart_7905340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905343 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_7905343 : Nat := 118140960795 + 7905343 * 2 ^ 59
def prefixEnd_7905343 : Nat := 4983230072969 + 3 ^ 40 * 7905343 * 2
def baseEnd_7905343 : Nat := 4059240697656169042856495

theorem tailTrace_7905343 : CollatzResearch.WordTrace tailWord_7905343 prefixEnd_7905343 4059240697656169042856495 := by
  unfold tailWord_7905343
  simp only [CollatzResearch.WordTrace]
  refine ⟨288331546599299910940560683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192221031066199940627040455 288331546599299910940560683)
  ·
    refine ⟨432497319898949866410841025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288331546599299910940560683 432497319898949866410841025)
    ·
      refine ⟨324372989924212399808130769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432497319898949866410841025 324372989924212399808130769)
      ·
        refine ⟨243279742443159299856098077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324372989924212399808130769 243279742443159299856098077)
        ·
          refine ⟨91229903416184737446036779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243279742443159299856098077 91229903416184737446036779)
          ·
            refine ⟨136844855124277106169055169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91229903416184737446036779 136844855124277106169055169)
            ·
              refine ⟨102633641343207829626791377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136844855124277106169055169 102633641343207829626791377)
              ·
                refine ⟨76975231007405872220093533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102633641343207829626791377 76975231007405872220093533)
                ·
                  refine ⟨28865711627777202082535075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76975231007405872220093533 28865711627777202082535075)
                  ·
                    refine ⟨43298567441665803123802613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28865711627777202082535075 43298567441665803123802613)
                    ·
                      refine ⟨4059240697656169042856495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43298567441665803123802613 4059240697656169042856495)
                      ·
                        rfl

theorem cell23_7905343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_7905343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905343 prefixEnd_7905343 := by exact prefixLift 7905343
  have htrace : WordTrace (prefixWord ++ tailWord_7905343) baseStart_7905343 baseEnd_7905343 := by
    simpa [prefixWord, tailWord_7905343, baseEnd_7905343] using wordTrace_append hprefix tailTrace_7905343
  have hstable : (prefixWord ++ tailWord_7905343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905343).length < 2 ^ (prefixWord ++ tailWord_7905343).sum := by decide
  have hdescent : baseEnd_7905343 < baseStart_7905343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905393 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_7905393 : Nat := 118140960795 + 7905393 * 2 ^ 59
def prefixEnd_7905393 : Nat := 4983230072969 + 3 ^ 40 * 7905393 * 2
def baseEnd_7905393 : Nat := 1353088790562964615743755

theorem tailTrace_7905393 : CollatzResearch.WordTrace tailWord_7905393 prefixEnd_7905393 1353088790562964615743755 := by
  unfold tailWord_7905393
  simp only [CollatzResearch.WordTrace]
  refine ⟨288333370249118769479880833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192222246832745846319920555 288333370249118769479880833)
  ·
    refine ⟨216250027686839077109910625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288333370249118769479880833 216250027686839077109910625)
    ·
      refine ⟨162187520765129307832432969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216250027686839077109910625 162187520765129307832432969)
      ·
        refine ⟨121640640573846980874324727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162187520765129307832432969 121640640573846980874324727)
        ·
          refine ⟨182460960860770471311487091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121640640573846980874324727 182460960860770471311487091)
          ·
            refine ⟨273691441291155706967230637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182460960860770471311487091 273691441291155706967230637)
            ·
              refine ⟨102634290484183390112711489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273691441291155706967230637 102634290484183390112711489)
              ·
                refine ⟨76975717863137542584533617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102634290484183390112711489 76975717863137542584533617)
                ·
                  refine ⟨57731788397353156938400213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76975717863137542584533617 57731788397353156938400213)
                  ·
                    refine ⟨1353088790562964615743755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57731788397353156938400213 1353088790562964615743755)
                    ·
                      rfl

theorem cell23_7905393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_7905393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905393 prefixEnd_7905393 := by exact prefixLift 7905393
  have htrace : WordTrace (prefixWord ++ tailWord_7905393) baseStart_7905393 baseEnd_7905393 := by
    simpa [prefixWord, tailWord_7905393, baseEnd_7905393] using wordTrace_append hprefix tailTrace_7905393
  have hstable : (prefixWord ++ tailWord_7905393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905393).length < 2 ^ (prefixWord ++ tailWord_7905393).sum := by decide
  have hdescent : baseEnd_7905393 < baseStart_7905393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905440 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_7905440 : Nat := 118140960795 + 7905440 * 2 ^ 59
def prefixEnd_7905440 : Nat := 4983230072969 + 3 ^ 40 * 7905440 * 2
def baseEnd_7905440 : Nat := 1353096835093218387781183

theorem tailTrace_7905440 : CollatzResearch.WordTrace tailWord_7905440 prefixEnd_7905440 1353096835093218387781183 := by
  unfold tailWord_7905440
  simp only [CollatzResearch.WordTrace]
  refine ⟨144167542239974248253420887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192223389653298997671227849 144167542239974248253420887)
  ·
    refine ⟨216251313359961372380131331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144167542239974248253420887 216251313359961372380131331)
    ·
      refine ⟨324376970039942058570196997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216251313359961372380131331 324376970039942058570196997)
      ·
        refine ⟨60820681882489135981911937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324376970039942058570196997 60820681882489135981911937)
        ·
          refine ⟨45615511411866851986433953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60820681882489135981911937 45615511411866851986433953)
          ·
            refine ⟨34211633558900138989825465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45615511411866851986433953 34211633558900138989825465)
            ·
              refine ⟨25658725169175104242369099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34211633558900138989825465 25658725169175104242369099)
              ·
                refine ⟨38488087753762656363553649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25658725169175104242369099 38488087753762656363553649)
                ·
                  refine ⟨28866065815321992272665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38488087753762656363553649 28866065815321992272665237)
                  ·
                    refine ⟨1353096835093218387781183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28866065815321992272665237 1353096835093218387781183)
                    ·
                      rfl

theorem cell23_7905440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_7905440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905440 prefixEnd_7905440 := by exact prefixLift 7905440
  have htrace : WordTrace (prefixWord ++ tailWord_7905440) baseStart_7905440 baseEnd_7905440 := by
    simpa [prefixWord, tailWord_7905440, baseEnd_7905440] using wordTrace_append hprefix tailTrace_7905440
  have hstable : (prefixWord ++ tailWord_7905440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905440).length < 2 ^ (prefixWord ++ tailWord_7905440).sum := by decide
  have hdescent : baseEnd_7905440 < baseStart_7905440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905441 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7905441 : Nat := 118140960795 + 7905441 * 2 ^ 59
def prefixEnd_7905441 : Nat := 4983230072969 + 3 ^ 40 * 7905441 * 2
def baseEnd_7905441 : Nat := 4059291018760309659431045

theorem tailTrace_7905441 : CollatzResearch.WordTrace tailWord_7905441 prefixEnd_7905441 4059291018760309659431045 := by
  unfold tailWord_7905441
  simp only [CollatzResearch.WordTrace]
  refine ⟨288335120952944873677628177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192223413968629915785085451 288335120952944873677628177)
  ·
    refine ⟨216251340714708655258221133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288335120952944873677628177 216251340714708655258221133)
    ·
      refine ⟨81094252768015745721832925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216251340714708655258221133 81094252768015745721832925)
      ·
        refine ⟨30410344788005904645687347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81094252768015745721832925 30410344788005904645687347)
        ·
          refine ⟨45615517182008856968531021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30410344788005904645687347 45615517182008856968531021)
          ·
            refine ⟨17105818943253321363199133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45615517182008856968531021 17105818943253321363199133)
            ·
              refine ⟨6414682103719995511199675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17105818943253321363199133 6414682103719995511199675)
              ·
                refine ⟨9622023155579993266799513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414682103719995511199675 9622023155579993266799513)
                ·
                  refine ⟨7216517366684994950099635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9622023155579993266799513 7216517366684994950099635)
                  ·
                    refine ⟨10824776050027492425149453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216517366684994950099635 10824776050027492425149453)
                    ·
                      refine ⟨4059291018760309659431045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824776050027492425149453 4059291018760309659431045)
                      ·
                        rfl

theorem cell23_7905441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7905441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905441 prefixEnd_7905441 := by exact prefixLift 7905441
  have htrace : WordTrace (prefixWord ++ tailWord_7905441) baseStart_7905441 baseEnd_7905441 := by
    simpa [prefixWord, tailWord_7905441, baseEnd_7905441] using wordTrace_append hprefix tailTrace_7905441
  have hstable : (prefixWord ++ tailWord_7905441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905441).length < 2 ^ (prefixWord ++ tailWord_7905441).sum := by decide
  have hdescent : baseEnd_7905441 < baseStart_7905441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905520 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_7905520 : Nat := 118140960795 + 7905520 * 2 ^ 59
def prefixEnd_7905520 : Nat := 4983230072969 + 3 ^ 40 * 7905520 * 2
def baseEnd_7905520 : Nat := 4059331583732014850343181

theorem tailTrace_7905520 : CollatzResearch.WordTrace tailWord_7905520 prefixEnd_7905520 4059331583732014850343181 := by
  unfold tailWord_7905520
  simp only [CollatzResearch.WordTrace]
  refine ⟨144169001159829335084877007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192225334879772446779836009 144169001159829335084877007)
  ·
    refine ⟨216253501739744002627315511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144169001159829335084877007 216253501739744002627315511)
    ·
      refine ⟨324380252609616003940973267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216253501739744002627315511 324380252609616003940973267)
      ·
        refine ⟨486570378914424005911459901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324380252609616003940973267 486570378914424005911459901)
        ·
          refine ⟨182463892092909002216797463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486570378914424005911459901 182463892092909002216797463)
          ·
            refine ⟨273695838139363503325196195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182463892092909002216797463 273695838139363503325196195)
            ·
              refine ⟨410543757209045254987794293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273695838139363503325196195 410543757209045254987794293)
              ·
                refine ⟨38488477238347992655105715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 410543757209045254987794293 38488477238347992655105715)
                ·
                  refine ⟨57732715857521988982658573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38488477238347992655105715 57732715857521988982658573)
                  ·
                    refine ⟨21649768446570745868496965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57732715857521988982658573 21649768446570745868496965)
                    ·
                      refine ⟨4059331583732014850343181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21649768446570745868496965 4059331583732014850343181)
                      ·
                        rfl

theorem cell23_7905520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_7905520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905520 prefixEnd_7905520 := by exact prefixLift 7905520
  have htrace : WordTrace (prefixWord ++ tailWord_7905520) baseStart_7905520 baseEnd_7905520 := by
    simpa [prefixWord, tailWord_7905520, baseEnd_7905520] using wordTrace_append hprefix tailTrace_7905520
  have hstable : (prefixWord ++ tailWord_7905520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905520).length < 2 ^ (prefixWord ++ tailWord_7905520).sum := by decide
  have hdescent : baseEnd_7905520 < baseStart_7905520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905537 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7905537 : Nat := 118140960795 + 7905537 * 2 ^ 59
def prefixEnd_7905537 : Nat := 4983230072969 + 3 ^ 40 * 7905537 * 2
def baseEnd_7905537 : Nat := 4059340312903141283830603

theorem tailTrace_7905537 : CollatzResearch.WordTrace tailWord_7905537 prefixEnd_7905537 4059340312903141283830603 := by
  unfold tailWord_7905537
  simp only [CollatzResearch.WordTrace]
  refine ⟨288338622360597082073122865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192225748240398054715415243 288338622360597082073122865)
  ·
    refine ⟨216253966770447811554842149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288338622360597082073122865 216253966770447811554842149)
    ·
      refine ⟨40547618769458964666532903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216253966770447811554842149 40547618769458964666532903)
      ·
        refine ⟨60821428154188446999799355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40547618769458964666532903 60821428154188446999799355)
        ·
          refine ⟨91232142231282670499699033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60821428154188446999799355 91232142231282670499699033)
          ·
            refine ⟨68424106673462002874774275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91232142231282670499699033 68424106673462002874774275)
            ·
              refine ⟨102636160010193004312161413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68424106673462002874774275 102636160010193004312161413)
              ·
                refine ⟨19244280001911188308530265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102636160010193004312161413 19244280001911188308530265)
                ·
                  refine ⟨14433210001433391231397699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19244280001911188308530265 14433210001433391231397699)
                  ·
                    refine ⟨21649815002150086847096549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14433210001433391231397699 21649815002150086847096549)
                    ·
                      refine ⟨4059340312903141283830603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21649815002150086847096549 4059340312903141283830603)
                      ·
                        rfl

theorem cell23_7905537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7905537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905537 prefixEnd_7905537 := by exact prefixLift 7905537
  have htrace : WordTrace (prefixWord ++ tailWord_7905537) baseStart_7905537 baseEnd_7905537 := by
    simpa [prefixWord, tailWord_7905537, baseEnd_7905537] using wordTrace_append hprefix tailTrace_7905537
  have hstable : (prefixWord ++ tailWord_7905537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905537).length < 2 ^ (prefixWord ++ tailWord_7905537).sum := by decide
  have hdescent : baseEnd_7905537 < baseStart_7905537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905538 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7905538 : Nat := 118140960795 + 7905538 * 2 ^ 59
def prefixEnd_7905538 : Nat := 4983230072969 + 3 ^ 40 * 7905538 * 2
def baseEnd_7905538 : Nat := 451037869598199531102011

theorem tailTrace_7905538 : CollatzResearch.WordTrace tailWord_7905538 prefixEnd_7905538 451037869598199531102011 := by
  unfold tailWord_7905538
  simp only [CollatzResearch.WordTrace]
  refine ⟨72084664708398364810977317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192225772555728972829272845 72084664708398364810977317)
  ·
    refine ⟨13515874632824693402058247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72084664708398364810977317 13515874632824693402058247)
    ·
      refine ⟨20273811949237040103087371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13515874632824693402058247 20273811949237040103087371)
      ·
        refine ⟨30410717923855560154631057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20273811949237040103087371 30410717923855560154631057)
        ·
          refine ⟨22808038442891670115973293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30410717923855560154631057 22808038442891670115973293)
          ·
            refine ⟨8553014416084376293489985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22808038442891670115973293 8553014416084376293489985)
            ·
              refine ⟨6414760812063282220117489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553014416084376293489985 6414760812063282220117489)
              ·
                refine ⟨4811070609047461665088117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414760812063282220117489 4811070609047461665088117)
                ·
                  refine ⟨451037869598199531102011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811070609047461665088117 451037869598199531102011)
                  ·
                    rfl

theorem cell23_7905538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7905538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905538 prefixEnd_7905538 := by exact prefixLift 7905538
  have htrace : WordTrace (prefixWord ++ tailWord_7905538) baseStart_7905538 baseEnd_7905538 := by
    simpa [prefixWord, tailWord_7905538, baseEnd_7905538] using wordTrace_append hprefix tailTrace_7905538
  have hstable : (prefixWord ++ tailWord_7905538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905538).length < 2 ^ (prefixWord ++ tailWord_7905538).sum := by decide
  have hdescent : baseEnd_7905538 < baseStart_7905538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905547 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 3, 4]
def baseStart_7905547 : Nat := 118140960795 + 7905547 * 2 ^ 59
def prefixEnd_7905547 : Nat := 4983230072969 + 3 ^ 40 * 7905547 * 2
def baseEnd_7905547 : Nat := 1353115149236562081568519

theorem tailTrace_7905547 : CollatzResearch.WordTrace tailWord_7905547 prefixEnd_7905547 1353115149236562081568519 := by
  unfold tailWord_7905547
  simp only [CollatzResearch.WordTrace]
  refine ⟨288338987090560853780986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192225991393707235853991263 288338987090560853780986895)
  ·
    refine ⟨432508480635841280671480343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288338987090560853780986895 432508480635841280671480343)
    ·
      refine ⟨648762720953761921007220515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432508480635841280671480343 648762720953761921007220515)
      ·
        refine ⟨973144081430642881510830773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648762720953761921007220515 973144081430642881510830773)
        ·
          refine ⟨91232257634122770141640385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 973144081430642881510830773 91232257634122770141640385)
          ·
            refine ⟨68424193225592077606230289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91232257634122770141640385 68424193225592077606230289)
            ·
              refine ⟨51318144919194058204672717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68424193225592077606230289 51318144919194058204672717)
              ·
                refine ⟨19244304344697771826752269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51318144919194058204672717 19244304344697771826752269)
                ·
                  refine ⟨7216614129261664435032101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19244304344697771826752269 7216614129261664435032101)
                  ·
                    refine ⟨1353115149236562081568519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216614129261664435032101 1353115149236562081568519)
                    ·
                      rfl

theorem cell23_7905547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 4].length) (baseStart_7905547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905547 prefixEnd_7905547 := by exact prefixLift 7905547
  have htrace : WordTrace (prefixWord ++ tailWord_7905547) baseStart_7905547 baseEnd_7905547 := by
    simpa [prefixWord, tailWord_7905547, baseEnd_7905547] using wordTrace_append hprefix tailTrace_7905547
  have hstable : (prefixWord ++ tailWord_7905547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905547).length < 2 ^ (prefixWord ++ tailWord_7905547).sum := by decide
  have hdescent : baseEnd_7905547 < baseStart_7905547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905557 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_7905557 : Nat := 118140960795 + 7905557 * 2 ^ 59
def prefixEnd_7905557 : Nat := 4983230072969 + 3 ^ 40 * 7905557 * 2
def baseEnd_7905557 : Nat := 4059350582516231205580511

theorem tailTrace_7905557 : CollatzResearch.WordTrace tailWord_7905557 prefixEnd_7905557 4059350582516231205580511 := by
  unfold tailWord_7905557
  simp only [CollatzResearch.WordTrace]
  refine ⟨288339351820524625488850925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192226234547016416992567283 288339351820524625488850925)
  ·
    refine ⟨108127256932696734558319097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288339351820524625488850925 108127256932696734558319097)
    ·
      refine ⟨81095442699522550918739323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108127256932696734558319097 81095442699522550918739323)
      ·
        refine ⟨121643164049283826378108985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81095442699522550918739323 121643164049283826378108985)
        ·
          refine ⟨91232373036962869783581739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121643164049283826378108985 91232373036962869783581739)
          ·
            refine ⟨136848559555444304675372609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91232373036962869783581739 136848559555444304675372609)
            ·
              refine ⟨102636419666583228506529457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136848559555444304675372609 102636419666583228506529457)
              ·
                refine ⟨76977314749937421379897093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102636419666583228506529457 76977314749937421379897093)
                ·
                  refine ⟨14433246515613266508730705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76977314749937421379897093 14433246515613266508730705)
                  ·
                    refine ⟨10824934886709949881548029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14433246515613266508730705 10824934886709949881548029)
                    ·
                      refine ⟨4059350582516231205580511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10824934886709949881548029 4059350582516231205580511)
                      ·
                        rfl

theorem cell23_7905557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_7905557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905557 prefixEnd_7905557 := by exact prefixLift 7905557
  have htrace : WordTrace (prefixWord ++ tailWord_7905557) baseStart_7905557 baseEnd_7905557 := by
    simpa [prefixWord, tailWord_7905557, baseEnd_7905557] using wordTrace_append hprefix tailTrace_7905557
  have hstable : (prefixWord ++ tailWord_7905557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905557).length < 2 ^ (prefixWord ++ tailWord_7905557).sum := by decide
  have hdescent : baseEnd_7905557 < baseStart_7905557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905594 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_7905594 : Nat := 118140960795 + 7905594 * 2 ^ 59
def prefixEnd_7905594 : Nat := 4983230072969 + 3 ^ 40 * 7905594 * 2
def baseEnd_7905594 : Nat := 451041064588938617868649

theorem tailTrace_7905594 : CollatzResearch.WordTrace tailWord_7905594 prefixEnd_7905594 451041064588938617868649 := by
  unfold tailWord_7905594
  simp only [CollatzResearch.WordTrace]
  refine ⟨72085175330347645201986959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192227134214260387205298557 72085175330347645201986959)
  ·
    refine ⟨108127762995521467802980439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72085175330347645201986959 108127762995521467802980439)
    ·
      refine ⟨162191644493282201704470659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108127762995521467802980439 162191644493282201704470659)
      ·
        refine ⟨243287466739923302556705989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162191644493282201704470659 243287466739923302556705989)
        ·
          refine ⟨45616400013735619229382373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243287466739923302556705989 45616400013735619229382373)
          ·
            refine ⟨8553075002575428605509195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45616400013735619229382373 8553075002575428605509195)
            ·
              refine ⟨12829612503863142908263793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553075002575428605509195 12829612503863142908263793)
              ·
                refine ⟨9622209377897357181197845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12829612503863142908263793 9622209377897357181197845)
                ·
                  refine ⟨451041064588938617868649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9622209377897357181197845 451041064588938617868649)
                  ·
                    rfl

theorem cell23_7905594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_7905594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905594 prefixEnd_7905594 := by exact prefixLift 7905594
  have htrace : WordTrace (prefixWord ++ tailWord_7905594) baseStart_7905594 baseEnd_7905594 := by
    simpa [prefixWord, tailWord_7905594, baseEnd_7905594] using wordTrace_append hprefix tailTrace_7905594
  have hstable : (prefixWord ++ tailWord_7905594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905594).length < 2 ^ (prefixWord ++ tailWord_7905594).sum := by decide
  have hdescent : baseEnd_7905594 < baseStart_7905594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905600 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_7905600 : Nat := 118140960795 + 7905600 * 2 ^ 59
def prefixEnd_7905600 : Nat := 4983230072969 + 3 ^ 40 * 7905600 * 2
def baseEnd_7905600 : Nat := 4059372662184374537342813

theorem tailTrace_7905600 : CollatzResearch.WordTrace tailWord_7905600 prefixEnd_7905600 4059372662184374537342813 := by
  unfold tailWord_7905600
  simp only [CollatzResearch.WordTrace]
  refine ⟨144170460079684421916333127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192227280106245895888444169 144170460079684421916333127)
  ·
    refine ⟨216255690119526632874499691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144170460079684421916333127 216255690119526632874499691)
    ·
      refine ⟨324383535179289949311749537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216255690119526632874499691 324383535179289949311749537)
      ·
        refine ⟨243287651384467461983812153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324383535179289949311749537 243287651384467461983812153)
        ·
          refine ⟨182465738538350596487859115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243287651384467461983812153 182465738538350596487859115)
          ·
            refine ⟨273698607807525894731788673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182465738538350596487859115 273698607807525894731788673)
            ·
              refine ⟨205273955855644421048841505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273698607807525894731788673 205273955855644421048841505)
              ·
                refine ⟨153955466891733315786631129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205273955855644421048841505 153955466891733315786631129)
                ·
                  refine ⟨115466600168799986839973347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153955466891733315786631129 115466600168799986839973347)
                  ·
                    refine ⟨173199900253199980259960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115466600168799986839973347 173199900253199980259960021)
                    ·
                      refine ⟨4059372662184374537342813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 173199900253199980259960021 4059372662184374537342813)
                      ·
                        rfl

theorem cell23_7905600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_7905600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905600 prefixEnd_7905600 := by exact prefixLift 7905600
  have htrace : WordTrace (prefixWord ++ tailWord_7905600) baseStart_7905600 baseEnd_7905600 := by
    simpa [prefixWord, tailWord_7905600, baseEnd_7905600] using wordTrace_append hprefix tailTrace_7905600
  have hstable : (prefixWord ++ tailWord_7905600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905600).length < 2 ^ (prefixWord ++ tailWord_7905600).sum := by decide
  have hdescent : baseEnd_7905600 < baseStart_7905600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905614 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_7905614 : Nat := 118140960795 + 7905614 * 2 ^ 59
def prefixEnd_7905614 : Nat := 4983230072969 + 3 ^ 40 * 7905614 * 2
def baseEnd_7905614 : Nat := 4059379850913537482567749

theorem tailTrace_7905614 : CollatzResearch.WordTrace tailWord_7905614 prefixEnd_7905614 4059379850913537482567749 := by
  unfold tailWord_7905614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36042678847664765527959487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192227620520878749482450597 36042678847664765527959487)
  ·
    refine ⟨54064018271497148291939231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36042678847664765527959487 54064018271497148291939231)
    ·
      refine ⟨81096027407245722437908847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54064018271497148291939231 81096027407245722437908847)
      ·
        refine ⟨121644041110868583656863271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81096027407245722437908847 121644041110868583656863271)
        ·
          refine ⟨182466061666302875485294907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121644041110868583656863271 182466061666302875485294907)
          ·
            refine ⟨273699092499454313227942361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182466061666302875485294907 273699092499454313227942361)
            ·
              refine ⟨205274319374590734920956771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273699092499454313227942361 205274319374590734920956771)
              ·
                refine ⟨307911479061886102381435157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205274319374590734920956771 307911479061886102381435157)
                ·
                  refine ⟨14433350581025911049129773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307911479061886102381435157 14433350581025911049129773)
                  ·
                    refine ⟨5412506467884716643423665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14433350581025911049129773 5412506467884716643423665)
                    ·
                      refine ⟨4059379850913537482567749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412506467884716643423665 4059379850913537482567749)
                      ·
                        rfl

theorem cell23_7905614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_7905614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905614 prefixEnd_7905614 := by exact prefixLift 7905614
  have htrace : WordTrace (prefixWord ++ tailWord_7905614) baseStart_7905614 baseEnd_7905614 := by
    simpa [prefixWord, tailWord_7905614, baseEnd_7905614] using wordTrace_append hprefix tailTrace_7905614
  have hstable : (prefixWord ++ tailWord_7905614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905614).length < 2 ^ (prefixWord ++ tailWord_7905614).sum := by decide
  have hdescent : baseEnd_7905614 < baseStart_7905614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905678 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7905678 : Nat := 118140960795 + 7905678 * 2 ^ 59
def prefixEnd_7905678 : Nat := 4983230072969 + 3 ^ 40 * 7905678 * 2
def baseEnd_7905678 : Nat := 4059412713675425232167455

theorem tailTrace_7905678 : CollatzResearch.WordTrace tailWord_7905678 prefixEnd_7905678 4059412713675425232167455 := by
  unfold tailWord_7905678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36042970631635782894250711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192229176702057508769337125 36042970631635782894250711)
  ·
    refine ⟨54064455947453674341376067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36042970631635782894250711 54064455947453674341376067)
    ·
      refine ⟨81096683921180511512064101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54064455947453674341376067 81096683921180511512064101)
      ·
        refine ⟨15205628235221345908512019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81096683921180511512064101 15205628235221345908512019)
        ·
          refine ⟨22808442352832018862768029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205628235221345908512019 22808442352832018862768029)
          ·
            refine ⟨8553165882312007073538011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22808442352832018862768029 8553165882312007073538011)
            ·
              refine ⟨12829748823468010610307017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553165882312007073538011 12829748823468010610307017)
              ·
                refine ⟨9622311617601007957730263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12829748823468010610307017 9622311617601007957730263)
                ·
                  refine ⟨14433467426401511936595395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622311617601007957730263 14433467426401511936595395)
                  ·
                    refine ⟨21650201139602267904893093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14433467426401511936595395 21650201139602267904893093)
                    ·
                      refine ⟨4059412713675425232167455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21650201139602267904893093 4059412713675425232167455)
                      ·
                        rfl

theorem cell23_7905678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7905678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905678 prefixEnd_7905678 := by exact prefixLift 7905678
  have htrace : WordTrace (prefixWord ++ tailWord_7905678) baseStart_7905678 baseEnd_7905678 := by
    simpa [prefixWord, tailWord_7905678, baseEnd_7905678] using wordTrace_append hprefix tailTrace_7905678
  have hstable : (prefixWord ++ tailWord_7905678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905678).length < 2 ^ (prefixWord ++ tailWord_7905678).sum := by decide
  have hdescent : baseEnd_7905678 < baseStart_7905678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905698 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7905698 : Nat := 118140960795 + 7905698 * 2 ^ 59
def prefixEnd_7905698 : Nat := 4983230072969 + 3 ^ 40 * 7905698 * 2
def baseEnd_7905698 : Nat := 4059422983288515153917363

theorem tailTrace_7905698 : CollatzResearch.WordTrace tailWord_7905698 prefixEnd_7905698 4059422983288515153917363 := by
  unfold tailWord_7905698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72086123628253451642433437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192229663008675871046489165 72086123628253451642433437)
  ·
    refine ⟨27032296360595044365912539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72086123628253451642433437 27032296360595044365912539)
    ·
      refine ⟨40548444540892566548868809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27032296360595044365912539 40548444540892566548868809)
      ·
        refine ⟨30411333405669424911651607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40548444540892566548868809 30411333405669424911651607)
        ·
          refine ⟨45617000108504137367477411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30411333405669424911651607 45617000108504137367477411)
          ·
            refine ⟨68425500162756206051216117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45617000108504137367477411 68425500162756206051216117)
            ·
              refine ⟨6414890640258394317301511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68425500162756206051216117 6414890640258394317301511)
              ·
                refine ⟨9622335960387591475952267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414890640258394317301511 9622335960387591475952267)
                ·
                  refine ⟨14433503940581387213928401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622335960387591475952267 14433503940581387213928401)
                  ·
                    refine ⟨10825127955436040410446301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14433503940581387213928401 10825127955436040410446301)
                    ·
                      refine ⟨4059422983288515153917363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825127955436040410446301 4059422983288515153917363)
                      ·
                        rfl

theorem cell23_7905698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7905698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905698 prefixEnd_7905698 := by exact prefixLift 7905698
  have htrace : WordTrace (prefixWord ++ tailWord_7905698) baseStart_7905698 baseEnd_7905698 := by
    simpa [prefixWord, tailWord_7905698, baseEnd_7905698] using wordTrace_append hprefix tailTrace_7905698
  have hstable : (prefixWord ++ tailWord_7905698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905698).length < 2 ^ (prefixWord ++ tailWord_7905698).sum := by decide
  have hdescent : baseEnd_7905698 < baseStart_7905698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905706 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7905706 : Nat := 118140960795 + 7905706 * 2 ^ 59
def prefixEnd_7905706 : Nat := 4983230072969 + 3 ^ 40 * 7905706 * 2
def baseEnd_7905706 : Nat := 4059427091133751122617327

theorem tailTrace_7905706 : CollatzResearch.WordTrace tailWord_7905706 prefixEnd_7905706 4059427091133751122617327 := by
  unfold tailWord_7905706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72086196574246205984006243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192229857531323215957349981 72086196574246205984006243)
  ·
    refine ⟨108129294861369308976009365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72086196574246205984006243 108129294861369308976009365)
    ·
      refine ⟨5068560696626686358250439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108129294861369308976009365 5068560696626686358250439)
      ·
        refine ⟨7602841044940029537375659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068560696626686358250439 7602841044940029537375659)
        ·
          refine ⟨11404261567410044306063489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602841044940029537375659 11404261567410044306063489)
          ·
            refine ⟨8553196175557533229547617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11404261567410044306063489 8553196175557533229547617)
            ·
              refine ⟨6414897131668149922160713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553196175557533229547617 6414897131668149922160713)
              ·
                refine ⟨4811172848751112441620535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414897131668149922160713 4811172848751112441620535)
                ·
                  refine ⟨7216759273126668662430803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811172848751112441620535 7216759273126668662430803)
                  ·
                    refine ⟨10825138909690002993646205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216759273126668662430803 10825138909690002993646205)
                    ·
                      refine ⟨4059427091133751122617327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825138909690002993646205 4059427091133751122617327)
                      ·
                        rfl

theorem cell23_7905706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7905706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905706 prefixEnd_7905706 := by exact prefixLift 7905706
  have htrace : WordTrace (prefixWord ++ tailWord_7905706) baseStart_7905706 baseEnd_7905706 := by
    simpa [prefixWord, tailWord_7905706, baseEnd_7905706] using wordTrace_append hprefix tailTrace_7905706
  have hstable : (prefixWord ++ tailWord_7905706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905706).length < 2 ^ (prefixWord ++ tailWord_7905706).sum := by decide
  have hdescent : baseEnd_7905706 < baseStart_7905706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905721 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7905721 : Nat := 118140960795 + 7905721 * 2 ^ 59
def prefixEnd_7905721 : Nat := 4983230072969 + 3 ^ 40 * 7905721 * 2
def baseEnd_7905721 : Nat := 4059434793343568563929757

theorem tailTrace_7905721 : CollatzResearch.WordTrace tailWord_7905721 prefixEnd_7905721 4059434793343568563929757 := by
  unfold tailWord_7905721
  simp only [CollatzResearch.WordTrace]
  refine ⟨288345333391930481497821017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192230222261286987665214011 288345333391930481497821017)
  ·
    refine ⟨216259000043947861123365763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288345333391930481497821017 216259000043947861123365763)
    ·
      refine ⟨324388500065921791685048645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216259000043947861123365763 324388500065921791685048645)
      ·
        refine ⟨60822843762360335940946621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324388500065921791685048645 60822843762360335940946621)
        ·
          refine ⟨22808566410885125977854983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60822843762360335940946621 22808566410885125977854983)
          ·
            refine ⟨34212849616327688966782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22808566410885125977854983 34212849616327688966782475)
            ·
              refine ⟨51319274424491533450173713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34212849616327688966782475 51319274424491533450173713)
              ·
                refine ⟨38489455818368650087630285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51319274424491533450173713 38489455818368650087630285)
                ·
                  refine ⟨14433545931888243782861357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38489455818368650087630285 14433545931888243782861357)
                  ·
                    refine ⟨5412579724458091418573009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14433545931888243782861357 5412579724458091418573009)
                    ·
                      refine ⟨4059434793343568563929757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412579724458091418573009 4059434793343568563929757)
                      ·
                        rfl

theorem cell23_7905721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7905721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905721 prefixEnd_7905721 := by exact prefixLift 7905721
  have htrace : WordTrace (prefixWord ++ tailWord_7905721) baseStart_7905721 baseEnd_7905721 := by
    simpa [prefixWord, tailWord_7905721, baseEnd_7905721] using wordTrace_append hprefix tailTrace_7905721
  have hstable : (prefixWord ++ tailWord_7905721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905721).length < 2 ^ (prefixWord ++ tailWord_7905721).sum := by decide
  have hdescent : baseEnd_7905721 < baseStart_7905721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905737 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_7905737 : Nat := 118140960795 + 7905737 * 2 ^ 59
def prefixEnd_7905737 : Nat := 4983230072969 + 3 ^ 40 * 7905737 * 2
def baseEnd_7905737 : Nat := 4059443009034040501329683

theorem tailTrace_7905737 : CollatzResearch.WordTrace tailWord_7905737 prefixEnd_7905737 4059443009034040501329683 := by
  unfold tailWord_7905737
  simp only [CollatzResearch.WordTrace]
  refine ⟨288345916959872516230403465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192230611306581677486935643 288345916959872516230403465)
  ·
    refine ⟨216259437719904387172802599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288345916959872516230403465 216259437719904387172802599)
    ·
      refine ⟨324389156579856580759203899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216259437719904387172802599 324389156579856580759203899)
      ·
        refine ⟨486583734869784871138805849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324389156579856580759203899 486583734869784871138805849)
        ·
          refine ⟨364937801152338653354104387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486583734869784871138805849 364937801152338653354104387)
          ·
            refine ⟨547406701728507980031156581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364937801152338653354104387 547406701728507980031156581)
            ·
              refine ⟨102638756574095246255841859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547406701728507980031156581 102638756574095246255841859)
              ·
                refine ⟨153958134861142869383762789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102638756574095246255841859 153958134861142869383762789)
                ·
                  refine ⟨28867150286464288009455523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153958134861142869383762789 28867150286464288009455523)
                  ·
                    refine ⟨43300725429696432014183285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28867150286464288009455523 43300725429696432014183285)
                    ·
                      refine ⟨4059443009034040501329683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43300725429696432014183285 4059443009034040501329683)
                      ·
                        rfl

theorem cell23_7905737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_7905737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905737 prefixEnd_7905737 := by exact prefixLift 7905737
  have htrace : WordTrace (prefixWord ++ tailWord_7905737) baseStart_7905737 baseEnd_7905737 := by
    simpa [prefixWord, tailWord_7905737, baseEnd_7905737] using wordTrace_append hprefix tailTrace_7905737
  have hstable : (prefixWord ++ tailWord_7905737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905737).length < 2 ^ (prefixWord ++ tailWord_7905737).sum := by decide
  have hdescent : baseEnd_7905737 < baseStart_7905737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905768 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7905768 : Nat := 118140960795 + 7905768 * 2 ^ 59
def prefixEnd_7905768 : Nat := 4983230072969 + 3 ^ 40 * 7905768 * 2
def baseEnd_7905768 : Nat := 4059458926934329880042041

theorem tailTrace_7905768 : CollatzResearch.WordTrace tailWord_7905768 prefixEnd_7905768 4059458926934329880042041 := by
  unfold tailWord_7905768
  simp only [CollatzResearch.WordTrace]
  refine ⟨144173523811380104262390979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192231365081840139016521305 144173523811380104262390979)
  ·
    refine ⟨216260285717070156393586469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144173523811380104262390979 216260285717070156393586469)
    ·
      refine ⟨40548803571950654323797463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216260285717070156393586469 40548803571950654323797463)
      ·
        refine ⟨60823205357925981485696195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40548803571950654323797463 60823205357925981485696195)
        ·
          refine ⟨91234808036888972228544293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60823205357925981485696195 91234808036888972228544293)
          ·
            refine ⟨17106526506916682292852055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91234808036888972228544293 17106526506916682292852055)
            ·
              refine ⟨25659789760375023439278083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17106526506916682292852055 25659789760375023439278083)
              ·
                refine ⟨38489684640562535158917125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25659789760375023439278083 38489684640562535158917125)
                ·
                  refine ⟨7216815870105475342296961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38489684640562535158917125 7216815870105475342296961)
                  ·
                    refine ⟨5412611902579106506722721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216815870105475342296961 5412611902579106506722721)
                    ·
                      refine ⟨4059458926934329880042041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412611902579106506722721 4059458926934329880042041)
                      ·
                        rfl

theorem cell23_7905768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7905768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905768 prefixEnd_7905768 := by exact prefixLift 7905768
  have htrace : WordTrace (prefixWord ++ tailWord_7905768) baseStart_7905768 baseEnd_7905768 := by
    simpa [prefixWord, tailWord_7905768, baseEnd_7905768] using wordTrace_append hprefix tailTrace_7905768
  have hstable : (prefixWord ++ tailWord_7905768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905768).length < 2 ^ (prefixWord ++ tailWord_7905768).sum := by decide
  have hdescent : baseEnd_7905768 < baseStart_7905768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905774 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_7905774 : Nat := 118140960795 + 7905774 * 2 ^ 59
def prefixEnd_7905774 : Nat := 4983230072969 + 3 ^ 40 * 7905774 * 2
def baseEnd_7905774 : Nat := 451051334202028539618557

theorem tailTrace_7905774 : CollatzResearch.WordTrace tailWord_7905774 prefixEnd_7905774 451051334202028539618557 := by
  unfold tailWord_7905774
  simp only [CollatzResearch.WordTrace]
  refine ⟨36043408307592308943687547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192231510973825647699666917 36043408307592308943687547)
  ·
    refine ⟨54065112461388463415531321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36043408307592308943687547 54065112461388463415531321)
    ·
      refine ⟨40548834346041347561648491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54065112461388463415531321 40548834346041347561648491)
      ·
        refine ⟨60823251519062021342472737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40548834346041347561648491 60823251519062021342472737)
        ·
          refine ⟨45617438639296516006854553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60823251519062021342472737 45617438639296516006854553)
          ·
            refine ⟨34213078979472387005140915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45617438639296516006854553 34213078979472387005140915)
            ·
              refine ⟨51319618469208580507711373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34213078979472387005140915 51319618469208580507711373)
              ·
                refine ⟨19244856925953217690391765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51319618469208580507711373 19244856925953217690391765)
                ·
                  refine ⟨451051334202028539618557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19244856925953217690391765 451051334202028539618557)
                  ·
                    rfl

theorem cell23_7905774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_7905774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905774 prefixEnd_7905774 := by exact prefixLift 7905774
  have htrace : WordTrace (prefixWord ++ tailWord_7905774) baseStart_7905774 baseEnd_7905774 := by
    simpa [prefixWord, tailWord_7905774, baseEnd_7905774] using wordTrace_append hprefix tailTrace_7905774
  have hstable : (prefixWord ++ tailWord_7905774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905774).length < 2 ^ (prefixWord ++ tailWord_7905774).sum := by decide
  have hdescent : baseEnd_7905774 < baseStart_7905774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905784 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_7905784 : Nat := 118140960795 + 7905784 * 2 ^ 59
def prefixEnd_7905784 : Nat := 4983230072969 + 3 ^ 40 * 7905784 * 2
def baseEnd_7905784 : Nat := 4059467142624801817441967

theorem tailTrace_7905784 : CollatzResearch.WordTrace tailWord_7905784 prefixEnd_7905784 4059467142624801817441967 := by
  unfold tailWord_7905784
  simp only [CollatzResearch.WordTrace]
  refine ⟨144173815595351121628682203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192231754127134828838242937 144173815595351121628682203)
  ·
    refine ⟨216260723393026682443023305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144173815595351121628682203 216260723393026682443023305)
    ·
      refine ⟨162195542544770011832267479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216260723393026682443023305 162195542544770011832267479)
      ·
        refine ⟨243293313817155017748401219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162195542544770011832267479 243293313817155017748401219)
        ·
          refine ⟨364939970725732526622601829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243293313817155017748401219 364939970725732526622601829)
          ·
            refine ⟨68426244511074848741737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 364939970725732526622601829 68426244511074848741737843)
            ·
              refine ⟨102639366766612273112606765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68426244511074848741737843 102639366766612273112606765)
              ·
                refine ⟨38489762537479602417227537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102639366766612273112606765 38489762537479602417227537)
                ·
                  refine ⟨28867321903109701812920653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38489762537479602417227537 28867321903109701812920653)
                  ·
                    refine ⟨10825245713666138179845245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28867321903109701812920653 10825245713666138179845245)
                    ·
                      refine ⟨4059467142624801817441967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825245713666138179845245 4059467142624801817441967)
                      ·
                        rfl

theorem cell23_7905784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_7905784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905784 prefixEnd_7905784 := by exact prefixLift 7905784
  have htrace : WordTrace (prefixWord ++ tailWord_7905784) baseStart_7905784 baseEnd_7905784 := by
    simpa [prefixWord, tailWord_7905784, baseEnd_7905784] using wordTrace_append hprefix tailTrace_7905784
  have hstable : (prefixWord ++ tailWord_7905784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905784).length < 2 ^ (prefixWord ++ tailWord_7905784).sum := by decide
  have hdescent : baseEnd_7905784 < baseStart_7905784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905804 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_7905804 : Nat := 118140960795 + 7905804 * 2 ^ 59
def prefixEnd_7905804 : Nat := 4983230072969 + 3 ^ 40 * 7905804 * 2
def baseEnd_7905804 : Nat := 1353159137412630579730625

theorem tailTrace_7905804 : CollatzResearch.WordTrace tailWord_7905804 prefixEnd_7905804 1353159137412630579730625 := by
  unfold tailWord_7905804
  simp only [CollatzResearch.WordTrace]
  refine ⟨144174180325314893336546233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192232240433753191115394977 144174180325314893336546233)
  ·
    refine ⟨108130635243986170002409675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144174180325314893336546233 108130635243986170002409675)
    ·
      refine ⟨162195952865979255003614513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108130635243986170002409675 162195952865979255003614513)
      ·
        refine ⟨121646964649484441252710885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162195952865979255003614513 121646964649484441252710885)
        ·
          refine ⟨22808805871778332734883291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121646964649484441252710885 22808805871778332734883291)
          ·
            refine ⟨34213208807667499102324937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22808805871778332734883291 34213208807667499102324937)
            ·
              refine ⟨25659906605750624326743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34213208807667499102324937 25659906605750624326743703)
              ·
                refine ⟨38489859908625936490115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25659906605750624326743703 38489859908625936490115555)
                ·
                  refine ⟨57734789862938904735173333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38489859908625936490115555 57734789862938904735173333)
                  ·
                    refine ⟨1353159137412630579730625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57734789862938904735173333 1353159137412630579730625)
                    ·
                      rfl

theorem cell23_7905804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_7905804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905804 prefixEnd_7905804 := by exact prefixLift 7905804
  have htrace : WordTrace (prefixWord ++ tailWord_7905804) baseStart_7905804 baseEnd_7905804 := by
    simpa [prefixWord, tailWord_7905804, baseEnd_7905804] using wordTrace_append hprefix tailTrace_7905804
  have hstable : (prefixWord ++ tailWord_7905804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905804).length < 2 ^ (prefixWord ++ tailWord_7905804).sum := by decide
  have hdescent : baseEnd_7905804 < baseStart_7905804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905817 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_7905817 : Nat := 118140960795 + 7905817 * 2 ^ 59
def prefixEnd_7905817 : Nat := 4983230072969 + 3 ^ 40 * 7905817 * 2
def baseEnd_7905817 : Nat := 1353161362495466729443105

theorem tailTrace_7905817 : CollatzResearch.WordTrace tailWord_7905817 prefixEnd_7905817 1353161362495466729443105 := by
  unfold tailWord_7905817
  simp only [CollatzResearch.WordTrace]
  refine ⟨288348834799582689893315705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192232556533055126595543803 288348834799582689893315705)
  ·
    refine ⟨216261626099687017419986779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288348834799582689893315705 216261626099687017419986779)
    ·
      refine ⟨324392439149530526129980169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216261626099687017419986779 324392439149530526129980169)
      ·
        refine ⟨243294329362147894597485127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324392439149530526129980169 243294329362147894597485127)
        ·
          refine ⟨364941494043221841896227691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243294329362147894597485127 364941494043221841896227691)
          ·
            refine ⟨547412241064832762844341537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364941494043221841896227691 547412241064832762844341537)
            ·
              refine ⟨410559180798624572133256153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547412241064832762844341537 410559180798624572133256153)
              ·
                refine ⟨307919385598968429099942115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410559180798624572133256153 307919385598968429099942115)
                ·
                  refine ⟨461879078398452643649913173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307919385598968429099942115 461879078398452643649913173)
                  ·
                    refine ⟨1353161362495466729443105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 461879078398452643649913173 1353161362495466729443105)
                    ·
                      rfl

theorem cell23_7905817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_7905817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905817 prefixEnd_7905817 := by exact prefixLift 7905817
  have htrace : WordTrace (prefixWord ++ tailWord_7905817) baseStart_7905817 baseEnd_7905817 := by
    simpa [prefixWord, tailWord_7905817, baseEnd_7905817] using wordTrace_append hprefix tailTrace_7905817
  have hstable : (prefixWord ++ tailWord_7905817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905817).length < 2 ^ (prefixWord ++ tailWord_7905817).sum := by decide
  have hdescent : baseEnd_7905817 < baseStart_7905817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905821 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7905821 : Nat := 118140960795 + 7905821 * 2 ^ 59
def prefixEnd_7905821 : Nat := 4983230072969 + 3 ^ 40 * 7905821 * 2
def baseEnd_7905821 : Nat := 1353162047136339390893099

theorem tailTrace_7905821 : CollatzResearch.WordTrace tailWord_7905821 prefixEnd_7905821 1353162047136339390893099 := by
  unfold tailWord_7905821
  simp only [CollatzResearch.WordTrace]
  refine ⟨288348980691568198576461317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192232653794378799050974211 288348980691568198576461317)
  ·
    refine ⟨54065433879669037233086497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288348980691568198576461317 54065433879669037233086497)
    ·
      refine ⟨40549075409751777924814873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54065433879669037233086497 40549075409751777924814873)
      ·
        refine ⟨30411806557313833443611155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40549075409751777924814873 30411806557313833443611155)
        ·
          refine ⟨45617709835970750165416733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30411806557313833443611155 45617709835970750165416733)
          ·
            refine ⟨17106641188489031312031275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45617709835970750165416733 17106641188489031312031275)
            ·
              refine ⟨25659961782733546968046913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17106641188489031312031275 25659961782733546968046913)
              ·
                refine ⟨19244971337050160226035185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25659961782733546968046913 19244971337050160226035185)
                ·
                  refine ⟨14433728502787620169526389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19244971337050160226035185 14433728502787620169526389)
                  ·
                    refine ⟨1353162047136339390893099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14433728502787620169526389 1353162047136339390893099)
                    ·
                      rfl

theorem cell23_7905821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7905821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905821 prefixEnd_7905821 := by exact prefixLift 7905821
  have htrace : WordTrace (prefixWord ++ tailWord_7905821) baseStart_7905821 baseEnd_7905821 := by
    simpa [prefixWord, tailWord_7905821, baseEnd_7905821] using wordTrace_append hprefix tailTrace_7905821
  have hstable : (prefixWord ++ tailWord_7905821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905821).length < 2 ^ (prefixWord ++ tailWord_7905821).sum := by decide
  have hdescent : baseEnd_7905821 < baseStart_7905821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905841 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_7905841 : Nat := 118140960795 + 7905841 * 2 ^ 59
def prefixEnd_7905841 : Nat := 4983230072969 + 3 ^ 40 * 7905841 * 2
def baseEnd_7905841 : Nat := 4059496411022108094429205

theorem tailTrace_7905841 : CollatzResearch.WordTrace tailWord_7905841 prefixEnd_7905841 4059496411022108094429205 := by
  unfold tailWord_7905841
  simp only [CollatzResearch.WordTrace]
  refine ⟨288349710151495741992189377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192233140100997161328126251 288349710151495741992189377)
  ·
    refine ⟨216262282613621806494142033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288349710151495741992189377 216262282613621806494142033)
    ·
      refine ⟨162196711960216354870606525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216262282613621806494142033 162196711960216354870606525)
      ·
        refine ⟨60823766985081133076477447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162196711960216354870606525 60823766985081133076477447)
        ·
          refine ⟨91235650477621699614716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60823766985081133076477447 91235650477621699614716171)
          ·
            refine ⟨136853475716432549422074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91235650477621699614716171 136853475716432549422074257)
            ·
              refine ⟨102640106787324412066555693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136853475716432549422074257 102640106787324412066555693)
              ·
                refine ⟨38490040045246654524958385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102640106787324412066555693 38490040045246654524958385)
                ·
                  refine ⟨28867530033934990893718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38490040045246654524958385 28867530033934990893718789)
                  ·
                    refine ⟨5412661881362810792572273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28867530033934990893718789 5412661881362810792572273)
                    ·
                      refine ⟨4059496411022108094429205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412661881362810792572273 4059496411022108094429205)
                      ·
                        rfl

theorem cell23_7905841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_7905841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905841 prefixEnd_7905841 := by exact prefixLift 7905841
  have htrace : WordTrace (prefixWord ++ tailWord_7905841) baseStart_7905841 baseEnd_7905841 := by
    simpa [prefixWord, tailWord_7905841, baseEnd_7905841] using wordTrace_append hprefix tailTrace_7905841
  have hstable : (prefixWord ++ tailWord_7905841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905841).length < 2 ^ (prefixWord ++ tailWord_7905841).sum := by decide
  have hdescent : baseEnd_7905841 < baseStart_7905841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905861 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_7905861 : Nat := 118140960795 + 7905861 * 2 ^ 59
def prefixEnd_7905861 : Nat := 4983230072969 + 3 ^ 40 * 7905861 * 2
def baseEnd_7905861 : Nat := 4059506680635198016179113

theorem tailTrace_7905861 : CollatzResearch.WordTrace tailWord_7905861 prefixEnd_7905861 4059506680635198016179113 := by
  unfold tailWord_7905861
  simp only [CollatzResearch.WordTrace]
  refine ⟨288350439611423285407917437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192233626407615523605278291 288350439611423285407917437)
  ·
    refine ⟨108131414854283732027969039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288350439611423285407917437 108131414854283732027969039)
    ·
      refine ⟨162197122281425598041953559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108131414854283732027969039 162197122281425598041953559)
      ·
        refine ⟨243295683422138397062930339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162197122281425598041953559 243295683422138397062930339)
        ·
          refine ⟨364943525133207595594395509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243295683422138397062930339 364943525133207595594395509)
          ·
            refine ⟨34213455481238212086974579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 364943525133207595594395509 34213455481238212086974579)
            ·
              refine ⟨51320183221857318130461869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34213455481238212086974579 51320183221857318130461869)
              ·
                refine ⟨19245068708196494298923201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51320183221857318130461869 19245068708196494298923201)
                ·
                  refine ⟨14433801531147370724192401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19245068708196494298923201 14433801531147370724192401)
                  ·
                    refine ⟨10825351148360528043144301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14433801531147370724192401 10825351148360528043144301)
                    ·
                      refine ⟨4059506680635198016179113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825351148360528043144301 4059506680635198016179113)
                      ·
                        rfl

theorem cell23_7905861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_7905861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905861 prefixEnd_7905861 := by exact prefixLift 7905861
  have htrace : WordTrace (prefixWord ++ tailWord_7905861) baseStart_7905861 baseEnd_7905861 := by
    simpa [prefixWord, tailWord_7905861, baseEnd_7905861] using wordTrace_append hprefix tailTrace_7905861
  have hstable : (prefixWord ++ tailWord_7905861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905861).length < 2 ^ (prefixWord ++ tailWord_7905861).sum := by decide
  have hdescent : baseEnd_7905861 < baseStart_7905861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905868 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_7905868 : Nat := 118140960795 + 7905868 * 2 ^ 59
def prefixEnd_7905868 : Nat := 4983230072969 + 3 ^ 40 * 7905868 * 2
def baseEnd_7905868 : Nat := 1353170091666593162930527

theorem tailTrace_7905868 : CollatzResearch.WordTrace tailWord_7905868 prefixEnd_7905868 1353170091666593162930527 := by
  unfold tailWord_7905868
  simp only [CollatzResearch.WordTrace]
  refine ⟨144175347461198962801711129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192233796614931950402281505 144175347461198962801711129)
  ·
    refine ⟨108131510595899222101283347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144175347461198962801711129 108131510595899222101283347)
    ·
      refine ⟨162197265893848833151925021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108131510595899222101283347 162197265893848833151925021)
      ·
        refine ⟨60823974710193312431971883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162197265893848833151925021 60823974710193312431971883)
        ·
          refine ⟨91235962065289968647957825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60823974710193312431971883 91235962065289968647957825)
          ·
            refine ⟨68426971548967476485968369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91235962065289968647957825 68426971548967476485968369)
            ·
              refine ⟨51320228661725607364476277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68426971548967476485968369 51320228661725607364476277)
              ·
                refine ⟨4811271437036775690419651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51320228661725607364476277 4811271437036775690419651)
                ·
                  refine ⟨7216907155555163535629477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811271437036775690419651 7216907155555163535629477)
                  ·
                    refine ⟨1353170091666593162930527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216907155555163535629477 1353170091666593162930527)
                    ·
                      rfl

theorem cell23_7905868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_7905868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905868 prefixEnd_7905868 := by exact prefixLift 7905868
  have htrace : WordTrace (prefixWord ++ tailWord_7905868) baseStart_7905868 baseEnd_7905868 := by
    simpa [prefixWord, tailWord_7905868, baseEnd_7905868] using wordTrace_append hprefix tailTrace_7905868
  have hstable : (prefixWord ++ tailWord_7905868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905868).length < 2 ^ (prefixWord ++ tailWord_7905868).sum := by decide
  have hdescent : baseEnd_7905868 < baseStart_7905868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905925 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_7905925 : Nat := 118140960795 + 7905925 * 2 ^ 59
def prefixEnd_7905925 : Nat := 4983230072969 + 3 ^ 40 * 7905925 * 2
def baseEnd_7905925 : Nat := 4059539543397085765778819

theorem tailTrace_7905925 : CollatzResearch.WordTrace tailWord_7905925 prefixEnd_7905925 4059539543397085765778819 := by
  unfold tailWord_7905925
  simp only [CollatzResearch.WordTrace]
  refine ⟨288352773883191424338247229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192235182588794282892164819 288352773883191424338247229)
  ·
    refine ⟨108132290206196784126842711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288352773883191424338247229 108132290206196784126842711)
    ·
      refine ⟨162198435309295176190264067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108132290206196784126842711 162198435309295176190264067)
      ·
        refine ⟨243297652963942764285396101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162198435309295176190264067 243297652963942764285396101)
        ·
          refine ⟨45618309930739268303511769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243297652963942764285396101 45618309930739268303511769)
          ·
            refine ⟨34213732448054451227633827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45618309930739268303511769 34213732448054451227633827)
            ·
              refine ⟨51320598672081676841450741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34213732448054451227633827 51320598672081676841450741)
              ·
                refine ⟨4811306125507657203886007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51320598672081676841450741 4811306125507657203886007)
                ·
                  refine ⟨7216959188261485805829011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811306125507657203886007 7216959188261485805829011)
                  ·
                    refine ⟨10825438782392228708743517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216959188261485805829011 10825438782392228708743517)
                    ·
                      refine ⟨4059539543397085765778819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825438782392228708743517 4059539543397085765778819)
                      ·
                        rfl

theorem cell23_7905925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_7905925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905925 prefixEnd_7905925 := by exact prefixLift 7905925
  have htrace : WordTrace (prefixWord ++ tailWord_7905925) baseStart_7905925 baseEnd_7905925 := by
    simpa [prefixWord, tailWord_7905925, baseEnd_7905925] using wordTrace_append hprefix tailTrace_7905925
  have hstable : (prefixWord ++ tailWord_7905925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905925).length < 2 ^ (prefixWord ++ tailWord_7905925).sum := by decide
  have hdescent : baseEnd_7905925 < baseStart_7905925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905962 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7905962 : Nat := 118140960795 + 7905962 * 2 ^ 59
def prefixEnd_7905962 : Nat := 4983230072969 + 3 ^ 40 * 7905962 * 2
def baseEnd_7905962 : Nat := 1353186180727100707005383

theorem tailTrace_7905962 : CollatzResearch.WordTrace tailWord_7905962 prefixEnd_7905962 1353186180727100707005383 := by
  unfold tailWord_7905962
  simp only [CollatzResearch.WordTrace]
  refine ⟨72088530846014344914336035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192236082256038253104896093 72088530846014344914336035)
  ·
    refine ⟨108132796269021517371504053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72088530846014344914336035 108132796269021517371504053)
    ·
      refine ⟨10137449650220767253578505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108132796269021517371504053 10137449650220767253578505)
      ·
        refine ⟨7603087237665575440183879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10137449650220767253578505 7603087237665575440183879)
        ·
          refine ⟨11404630856498363160275819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603087237665575440183879 11404630856498363160275819)
          ·
            refine ⟨17106946284747544740413729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404630856498363160275819 17106946284747544740413729)
            ·
              refine ⟨12830209713560658555310297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17106946284747544740413729 12830209713560658555310297)
              ·
                refine ⟨9622657285170493916482723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830209713560658555310297 9622657285170493916482723)
                ·
                  refine ⟨14433985927755740874724085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622657285170493916482723 14433985927755740874724085)
                  ·
                    refine ⟨1353186180727100707005383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14433985927755740874724085 1353186180727100707005383)
                    ·
                      rfl

theorem cell23_7905962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7905962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905962 prefixEnd_7905962 := by exact prefixLift 7905962
  have htrace : WordTrace (prefixWord ++ tailWord_7905962) baseStart_7905962 baseEnd_7905962 := by
    simpa [prefixWord, tailWord_7905962, baseEnd_7905962] using wordTrace_append hprefix tailTrace_7905962
  have hstable : (prefixWord ++ tailWord_7905962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905962).length < 2 ^ (prefixWord ++ tailWord_7905962).sum := by decide
  have hdescent : baseEnd_7905962 < baseStart_7905962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905965 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_7905965 : Nat := 118140960795 + 7905965 * 2 ^ 59
def prefixEnd_7905965 : Nat := 4983230072969 + 3 ^ 40 * 7905965 * 2
def baseEnd_7905965 : Nat := 4059560082623265609278635

theorem tailTrace_7905965 : CollatzResearch.WordTrace tailWord_7905965 prefixEnd_7905965 4059560082623265609278635 := by
  unfold tailWord_7905965
  simp only [CollatzResearch.WordTrace]
  refine ⟨288354232803046511169703349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192236155202031007446468899 288354232803046511169703349)
  ·
    refine ⟨27033209325285610422159689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288354232803046511169703349 27033209325285610422159689)
    ·
      refine ⟨20274906993964207816619767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27033209325285610422159689 20274906993964207816619767)
      ·
        refine ⟨30412360490946311724929651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20274906993964207816619767 30412360490946311724929651)
        ·
          refine ⟨45618540736419467587394477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30412360490946311724929651 45618540736419467587394477)
          ·
            refine ⟨17106952776157300345272929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45618540736419467587394477 17106952776157300345272929)
            ·
              refine ⟨12830214582117975258954697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17106952776157300345272929 12830214582117975258954697)
              ·
                refine ⟨9622660936588481444216023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830214582117975258954697 9622660936588481444216023)
                ·
                  refine ⟨14433991404882722166324035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622660936588481444216023 14433991404882722166324035)
                  ·
                    refine ⟨21650987107324083249486053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14433991404882722166324035 21650987107324083249486053)
                    ·
                      refine ⟨4059560082623265609278635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21650987107324083249486053 4059560082623265609278635)
                      ·
                        rfl

theorem cell23_7905965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_7905965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905965 prefixEnd_7905965 := by exact prefixLift 7905965
  have htrace : WordTrace (prefixWord ++ tailWord_7905965) baseStart_7905965 baseEnd_7905965 := by
    simpa [prefixWord, tailWord_7905965, baseEnd_7905965] using wordTrace_append hprefix tailTrace_7905965
  have hstable : (prefixWord ++ tailWord_7905965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905965).length < 2 ^ (prefixWord ++ tailWord_7905965).sum := by decide
  have hdescent : baseEnd_7905965 < baseStart_7905965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905971 : List Nat := [1, 1, 1, 2, 3, 4, 4, 7]
def baseStart_7905971 : Nat := 118140960795 + 7905971 * 2 ^ 59
def prefixEnd_7905971 : Nat := 4983230072969 + 3 ^ 40 * 7905971 * 2
def baseEnd_7905971 : Nat := 150354191241007132807541

theorem tailTrace_7905971 : CollatzResearch.WordTrace tailWord_7905971 prefixEnd_7905971 150354191241007132807541 := by
  unfold tailWord_7905971
  simp only [CollatzResearch.WordTrace]
  refine ⟨288354451641024774194421767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192236301094016516129614511 288354451641024774194421767)
  ·
    refine ⟨432531677461537161291632651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288354451641024774194421767 432531677461537161291632651)
    ·
      refine ⟨648797516192305741937448977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432531677461537161291632651 648797516192305741937448977)
      ·
        refine ⟨486598137144229306453086733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648797516192305741937448977 486598137144229306453086733)
        ·
          refine ⟨182474301429085989919907525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486598137144229306453086733 182474301429085989919907525)
          ·
            refine ⟨34213931517953623109982661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182474301429085989919907525 34213931517953623109982661)
            ·
              refine ⟨6415112159616304333121749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34213931517953623109982661 6415112159616304333121749)
              ·
                refine ⟨150354191241007132807541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6415112159616304333121749 150354191241007132807541)
                ·
                  rfl

theorem cell23_7905971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 7].length) (baseStart_7905971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7905971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7905971 prefixEnd_7905971 := by exact prefixLift 7905971
  have htrace : WordTrace (prefixWord ++ tailWord_7905971) baseStart_7905971 baseEnd_7905971 := by
    simpa [prefixWord, tailWord_7905971, baseEnd_7905971] using wordTrace_append hprefix tailTrace_7905971
  have hstable : (prefixWord ++ tailWord_7905971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905971).length < 2 ^ (prefixWord ++ tailWord_7905971).sum := by decide
  have hdescent : baseEnd_7905971 < baseStart_7905971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906015 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_7906015 : Nat := 118140960795 + 7906015 * 2 ^ 59
def prefixEnd_7906015 : Nat := 4983230072969 + 3 ^ 40 * 7906015 * 2
def baseEnd_7906015 : Nat := 4059585756655990413653405

theorem tailTrace_7906015 : CollatzResearch.WordTrace tailWord_7906015 prefixEnd_7906015 4059585756655990413653405 := by
  unfold tailWord_7906015
  simp only [CollatzResearch.WordTrace]
  refine ⟨288356056452865369709023499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192237370968576913139348999 288356056452865369709023499)
  ·
    refine ⟨432534084679298054563535249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288356056452865369709023499 432534084679298054563535249)
    ·
      refine ⟨324400563509473540922651437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432534084679298054563535249 324400563509473540922651437)
      ·
        refine ⟨121650211316052577845994289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324400563509473540922651437 121650211316052577845994289)
        ·
          refine ⟨91237658487039433384495717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121650211316052577845994289 91237658487039433384495717)
          ·
            refine ⟨17107060966319893759592947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91237658487039433384495717 17107060966319893759592947)
            ·
              refine ⟨25660591449479840639389421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17107060966319893759592947 25660591449479840639389421)
              ·
                refine ⟨9622721793554940239771033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25660591449479840639389421 9622721793554940239771033)
                ·
                  refine ⟨7217041345166205179828275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9622721793554940239771033 7217041345166205179828275)
                  ·
                    refine ⟨10825562017749307769742413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217041345166205179828275 10825562017749307769742413)
                    ·
                      refine ⟨4059585756655990413653405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825562017749307769742413 4059585756655990413653405)
                      ·
                        rfl

theorem cell23_7906015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_7906015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906015 prefixEnd_7906015 := by exact prefixLift 7906015
  have htrace : WordTrace (prefixWord ++ tailWord_7906015) baseStart_7906015 baseEnd_7906015 := by
    simpa [prefixWord, tailWord_7906015, baseEnd_7906015] using wordTrace_append hprefix tailTrace_7906015
  have hstable : (prefixWord ++ tailWord_7906015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906015).length < 2 ^ (prefixWord ++ tailWord_7906015).sum := by decide
  have hdescent : baseEnd_7906015 < baseStart_7906015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906025 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 1, 3, 2]
def baseStart_7906025 : Nat := 118140960795 + 7906025 * 2 ^ 59
def prefixEnd_7906025 : Nat := 4983230072969 + 3 ^ 40 * 7906025 * 2
def baseEnd_7906025 : Nat := 4059590891462535374528359

theorem tailTrace_7906025 : CollatzResearch.WordTrace tailWord_7906025 prefixEnd_7906025 4059590891462535374528359 := by
  unfold tailWord_7906025
  simp only [CollatzResearch.WordTrace]
  refine ⟨288356421182829141416887529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192237614121886094277925019 288356421182829141416887529)
  ·
    refine ⟨216267315887121856062665647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288356421182829141416887529 216267315887121856062665647)
    ·
      refine ⟨324400973830682784093998471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216267315887121856062665647 324400973830682784093998471)
      ·
        refine ⟨486601460746024176140997707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324400973830682784093998471 486601460746024176140997707)
        ·
          refine ⟨729902191119036264211496561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486601460746024176140997707 729902191119036264211496561)
          ·
            refine ⟨547426643339277198158622421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 729902191119036264211496561 547426643339277198158622421)
            ·
              refine ⟨12830311953264309331842713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 547426643339277198158622421 12830311953264309331842713)
              ·
                refine ⟨9622733964948231998882035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830311953264309331842713 9622733964948231998882035)
                ·
                  refine ⟨14434100947422347998323053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622733964948231998882035 14434100947422347998323053)
                  ·
                    refine ⟨5412787855283380499371145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14434100947422347998323053 5412787855283380499371145)
                    ·
                      refine ⟨4059590891462535374528359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412787855283380499371145 4059590891462535374528359)
                      ·
                        rfl

theorem cell23_7906025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3, 2].length) (baseStart_7906025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906025 prefixEnd_7906025 := by exact prefixLift 7906025
  have htrace : WordTrace (prefixWord ++ tailWord_7906025) baseStart_7906025 baseEnd_7906025 := by
    simpa [prefixWord, tailWord_7906025, baseEnd_7906025] using wordTrace_append hprefix tailTrace_7906025
  have hstable : (prefixWord ++ tailWord_7906025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906025).length < 2 ^ (prefixWord ++ tailWord_7906025).sum := by decide
  have hdescent : baseEnd_7906025 < baseStart_7906025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906036 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7906036 : Nat := 118140960795 + 7906036 * 2 ^ 59
def prefixEnd_7906036 : Nat := 4983230072969 + 3 ^ 40 * 7906036 * 2
def baseEnd_7906036 : Nat := 4059596539749734831490809

theorem tailTrace_7906036 : CollatzResearch.WordTrace tailWord_7906036 prefixEnd_7906036 4059596539749734831490809 := by
  unfold tailWord_7906036
  simp only [CollatzResearch.WordTrace]
  refine ⟨144178411192894645147768981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192237881590526193530358641 144178411192894645147768981)
  ·
    refine ⟨6758363024666936491301671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144178411192894645147768981 6758363024666936491301671)
    ·
      refine ⟨10137544537000404736952507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6758363024666936491301671 10137544537000404736952507)
      ·
        refine ⟨15206316805500607105428761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137544537000404736952507 15206316805500607105428761)
        ·
          refine ⟨11404737604125455329071571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15206316805500607105428761 11404737604125455329071571)
          ·
            refine ⟨17107106406188182993607357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404737604125455329071571 17107106406188182993607357)
            ·
              refine ⟨6415164902320568622602759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17107106406188182993607357 6415164902320568622602759)
              ·
                refine ⟨9622747353480852933904139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415164902320568622602759 9622747353480852933904139)
                ·
                  refine ⟨14434121030221279400856209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622747353480852933904139 14434121030221279400856209)
                  ·
                    refine ⟨10825590772665959550642157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14434121030221279400856209 10825590772665959550642157)
                    ·
                      refine ⟨4059596539749734831490809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825590772665959550642157 4059596539749734831490809)
                      ·
                        rfl

theorem cell23_7906036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7906036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906036 prefixEnd_7906036 := by exact prefixLift 7906036
  have htrace : WordTrace (prefixWord ++ tailWord_7906036) baseStart_7906036 baseEnd_7906036 := by
    simpa [prefixWord, tailWord_7906036, baseEnd_7906036] using wordTrace_append hprefix tailTrace_7906036
  have hstable : (prefixWord ++ tailWord_7906036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906036).length < 2 ^ (prefixWord ++ tailWord_7906036).sum := by decide
  have hdescent : baseEnd_7906036 < baseStart_7906036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906041 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_7906041 : Nat := 118140960795 + 7906041 * 2 ^ 59
def prefixEnd_7906041 : Nat := 4983230072969 + 3 ^ 40 * 7906041 * 2
def baseEnd_7906041 : Nat := 4059599107153007311928285

theorem tailTrace_7906041 : CollatzResearch.WordTrace tailWord_7906041 prefixEnd_7906041 4059599107153007311928285 := by
  unfold tailWord_7906041
  simp only [CollatzResearch.WordTrace]
  refine ⟨288357004750771176149469977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192238003167180784099646651 288357004750771176149469977)
  ·
    refine ⟨216267753563078382112102483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288357004750771176149469977 216267753563078382112102483)
    ·
      refine ⟨324401630344617573168153725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216267753563078382112102483 324401630344617573168153725)
      ·
        refine ⟨121650611379231589938057647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324401630344617573168153725 121650611379231589938057647)
        ·
          refine ⟨182475917068847384907086471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121650611379231589938057647 182475917068847384907086471)
          ·
            refine ⟨273713875603271077360629707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182475917068847384907086471 273713875603271077360629707)
            ·
              refine ⟨410570813404906616040944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273713875603271077360629707 410570813404906616040944561)
              ·
                refine ⟨307928110053679962030708421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410570813404906616040944561 307928110053679962030708421)
                ·
                  refine ⟨57736520635064992880757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307928110053679962030708421 57736520635064992880757829)
                  ·
                    refine ⟨10825597619074686165142093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57736520635064992880757829 10825597619074686165142093)
                    ·
                      refine ⟨4059599107153007311928285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825597619074686165142093 4059599107153007311928285)
                      ·
                        rfl

theorem cell23_7906041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_7906041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906041 prefixEnd_7906041 := by exact prefixLift 7906041
  have htrace : WordTrace (prefixWord ++ tailWord_7906041) baseStart_7906041 baseEnd_7906041 := by
    simpa [prefixWord, tailWord_7906041, baseEnd_7906041] using wordTrace_append hprefix tailTrace_7906041
  have hstable : (prefixWord ++ tailWord_7906041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906041).length < 2 ^ (prefixWord ++ tailWord_7906041).sum := by decide
  have hdescent : baseEnd_7906041 < baseStart_7906041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906051 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_7906051 : Nat := 118140960795 + 7906051 * 2 ^ 59
def prefixEnd_7906051 : Nat := 4983230072969 + 3 ^ 40 * 7906051 * 2
def baseEnd_7906051 : Nat := 4059604241959552272803239

theorem tailTrace_7906051 : CollatzResearch.WordTrace tailWord_7906051 prefixEnd_7906051 4059604241959552272803239 := by
  unfold tailWord_7906051
  simp only [CollatzResearch.WordTrace]
  refine ⟨288357369480734947857334007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192238246320489965238222671 288357369480734947857334007)
  ·
    refine ⟨432536054221102421786001011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288357369480734947857334007 432536054221102421786001011)
    ·
      refine ⟨648804081331653632679001517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432536054221102421786001011 648804081331653632679001517)
      ·
        refine ⟨243301530499370112254625569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648804081331653632679001517 243301530499370112254625569)
        ·
          refine ⟨182476147874527584190969177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243301530499370112254625569 182476147874527584190969177)
          ·
            refine ⟨136857110905895688143226883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182476147874527584190969177 136857110905895688143226883)
            ·
              refine ⟨205285666358843532214840325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136857110905895688143226883 205285666358843532214840325)
              ·
                refine ⟨38491062442283162290282561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205285666358843532214840325 38491062442283162290282561)
                ·
                  refine ⟨28868296831712371717711921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38491062442283162290282561 28868296831712371717711921)
                  ·
                    refine ⟨21651222623784278788283941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28868296831712371717711921 21651222623784278788283941)
                    ·
                      refine ⟨4059604241959552272803239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21651222623784278788283941 4059604241959552272803239)
                      ·
                        rfl

theorem cell23_7906051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_7906051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906051 prefixEnd_7906051 := by exact prefixLift 7906051
  have htrace : WordTrace (prefixWord ++ tailWord_7906051) baseStart_7906051 baseEnd_7906051 := by
    simpa [prefixWord, tailWord_7906051, baseEnd_7906051] using wordTrace_append hprefix tailTrace_7906051
  have hstable : (prefixWord ++ tailWord_7906051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906051).length < 2 ^ (prefixWord ++ tailWord_7906051).sum := by decide
  have hdescent : baseEnd_7906051 < baseStart_7906051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906088 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7906088 : Nat := 118140960795 + 7906088 * 2 ^ 59
def prefixEnd_7906088 : Nat := 4983230072969 + 3 ^ 40 * 7906088 * 2
def baseEnd_7906088 : Nat := 4059623240743768628040569

theorem tailTrace_7906088 : CollatzResearch.WordTrace tailWord_7906088 prefixEnd_7906088 4059623240743768628040569 := by
  unfold tailWord_7906088
  simp only [CollatzResearch.WordTrace]
  refine ⟨144179359490800451588215459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192239145987733935450953945 144179359490800451588215459)
  ·
    refine ⟨216269039236200677382323189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144179359490800451588215459 216269039236200677382323189)
    ·
      refine ⟨20275222428393813504592799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216269039236200677382323189 20275222428393813504592799)
      ·
        refine ⟨30412833642590720256889199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275222428393813504592799 30412833642590720256889199)
        ·
          refine ⟨45619250463886080385333799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30412833642590720256889199 45619250463886080385333799)
          ·
            refine ⟨68428875695829120578000699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45619250463886080385333799 68428875695829120578000699)
            ·
              refine ⟨102643313543743680867001049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68428875695829120578000699 102643313543743680867001049)
              ·
                refine ⟨76982485157807760650250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102643313543743680867001049 76982485157807760650250787)
                ·
                  refine ⟨115473727736711640975376181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76982485157807760650250787 115473727736711640975376181)
                  ·
                    refine ⟨10825661975316716341441517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115473727736711640975376181 10825661975316716341441517)
                    ·
                      refine ⟨4059623240743768628040569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825661975316716341441517 4059623240743768628040569)
                      ·
                        rfl

theorem cell23_7906088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7906088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906088 prefixEnd_7906088 := by exact prefixLift 7906088
  have htrace : WordTrace (prefixWord ++ tailWord_7906088) baseStart_7906088 baseEnd_7906088 := by
    simpa [prefixWord, tailWord_7906088, baseEnd_7906088] using wordTrace_append hprefix tailTrace_7906088
  have hstable : (prefixWord ++ tailWord_7906088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906088).length < 2 ^ (prefixWord ++ tailWord_7906088).sum := by decide
  have hdescent : baseEnd_7906088 < baseStart_7906088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906093 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7906093 : Nat := 118140960795 + 7906093 * 2 ^ 59
def prefixEnd_7906093 : Nat := 4983230072969 + 3 ^ 40 * 7906093 * 2
def baseEnd_7906093 : Nat := 4059625808147041108478047

theorem tailTrace_7906093 : CollatzResearch.WordTrace tailWord_7906093 prefixEnd_7906093 4059625808147041108478047 := by
  unfold tailWord_7906093
  simp only [CollatzResearch.WordTrace]
  refine ⟨288358901346582789030362933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192239267564388526020241955 288358901346582789030362933)
  ·
    refine ⟨27033647001242136471596525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 288358901346582789030362933 27033647001242136471596525)
    ·
      refine ⟨10137617625465801176848697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27033647001242136471596525 10137617625465801176848697)
      ·
        refine ⟨7603213219099350882636523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10137617625465801176848697 7603213219099350882636523)
        ·
          refine ⟨11404819828649026323954785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603213219099350882636523 11404819828649026323954785)
          ·
            refine ⟨8553614871486769742966089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11404819828649026323954785 8553614871486769742966089)
            ·
              refine ⟨6415211153615077307224567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553614871486769742966089 6415211153615077307224567)
              ·
                refine ⟨9622816730422615960836851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415211153615077307224567 9622816730422615960836851)
                ·
                  refine ⟨14434225095633923941255277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9622816730422615960836851 14434225095633923941255277)
                  ·
                    refine ⟨5412834410862721477970729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14434225095633923941255277 5412834410862721477970729)
                    ·
                      refine ⟨4059625808147041108478047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412834410862721477970729 4059625808147041108478047)
                      ·
                        rfl

theorem cell23_7906093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7906093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906093 prefixEnd_7906093 := by exact prefixLift 7906093
  have htrace : WordTrace (prefixWord ++ tailWord_7906093) baseStart_7906093 baseEnd_7906093 := by
    simpa [prefixWord, tailWord_7906093, baseEnd_7906093] using wordTrace_append hprefix tailTrace_7906093
  have hstable : (prefixWord ++ tailWord_7906093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906093).length < 2 ^ (prefixWord ++ tailWord_7906093).sum := by decide
  have hdescent : baseEnd_7906093 < baseStart_7906093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906106 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_7906106 : Nat := 118140960795 + 7906106 * 2 ^ 59
def prefixEnd_7906106 : Nat := 4983230072969 + 3 ^ 40 * 7906106 * 2
def baseEnd_7906106 : Nat := 4059632483395549557615487

theorem tailTrace_7906106 : CollatzResearch.WordTrace tailWord_7906106 prefixEnd_7906106 4059632483395549557615487 := by
  unfold tailWord_7906106
  simp only [CollatzResearch.WordTrace]
  refine ⟨72089843873883923062646543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192239583663690461500390781 72089843873883923062646543)
  ·
    refine ⟨108134765810825884593969815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72089843873883923062646543 108134765810825884593969815)
    ·
      refine ⟨162202148716238826890954723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108134765810825884593969815 162202148716238826890954723)
      ·
        refine ⟨243303223074358240336432085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162202148716238826890954723 243303223074358240336432085)
        ·
          refine ⟨5702419290805271257885127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 243303223074358240336432085 5702419290805271257885127)
          ·
            refine ⟨8553628936207906886827691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702419290805271257885127 8553628936207906886827691)
            ·
              refine ⟨12830443404311860330241537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553628936207906886827691 12830443404311860330241537)
              ·
                refine ⟨9622832553233895247681153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830443404311860330241537 9622832553233895247681153)
                ·
                  refine ⟨7217124414925421435760865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9622832553233895247681153 7217124414925421435760865)
                  ·
                    refine ⟨5412843311194066076820649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217124414925421435760865 5412843311194066076820649)
                    ·
                      refine ⟨4059632483395549557615487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412843311194066076820649 4059632483395549557615487)
                      ·
                        rfl

theorem cell23_7906106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_7906106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906106 prefixEnd_7906106 := by exact prefixLift 7906106
  have htrace : WordTrace (prefixWord ++ tailWord_7906106) baseStart_7906106 baseEnd_7906106 := by
    simpa [prefixWord, tailWord_7906106, baseEnd_7906106] using wordTrace_append hprefix tailTrace_7906106
  have hstable : (prefixWord ++ tailWord_7906106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906106).length < 2 ^ (prefixWord ++ tailWord_7906106).sum := by decide
  have hdescent : baseEnd_7906106 < baseStart_7906106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906165 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7906165 : Nat := 118140960795 + 7906165 * 2 ^ 59
def prefixEnd_7906165 : Nat := 4983230072969 + 3 ^ 40 * 7906165 * 2
def baseEnd_7906165 : Nat := 4059662778754164826777715

theorem tailTrace_7906165 : CollatzResearch.WordTrace tailWord_7906165 prefixEnd_7906165 4059662778754164826777715 := by
  unfold tailWord_7906165
  simp only [CollatzResearch.WordTrace]
  refine ⟨288361527402321945326983949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192241018268214630217989299 288361527402321945326983949)
  ·
    refine ⟨108135572775870729497618981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288361527402321945326983949 108135572775870729497618981)
    ·
      refine ⟨20275419895475761780803559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108135572775870729497618981 20275419895475761780803559)
      ·
        refine ⟨30413129843213642671205339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275419895475761780803559 30413129843213642671205339)
        ·
          refine ⟨45619694764820464006808009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30413129843213642671205339 45619694764820464006808009)
          ·
            refine ⟨34214771073615348005106007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45619694764820464006808009 34214771073615348005106007)
            ·
              refine ⟨51322156610423022007659011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34214771073615348005106007 51322156610423022007659011)
              ·
                refine ⟨76983234915634533011488517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51322156610423022007659011 76983234915634533011488517)
                ·
                  refine ⟨14434356546681474939654097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76983234915634533011488517 14434356546681474939654097)
                  ·
                    refine ⟨10825767410011106204740573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14434356546681474939654097 10825767410011106204740573)
                    ·
                      refine ⟨4059662778754164826777715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825767410011106204740573 4059662778754164826777715)
                      ·
                        rfl

theorem cell23_7906165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7906165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906165 prefixEnd_7906165 := by exact prefixLift 7906165
  have htrace : WordTrace (prefixWord ++ tailWord_7906165) baseStart_7906165 baseEnd_7906165 := by
    simpa [prefixWord, tailWord_7906165, baseEnd_7906165] using wordTrace_append hprefix tailTrace_7906165
  have hstable : (prefixWord ++ tailWord_7906165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906165).length < 2 ^ (prefixWord ++ tailWord_7906165).sum := by decide
  have hdescent : baseEnd_7906165 < baseStart_7906165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906171 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_7906171 : Nat := 118140960795 + 7906171 * 2 ^ 59
def prefixEnd_7906171 : Nat := 4983230072969 + 3 ^ 40 * 7906171 * 2
def baseEnd_7906171 : Nat := 4059665859638091803302687

theorem tailTrace_7906171 : CollatzResearch.WordTrace tailWord_7906171 prefixEnd_7906171 4059665859638091803302687 := by
  unfold tailWord_7906171
  simp only [CollatzResearch.WordTrace]
  refine ⟨288361746240300208351702367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192241164160200138901134911 288361746240300208351702367)
  ·
    refine ⟨432542619360450312527553551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288361746240300208351702367 432542619360450312527553551)
    ·
      refine ⟨648813929040675468791330327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432542619360450312527553551 648813929040675468791330327)
      ·
        refine ⟨973220893561013203186995491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648813929040675468791330327 973220893561013203186995491)
        ·
          refine ⟨1459831340341519804780493237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973220893561013203186995491 1459831340341519804780493237)
          ·
            refine ⟨136859188157017481698171241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1459831340341519804780493237 136859188157017481698171241)
            ·
              refine ⟨102644391117763111273628431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136859188157017481698171241 102644391117763111273628431)
              ·
                refine ⟨153966586676644666910442647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102644391117763111273628431 153966586676644666910442647)
                ·
                  refine ⟨230949880014967000365663971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153966586676644666910442647 230949880014967000365663971)
                  ·
                    refine ⟨346424820022450500548495957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230949880014967000365663971 346424820022450500548495957)
                    ·
                      refine ⟨4059665859638091803302687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 346424820022450500548495957 4059665859638091803302687)
                      ·
                        rfl

theorem cell23_7906171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_7906171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906171 prefixEnd_7906171 := by exact prefixLift 7906171
  have htrace : WordTrace (prefixWord ++ tailWord_7906171) baseStart_7906171 baseEnd_7906171 := by
    simpa [prefixWord, tailWord_7906171, baseEnd_7906171] using wordTrace_append hprefix tailTrace_7906171
  have hstable : (prefixWord ++ tailWord_7906171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906171).length < 2 ^ (prefixWord ++ tailWord_7906171).sum := by decide
  have hdescent : baseEnd_7906171 < baseStart_7906171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906185 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 6]
def baseStart_7906185 : Nat := 118140960795 + 7906185 * 2 ^ 59
def prefixEnd_7906185 : Nat := 4983230072969 + 3 ^ 40 * 7906185 * 2
def baseEnd_7906185 : Nat := 451074783151917194280847

theorem tailTrace_7906185 : CollatzResearch.WordTrace tailWord_7906185 prefixEnd_7906185 451074783151917194280847 := by
  unfold tailWord_7906185
  simp only [CollatzResearch.WordTrace]
  refine ⟨288362256862249488742712009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192241504574832992495141339 288362256862249488742712009)
  ·
    refine ⟨216271692646687116557034007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288362256862249488742712009 216271692646687116557034007)
    ·
      refine ⟨324407538970030674835551011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216271692646687116557034007 324407538970030674835551011)
      ·
        refine ⟨486611308455046012253326517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324407538970030674835551011 486611308455046012253326517)
        ·
          refine ⟨45619810167660563648749361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 486611308455046012253326517 45619810167660563648749361)
          ·
            refine ⟨34214857625745422736562021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45619810167660563648749361 34214857625745422736562021)
            ·
              refine ⟨6415285804827266763105379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34214857625745422736562021 6415285804827266763105379)
              ·
                refine ⟨9622928707240900144658069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415285804827266763105379 9622928707240900144658069)
                ·
                  refine ⟨451074783151917194280847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9622928707240900144658069 451074783151917194280847)
                  ·
                    rfl

theorem cell23_7906185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_7906185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906185 prefixEnd_7906185 := by exact prefixLift 7906185
  have htrace : WordTrace (prefixWord ++ tailWord_7906185) baseStart_7906185 baseEnd_7906185 := by
    simpa [prefixWord, tailWord_7906185, baseEnd_7906185] using wordTrace_append hprefix tailTrace_7906185
  have hstable : (prefixWord ++ tailWord_7906185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906185).length < 2 ^ (prefixWord ++ tailWord_7906185).sum := by decide
  have hdescent : baseEnd_7906185 < baseStart_7906185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906229 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7906229 : Nat := 118140960795 + 7906229 * 2 ^ 59
def prefixEnd_7906229 : Nat := 4983230072969 + 3 ^ 40 * 7906229 * 2
def baseEnd_7906229 : Nat := 4059695641516052576377421

theorem tailTrace_7906229 : CollatzResearch.WordTrace tailWord_7906229 prefixEnd_7906229 4059695641516052576377421 := by
  unfold tailWord_7906229
  simp only [CollatzResearch.WordTrace]
  refine ⟨288363861674090084257313741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192242574449393389504875827 288363861674090084257313741)
  ·
    refine ⟨108136448127783781596492653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288363861674090084257313741 108136448127783781596492653)
    ·
      refine ⟨40551168047918918098684745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108136448127783781596492653 40551168047918918098684745)
      ·
        refine ⟨30413376035939188574013559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40551168047918918098684745 30413376035939188574013559)
        ·
          refine ⟨45620064053908782861020339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30413376035939188574013559 45620064053908782861020339)
          ·
            refine ⟨68430096080863174291530509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45620064053908782861020339 68430096080863174291530509)
            ·
              refine ⟨25661286030323690359323941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68430096080863174291530509 25661286030323690359323941)
              ·
                refine ⟨4811491130685691942373239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25661286030323690359323941 4811491130685691942373239)
                ·
                  refine ⟨7217236696028537913559859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811491130685691942373239 7217236696028537913559859)
                  ·
                    refine ⟨10825855044042806870339789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217236696028537913559859 10825855044042806870339789)
                    ·
                      refine ⟨4059695641516052576377421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825855044042806870339789 4059695641516052576377421)
                      ·
                        rfl

theorem cell23_7906229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7906229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906229 prefixEnd_7906229 := by exact prefixLift 7906229
  have htrace : WordTrace (prefixWord ++ tailWord_7906229) baseStart_7906229 baseEnd_7906229 := by
    simpa [prefixWord, tailWord_7906229, baseEnd_7906229] using wordTrace_append hprefix tailTrace_7906229
  have hstable : (prefixWord ++ tailWord_7906229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906229).length < 2 ^ (prefixWord ++ tailWord_7906229).sum := by decide
  have hdescent : baseEnd_7906229 < baseStart_7906229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906255 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_7906255 : Nat := 118140960795 + 7906255 * 2 ^ 59
def prefixEnd_7906255 : Nat := 4983230072969 + 3 ^ 40 * 7906255 * 2
def baseEnd_7906255 : Nat := 4059708992013069474652301

theorem tailTrace_7906255 : CollatzResearch.WordTrace tailWord_7906255 prefixEnd_7906255 4059708992013069474652301 := by
  unfold tailWord_7906255
  simp only [CollatzResearch.WordTrace]
  refine ⟨288364809971995890697760219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192243206647997260465173479 288364809971995890697760219)
  ·
    refine ⟨432547214957993836046640329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288364809971995890697760219 432547214957993836046640329)
    ·
      refine ⟨324410411218495377034980247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432547214957993836046640329 324410411218495377034980247)
      ·
        refine ⟨486615616827743065552470371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324410411218495377034980247 486615616827743065552470371)
        ·
          refine ⟨729923425241614598328705557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486615616827743065552470371 729923425241614598328705557)
          ·
            refine ⟨34215160558200684296658073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 729923425241614598328705557 34215160558200684296658073)
            ·
              refine ⟨25661370418650513222493555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34215160558200684296658073 25661370418650513222493555)
              ·
                refine ⟨38492055627975769833740333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25661370418650513222493555 38492055627975769833740333)
                ·
                  refine ⟨14434520860490913687652625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38492055627975769833740333 14434520860490913687652625)
                  ·
                    refine ⟨10825890645368185265739469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14434520860490913687652625 10825890645368185265739469)
                    ·
                      refine ⟨4059708992013069474652301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10825890645368185265739469 4059708992013069474652301)
                      ·
                        rfl

theorem cell23_7906255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_7906255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906255 prefixEnd_7906255 := by exact prefixLift 7906255
  have htrace : WordTrace (prefixWord ++ tailWord_7906255) baseStart_7906255 baseEnd_7906255 := by
    simpa [prefixWord, tailWord_7906255, baseEnd_7906255] using wordTrace_append hprefix tailTrace_7906255
  have hstable : (prefixWord ++ tailWord_7906255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906255).length < 2 ^ (prefixWord ++ tailWord_7906255).sum := by decide
  have hdescent : baseEnd_7906255 < baseStart_7906255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906262 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7906262 : Nat := 118140960795 + 7906262 * 2 ^ 59
def prefixEnd_7906262 : Nat := 4983230072969 + 3 ^ 40 * 7906262 * 2
def baseEnd_7906262 : Nat := 1353237528792550315754923

theorem tailTrace_7906262 : CollatzResearch.WordTrace tailWord_7906262 prefixEnd_7906262 1353237528792550315754923 := by
  unfold tailWord_7906262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022816580185658180829065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 192243376855313687262176693 18022816580185658180829065)
  ·
    refine ⟨13517112435139243635621799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18022816580185658180829065 13517112435139243635621799)
    ·
      refine ⟨20275668652708865453432699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13517112435139243635621799 20275668652708865453432699)
      ·
        refine ⟨30413502979063298180149049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275668652708865453432699 30413502979063298180149049)
        ·
          refine ⟨22810127234297473635111787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30413502979063298180149049 22810127234297473635111787)
          ·
            refine ⟨34215190851446210452667681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810127234297473635111787 34215190851446210452667681)
            ·
              refine ⟨25661393138584657839500761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34215190851446210452667681 25661393138584657839500761)
              ·
                refine ⟨19246044853938493379625571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25661393138584657839500761 19246044853938493379625571)
                ·
                  refine ⟨28869067280907740069438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246044853938493379625571 28869067280907740069438357)
                  ·
                    refine ⟨1353237528792550315754923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28869067280907740069438357 1353237528792550315754923)
                    ·
                      rfl

theorem cell23_7906262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7906262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906262 prefixEnd_7906262 := by exact prefixLift 7906262
  have htrace : WordTrace (prefixWord ++ tailWord_7906262) baseStart_7906262 baseEnd_7906262 := by
    simpa [prefixWord, tailWord_7906262, baseEnd_7906262] using wordTrace_append hprefix tailTrace_7906262
  have hstable : (prefixWord ++ tailWord_7906262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906262).length < 2 ^ (prefixWord ++ tailWord_7906262).sum := by decide
  have hdescent : baseEnd_7906262 < baseStart_7906262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906265 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_7906265 : Nat := 118140960795 + 7906265 * 2 ^ 59
def prefixEnd_7906265 : Nat := 4983230072969 + 3 ^ 40 * 7906265 * 2
def baseEnd_7906265 : Nat := 4059714126819614435527255

theorem tailTrace_7906265 : CollatzResearch.WordTrace tailWord_7906265 prefixEnd_7906265 4059714126819614435527255 := by
  unfold tailWord_7906265
  simp only [CollatzResearch.WordTrace]
  refine ⟨288365174701959662405624249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192243449801306441603749499 288365174701959662405624249)
  ·
    refine ⟨216273881026469746804218187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288365174701959662405624249 216273881026469746804218187)
    ·
      refine ⟨324410821539704620206327281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216273881026469746804218187 324410821539704620206327281)
      ·
        refine ⟨243308116154778465154745461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324410821539704620206327281 243308116154778465154745461)
        ·
          refine ⟨22810135889510481108257387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243308116154778465154745461 22810135889510481108257387)
          ·
            refine ⟨34215203834265721662386081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810135889510481108257387 34215203834265721662386081)
            ·
              refine ⟨25661402875699291246789561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34215203834265721662386081 25661402875699291246789561)
              ·
                refine ⟨19246052156774468435092171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25661402875699291246789561 19246052156774468435092171)
                ·
                  refine ⟨28869078235161702652638257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246052156774468435092171 28869078235161702652638257)
                  ·
                    refine ⟨21651808676371276989478693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28869078235161702652638257 21651808676371276989478693)
                    ·
                      refine ⟨4059714126819614435527255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21651808676371276989478693 4059714126819614435527255)
                      ·
                        rfl

theorem cell23_7906265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_7906265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906265 prefixEnd_7906265 := by exact prefixLift 7906265
  have htrace : WordTrace (prefixWord ++ tailWord_7906265) baseStart_7906265 baseEnd_7906265 := by
    simpa [prefixWord, tailWord_7906265, baseEnd_7906265] using wordTrace_append hprefix tailTrace_7906265
  have hstable : (prefixWord ++ tailWord_7906265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906265).length < 2 ^ (prefixWord ++ tailWord_7906265).sum := by decide
  have hdescent : baseEnd_7906265 < baseStart_7906265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906269 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7906269 : Nat := 118140960795 + 7906269 * 2 ^ 59
def prefixEnd_7906269 : Nat := 4983230072969 + 3 ^ 40 * 7906269 * 2
def baseEnd_7906269 : Nat := 4059716180742232419877237

theorem tailTrace_7906269 : CollatzResearch.WordTrace tailWord_7906269 prefixEnd_7906269 4059716180742232419877237 := by
  unfold tailWord_7906269
  simp only [CollatzResearch.WordTrace]
  refine ⟨288365320593945171088769861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192243547062630114059179907 288365320593945171088769861)
  ·
    refine ⟨54068497611364719579144349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288365320593945171088769861 54068497611364719579144349)
    ·
      refine ⟨20275686604261769842179131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54068497611364719579144349 20275686604261769842179131)
      ·
        refine ⟨30413529906392654763268697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275686604261769842179131 30413529906392654763268697)
        ·
          refine ⟨22810147429794491072451523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30413529906392654763268697 22810147429794491072451523)
          ·
            refine ⟨34215221144691736608677285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810147429794491072451523 34215221144691736608677285)
            ·
              refine ⟨6415353964629700614126991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34215221144691736608677285 6415353964629700614126991)
              ·
                refine ⟨9623030946944550921190487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415353964629700614126991 9623030946944550921190487)
                ·
                  refine ⟨14434546420416826381785731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623030946944550921190487 14434546420416826381785731)
                  ·
                    refine ⟨21651819630625239572678597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14434546420416826381785731 21651819630625239572678597)
                    ·
                      refine ⟨4059716180742232419877237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21651819630625239572678597 4059716180742232419877237)
                      ·
                        rfl

theorem cell23_7906269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7906269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906269 prefixEnd_7906269 := by exact prefixLift 7906269
  have htrace : WordTrace (prefixWord ++ tailWord_7906269) baseStart_7906269 baseEnd_7906269 := by
    simpa [prefixWord, tailWord_7906269, baseEnd_7906269] using wordTrace_append hprefix tailTrace_7906269
  have hstable : (prefixWord ++ tailWord_7906269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906269).length < 2 ^ (prefixWord ++ tailWord_7906269).sum := by decide
  have hdescent : baseEnd_7906269 < baseStart_7906269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906279 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 2, 4]
def baseStart_7906279 : Nat := 118140960795 + 7906279 * 2 ^ 59
def prefixEnd_7906279 : Nat := 4983230072969 + 3 ^ 40 * 7906279 * 2
def baseEnd_7906279 : Nat := 1353240438516259126917397

theorem tailTrace_7906279 : CollatzResearch.WordTrace tailWord_7906279 prefixEnd_7906279 1353240438516259126917397 := by
  unfold tailWord_7906279
  simp only [CollatzResearch.WordTrace]
  refine ⟨288365685323908942796633891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192243790215939295197755927 288365685323908942796633891)
  ·
    refine ⟨432548527985863414194950837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288365685323908942796633891 432548527985863414194950837)
    ·
      refine ⟨40551424498674695080776641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 432548527985863414194950837 40551424498674695080776641)
      ·
        refine ⟨30413568374006021310582481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40551424498674695080776641 30413568374006021310582481)
        ·
          refine ⟨22810176280504515982936861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30413568374006021310582481 22810176280504515982936861)
          ·
            refine ⟨8553816105189193493601323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22810176280504515982936861 8553816105189193493601323)
            ·
              refine ⟨12830724157783790240401985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553816105189193493601323 12830724157783790240401985)
              ·
                refine ⟨9623043118337842680301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830724157783790240401985 9623043118337842680301489)
                ·
                  refine ⟨7217282338753382010226117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623043118337842680301489 7217282338753382010226117)
                  ·
                    refine ⟨1353240438516259126917397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217282338753382010226117 1353240438516259126917397)
                    ·
                      rfl

theorem cell23_7906279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_7906279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906279 prefixEnd_7906279 := by exact prefixLift 7906279
  have htrace : WordTrace (prefixWord ++ tailWord_7906279) baseStart_7906279 baseEnd_7906279 := by
    simpa [prefixWord, tailWord_7906279, baseEnd_7906279] using wordTrace_append hprefix tailTrace_7906279
  have hstable : (prefixWord ++ tailWord_7906279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906279).length < 2 ^ (prefixWord ++ tailWord_7906279).sum := by decide
  have hdescent : baseEnd_7906279 < baseStart_7906279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906286 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_7906286 : Nat := 118140960795 + 7906286 * 2 ^ 59
def prefixEnd_7906286 : Nat := 4983230072969 + 3 ^ 40 * 7906286 * 2
def baseEnd_7906286 : Nat := 4059724909913358853364659

theorem tailTrace_7906286 : CollatzResearch.WordTrace tailWord_7906286 prefixEnd_7906286 4059724909913358853364659 := by
  unfold tailWord_7906286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36045742579360447874017339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192243960423255721994759141 36045742579360447874017339)
  ·
    refine ⟨54068613869040671811026009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36045742579360447874017339 54068613869040671811026009)
    ·
      refine ⟨40551460401780503858269507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54068613869040671811026009 40551460401780503858269507)
      ·
        refine ⟨60827190602670755787404261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40551460401780503858269507 60827190602670755787404261)
        ·
          refine ⟨11405098238000766710138299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60827190602670755787404261 11405098238000766710138299)
          ·
            refine ⟨17107647357001150065207449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11405098238000766710138299 17107647357001150065207449)
            ·
              refine ⟨12830735517750862548905587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17107647357001150065207449 12830735517750862548905587)
              ·
                refine ⟨19246103276626293823358381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12830735517750862548905587 19246103276626293823358381)
                ·
                  refine ⟨7217288728734860183759393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19246103276626293823358381 7217288728734860183759393)
                  ·
                    refine ⟨5412966546551145137819545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217288728734860183759393 5412966546551145137819545)
                    ·
                      refine ⟨4059724909913358853364659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5412966546551145137819545 4059724909913358853364659)
                      ·
                        rfl

theorem cell23_7906286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_7906286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906286 prefixEnd_7906286 := by exact prefixLift 7906286
  have htrace : WordTrace (prefixWord ++ tailWord_7906286) baseStart_7906286 baseEnd_7906286 := by
    simpa [prefixWord, tailWord_7906286, baseEnd_7906286] using wordTrace_append hprefix tailTrace_7906286
  have hstable : (prefixWord ++ tailWord_7906286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906286).length < 2 ^ (prefixWord ++ tailWord_7906286).sum := by decide
  have hdescent : baseEnd_7906286 < baseStart_7906286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906298 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_7906298 : Nat := 118140960795 + 7906298 * 2 ^ 59
def prefixEnd_7906298 : Nat := 4983230072969 + 3 ^ 40 * 7906298 * 2
def baseEnd_7906298 : Nat := 4059731071681212806414603

theorem tailTrace_7906298 : CollatzResearch.WordTrace tailWord_7906298 prefixEnd_7906298 4059731071681212806414603 := by
  unfold tailWord_7906298
  simp only [CollatzResearch.WordTrace]
  refine ⟨72091594577710027260393887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192244252207226739361050365 72091594577710027260393887)
  ·
    refine ⟨108137391866565040890590831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72091594577710027260393887 108137391866565040890590831)
    ·
      refine ⟨162206087799847561335886247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108137391866565040890590831 162206087799847561335886247)
      ·
        refine ⟨243309131699771342003829371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162206087799847561335886247 243309131699771342003829371)
        ·
          refine ⟨364963697549657013005744057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243309131699771342003829371 364963697549657013005744057)
          ·
            refine ⟨273722773162242759754308043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364963697549657013005744057 273722773162242759754308043)
            ·
              refine ⟨410584159743364139631462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273722773162242759754308043 410584159743364139631462065)
              ·
                refine ⟨307938119807523104723596549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410584159743364139631462065 307938119807523104723596549)
                ·
                  refine ⟨57738397463910582135674353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307938119807523104723596549 57738397463910582135674353)
                  ·
                    refine ⟨43303798097932936601755765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57738397463910582135674353 43303798097932936601755765)
                    ·
                      refine ⟨4059731071681212806414603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43303798097932936601755765 4059731071681212806414603)
                      ·
                        rfl

theorem cell23_7906298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_7906298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906298 prefixEnd_7906298 := by exact prefixLift 7906298
  have htrace : WordTrace (prefixWord ++ tailWord_7906298) baseStart_7906298 baseEnd_7906298 := by
    simpa [prefixWord, tailWord_7906298, baseEnd_7906298] using wordTrace_append hprefix tailTrace_7906298
  have hstable : (prefixWord ++ tailWord_7906298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906298).length < 2 ^ (prefixWord ++ tailWord_7906298).sum := by decide
  have hdescent : baseEnd_7906298 < baseStart_7906298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906382 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_7906382 : Nat := 118140960795 + 7906382 * 2 ^ 59
def prefixEnd_7906382 : Nat := 4983230072969 + 3 ^ 40 * 7906382 * 2
def baseEnd_7906382 : Nat := 451086022672910053084913

theorem tailTrace_7906382 : CollatzResearch.WordTrace tailWord_7906382 prefixEnd_7906382 451086022672910053084913 := by
  unfold tailWord_7906382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046180255316973923454175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192246294695023860925088933 36046180255316973923454175)
  ·
    refine ⟨54069270382975460885181263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36046180255316973923454175 54069270382975460885181263)
    ·
      refine ⟨81103905574463191327771895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54069270382975460885181263 81103905574463191327771895)
      ·
        refine ⟨121655858361694786991657843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81103905574463191327771895 121655858361694786991657843)
        ·
          refine ⟨182483787542542180487486765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121655858361694786991657843 182483787542542180487486765)
          ·
            refine ⟨68431420328453317682807537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182483787542542180487486765 68431420328453317682807537)
            ·
              refine ⟨51323565246339988262105653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68431420328453317682807537 51323565246339988262105653)
              ·
                refine ⟨4811584241844373899572405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51323565246339988262105653 4811584241844373899572405)
                ·
                  refine ⟨451086022672910053084913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811584241844373899572405 451086022672910053084913)
                  ·
                    rfl

theorem cell23_7906382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_7906382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906382 prefixEnd_7906382 := by exact prefixLift 7906382
  have htrace : WordTrace (prefixWord ++ tailWord_7906382) baseStart_7906382 baseEnd_7906382 := by
    simpa [prefixWord, tailWord_7906382, baseEnd_7906382] using wordTrace_append hprefix tailTrace_7906382
  have hstable : (prefixWord ++ tailWord_7906382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906382).length < 2 ^ (prefixWord ++ tailWord_7906382).sum := by decide
  have hdescent : baseEnd_7906382 < baseStart_7906382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906405 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7906405 : Nat := 118140960795 + 7906405 * 2 ^ 59
def prefixEnd_7906405 : Nat := 4983230072969 + 3 ^ 40 * 7906405 * 2
def baseEnd_7906405 : Nat := 4059786014111243887776611

theorem tailTrace_7906405 : CollatzResearch.WordTrace tailWord_7906405 prefixEnd_7906405 4059786014111243887776611 := by
  unfold tailWord_7906405
  simp only [CollatzResearch.WordTrace]
  refine ⟨288370280921452466315720669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192246853947634977543813779 288370280921452466315720669)
  ·
    refine ⟨108138855345544674868395251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288370280921452466315720669 108138855345544674868395251)
    ·
      refine ⟨162208283018317012302592877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108138855345544674868395251 162208283018317012302592877)
      ·
        refine ⟨60828106131868879613472329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162208283018317012302592877 60828106131868879613472329)
        ·
          refine ⟨45621079598901659710104247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60828106131868879613472329 45621079598901659710104247)
          ·
            refine ⟨68431619398352489565156371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45621079598901659710104247 68431619398352489565156371)
            ·
              refine ⟨102647429097528734347734557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68431619398352489565156371 102647429097528734347734557)
              ·
                refine ⟨38492785911573275380400459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102647429097528734347734557 38492785911573275380400459)
                ·
                  refine ⟨57739178867359913070600689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38492785911573275380400459 57739178867359913070600689)
                  ·
                    refine ⟨43304384150519934802950517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57739178867359913070600689 43304384150519934802950517)
                    ·
                      refine ⟨4059786014111243887776611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43304384150519934802950517 4059786014111243887776611)
                      ·
                        rfl

theorem cell23_7906405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7906405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906405 prefixEnd_7906405 := by exact prefixLift 7906405
  have htrace : WordTrace (prefixWord ++ tailWord_7906405) baseStart_7906405 baseEnd_7906405 := by
    simpa [prefixWord, tailWord_7906405, baseEnd_7906405] using wordTrace_append hprefix tailTrace_7906405
  have hstable : (prefixWord ++ tailWord_7906405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906405).length < 2 ^ (prefixWord ++ tailWord_7906405).sum := by decide
  have hdescent : baseEnd_7906405 < baseStart_7906405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906415 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_7906415 : Nat := 118140960795 + 7906415 * 2 ^ 59
def prefixEnd_7906415 : Nat := 4983230072969 + 3 ^ 40 * 7906415 * 2
def baseEnd_7906415 : Nat := 4059791148917788848651565

theorem tailTrace_7906415 : CollatzResearch.WordTrace tailWord_7906415 prefixEnd_7906415 4059791148917788848651565 := by
  unfold tailWord_7906415
  simp only [CollatzResearch.WordTrace]
  refine ⟨288370645651416238023584699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192247097100944158682389799 288370645651416238023584699)
  ·
    refine ⟨432555968477124357035377049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288370645651416238023584699 432555968477124357035377049)
    ·
      refine ⟨324416976357843267776532787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432555968477124357035377049 324416976357843267776532787)
      ·
        refine ⟨486625464536764901664799181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324416976357843267776532787 486625464536764901664799181)
        ·
          refine ⟨182484549201286838124299693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486625464536764901664799181 182484549201286838124299693)
          ·
            refine ⟨68431705950482564296612385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182484549201286838124299693 68431705950482564296612385)
            ·
              refine ⟨51323779462861923222459289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68431705950482564296612385 51323779462861923222459289)
              ·
                refine ⟨38492834597146442416844467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51323779462861923222459289 38492834597146442416844467)
                ·
                  refine ⟨57739251895719663625266701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38492834597146442416844467 57739251895719663625266701)
                  ·
                    refine ⟨21652219460894873859475013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57739251895719663625266701 21652219460894873859475013)
                    ·
                      refine ⟨4059791148917788848651565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21652219460894873859475013 4059791148917788848651565)
                      ·
                        rfl

theorem cell23_7906415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_7906415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906415 prefixEnd_7906415 := by exact prefixLift 7906415
  have htrace : WordTrace (prefixWord ++ tailWord_7906415) baseStart_7906415 baseEnd_7906415 := by
    simpa [prefixWord, tailWord_7906415, baseEnd_7906415] using wordTrace_append hprefix tailTrace_7906415
  have hstable : (prefixWord ++ tailWord_7906415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906415).length < 2 ^ (prefixWord ++ tailWord_7906415).sum := by decide
  have hdescent : baseEnd_7906415 < baseStart_7906415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906432 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_7906432 : Nat := 118140960795 + 7906432 * 2 ^ 59
def prefixEnd_7906432 : Nat := 4983230072969 + 3 ^ 40 * 7906432 * 2
def baseEnd_7906432 : Nat := 4059799878088915282138987

theorem tailTrace_7906432 : CollatzResearch.WordTrace tailWord_7906432 prefixEnd_7906432 4059799878088915282138987 := by
  unfold tailWord_7906432
  simp only [CollatzResearch.WordTrace]
  refine ⟨144185632846177324963476775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192247510461569766617969033 144185632846177324963476775)
  ·
    refine ⟨216278449269265987445215163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144185632846177324963476775 216278449269265987445215163)
    ·
      refine ⟨324417673903898981167822745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216278449269265987445215163 324417673903898981167822745)
      ·
        refine ⟨243313255427924235875867059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324417673903898981167822745 243313255427924235875867059)
        ·
          refine ⟨364969883141886353813800589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243313255427924235875867059 364969883141886353813800589)
          ·
            refine ⟨136863706178207382680175221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 364969883141886353813800589 136863706178207382680175221)
            ·
              refine ⟨12830972454206942126266427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136863706178207382680175221 12830972454206942126266427)
              ·
                refine ⟨19246458681310413189399641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12830972454206942126266427 19246458681310413189399641)
                ·
                  refine ⟨14434844010982809892049731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19246458681310413189399641 14434844010982809892049731)
                  ·
                    refine ⟨21652266016474214838074597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14434844010982809892049731 21652266016474214838074597)
                    ·
                      refine ⟨4059799878088915282138987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21652266016474214838074597 4059799878088915282138987)
                      ·
                        rfl

theorem cell23_7906432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_7906432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906432 prefixEnd_7906432 := by exact prefixLift 7906432
  have htrace : WordTrace (prefixWord ++ tailWord_7906432) baseStart_7906432 baseEnd_7906432 := by
    simpa [prefixWord, tailWord_7906432, baseEnd_7906432] using wordTrace_append hprefix tailTrace_7906432
  have hstable : (prefixWord ++ tailWord_7906432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906432).length < 2 ^ (prefixWord ++ tailWord_7906432).sum := by decide
  have hdescent : baseEnd_7906432 < baseStart_7906432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906442 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_7906442 : Nat := 118140960795 + 7906442 * 2 ^ 59
def prefixEnd_7906442 : Nat := 4983230072969 + 3 ^ 40 * 7906442 * 2
def baseEnd_7906442 : Nat := 1353268337631820081004647

theorem tailTrace_7906442 : CollatzResearch.WordTrace tailWord_7906442 prefixEnd_7906442 1353268337631820081004647 := by
  unfold tailWord_7906442
  simp only [CollatzResearch.WordTrace]
  refine ⟨72092907605579605408704395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192247753614878947756545053 72092907605579605408704395)
  ·
    refine ⟨108139361408369408113056593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72092907605579605408704395 108139361408369408113056593)
    ·
      refine ⟨81104521056277056084792445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108139361408369408113056593 81104521056277056084792445)
      ·
        refine ⟨30414195396103896031797167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81104521056277056084792445 30414195396103896031797167)
        ·
          refine ⟨45621293094155844047695751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30414195396103896031797167 45621293094155844047695751)
          ·
            refine ⟨68431939641233766071543627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45621293094155844047695751 68431939641233766071543627)
            ·
              refine ⟨102647909461850649107315441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68431939641233766071543627 102647909461850649107315441)
              ·
                refine ⟨76985932096387986830486581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102647909461850649107315441 76985932096387986830486581)
                ·
                  refine ⟨7217431134036373765358117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76985932096387986830486581 7217431134036373765358117)
                  ·
                    refine ⟨1353268337631820081004647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217431134036373765358117 1353268337631820081004647)
                    ·
                      rfl

theorem cell23_7906442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_7906442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906442 prefixEnd_7906442 := by exact prefixLift 7906442
  have htrace : WordTrace (prefixWord ++ tailWord_7906442) baseStart_7906442 baseEnd_7906442 := by
    simpa [prefixWord, tailWord_7906442, baseEnd_7906442] using wordTrace_append hprefix tailTrace_7906442
  have hstable : (prefixWord ++ tailWord_7906442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906442).length < 2 ^ (prefixWord ++ tailWord_7906442).sum := by decide
  have hdescent : baseEnd_7906442 < baseStart_7906442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906505 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_7906505 : Nat := 118140960795 + 7906505 * 2 ^ 59
def prefixEnd_7906505 : Nat := 4983230072969 + 3 ^ 40 * 7906505 * 2
def baseEnd_7906505 : Nat := 4059837362176693496526151

theorem tailTrace_7906505 : CollatzResearch.WordTrace tailWord_7906505 prefixEnd_7906505 4059837362176693496526151 := by
  unfold tailWord_7906505
  simp only [CollatzResearch.WordTrace]
  refine ⟨288373928221090183394360969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192249285480726788929573979 288373928221090183394360969)
  ·
    refine ⟨216280446165817637545770727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288373928221090183394360969 216280446165817637545770727)
    ·
      refine ⟨324420669248726456318656091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216280446165817637545770727 324420669248726456318656091)
      ·
        refine ⟨486631003873089684477984137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324420669248726456318656091 486631003873089684477984137)
        ·
          refine ⟨364973252904817263358488103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486631003873089684477984137 364973252904817263358488103)
          ·
            refine ⟨547459879357225895037732155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364973252904817263358488103 547459879357225895037732155)
            ·
              refine ⟨821189819035838842556598233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547459879357225895037732155 821189819035838842556598233)
              ·
                refine ⟨615892364276879131917448675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821189819035838842556598233 615892364276879131917448675)
                ·
                  refine ⟨923838546415318697876173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615892364276879131917448675 923838546415318697876173013)
                  ·
                    refine ⟨21652465931609031981472805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 923838546415318697876173013 21652465931609031981472805)
                    ·
                      refine ⟨4059837362176693496526151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21652465931609031981472805 4059837362176693496526151)
                      ·
                        rfl

theorem cell23_7906505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_7906505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906505 prefixEnd_7906505 := by exact prefixLift 7906505
  have htrace : WordTrace (prefixWord ++ tailWord_7906505) baseStart_7906505 baseEnd_7906505 := by
    simpa [prefixWord, tailWord_7906505, baseEnd_7906505] using wordTrace_append hprefix tailTrace_7906505
  have hstable : (prefixWord ++ tailWord_7906505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906505).length < 2 ^ (prefixWord ++ tailWord_7906505).sum := by decide
  have hdescent : baseEnd_7906505 < baseStart_7906505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906515 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 3, 6]
def baseStart_7906515 : Nat := 118140960795 + 7906515 * 2 ^ 59
def prefixEnd_7906515 : Nat := 4983230072969 + 3 ^ 40 * 7906515 * 2
def baseEnd_7906515 : Nat := 1353280832327746152467035

theorem tailTrace_7906515 : CollatzResearch.WordTrace tailWord_7906515 prefixEnd_7906515 1353280832327746152467035 := by
  unfold tailWord_7906515
  simp only [CollatzResearch.WordTrace]
  refine ⟨288374292951053955102224999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192249528634035970068149999 288374292951053955102224999)
  ·
    refine ⟨432561439426580932653337499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288374292951053955102224999 432561439426580932653337499)
    ·
      refine ⟨648842159139871398980006249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432561439426580932653337499 648842159139871398980006249)
      ·
        refine ⟨486631619354903549235004687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648842159139871398980006249 486631619354903549235004687)
        ·
          refine ⟨729947429032355323852507031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486631619354903549235004687 729947429032355323852507031)
          ·
            refine ⟨1094921143548532985778760547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729947429032355323852507031 1094921143548532985778760547)
            ·
              refine ⟨1642381715322799478668140821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094921143548532985778760547 1642381715322799478668140821)
              ·
                refine ⟨76986642905756225562569101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1642381715322799478668140821 76986642905756225562569101)
                ·
                  refine ⟨28869991089658584585963413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76986642905756225562569101 28869991089658584585963413)
                  ·
                    refine ⟨1353280832327746152467035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28869991089658584585963413 1353280832327746152467035)
                    ·
                      rfl

theorem cell23_7906515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_7906515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906515 prefixEnd_7906515 := by exact prefixLift 7906515
  have htrace : WordTrace (prefixWord ++ tailWord_7906515) baseStart_7906515 baseEnd_7906515 := by
    simpa [prefixWord, tailWord_7906515, baseEnd_7906515] using wordTrace_append hprefix tailTrace_7906515
  have hstable : (prefixWord ++ tailWord_7906515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906515).length < 2 ^ (prefixWord ++ tailWord_7906515).sum := by decide
  have hdescent : baseEnd_7906515 < baseStart_7906515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906522 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_7906522 : Nat := 118140960795 + 7906522 * 2 ^ 59
def prefixEnd_7906522 : Nat := 4983230072969 + 3 ^ 40 * 7906522 * 2
def baseEnd_7906522 : Nat := 4059846091347819930013573

theorem tailTrace_7906522 : CollatzResearch.WordTrace tailWord_7906522 prefixEnd_7906522 4059846091347819930013573 := by
  unfold tailWord_7906522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72093637065507148824432455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192249698841352396865153213 72093637065507148824432455)
  ·
    refine ⟨108140455598260723236648683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72093637065507148824432455 108140455598260723236648683)
    ·
      refine ⟨162210683397391084854973025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108140455598260723236648683 162210683397391084854973025)
      ·
        refine ⟨121658012548043313641229769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162210683397391084854973025 121658012548043313641229769)
        ·
          refine ⟨91243509411032485230922327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121658012548043313641229769 91243509411032485230922327)
          ·
            refine ⟨136865264116548727846383491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91243509411032485230922327 136865264116548727846383491)
            ·
              refine ⟨205297896174823091769575237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136865264116548727846383491 205297896174823091769575237)
              ·
                refine ⟨38493355532779329706795357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205297896174823091769575237 38493355532779329706795357)
                ·
                  refine ⟨14435008324792248640048259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38493355532779329706795357 14435008324792248640048259)
                  ·
                    refine ⟨21652512487188372960072389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14435008324792248640048259 21652512487188372960072389)
                    ·
                      refine ⟨4059846091347819930013573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21652512487188372960072389 4059846091347819930013573)
                      ·
                        rfl

theorem cell23_7906522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_7906522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906522 prefixEnd_7906522 := by exact prefixLift 7906522
  have htrace : WordTrace (prefixWord ++ tailWord_7906522) baseStart_7906522 baseEnd_7906522 := by
    simpa [prefixWord, tailWord_7906522, baseEnd_7906522] using wordTrace_append hprefix tailTrace_7906522
  have hstable : (prefixWord ++ tailWord_7906522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906522).length < 2 ^ (prefixWord ++ tailWord_7906522).sum := by decide
  have hdescent : baseEnd_7906522 < baseStart_7906522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906539 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 4]
def baseStart_7906539 : Nat := 118140960795 + 7906539 * 2 ^ 59
def prefixEnd_7906539 : Nat := 4983230072969 + 3 ^ 40 * 7906539 * 2
def baseEnd_7906539 : Nat := 4059854820518946363500995

theorem tailTrace_7906539 : CollatzResearch.WordTrace tailWord_7906539 prefixEnd_7906539 4059854820518946363500995 := by
  unfold tailWord_7906539
  simp only [CollatzResearch.WordTrace]
  refine ⟨288375168302967007201098671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192250112201978004800732447 288375168302967007201098671)
  ·
    refine ⟨432562752454450510801648007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288375168302967007201098671 432562752454450510801648007)
    ·
      refine ⟨648844128681675766202472011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432562752454450510801648007 648844128681675766202472011)
      ·
        refine ⟨973266193022513649303708017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648844128681675766202472011 973266193022513649303708017)
        ·
          refine ⟨729949644766885236977781013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973266193022513649303708017 729949644766885236977781013)
          ·
            refine ⟨34216389598447745483333485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 729949644766885236977781013 34216389598447745483333485)
            ·
              refine ⟨12831146099417904556250057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34216389598447745483333485 12831146099417904556250057)
              ·
                refine ⟨9623359574563428417187543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12831146099417904556250057 9623359574563428417187543)
                ·
                  refine ⟨14435039361845142625781315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623359574563428417187543 14435039361845142625781315)
                  ·
                    refine ⟨21652559042767713938671973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14435039361845142625781315 21652559042767713938671973)
                    ·
                      refine ⟨4059854820518946363500995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21652559042767713938671973 4059854820518946363500995)
                      ·
                        rfl

theorem cell23_7906539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 4].length) (baseStart_7906539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906539 prefixEnd_7906539 := by exact prefixLift 7906539
  have htrace : WordTrace (prefixWord ++ tailWord_7906539) baseStart_7906539 baseEnd_7906539 := by
    simpa [prefixWord, tailWord_7906539, baseEnd_7906539] using wordTrace_append hprefix tailTrace_7906539
  have hstable : (prefixWord ++ tailWord_7906539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906539).length < 2 ^ (prefixWord ++ tailWord_7906539).sum := by decide
  have hdescent : baseEnd_7906539 < baseStart_7906539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906542 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7906542 : Nat := 118140960795 + 7906542 * 2 ^ 59
def prefixEnd_7906542 : Nat := 4983230072969 + 3 ^ 40 * 7906542 * 2
def baseEnd_7906542 : Nat := 4059856360960909851763481

theorem tailTrace_7906542 : CollatzResearch.WordTrace tailWord_7906542 prefixEnd_7906542 4059856360960909851763481 := by
  unfold tailWord_7906542
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046909715244517339182235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 192250185147970759142305253 36046909715244517339182235)
  ·
    refine ⟨54070364572866776008773353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36046909715244517339182235 54070364572866776008773353)
    ·
      refine ⟨40552773429650082006580015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54070364572866776008773353 40552773429650082006580015)
      ·
        refine ⟨60829160144475123009870023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40552773429650082006580015 60829160144475123009870023)
        ·
          refine ⟨91243740216712684514805035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60829160144475123009870023 91243740216712684514805035)
          ·
            refine ⟨136865610325069026772207553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91243740216712684514805035 136865610325069026772207553)
            ·
              refine ⟨102649207743801770079155665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136865610325069026772207553 102649207743801770079155665)
              ·
                refine ⟨76986905807851327559366749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102649207743801770079155665 76986905807851327559366749)
                ·
                  refine ⟨28870089677944247834762531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76986905807851327559366749 28870089677944247834762531)
                  ·
                    refine ⟨43305134516916371752143797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870089677944247834762531 43305134516916371752143797)
                    ·
                      refine ⟨4059856360960909851763481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43305134516916371752143797 4059856360960909851763481)
                      ·
                        rfl

theorem cell23_7906542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7906542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906542 prefixEnd_7906542 := by exact prefixLift 7906542
  have htrace : WordTrace (prefixWord ++ tailWord_7906542) baseStart_7906542 baseEnd_7906542 := by
    simpa [prefixWord, tailWord_7906542, baseEnd_7906542] using wordTrace_append hprefix tailTrace_7906542
  have hstable : (prefixWord ++ tailWord_7906542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906542).length < 2 ^ (prefixWord ++ tailWord_7906542).sum := by decide
  have hdescent : baseEnd_7906542 < baseStart_7906542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906559 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_7906559 : Nat := 118140960795 + 7906559 * 2 ^ 59
def prefixEnd_7906559 : Nat := 4983230072969 + 3 ^ 40 * 7906559 * 2
def baseEnd_7906559 : Nat := 4059865090132036285250903

theorem tailTrace_7906559 : CollatzResearch.WordTrace tailWord_7906559 prefixEnd_7906559 4059865090132036285250903 := by
  unfold tailWord_7906559
  simp only [CollatzResearch.WordTrace]
  refine ⟨288375897762894550616826731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192250598508596367077884487 288375897762894550616826731)
  ·
    refine ⟨432563846644341825925240097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288375897762894550616826731 432563846644341825925240097)
    ·
      refine ⟨324422884983256369443930073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432563846644341825925240097 324422884983256369443930073)
      ·
        refine ⟨243317163737442277082947555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324422884983256369443930073 243317163737442277082947555)
        ·
          refine ⟨364975745606163415624421333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243317163737442277082947555 364975745606163415624421333)
          ·
            refine ⟨8554119037644455053697375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364975745606163415624421333 8554119037644455053697375)
            ·
              refine ⟨12831178556466682580546063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554119037644455053697375 12831178556466682580546063)
              ·
                refine ⟨19246767834700023870819095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12831178556466682580546063 19246767834700023870819095)
                ·
                  refine ⟨28870151752050035806228643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246767834700023870819095 28870151752050035806228643)
                  ·
                    refine ⟨43305227628075053709342965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870151752050035806228643 43305227628075053709342965)
                    ·
                      refine ⟨4059865090132036285250903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43305227628075053709342965 4059865090132036285250903)
                      ·
                        rfl

theorem cell23_7906559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_7906559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906559 prefixEnd_7906559 := by exact prefixLift 7906559
  have htrace : WordTrace (prefixWord ++ tailWord_7906559) baseStart_7906559 baseEnd_7906559 := by
    simpa [prefixWord, tailWord_7906559, baseEnd_7906559] using wordTrace_append hprefix tailTrace_7906559
  have hstable : (prefixWord ++ tailWord_7906559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906559).length < 2 ^ (prefixWord ++ tailWord_7906559).sum := by decide
  have hdescent : baseEnd_7906559 < baseStart_7906559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906562 : List Nat := [3, 4, 1, 1, 14]
def baseStart_7906562 : Nat := 118140960795 + 7906562 * 2 ^ 59
def prefixEnd_7906562 : Nat := 4983230072969 + 3 ^ 40 * 7906562 * 2
def baseEnd_7906562 : Nat := 5569090028222221911541

theorem tailTrace_7906562 : CollatzResearch.WordTrace tailWord_7906562 prefixEnd_7906562 5569090028222221911541 := by
  unfold tailWord_7906562
  simp only [CollatzResearch.WordTrace]
  refine ⟨72094001795470920532296485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192250671454589121419457293 72094001795470920532296485)
  ·
    refine ⟨13517625336650797599805591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72094001795470920532296485 13517625336650797599805591)
    ·
      refine ⟨20276438004976196399708387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13517625336650797599805591 20276438004976196399708387)
      ·
        refine ⟨30414657007464294599562581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276438004976196399708387 30414657007464294599562581)
        ·
          refine ⟨5569090028222221911541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 30414657007464294599562581 5569090028222221911541)
          ·
            rfl

theorem cell23_7906562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 14].length) (baseStart_7906562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906562 prefixEnd_7906562 := by exact prefixLift 7906562
  have htrace : WordTrace (prefixWord ++ tailWord_7906562) baseStart_7906562 baseEnd_7906562 := by
    simpa [prefixWord, tailWord_7906562, baseEnd_7906562] using wordTrace_append hprefix tailTrace_7906562
  have hstable : (prefixWord ++ tailWord_7906562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906562).length < 2 ^ (prefixWord ++ tailWord_7906562).sum := by decide
  have hdescent : baseEnd_7906562 < baseStart_7906562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906623 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_7906623 : Nat := 118140960795 + 7906623 * 2 ^ 59
def prefixEnd_7906623 : Nat := 4983230072969 + 3 ^ 40 * 7906623 * 2
def baseEnd_7906623 : Nat := 4059897952893924034850609

theorem tailTrace_7906623 : CollatzResearch.WordTrace tailWord_7906623 prefixEnd_7906623 4059897952893924034850609 := by
  unfold tailWord_7906623
  simp only [CollatzResearch.WordTrace]
  refine ⟨288378232034662689547156523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192252154689775126364771015 288378232034662689547156523)
  ·
    refine ⟨432567348051994034320734785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288378232034662689547156523 432567348051994034320734785)
    ·
      refine ⟨324425511038995525740551089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 432567348051994034320734785 324425511038995525740551089)
      ·
        refine ⟨243319133279246644305413317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324425511038995525740551089 243319133279246644305413317)
        ·
          refine ⟨45622337489858745807264997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243319133279246644305413317 45622337489858745807264997)
          ·
            refine ⟨8554188279348514838862187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45622337489858745807264997 8554188279348514838862187)
            ·
              refine ⟨12831282419022772258293281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554188279348514838862187 12831282419022772258293281)
              ·
                refine ⟨9623461814267079193719961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12831282419022772258293281 9623461814267079193719961)
                ·
                  refine ⟨7217596360700309395289971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623461814267079193719961 7217596360700309395289971)
                  ·
                    refine ⟨10826394541050464092934957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217596360700309395289971 10826394541050464092934957)
                    ·
                      refine ⟨4059897952893924034850609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10826394541050464092934957 4059897952893924034850609)
                      ·
                        rfl

theorem cell23_7906623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_7906623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906623 prefixEnd_7906623 := by exact prefixLift 7906623
  have htrace : WordTrace (prefixWord ++ tailWord_7906623) baseStart_7906623 baseEnd_7906623 := by
    simpa [prefixWord, tailWord_7906623, baseEnd_7906623] using wordTrace_append hprefix tailTrace_7906623
  have hstable : (prefixWord ++ tailWord_7906623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906623).length < 2 ^ (prefixWord ++ tailWord_7906623).sum := by decide
  have hdescent : baseEnd_7906623 < baseStart_7906623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906629 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_7906629 : Nat := 118140960795 + 7906629 * 2 ^ 59
def prefixEnd_7906629 : Nat := 4983230072969 + 3 ^ 40 * 7906629 * 2
def baseEnd_7906629 : Nat := 4059901033777851011375581

theorem tailTrace_7906629 : CollatzResearch.WordTrace tailWord_7906629 prefixEnd_7906629 4059901033777851011375581 := by
  unfold tailWord_7906629
  simp only [CollatzResearch.WordTrace]
  refine ⟨288378450872640952571874941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192252300581760635047916627 288378450872640952571874941)
  ·
    refine ⟨108141919077240357214453103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288378450872640952571874941 108141919077240357214453103)
    ·
      refine ⟨162212878615860535821679655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108141919077240357214453103 162212878615860535821679655)
      ·
        refine ⟨243319317923790803732519483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162212878615860535821679655 243319317923790803732519483)
        ·
          refine ⟨364978976885686205598779225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243319317923790803732519483 364978976885686205598779225)
          ·
            refine ⟨273734232664264654199084419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364978976885686205598779225 273734232664264654199084419)
            ·
              refine ⟨410601348996396981298626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273734232664264654199084419 410601348996396981298626629)
              ·
                refine ⟨76987752936824433993492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410601348996396981298626629 76987752936824433993492493)
                ·
                  refine ⟨28870407351309162747559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76987752936824433993492493 28870407351309162747559685)
                  ·
                    refine ⟨5413201378370468015167441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28870407351309162747559685 5413201378370468015167441)
                    ·
                      refine ⟨4059901033777851011375581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413201378370468015167441 4059901033777851011375581)
                      ·
                        rfl

theorem cell23_7906629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_7906629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906629 prefixEnd_7906629 := by exact prefixLift 7906629
  have htrace : WordTrace (prefixWord ++ tailWord_7906629) baseStart_7906629 baseEnd_7906629 := by
    simpa [prefixWord, tailWord_7906629, baseEnd_7906629] using wordTrace_append hprefix tailTrace_7906629
  have hstable : (prefixWord ++ tailWord_7906629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906629).length < 2 ^ (prefixWord ++ tailWord_7906629).sum := by decide
  have hdescent : baseEnd_7906629 < baseStart_7906629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906632 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_7906632 : Nat := 118140960795 + 7906632 * 2 ^ 59
def prefixEnd_7906632 : Nat := 4983230072969 + 3 ^ 40 * 7906632 * 2
def baseEnd_7906632 : Nat := 4059902574219814499638067

theorem tailTrace_7906632 : CollatzResearch.WordTrace tailWord_7906632 prefixEnd_7906632 4059902574219814499638067 := by
  unfold tailWord_7906632
  simp only [CollatzResearch.WordTrace]
  refine ⟨144189280145815042042117075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192252373527753389389489433 144189280145815042042117075)
  ·
    refine ⟨216283920218722563063175613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144189280145815042042117075 216283920218722563063175613)
    ·
      refine ⟨81106470082020961148690855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216283920218722563063175613 81106470082020961148690855)
      ·
        refine ⟨121659705123031441723036283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81106470082020961148690855 121659705123031441723036283)
        ·
          refine ⟨182489557684547162584554425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121659705123031441723036283 182489557684547162584554425)
          ·
            refine ⟨136867168263410371938415819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182489557684547162584554425 136867168263410371938415819)
            ·
              refine ⟨205300752395115557907623729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136867168263410371938415819 205300752395115557907623729)
              ·
                refine ⟨153975564296336668430717797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205300752395115557907623729 153975564296336668430717797)
                ·
                  refine ⟨28870418305563125330759587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153975564296336668430717797 28870418305563125330759587)
                  ·
                    refine ⟨43305627458344687996139381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870418305563125330759587 43305627458344687996139381)
                    ·
                      refine ⟨4059902574219814499638067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43305627458344687996139381 4059902574219814499638067)
                      ·
                        rfl

theorem cell23_7906632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_7906632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906632 prefixEnd_7906632 := by exact prefixLift 7906632
  have htrace : WordTrace (prefixWord ++ tailWord_7906632) baseStart_7906632 baseEnd_7906632 := by
    simpa [prefixWord, tailWord_7906632, baseEnd_7906632] using wordTrace_append hprefix tailTrace_7906632
  have hstable : (prefixWord ++ tailWord_7906632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906632).length < 2 ^ (prefixWord ++ tailWord_7906632).sum := by decide
  have hdescent : baseEnd_7906632 < baseStart_7906632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906666 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7906666 : Nat := 118140960795 + 7906666 * 2 ^ 59
def prefixEnd_7906666 : Nat := 4983230072969 + 3 ^ 40 * 7906666 * 2
def baseEnd_7906666 : Nat := 4059920032562067366612911

theorem tailTrace_7906666 : CollatzResearch.WordTrace tailWord_7906666 prefixEnd_7906666 4059920032562067366612911 := by
  unfold tailWord_7906666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72094950093376726972742963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 192253200249004605260647901 72094950093376726972742963)
  ·
    refine ⟨108142425140065090459114445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72094950093376726972742963 108142425140065090459114445)
    ·
      refine ⟨40553409427524408922167917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108142425140065090459114445 40553409427524408922167917)
      ·
        refine ⟨15207528535321653345812969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40553409427524408922167917 15207528535321653345812969)
        ·
          refine ⟨11405646401491240009359727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15207528535321653345812969 11405646401491240009359727)
          ·
            refine ⟨17108469602236860014039591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11405646401491240009359727 17108469602236860014039591)
            ·
              refine ⟨25662704403355290021059387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17108469602236860014039591 25662704403355290021059387)
              ·
                refine ⟨38494056605032935031589081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25662704403355290021059387 38494056605032935031589081)
                ·
                  refine ⟨28870542453774701273691811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38494056605032935031589081 28870542453774701273691811)
                  ·
                    refine ⟨43305813680662051910537717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870542453774701273691811 43305813680662051910537717)
                    ·
                      refine ⟨4059920032562067366612911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43305813680662051910537717 4059920032562067366612911)
                      ·
                        rfl

theorem cell23_7906666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7906666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906666 prefixEnd_7906666 := by exact prefixLift 7906666
  have htrace : WordTrace (prefixWord ++ tailWord_7906666) baseStart_7906666 baseEnd_7906666 := by
    simpa [prefixWord, tailWord_7906666, baseEnd_7906666] using wordTrace_append hprefix tailTrace_7906666
  have hstable : (prefixWord ++ tailWord_7906666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906666).length < 2 ^ (prefixWord ++ tailWord_7906666).sum := by decide
  have hdescent : baseEnd_7906666 < baseStart_7906666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906697 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 2, 2, 2]
def baseStart_7906697 : Nat := 118140960795 + 7906697 * 2 ^ 59
def prefixEnd_7906697 : Nat := 4983230072969 + 3 ^ 40 * 7906697 * 2
def baseEnd_7906697 : Nat := 4059935950462356745325269

theorem tailTrace_7906697 : CollatzResearch.WordTrace tailWord_7906697 prefixEnd_7906697 4059935950462356745325269 := by
  unfold tailWord_7906697
  simp only [CollatzResearch.WordTrace]
  refine ⟨288380931036394600185350345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192253954024263066790233563 288380931036394600185350345)
  ·
    refine ⟨216285698277295950139012759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288380931036394600185350345 216285698277295950139012759)
    ·
      refine ⟨324428547415943925208519139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216285698277295950139012759 324428547415943925208519139)
      ·
        refine ⟨486642821123915887812778709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324428547415943925208519139 486642821123915887812778709)
        ·
          refine ⟨11405691120091778620612001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 486642821123915887812778709 11405691120091778620612001)
          ·
            refine ⟨8554268340068833965459001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11405691120091778620612001 8554268340068833965459001)
            ·
              refine ⟨6415701255051625474094251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554268340068833965459001 6415701255051625474094251)
              ·
                refine ⟨9623551882577438211141377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415701255051625474094251 9623551882577438211141377)
                ·
                  refine ⟨7217663911933078658356033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623551882577438211141377 7217663911933078658356033)
                  ·
                    refine ⟨5413247933949808993767025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7217663911933078658356033 5413247933949808993767025)
                    ·
                      refine ⟨4059935950462356745325269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5413247933949808993767025 4059935950462356745325269)
                      ·
                        rfl

theorem cell23_7906697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 2, 2, 2].length) (baseStart_7906697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906697 prefixEnd_7906697 := by exact prefixLift 7906697
  have htrace : WordTrace (prefixWord ++ tailWord_7906697) baseStart_7906697 baseEnd_7906697 := by
    simpa [prefixWord, tailWord_7906697, baseEnd_7906697] using wordTrace_append hprefix tailTrace_7906697
  have hstable : (prefixWord ++ tailWord_7906697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906697).length < 2 ^ (prefixWord ++ tailWord_7906697).sum := by decide
  have hdescent : baseEnd_7906697 < baseStart_7906697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906759 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 6]
def baseStart_7906759 : Nat := 118140960795 + 7906759 * 2 ^ 59
def prefixEnd_7906759 : Nat := 4983230072969 + 3 ^ 40 * 7906759 * 2
def baseEnd_7906759 : Nat := 451107531806992833638887

theorem tailTrace_7906759 : CollatzResearch.WordTrace tailWord_7906759 prefixEnd_7906759 451107531806992833638887 := by
  unfold tailWord_7906759
  simp only [CollatzResearch.WordTrace]
  refine ⟨288383192362169984774107331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192255461574779989849404887 288383192362169984774107331)
  ·
    refine ⟨432574788543254977161160997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288383192362169984774107331 432574788543254977161160997)
    ·
      refine ⟨81107772851860308217717687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432574788543254977161160997 81107772851860308217717687)
      ·
        refine ⟨121661659277790462326576531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81107772851860308217717687 121661659277790462326576531)
        ·
          refine ⟨182492488916685693489864797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121661659277790462326576531 182492488916685693489864797)
          ·
            refine ⟨68434683343757135058699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182492488916685693489864797 68434683343757135058699299)
            ·
              refine ⟨102652025015635702588048949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68434683343757135058699299 102652025015635702588048949)
              ·
                refine ⟨9623627345215847117629589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102652025015635702588048949 9623627345215847117629589)
                ·
                  refine ⟨451107531806992833638887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9623627345215847117629589 451107531806992833638887)
                  ·
                    rfl

theorem cell23_7906759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 6].length) (baseStart_7906759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906759 prefixEnd_7906759 := by exact prefixLift 7906759
  have htrace : WordTrace (prefixWord ++ tailWord_7906759) baseStart_7906759 baseEnd_7906759 := by
    simpa [prefixWord, tailWord_7906759, baseEnd_7906759] using wordTrace_append hprefix tailTrace_7906759
  have hstable : (prefixWord ++ tailWord_7906759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906759).length < 2 ^ (prefixWord ++ tailWord_7906759).sum := by decide
  have hdescent : baseEnd_7906759 < baseStart_7906759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906819 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 6]
def baseStart_7906819 : Nat := 118140960795 + 7906819 * 2 ^ 59
def prefixEnd_7906819 : Nat := 4983230072969 + 3 ^ 40 * 7906819 * 2
def baseEnd_7906819 : Nat := 1353332865034068422666569

theorem tailTrace_7906819 : CollatzResearch.WordTrace tailWord_7906819 prefixEnd_7906819 1353332865034068422666569 := by
  unfold tailWord_7906819
  simp only [CollatzResearch.WordTrace]
  refine ⟨288385380741952615021291511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192256920494635076680861007 288385380741952615021291511)
  ·
    refine ⟨432578071112928922531937267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288385380741952615021291511 432578071112928922531937267)
    ·
      refine ⟨648867106669393383797905901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432578071112928922531937267 648867106669393383797905901)
      ·
        refine ⟨243325165001022518924214713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648867106669393383797905901 243325165001022518924214713)
        ·
          refine ⟨182493873750766889193161035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243325165001022518924214713 182493873750766889193161035)
          ·
            refine ⟨273740810626150333789741553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182493873750766889193161035 273740810626150333789741553)
            ·
              refine ⟨205305607969612750342306165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273740810626150333789741553 205305607969612750342306165)
              ·
                refine ⟨19247400747151195344591203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205305607969612750342306165 19247400747151195344591203)
                ·
                  refine ⟨28871101120726793016886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19247400747151195344591203 28871101120726793016886805)
                  ·
                    refine ⟨1353332865034068422666569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28871101120726793016886805 1353332865034068422666569)
                    ·
                      rfl

theorem cell23_7906819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_7906819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906819 prefixEnd_7906819 := by exact prefixLift 7906819
  have htrace : WordTrace (prefixWord ++ tailWord_7906819) baseStart_7906819 baseEnd_7906819 := by
    simpa [prefixWord, tailWord_7906819, baseEnd_7906819] using wordTrace_append hprefix tailTrace_7906819
  have hstable : (prefixWord ++ tailWord_7906819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906819).length < 2 ^ (prefixWord ++ tailWord_7906819).sum := by decide
  have hdescent : baseEnd_7906819 < baseStart_7906819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906823 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 1, 5]
def baseStart_7906823 : Nat := 118140960795 + 7906823 * 2 ^ 59
def prefixEnd_7906823 : Nat := 4983230072969 + 3 ^ 40 * 7906823 * 2
def baseEnd_7906823 : Nat := 1353333549674941084116563

theorem tailTrace_7906823 : CollatzResearch.WordTrace tailWord_7906823 prefixEnd_7906823 1353333549674941084116563 := by
  unfold tailWord_7906823
  simp only [CollatzResearch.WordTrace]
  refine ⟨288385526633938123704437123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192257017755958749136291415 288385526633938123704437123)
  ·
    refine ⟨432578289950907185556655685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288385526633938123704437123 432578289950907185556655685)
    ·
      refine ⟨81108429365795097291872941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432578289950907185556655685 81108429365795097291872941)
      ·
        refine ⟨30415661012173161484452353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81108429365795097291872941 30415661012173161484452353)
        ·
          refine ⟨22811745759129871113339265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30415661012173161484452353 22811745759129871113339265)
          ·
            refine ⟨17108809319347403335004449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22811745759129871113339265 17108809319347403335004449)
            ·
              refine ⟨12831606989510552501253337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17108809319347403335004449 12831606989510552501253337)
              ·
                refine ⟨9623705242132914375940003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12831606989510552501253337 9623705242132914375940003)
                ·
                  refine ⟨14435557863199371563910005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623705242132914375940003 14435557863199371563910005)
                  ·
                    refine ⟨1353333549674941084116563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14435557863199371563910005 1353333549674941084116563)
                    ·
                      rfl

theorem cell23_7906823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_7906823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906823 prefixEnd_7906823 := by exact prefixLift 7906823
  have htrace : WordTrace (prefixWord ++ tailWord_7906823) baseStart_7906823 baseEnd_7906823 := by
    simpa [prefixWord, tailWord_7906823, baseEnd_7906823] using wordTrace_append hprefix tailTrace_7906823
  have hstable : (prefixWord ++ tailWord_7906823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906823).length < 2 ^ (prefixWord ++ tailWord_7906823).sum := by decide
  have hdescent : baseEnd_7906823 < baseStart_7906823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906837 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_7906837 : Nat := 118140960795 + 7906837 * 2 ^ 59
def prefixEnd_7906837 : Nat := 4983230072969 + 3 ^ 40 * 7906837 * 2
def baseEnd_7906837 : Nat := 4060007837753986197574625

theorem tailTrace_7906837 : CollatzResearch.WordTrace tailWord_7906837 prefixEnd_7906837 4060007837753986197574625 := by
  unfold tailWord_7906837
  simp only [CollatzResearch.WordTrace]
  refine ⟨288386037255887404095446765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192257358170591602730297843 288386037255887404095446765)
  ·
    refine ⟨108144763970957776535792537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 288386037255887404095446765 108144763970957776535792537)
    ·
      refine ⟨81108572978218332401844403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108144763970957776535792537 81108572978218332401844403)
      ·
        refine ⟨121662859467327498602766605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81108572978218332401844403 121662859467327498602766605)
        ·
          refine ⟨45623572300247811976037477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121662859467327498602766605 45623572300247811976037477)
          ·
            refine ⟨8554419806296464745507027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45623572300247811976037477 8554419806296464745507027)
            ·
              refine ⟨12831629709444697118260541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554419806296464745507027 12831629709444697118260541)
              ·
                refine ⟨4811861141041761419347703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12831629709444697118260541 4811861141041761419347703)
                ·
                  refine ⟨7217791711562642129021555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811861141041761419347703 7217791711562642129021555)
                  ·
                    refine ⟨10826687567343963193532333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217791711562642129021555 10826687567343963193532333)
                    ·
                      refine ⟨4060007837753986197574625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10826687567343963193532333 4060007837753986197574625)
                      ·
                        rfl

theorem cell23_7906837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_7906837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906837 prefixEnd_7906837 := by exact prefixLift 7906837
  have htrace : WordTrace (prefixWord ++ tailWord_7906837) baseStart_7906837 baseEnd_7906837 := by
    simpa [prefixWord, tailWord_7906837, baseEnd_7906837] using wordTrace_append hprefix tailTrace_7906837
  have hstable : (prefixWord ++ tailWord_7906837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906837).length < 2 ^ (prefixWord ++ tailWord_7906837).sum := by decide
  have hdescent : baseEnd_7906837 < baseStart_7906837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906849 : List Nat := [1, 2, 3, 2, 2, 2, 11]
def baseStart_7906849 : Nat := 118140960795 + 7906849 * 2 ^ 59
def prefixEnd_7906849 : Nat := 4983230072969 + 3 ^ 40 * 7906849 * 2
def baseEnd_7906849 : Nat := 50123629623726421612649

theorem tailTrace_7906849 : CollatzResearch.WordTrace tailWord_7906849 prefixEnd_7906849 50123629623726421612649 := by
  unfold tailWord_7906849
  simp only [CollatzResearch.WordTrace]
  refine ⟨288386474931843930144883601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192257649954562620096589067 288386474931843930144883601)
  ·
    refine ⟨216289856198882947608662701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288386474931843930144883601 216289856198882947608662701)
    ·
      refine ⟨81108696074581105353248513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216289856198882947608662701 81108696074581105353248513)
      ·
        refine ⟨60831522055935829014936385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81108696074581105353248513 60831522055935829014936385)
        ·
          refine ⟨45623641541951871761202289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60831522055935829014936385 45623641541951871761202289)
          ·
            refine ⟨34217731156463903820901717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45623641541951871761202289 34217731156463903820901717)
            ·
              refine ⟨50123629623726421612649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34217731156463903820901717 50123629623726421612649)
              ·
                rfl

theorem cell23_7906849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 11].length) (baseStart_7906849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906849 prefixEnd_7906849 := by exact prefixLift 7906849
  have htrace : WordTrace (prefixWord ++ tailWord_7906849) baseStart_7906849 baseEnd_7906849 := by
    simpa [prefixWord, tailWord_7906849, baseEnd_7906849] using wordTrace_append hprefix tailTrace_7906849
  have hstable : (prefixWord ++ tailWord_7906849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906849).length < 2 ^ (prefixWord ++ tailWord_7906849).sum := by decide
  have hdescent : baseEnd_7906849 < baseStart_7906849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906877 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7906877 : Nat := 118140960795 + 7906877 * 2 ^ 59
def prefixEnd_7906877 : Nat := 4983230072969 + 3 ^ 40 * 7906877 * 2
def baseEnd_7906877 : Nat := 4060028376980166041074441

theorem tailTrace_7906877 : CollatzResearch.WordTrace tailWord_7906877 prefixEnd_7906877 4060028376980166041074441 := by
  unfold tailWord_7906877
  simp only [CollatzResearch.WordTrace]
  refine ⟨288387496175742490926902885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192258330783828327284601923 288387496175742490926902885)
  ·
    refine ⟨54072655532951717048794291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288387496175742490926902885 54072655532951717048794291)
    ·
      refine ⟨81108983299427575573191437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54072655532951717048794291 81108983299427575573191437)
      ·
        refine ⟨30415868737285340839946789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81108983299427575573191437 30415868737285340839946789)
        ·
          refine ⟨5702975388241001407490023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30415868737285340839946789 5702975388241001407490023)
          ·
            refine ⟨8554463082361502111235035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702975388241001407490023 8554463082361502111235035)
            ·
              refine ⟨12831694623542253166852553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554463082361502111235035 12831694623542253166852553)
              ·
                refine ⟨9623770967656689875139415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12831694623542253166852553 9623770967656689875139415)
                ·
                  refine ⟨14435656451485034812709123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623770967656689875139415 14435656451485034812709123)
                  ·
                    refine ⟨21653484677227552219063685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14435656451485034812709123 21653484677227552219063685)
                    ·
                      refine ⟨4060028376980166041074441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21653484677227552219063685 4060028376980166041074441)
                      ·
                        rfl

theorem cell23_7906877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7906877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906877 prefixEnd_7906877 := by exact prefixLift 7906877
  have htrace : WordTrace (prefixWord ++ tailWord_7906877) baseStart_7906877 baseEnd_7906877 := by
    simpa [prefixWord, tailWord_7906877, baseEnd_7906877] using wordTrace_append hprefix tailTrace_7906877
  have hstable : (prefixWord ++ tailWord_7906877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906877).length < 2 ^ (prefixWord ++ tailWord_7906877).sum := by decide
  have hdescent : baseEnd_7906877 < baseStart_7906877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906889 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_7906889 : Nat := 118140960795 + 7906889 * 2 ^ 59
def prefixEnd_7906889 : Nat := 4983230072969 + 3 ^ 40 * 7906889 * 2
def baseEnd_7906889 : Nat := 4060034538748019994124385

theorem tailTrace_7906889 : CollatzResearch.WordTrace tailWord_7906889 prefixEnd_7906889 4060034538748019994124385 := by
  unfold tailWord_7906889
  simp only [CollatzResearch.WordTrace]
  refine ⟨288387933851699016976339721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192258622567799344650893147 288387933851699016976339721)
  ·
    refine ⟨216290950388774262732254791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288387933851699016976339721 216290950388774262732254791)
    ·
      refine ⟨324436425583161394098382187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216290950388774262732254791 324436425583161394098382187)
      ·
        refine ⟨486654638374742091147573281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324436425583161394098382187 486654638374742091147573281)
        ·
          refine ⟨364990978781056568360679961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486654638374742091147573281 364990978781056568360679961)
          ·
            refine ⟨273743234085792426270509971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364990978781056568360679961 273743234085792426270509971)
            ·
              refine ⟨410614851128688639405764957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273743234085792426270509971 410614851128688639405764957)
              ·
                refine ⟨153980569173258239777161859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410614851128688639405764957 153980569173258239777161859)
                ·
                  refine ⟨230970853759887359665742789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153980569173258239777161859 230970853759887359665742789)
                  ·
                    refine ⟨43307035079978879937326773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 230970853759887359665742789 43307035079978879937326773)
                    ·
                      refine ⟨4060034538748019994124385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43307035079978879937326773 4060034538748019994124385)
                      ·
                        rfl

theorem cell23_7906889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_7906889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906889 prefixEnd_7906889 := by exact prefixLift 7906889
  have htrace : WordTrace (prefixWord ++ tailWord_7906889) baseStart_7906889 baseEnd_7906889 := by
    simpa [prefixWord, tailWord_7906889, baseEnd_7906889] using wordTrace_append hprefix tailTrace_7906889
  have hstable : (prefixWord ++ tailWord_7906889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906889).length < 2 ^ (prefixWord ++ tailWord_7906889).sum := by decide
  have hdescent : baseEnd_7906889 < baseStart_7906889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7906916 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7906916 : Nat := 118140960795 + 7906916 * 2 ^ 59
def prefixEnd_7906916 : Nat := 4983230072969 + 3 ^ 40 * 7906916 * 2
def baseEnd_7906916 : Nat := 4060048402725691388486761

theorem tailTrace_7906916 : CollatzResearch.WordTrace tailWord_7906916 prefixEnd_7906916 4060048402725691388486761 := by
  unfold tailWord_7906916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144194459311300600293786301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192259279081734133725048401 144194459311300600293786301)
  ·
    refine ⟨54072922241737725110169863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144194459311300600293786301 54072922241737725110169863)
    ·
      refine ⟨81109383362606587665254795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54072922241737725110169863 81109383362606587665254795)
      ·
        refine ⟨121664075043909881497882193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81109383362606587665254795 121664075043909881497882193)
        ·
          refine ⟨91248056282932411123411645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121664075043909881497882193 91248056282932411123411645)
          ·
            refine ⟨34218021106099654171279367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91248056282932411123411645 34218021106099654171279367)
            ·
              refine ⟨51327031659149481256919051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34218021106099654171279367 51327031659149481256919051)
              ·
                refine ⟨76990547488724221885378577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51327031659149481256919051 76990547488724221885378577)
                ·
                  refine ⟨57742910616543166414033933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76990547488724221885378577 57742910616543166414033933)
                  ·
                    refine ⟨21653591481203687405262725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57742910616543166414033933 21653591481203687405262725)
                    ·
                      refine ⟨4060048402725691388486761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21653591481203687405262725 4060048402725691388486761)
                      ·
                        rfl

theorem cell23_7906916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7906916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7906916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7906916 prefixEnd_7906916 := by exact prefixLift 7906916
  have htrace : WordTrace (prefixWord ++ tailWord_7906916) baseStart_7906916 baseEnd_7906916 := by
    simpa [prefixWord, tailWord_7906916, baseEnd_7906916] using wordTrace_append hprefix tailTrace_7906916
  have hstable : (prefixWord ++ tailWord_7906916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7906916).length < 2 ^ (prefixWord ++ tailWord_7906916).sum := by decide
  have hdescent : baseEnd_7906916 < baseStart_7906916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7906916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
