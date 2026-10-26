import V185TrunkScan21Chunk091

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1114557 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1114557 : Nat := 118140960795 + 1114557 * 2 ^ 59
def prefixEnd_1114557 : Nat := 4983230072969 + 3 ^ 40 * 1114557 * 2
def baseEnd_1114557 : Nat := 254357092370356010805223

theorem tailTrace_1114557 : CollatzResearch.WordTrace tailWord_1114557 prefixEnd_1114557 254357092370356010805223 := by
  unfold tailWord_1114557
  simp only [CollatzResearch.WordTrace]
  refine ⟨40651233423157815026077925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27100822282105210017385283 40651233423157815026077925)
  ·
    refine ⟨7622106266842090317389611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40651233423157815026077925 7622106266842090317389611)
    ·
      refine ⟨11433159400263135476084417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622106266842090317389611 11433159400263135476084417)
      ·
        refine ⟨8574869550197351607063313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11433159400263135476084417 8574869550197351607063313)
        ·
          refine ⟨6431152162648013705297485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8574869550197351607063313 6431152162648013705297485)
          ·
            refine ⟨2411682060993005139486557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6431152162648013705297485 2411682060993005139486557)
            ·
              refine ⟨904380772872376927307459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2411682060993005139486557 904380772872376927307459)
              ·
                refine ⟨1356571159308565390961189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904380772872376927307459 1356571159308565390961189)
                ·
                  refine ⟨254357092370356010805223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356571159308565390961189 254357092370356010805223)
                  ·
                    rfl

theorem cell21_1114557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1114557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114557 prefixEnd_1114557 := by exact prefixLift 1114557
  have htrace : WordTrace (prefixWord ++ tailWord_1114557) baseStart_1114557 baseEnd_1114557 := by
    simpa [prefixWord, tailWord_1114557, baseEnd_1114557] using wordTrace_append hprefix tailTrace_1114557
  have hstable : (prefixWord ++ tailWord_1114557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114557).length < 2 ^ (prefixWord ++ tailWord_1114557).sum := by decide
  have hdescent : baseEnd_1114557 < baseStart_1114557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114599 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_1114599 : Nat := 118140960795 + 1114599 * 2 ^ 59
def prefixEnd_1114599 : Nat := 4983230072969 + 3 ^ 40 * 1114599 * 2
def baseEnd_1114599 : Nat := 254366677342573271105137

theorem tailTrace_1114599 : CollatzResearch.WordTrace tailWord_1114599 prefixEnd_1114599 254366677342573271105137 := by
  unfold tailWord_1114599
  simp only [CollatzResearch.WordTrace]
  refine ⟨40652765289005656199106851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27101843526003770799404567 40652765289005656199106851)
  ·
    refine ⟨60979147933508484298660277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40652765289005656199106851 60979147933508484298660277)
    ·
      refine ⟨5716795118766420402999401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60979147933508484298660277 5716795118766420402999401)
      ·
        refine ⟨4287596339074815302249551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5716795118766420402999401 4287596339074815302249551)
        ·
          refine ⟨6431394508612222953374327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287596339074815302249551 6431394508612222953374327)
          ·
            refine ⟨9647091762918334430061491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6431394508612222953374327 9647091762918334430061491)
            ·
              refine ⟨14470637644377501645092237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9647091762918334430061491 14470637644377501645092237)
              ·
                refine ⟨5426489116641563116909589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14470637644377501645092237 5426489116641563116909589)
                ·
                  refine ⟨254366677342573271105137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5426489116641563116909589 254366677342573271105137)
                  ·
                    rfl

theorem cell21_1114599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_1114599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114599 prefixEnd_1114599 := by exact prefixLift 1114599
  have htrace : WordTrace (prefixWord ++ tailWord_1114599) baseStart_1114599 baseEnd_1114599 := by
    simpa [prefixWord, tailWord_1114599, baseEnd_1114599] using wordTrace_append hprefix tailTrace_1114599
  have hstable : (prefixWord ++ tailWord_1114599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114599).length < 2 ^ (prefixWord ++ tailWord_1114599).sum := by decide
  have hdescent : baseEnd_1114599 < baseStart_1114599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114602 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1114602 : Nat := 118140960795 + 1114602 * 2 ^ 59
def prefixEnd_1114602 : Nat := 4983230072969 + 3 ^ 40 * 1114602 * 2
def baseEnd_1114602 : Nat := 254367361983445932555131

theorem tailTrace_1114602 : CollatzResearch.WordTrace tailWord_1114602 prefixEnd_1114602 254367361983445932555131 := by
  unfold tailWord_1114602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163218676998696927866515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27101916471996525140977373 10163218676998696927866515)
  ·
    refine ⟨15244828015498045391799773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10163218676998696927866515 15244828015498045391799773)
    ·
      refine ⟨5716810505811767021924915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15244828015498045391799773 5716810505811767021924915)
      ·
        refine ⟨8575215758717650532887373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716810505811767021924915 8575215758717650532887373)
        ·
          refine ⟨3215705909519118949832765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8575215758717650532887373 3215705909519118949832765)
          ·
            refine ⟨1205889716069669606187287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215705909519118949832765 1205889716069669606187287)
            ·
              refine ⟨1808834574104504409280931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205889716069669606187287 1808834574104504409280931)
              ·
                refine ⟨2713251861156756613921397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808834574104504409280931 2713251861156756613921397)
                ·
                  refine ⟨254367361983445932555131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2713251861156756613921397 254367361983445932555131)
                  ·
                    rfl

theorem cell21_1114602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1114602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114602 prefixEnd_1114602 := by exact prefixLift 1114602
  have htrace : WordTrace (prefixWord ++ tailWord_1114602) baseStart_1114602 baseEnd_1114602 := by
    simpa [prefixWord, tailWord_1114602, baseEnd_1114602] using wordTrace_append hprefix tailTrace_1114602
  have hstable : (prefixWord ++ tailWord_1114602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114602).length < 2 ^ (prefixWord ++ tailWord_1114602).sum := by decide
  have hdescent : baseEnd_1114602 < baseStart_1114602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114647 : List Nat := [1, 1, 3, 6, 2, 8]
def baseStart_1114647 : Nat := 118140960795 + 1114647 * 2 ^ 59
def prefixEnd_1114647 : Nat := 4983230072969 + 3 ^ 40 * 1114647 * 2
def baseEnd_1114647 : Nat := 9421393762834661270557

theorem tailTrace_1114647 : CollatzResearch.WordTrace tailWord_1114647 prefixEnd_1114647 9421393762834661270557 := by
  unfold tailWord_1114647
  simp only [CollatzResearch.WordTrace]
  refine ⟨40654515992831760396854195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27103010661887840264569463 40654515992831760396854195)
  ·
    refine ⟨60981773989247640595281293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40654515992831760396854195 60981773989247640595281293)
    ·
      refine ⟨22868165245967865223230485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60981773989247640595281293 22868165245967865223230485)
      ·
        refine ⟨1071945245904743682338929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22868165245967865223230485 1071945245904743682338929)
        ·
          refine ⟨803958934428557761754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071945245904743682338929 803958934428557761754197)
          ·
            refine ⟨9421393762834661270557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 803958934428557761754197 9421393762834661270557)
            ·
              rfl

theorem cell21_1114647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 8].length) (baseStart_1114647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114647 prefixEnd_1114647 := by exact prefixLift 1114647
  have htrace : WordTrace (prefixWord ++ tailWord_1114647) baseStart_1114647 baseEnd_1114647 := by
    simpa [prefixWord, tailWord_1114647, baseEnd_1114647] using wordTrace_append hprefix tailTrace_1114647
  have hstable : (prefixWord ++ tailWord_1114647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114647).length < 2 ^ (prefixWord ++ tailWord_1114647).sum := by decide
  have hdescent : baseEnd_1114647 < baseStart_1114647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114675 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_1114675 : Nat := 118140960795 + 1114675 * 2 ^ 59
def prefixEnd_1114675 : Nat := 4983230072969 + 3 ^ 40 * 1114675 * 2
def baseEnd_1114675 : Nat := 254384021578014027838315

theorem tailTrace_1114675 : CollatzResearch.WordTrace tailWord_1114675 prefixEnd_1114675 254384021578014027838315 := by
  unfold tailWord_1114675
  simp only [CollatzResearch.WordTrace]
  refine ⟨40655537236730321178873479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27103691491153547452582319 40655537236730321178873479)
  ·
    refine ⟨60983305855095481768310219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40655537236730321178873479 60983305855095481768310219)
    ·
      refine ⟨91474958782643222652465329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60983305855095481768310219 91474958782643222652465329)
      ·
        refine ⟨68606219086982416989348997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91474958782643222652465329 68606219086982416989348997)
        ·
          refine ⟨12863666078809203185502937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68606219086982416989348997 12863666078809203185502937)
          ·
            refine ⟨9647749559106902389127203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12863666078809203185502937 9647749559106902389127203)
            ·
              refine ⟨14471624338660353583690805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9647749559106902389127203 14471624338660353583690805)
              ·
                refine ⟨1356714781749408148471013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14471624338660353583690805 1356714781749408148471013)
                ·
                  refine ⟨254384021578014027838315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1356714781749408148471013 254384021578014027838315)
                  ·
                    rfl

theorem cell21_1114675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_1114675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114675 prefixEnd_1114675 := by exact prefixLift 1114675
  have htrace : WordTrace (prefixWord ++ tailWord_1114675) baseStart_1114675 baseEnd_1114675 := by
    simpa [prefixWord, tailWord_1114675, baseEnd_1114675] using wordTrace_append hprefix tailTrace_1114675
  have hstable : (prefixWord ++ tailWord_1114675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114675).length < 2 ^ (prefixWord ++ tailWord_1114675).sum := by decide
  have hdescent : baseEnd_1114675 < baseStart_1114675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114678 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1114678 : Nat := 118140960795 + 1114678 * 2 ^ 59
def prefixEnd_1114678 : Nat := 4983230072969 + 3 ^ 40 * 1114678 * 2
def baseEnd_1114678 : Nat := 254384706218886689288309

theorem tailTrace_1114678 : CollatzResearch.WordTrace tailWord_1114678 prefixEnd_1114678 254384706218886689288309 := by
  unfold tailWord_1114678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540977915982465793202043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27103764437146301794155125 2540977915982465793202043)
  ·
    refine ⟨3811466873973698689803065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2540977915982465793202043 3811466873973698689803065)
    ·
      refine ⟨2858600155480274017352299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3811466873973698689803065 2858600155480274017352299)
      ·
        refine ⟨4287900233220411026028449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858600155480274017352299 4287900233220411026028449)
        ·
          refine ⟨3215925174915308269521337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4287900233220411026028449 3215925174915308269521337)
          ·
            refine ⟨2411943881186481202141003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3215925174915308269521337 2411943881186481202141003)
            ·
              refine ⟨3617915821779721803211505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411943881186481202141003 3617915821779721803211505)
              ·
                refine ⟨2713436866334791352408629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617915821779721803211505 2713436866334791352408629)
                ·
                  refine ⟨254384706218886689288309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2713436866334791352408629 254384706218886689288309)
                  ·
                    rfl

theorem cell21_1114678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1114678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114678 prefixEnd_1114678 := by exact prefixLift 1114678
  have htrace : WordTrace (prefixWord ++ tailWord_1114678) baseStart_1114678 baseEnd_1114678 := by
    simpa [prefixWord, tailWord_1114678, baseEnd_1114678] using wordTrace_append hprefix tailTrace_1114678
  have hstable : (prefixWord ++ tailWord_1114678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114678).length < 2 ^ (prefixWord ++ tailWord_1114678).sum := by decide
  have hdescent : baseEnd_1114678 < baseStart_1114678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114720 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1114720 : Nat := 118140960795 + 1114720 * 2 ^ 59
def prefixEnd_1114720 : Nat := 4983230072969 + 3 ^ 40 * 1114720 * 2
def baseEnd_1114720 : Nat := 254394291191103949588223

theorem tailTrace_1114720 : CollatzResearch.WordTrace tailWord_1114720 prefixEnd_1114720 254394291191103949588223 := by
  unfold tailWord_1114720
  simp only [CollatzResearch.WordTrace]
  refine ⟨20328589260783646932130807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27104785681044862576174409 20328589260783646932130807)
  ·
    refine ⟨30492883891175470398196211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20328589260783646932130807 30492883891175470398196211)
    ·
      refine ⟨45739325836763205597294317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30492883891175470398196211 45739325836763205597294317)
      ·
        refine ⟨17152247188786202098985369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45739325836763205597294317 17152247188786202098985369)
        ·
          refine ⟨12864185391589651574239027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17152247188786202098985369 12864185391589651574239027)
          ·
            refine ⟨19296278087384477361358541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864185391589651574239027 19296278087384477361358541)
            ·
              refine ⟨7236104282769179010509453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19296278087384477361358541 7236104282769179010509453)
              ·
                refine ⟨2713539106038442128941045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7236104282769179010509453 2713539106038442128941045)
                ·
                  refine ⟨254394291191103949588223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2713539106038442128941045 254394291191103949588223)
                  ·
                    rfl

theorem cell21_1114720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1114720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114720 prefixEnd_1114720 := by exact prefixLift 1114720
  have htrace : WordTrace (prefixWord ++ tailWord_1114720) baseStart_1114720 baseEnd_1114720 := by
    simpa [prefixWord, tailWord_1114720, baseEnd_1114720] using wordTrace_append hprefix tailTrace_1114720
  have hstable : (prefixWord ++ tailWord_1114720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114720).length < 2 ^ (prefixWord ++ tailWord_1114720).sum := by decide
  have hdescent : baseEnd_1114720 < baseStart_1114720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114822 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1114822 : Nat := 118140960795 + 1114822 * 2 ^ 59
def prefixEnd_1114822 : Nat := 4983230072969 + 3 ^ 40 * 1114822 * 2
def baseEnd_1114822 : Nat := 254417568980774438888015

theorem tailTrace_1114822 : CollatzResearch.WordTrace tailWord_1114822 prefixEnd_1114822 254417568980774438888015 := by
  unfold tailWord_1114822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270653086474930165139835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27107265844798510189649813 1270653086474930165139835)
  ·
    refine ⟨1905979629712395247709753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270653086474930165139835 1905979629712395247709753)
    ·
      refine ⟨1429484722284296435782315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905979629712395247709753 1429484722284296435782315)
      ·
        refine ⟨2144227083426444653673473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429484722284296435782315 2144227083426444653673473)
        ·
          refine ⟨1608170312569833490255105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2144227083426444653673473 1608170312569833490255105)
          ·
            refine ⟨1206127734427375117691329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608170312569833490255105 1206127734427375117691329)
            ·
              refine ⟨904595800820531338268497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206127734427375117691329 904595800820531338268497)
              ·
                refine ⟨678446850615398503701373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904595800820531338268497 678446850615398503701373)
                ·
                  refine ⟨254417568980774438888015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678446850615398503701373 254417568980774438888015)
                  ·
                    rfl

theorem cell21_1114822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1114822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114822 prefixEnd_1114822 := by exact prefixLift 1114822
  have htrace : WordTrace (prefixWord ++ tailWord_1114822) baseStart_1114822 baseEnd_1114822 := by
    simpa [prefixWord, tailWord_1114822, baseEnd_1114822] using wordTrace_append hprefix tailTrace_1114822
  have hstable : (prefixWord ++ tailWord_1114822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114822).length < 2 ^ (prefixWord ++ tailWord_1114822).sum := by decide
  have hdescent : baseEnd_1114822 < baseStart_1114822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114830 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1114830 : Nat := 118140960795 + 1114830 * 2 ^ 59
def prefixEnd_1114830 : Nat := 4983230072969 + 3 ^ 40 * 1114830 * 2
def baseEnd_1114830 : Nat := 254419394689768202754665

theorem tailTrace_1114830 : CollatzResearch.WordTrace tailWord_1114830 prefixEnd_1114830 254419394689768202754665 := by
  unfold tailWord_1114830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082648818896097831345743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27107460367445855100510629 5082648818896097831345743)
  ·
    refine ⟨7623973228344146747018615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082648818896097831345743 7623973228344146747018615)
    ·
      refine ⟨11435959842516220120527923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7623973228344146747018615 11435959842516220120527923)
      ·
        refine ⟨17153939763774330180791885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11435959842516220120527923 17153939763774330180791885)
        ·
          refine ⟨6432727411415373817796957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17153939763774330180791885 6432727411415373817796957)
          ·
            refine ⟨2412272779280765181673859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6432727411415373817796957 2412272779280765181673859)
            ·
              refine ⟨3618409168921147772510789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412272779280765181673859 3618409168921147772510789)
              ·
                refine ⟨678451719172715207345773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3618409168921147772510789 678451719172715207345773)
                ·
                  refine ⟨254419394689768202754665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678451719172715207345773 254419394689768202754665)
                  ·
                    rfl

theorem cell21_1114830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1114830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114830 prefixEnd_1114830 := by exact prefixLift 1114830
  have htrace : WordTrace (prefixWord ++ tailWord_1114830) baseStart_1114830 baseEnd_1114830 := by
    simpa [prefixWord, tailWord_1114830, baseEnd_1114830] using wordTrace_append hprefix tailTrace_1114830
  have hstable : (prefixWord ++ tailWord_1114830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114830).length < 2 ^ (prefixWord ++ tailWord_1114830).sum := by decide
  have hdescent : baseEnd_1114830 < baseStart_1114830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114889 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 3]
def baseStart_1114889 : Nat := 118140960795 + 1114889 * 2 ^ 59
def prefixEnd_1114889 : Nat := 4983230072969 + 3 ^ 40 * 1114889 * 2
def baseEnd_1114889 : Nat := 254432859293597211271211

theorem tailTrace_1114889 : CollatzResearch.WordTrace tailWord_1114889 prefixEnd_1114889 254432859293597211271211 := by
  unfold tailWord_1114889
  simp only [CollatzResearch.WordTrace]
  refine ⟨40663342457955035727163721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27108894971970023818109147 40663342457955035727163721)
  ·
    refine ⟨30497506843466276795372791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40663342457955035727163721 30497506843466276795372791)
    ·
      refine ⟨45746260265199415193059187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30497506843466276795372791 45746260265199415193059187)
      ·
        refine ⟨68619390397799122789588781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45746260265199415193059187 68619390397799122789588781)
        ·
          refine ⟨25732271399174671046095793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68619390397799122789588781 25732271399174671046095793)
          ·
            refine ⟨19299203549381003284571845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25732271399174671046095793 19299203549381003284571845)
            ·
              refine ⟨3618600665508938115857221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19299203549381003284571845 3618600665508938115857221)
              ·
                refine ⟨678487624782925896723229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3618600665508938115857221 678487624782925896723229)
                ·
                  refine ⟨254432859293597211271211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678487624782925896723229 254432859293597211271211)
                  ·
                    rfl

theorem cell21_1114889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_1114889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114889 prefixEnd_1114889 := by exact prefixLift 1114889
  have htrace : WordTrace (prefixWord ++ tailWord_1114889) baseStart_1114889 baseEnd_1114889 := by
    simpa [prefixWord, tailWord_1114889, baseEnd_1114889] using wordTrace_append hprefix tailTrace_1114889
  have hstable : (prefixWord ++ tailWord_1114889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114889).length < 2 ^ (prefixWord ++ tailWord_1114889).sum := by decide
  have hdescent : baseEnd_1114889 < baseStart_1114889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114909 : List Nat := [1, 4, 2, 4, 2, 1, 2, 5]
def baseStart_1114909 : Nat := 118140960795 + 1114909 * 2 ^ 59
def prefixEnd_1114909 : Nat := 4983230072969 + 3 ^ 40 * 1114909 * 2
def baseEnd_1114909 : Nat := 84812474522027206979279

theorem tailTrace_1114909 : CollatzResearch.WordTrace tailWord_1114909 prefixEnd_1114909 84812474522027206979279 := by
  unfold tailWord_1114909
  simp only [CollatzResearch.WordTrace]
  refine ⟨40664071917882579142891781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27109381278588386095261187 40664071917882579142891781)
  ·
    refine ⟨7624513484602983589292209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40664071917882579142891781 7624513484602983589292209)
    ·
      refine ⟨5718385113452237691969157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7624513484602983589292209 5718385113452237691969157)
      ·
        refine ⟨1072197208772294567244217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5718385113452237691969157 1072197208772294567244217)
        ·
          refine ⟨804147906579220925433163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072197208772294567244217 804147906579220925433163)
          ·
            refine ⟨1206221859868831388149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804147906579220925433163 1206221859868831388149745)
            ·
              refine ⟨904666394901623541112309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206221859868831388149745 904666394901623541112309)
              ·
                refine ⟨84812474522027206979279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 904666394901623541112309 84812474522027206979279)
                ·
                  rfl

theorem cell21_1114909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].length) (baseStart_1114909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114909 prefixEnd_1114909 := by exact prefixLift 1114909
  have htrace : WordTrace (prefixWord ++ tailWord_1114909) baseStart_1114909 baseEnd_1114909 := by
    simpa [prefixWord, tailWord_1114909, baseEnd_1114909] using wordTrace_append hprefix tailTrace_1114909
  have hstable : (prefixWord ++ tailWord_1114909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114909).length < 2 ^ (prefixWord ++ tailWord_1114909).sum := by decide
  have hdescent : baseEnd_1114909 < baseStart_1114909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114917 : List Nat := [1, 3, 1, 2, 3, 1, 3, 7]
def baseStart_1114917 : Nat := 118140960795 + 1114917 * 2 ^ 59
def prefixEnd_1114917 : Nat := 4983230072969 + 3 ^ 40 * 1114917 * 2
def baseEnd_1114917 : Nat := 84813083091691794934829

theorem tailTrace_1114917 : CollatzResearch.WordTrace tailWord_1114917 prefixEnd_1114917 84813083091691794934829 := by
  unfold tailWord_1114917
  simp only [CollatzResearch.WordTrace]
  refine ⟨40664363701853596509183005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27109575801235731006122003 40664363701853596509183005)
  ·
    refine ⟨15249136388195098690943627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40664363701853596509183005 15249136388195098690943627)
    ·
      refine ⟨22873704582292648036415441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249136388195098690943627 22873704582292648036415441)
      ·
        refine ⟨17155278436719486027311581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22873704582292648036415441 17155278436719486027311581)
        ·
          refine ⟨6433229413769807260241843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17155278436719486027311581 6433229413769807260241843)
          ·
            refine ⟨9649844120654710890362765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6433229413769807260241843 9649844120654710890362765)
            ·
              refine ⟨3618691545245516583886037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9649844120654710890362765 3618691545245516583886037)
              ·
                refine ⟨84813083091691794934829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3618691545245516583886037 84813083091691794934829)
                ·
                  rfl

theorem cell21_1114917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_1114917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1114917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1114917 prefixEnd_1114917 := by exact prefixLift 1114917
  have htrace : WordTrace (prefixWord ++ tailWord_1114917) baseStart_1114917 baseEnd_1114917 := by
    simpa [prefixWord, tailWord_1114917, baseEnd_1114917] using wordTrace_append hprefix tailTrace_1114917
  have hstable : (prefixWord ++ tailWord_1114917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114917).length < 2 ^ (prefixWord ++ tailWord_1114917).sum := by decide
  have hdescent : baseEnd_1114917 < baseStart_1114917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115072 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_1115072 : Nat := 118140960795 + 1115072 * 2 ^ 59
def prefixEnd_1115072 : Nat := 4983230072969 + 3 ^ 40 * 1115072 * 2
def baseEnd_1115072 : Nat := 254474622386829559720837

theorem tailTrace_1115072 : CollatzResearch.WordTrace tailWord_1115072 prefixEnd_1115072 254474622386829559720837 := by
  unfold tailWord_1115072
  simp only [CollatzResearch.WordTrace]
  refine ⟨20335008508146028990537735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27113344677528038654050313 20335008508146028990537735)
  ·
    refine ⟨30502512762219043485806603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20335008508146028990537735 30502512762219043485806603)
    ·
      refine ⟨45753769143328565228709905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30502512762219043485806603 45753769143328565228709905)
      ·
        refine ⟨34315326857496423921532429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45753769143328565228709905 34315326857496423921532429)
        ·
          refine ⟨12868247571561158970574661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34315326857496423921532429 12868247571561158970574661)
          ·
            refine ⟨2412796419667717306982749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12868247571561158970574661 2412796419667717306982749)
            ·
              refine ⟨904798657375393990118531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412796419667717306982749 904798657375393990118531)
              ·
                refine ⟨1357197986063090985177797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904798657375393990118531 1357197986063090985177797)
                ·
                  refine ⟨254474622386829559720837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357197986063090985177797 254474622386829559720837)
                  ·
                    rfl

theorem cell21_1115072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_1115072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115072 prefixEnd_1115072 := by exact prefixLift 1115072
  have htrace : WordTrace (prefixWord ++ tailWord_1115072) baseStart_1115072 baseEnd_1115072 := by
    simpa [prefixWord, tailWord_1115072, baseEnd_1115072] using wordTrace_append hprefix tailTrace_1115072
  have hstable : (prefixWord ++ tailWord_1115072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115072).length < 2 ^ (prefixWord ++ tailWord_1115072).sum := by decide
  have hdescent : baseEnd_1115072 < baseStart_1115072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115086 : List Nat := [4, 1, 1, 1, 2, 3, 4, 5]
def baseStart_1115086 : Nat := 118140960795 + 1115086 * 2 ^ 59
def prefixEnd_1115086 : Nat := 4983230072969 + 3 ^ 40 * 1115086 * 2
def baseEnd_1115086 : Nat := 84825939125856215495825

theorem tailTrace_1115086 : CollatzResearch.WordTrace tailWord_1115086 prefixEnd_1115086 84825939125856215495825 := by
  unfold tailWord_1115086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083815954780167296510639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27113685092160892248056741 5083815954780167296510639)
  ·
    refine ⟨7625723932170250944765959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5083815954780167296510639 7625723932170250944765959)
    ·
      refine ⟨11438585898255376417148939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7625723932170250944765959 11438585898255376417148939)
      ·
        refine ⟨17157878847383064625723409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11438585898255376417148939 17157878847383064625723409)
        ·
          refine ⟨12868409135537298469292557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17157878847383064625723409 12868409135537298469292557)
          ·
            refine ⟨4825653425826486925984709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12868409135537298469292557 4825653425826486925984709)
            ·
              refine ⟨904810017342466298622133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4825653425826486925984709 904810017342466298622133)
              ·
                refine ⟨84825939125856215495825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 904810017342466298622133 84825939125856215495825)
                ·
                  rfl

theorem cell21_1115086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_1115086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115086 prefixEnd_1115086 := by exact prefixLift 1115086
  have htrace : WordTrace (prefixWord ++ tailWord_1115086) baseStart_1115086 baseEnd_1115086 := by
    simpa [prefixWord, tailWord_1115086, baseEnd_1115086] using wordTrace_append hprefix tailTrace_1115086
  have hstable : (prefixWord ++ tailWord_1115086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115086).length < 2 ^ (prefixWord ++ tailWord_1115086).sum := by decide
  have hdescent : baseEnd_1115086 < baseStart_1115086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115168 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_1115168 : Nat := 118140960795 + 1115168 * 2 ^ 59
def prefixEnd_1115168 : Nat := 4983230072969 + 3 ^ 40 * 1115168 * 2
def baseEnd_1115168 : Nat := 254496530894754726120641

theorem tailTrace_1115168 : CollatzResearch.WordTrace tailWord_1115168 prefixEnd_1115168 254496530894754726120641 := by
  unfold tailWord_1115168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336759211972133188285079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27115678949296177584380105 20336759211972133188285079)
  ·
    refine ⟨30505138817958199782427619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20336759211972133188285079 30505138817958199782427619)
    ·
      refine ⟨45757708226937299673641429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30505138817958199782427619 45757708226937299673641429)
      ·
        refine ⟨1072446286568842961100971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45757708226937299673641429 1072446286568842961100971)
        ·
          refine ⟨1608669429853264441651457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072446286568842961100971 1608669429853264441651457)
          ·
            refine ⟨1206502072389948331238593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608669429853264441651457 1206502072389948331238593)
            ·
              refine ⟨904876554292461248428945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206502072389948331238593 904876554292461248428945)
              ·
                refine ⟨678657415719345936321709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904876554292461248428945 678657415719345936321709)
                ·
                  refine ⟨254496530894754726120641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678657415719345936321709 254496530894754726120641)
                  ·
                    rfl

theorem cell21_1115168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_1115168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115168 prefixEnd_1115168 := by exact prefixLift 1115168
  have htrace : WordTrace (prefixWord ++ tailWord_1115168) baseStart_1115168 baseEnd_1115168 := by
    simpa [prefixWord, tailWord_1115168, baseEnd_1115168] using wordTrace_append hprefix tailTrace_1115168
  have hstable : (prefixWord ++ tailWord_1115168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115168).length < 2 ^ (prefixWord ++ tailWord_1115168).sum := by decide
  have hdescent : baseEnd_1115168 < baseStart_1115168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115297 : List Nat := [1, 2, 3, 3, 1, 1, 4, 6]
def baseStart_1115297 : Nat := 118140960795 + 1115297 * 2 ^ 59
def prefixEnd_1115297 : Nat := 4983230072969 + 3 ^ 40 * 1115297 * 2
def baseEnd_1115297 : Nat := 84841990150759722823459

theorem tailTrace_1115297 : CollatzResearch.WordTrace tailWord_1115297 prefixEnd_1115297 84841990150759722823459 := by
  unfold tailWord_1115297
  simp only [CollatzResearch.WordTrace]
  refine ⟨40678223440476921408016145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27118815626984614272010763 40678223440476921408016145)
  ·
    refine ⟨30508667580357691056012109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40678223440476921408016145 30508667580357691056012109)
    ·
      refine ⟨11440750342634134146004541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30508667580357691056012109 11440750342634134146004541)
      ·
        refine ⟨4290281378487800304751703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11440750342634134146004541 4290281378487800304751703)
        ·
          refine ⟨6435422067731700457127555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290281378487800304751703 6435422067731700457127555)
          ·
            refine ⟨9653133101597550685691333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6435422067731700457127555 9653133101597550685691333)
            ·
              refine ⟨1809962456549540753567125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9653133101597550685691333 1809962456549540753567125)
              ·
                refine ⟨84841990150759722823459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1809962456549540753567125 84841990150759722823459)
                ·
                  rfl

theorem cell21_1115297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_1115297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115297 prefixEnd_1115297 := by exact prefixLift 1115297
  have htrace : WordTrace (prefixWord ++ tailWord_1115297) baseStart_1115297 baseEnd_1115297 := by
    simpa [prefixWord, tailWord_1115297, baseEnd_1115297] using wordTrace_append hprefix tailTrace_1115297
  have hstable : (prefixWord ++ tailWord_1115297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115297).length < 2 ^ (prefixWord ++ tailWord_1115297).sum := by decide
  have hdescent : baseEnd_1115297 < baseStart_1115297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115300 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1115300 : Nat := 118140960795 + 1115300 * 2 ^ 59
def prefixEnd_1115300 : Nat := 4983230072969 + 3 ^ 40 * 1115300 * 2
def baseEnd_1115300 : Nat := 254526655093151829920371

theorem tailTrace_1115300 : CollatzResearch.WordTrace tailWord_1115300 prefixEnd_1115300 254526655093151829920371 := by
  unfold tailWord_1115300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20339166429733026460187677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27118888572977368613583569 20339166429733026460187677)
  ·
    refine ⟨7627187411149884922570379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20339166429733026460187677 7627187411149884922570379)
    ·
      refine ⟨11440781116724827383855569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7627187411149884922570379 11440781116724827383855569)
      ·
        refine ⟨8580585837543620537891677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11440781116724827383855569 8580585837543620537891677)
        ·
          refine ⟨3217719689078857701709379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8580585837543620537891677 3217719689078857701709379)
          ·
            refine ⟨4826579533618286552564069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217719689078857701709379 4826579533618286552564069)
            ·
              refine ⟨904983662553428728605763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4826579533618286552564069 904983662553428728605763)
              ·
                refine ⟨1357475493830143092908645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904983662553428728605763 1357475493830143092908645)
                ·
                  refine ⟨254526655093151829920371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357475493830143092908645 254526655093151829920371)
                  ·
                    rfl

theorem cell21_1115300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1115300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115300 prefixEnd_1115300 := by exact prefixLift 1115300
  have htrace : WordTrace (prefixWord ++ tailWord_1115300) baseStart_1115300 baseEnd_1115300 := by
    simpa [prefixWord, tailWord_1115300, baseEnd_1115300] using wordTrace_append hprefix tailTrace_1115300
  have hstable : (prefixWord ++ tailWord_1115300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115300).length < 2 ^ (prefixWord ++ tailWord_1115300).sum := by decide
  have hdescent : baseEnd_1115300 < baseStart_1115300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115311 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 5]
def baseStart_1115311 : Nat := 118140960795 + 1115311 * 2 ^ 59
def prefixEnd_1115311 : Nat := 4983230072969 + 3 ^ 40 * 1115311 * 2
def baseEnd_1115311 : Nat := 254529165443018255237015

theorem tailTrace_1115311 : CollatzResearch.WordTrace tailWord_1115311 prefixEnd_1115311 254529165443018255237015 := by
  unfold tailWord_1115311
  simp only [CollatzResearch.WordTrace]
  refine ⟨40678734062426201799025787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27119156041617467866017191 40678734062426201799025787)
  ·
    refine ⟨61018101093639302698538681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40678734062426201799025787 61018101093639302698538681)
    ·
      refine ⟨45763575820229477023904011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61018101093639302698538681 45763575820229477023904011)
      ·
        refine ⟨68645363730344215535856017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45763575820229477023904011 68645363730344215535856017)
        ·
          refine ⟨51484022797758161651892013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68645363730344215535856017 51484022797758161651892013)
          ·
            refine ⟨19306508549159310619459505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51484022797758161651892013 19306508549159310619459505)
            ·
              refine ⟨14479881411869482964594629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19306508549159310619459505 14479881411869482964594629)
              ·
                refine ⟨2714977764725528055861493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14479881411869482964594629 2714977764725528055861493)
                ·
                  refine ⟨254529165443018255237015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2714977764725528055861493 254529165443018255237015)
                  ·
                    rfl

theorem cell21_1115311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_1115311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115311 prefixEnd_1115311 := by exact prefixLift 1115311
  have htrace : WordTrace (prefixWord ++ tailWord_1115311) baseStart_1115311 baseEnd_1115311 := by
    simpa [prefixWord, tailWord_1115311, baseEnd_1115311] using wordTrace_append hprefix tailTrace_1115311
  have hstable : (prefixWord ++ tailWord_1115311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115311).length < 2 ^ (prefixWord ++ tailWord_1115311).sum := by decide
  have hdescent : baseEnd_1115311 < baseStart_1115311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115348 : List Nat := [2, 4, 1, 4, 2, 1, 1, 6]
def baseStart_1115348 : Nat := 118140960795 + 1115348 * 2 ^ 59
def prefixEnd_1115348 : Nat := 4983230072969 + 3 ^ 40 * 1115348 * 2
def baseEnd_1115348 : Nat := 84845869782371471040091

theorem tailTrace_1115348 : CollatzResearch.WordTrace tailWord_1115348 prefixEnd_1115348 84845869782371471040091 := by
  unfold tailWord_1115348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340041781646078559061349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27120055708861438078748465 20340041781646078559061349)
  ·
    refine ⟨3813757834058639729824003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20340041781646078559061349 3813757834058639729824003)
    ·
      refine ⟨5720636751087959594736005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3813757834058639729824003 5720636751087959594736005)
      ·
        refine ⟨1072619390828992424013001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5720636751087959594736005 1072619390828992424013001)
        ·
          refine ⟨804464543121744318009751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072619390828992424013001 804464543121744318009751)
          ·
            refine ⟨1206696814682616477014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804464543121744318009751 1206696814682616477014627)
            ·
              refine ⟨1810045222023924715521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206696814682616477014627 1810045222023924715521941)
              ·
                refine ⟨84845869782371471040091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1810045222023924715521941 84845869782371471040091)
                ·
                  rfl

theorem cell21_1115348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_1115348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115348 prefixEnd_1115348 := by exact prefixLift 1115348
  have htrace : WordTrace (prefixWord ++ tailWord_1115348) baseStart_1115348 baseEnd_1115348 := by
    simpa [prefixWord, tailWord_1115348, baseEnd_1115348] using wordTrace_append hprefix tailTrace_1115348
  have hstable : (prefixWord ++ tailWord_1115348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115348).length < 2 ^ (prefixWord ++ tailWord_1115348).sum := by decide
  have hdescent : baseEnd_1115348 < baseStart_1115348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115404 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1115404 : Nat := 118140960795 + 1115404 * 2 ^ 59
def prefixEnd_1115404 : Nat := 4983230072969 + 3 ^ 40 * 1115404 * 2
def baseEnd_1115404 : Nat := 254550389310070760186825

theorem tailTrace_1115404 : CollatzResearch.WordTrace tailWord_1115404 prefixEnd_1115404 254550389310070760186825 := by
  unfold tailWord_1115404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20341063025544639341080633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27121417367392852454774177 20341063025544639341080633)
  ·
    refine ⟨15255797269158479505810475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20341063025544639341080633 15255797269158479505810475)
    ·
      refine ⟨22883695903737719258715713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15255797269158479505810475 22883695903737719258715713)
      ·
        refine ⟨17162771927803289444036785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22883695903737719258715713 17162771927803289444036785)
        ·
          refine ⟨12872078945852467083027589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17162771927803289444036785 12872078945852467083027589)
          ·
            refine ⟨2413514802347337578067673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12872078945852467083027589 2413514802347337578067673)
            ·
              refine ⟨1810136101760503183550755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413514802347337578067673 1810136101760503183550755)
              ·
                refine ⟨2715204152640754775326133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810136101760503183550755 2715204152640754775326133)
                ·
                  refine ⟨254550389310070760186825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715204152640754775326133 254550389310070760186825)
                  ·
                    rfl

theorem cell21_1115404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1115404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115404 prefixEnd_1115404 := by exact prefixLift 1115404
  have htrace : WordTrace (prefixWord ++ tailWord_1115404) baseStart_1115404 baseEnd_1115404 := by
    simpa [prefixWord, tailWord_1115404, baseEnd_1115404] using wordTrace_append hprefix tailTrace_1115404
  have hstable : (prefixWord ++ tailWord_1115404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115404).length < 2 ^ (prefixWord ++ tailWord_1115404).sum := by decide
  have hdescent : baseEnd_1115404 < baseStart_1115404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115410 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1115410 : Nat := 118140960795 + 1115410 * 2 ^ 59
def prefixEnd_1115410 : Nat := 4983230072969 + 3 ^ 40 * 1115410 * 2
def baseEnd_1115410 : Nat := 254551758591816083086813

theorem tailTrace_1115410 : CollatzResearch.WordTrace tailWord_1115410 prefixEnd_1115410 254551758591816083086813 := by
  unfold tailWord_1115410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10170586222266885426719921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27121563259378361137919789 10170586222266885426719921)
  ·
    refine ⟨7627939666700164070039941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10170586222266885426719921 7627939666700164070039941)
    ·
      refine ⟨1430238687506280763132489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7627939666700164070039941 1430238687506280763132489)
      ·
        refine ⟨1072679015629710572349367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430238687506280763132489 1072679015629710572349367)
        ·
          refine ⟨1609018523444565858524051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072679015629710572349367 1609018523444565858524051)
          ·
            refine ⟨2413527785166848787786077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609018523444565858524051 2413527785166848787786077)
            ·
              refine ⟨905072919437568295419779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2413527785166848787786077 905072919437568295419779)
              ·
                refine ⟨1357609379156352443129669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905072919437568295419779 1357609379156352443129669)
                ·
                  refine ⟨254551758591816083086813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357609379156352443129669 254551758591816083086813)
                  ·
                    rfl

theorem cell21_1115410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1115410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115410 prefixEnd_1115410 := by exact prefixLift 1115410
  have htrace : WordTrace (prefixWord ++ tailWord_1115410) baseStart_1115410 baseEnd_1115410 := by
    simpa [prefixWord, tailWord_1115410, baseEnd_1115410] using wordTrace_append hprefix tailTrace_1115410
  have hstable : (prefixWord ++ tailWord_1115410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115410).length < 2 ^ (prefixWord ++ tailWord_1115410).sum := by decide
  have hdescent : baseEnd_1115410 < baseStart_1115410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115469 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1115469 : Nat := 118140960795 + 1115469 * 2 ^ 59
def prefixEnd_1115469 : Nat := 4983230072969 + 3 ^ 40 * 1115469 * 2
def baseEnd_1115469 : Nat := 254565223195645091603359

theorem tailTrace_1115469 : CollatzResearch.WordTrace tailWord_1115469 prefixEnd_1115469 254565223195645091603359 := by
  unfold tailWord_1115469
  simp only [CollatzResearch.WordTrace]
  refine ⟨40684496795853794783277461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27122997863902529855518307 40684496795853794783277461)
  ·
    refine ⟨1907085787305646630466131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40684496795853794783277461 1907085787305646630466131)
    ·
      refine ⟨2860628680958469945699197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907085787305646630466131 2860628680958469945699197)
      ·
        refine ⟨1072735755359426229637199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2860628680958469945699197 1072735755359426229637199)
        ·
          refine ⟨1609103633039139344455799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072735755359426229637199 1609103633039139344455799)
          ·
            refine ⟨2413655449558709016683699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609103633039139344455799 2413655449558709016683699)
            ·
              refine ⟨3620483174338063525025549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413655449558709016683699 3620483174338063525025549)
              ·
                refine ⟨1357681190376773821884581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3620483174338063525025549 1357681190376773821884581)
                ·
                  refine ⟨254565223195645091603359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357681190376773821884581 254565223195645091603359)
                  ·
                    rfl

theorem cell21_1115469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1115469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115469 prefixEnd_1115469 := by exact prefixLift 1115469
  have htrace : WordTrace (prefixWord ++ tailWord_1115469) baseStart_1115469 baseEnd_1115469 := by
    simpa [prefixWord, tailWord_1115469, baseEnd_1115469] using wordTrace_append hprefix tailTrace_1115469
  have hstable : (prefixWord ++ tailWord_1115469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115469).length < 2 ^ (prefixWord ++ tailWord_1115469).sum := by decide
  have hdescent : baseEnd_1115469 < baseStart_1115469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115570 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1115570 : Nat := 118140960795 + 1115570 * 2 ^ 59
def prefixEnd_1115570 : Nat := 4983230072969 + 3 ^ 40 * 1115570 * 2
def baseEnd_1115570 : Nat := 254588272771691360419819

theorem tailTrace_1115570 : CollatzResearch.WordTrace tailWord_1115570 prefixEnd_1115570 254588272771691360419819 := by
  unfold tailWord_1115570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10172045142121972258176041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27125453712325259355136109 10172045142121972258176041)
  ·
    refine ⟨7629033856591479193632031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10172045142121972258176041 7629033856591479193632031)
    ·
      refine ⟨11443550784887218790448047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7629033856591479193632031 11443550784887218790448047)
      ·
        refine ⟨17165326177330828185672071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11443550784887218790448047 17165326177330828185672071)
        ·
          refine ⟨25747989265996242278508107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165326177330828185672071 25747989265996242278508107)
          ·
            refine ⟨38621983898994363417762161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25747989265996242278508107 38621983898994363417762161)
            ·
              refine ⟨28966487924245772563321621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38621983898994363417762161 28966487924245772563321621)
              ·
                refine ⟨1357804121449020588905701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28966487924245772563321621 1357804121449020588905701)
                ·
                  refine ⟨254588272771691360419819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1357804121449020588905701 254588272771691360419819)
                  ·
                    rfl

theorem cell21_1115570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1115570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115570 prefixEnd_1115570 := by exact prefixLift 1115570
  have htrace : WordTrace (prefixWord ++ tailWord_1115570) baseStart_1115570 baseEnd_1115570 := by
    simpa [prefixWord, tailWord_1115570, baseEnd_1115570] using wordTrace_append hprefix tailTrace_1115570
  have hstable : (prefixWord ++ tailWord_1115570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115570).length < 2 ^ (prefixWord ++ tailWord_1115570).sum := by decide
  have hdescent : baseEnd_1115570 < baseStart_1115570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115573 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1115573 : Nat := 118140960795 + 1115573 * 2 ^ 59
def prefixEnd_1115573 : Nat := 4983230072969 + 3 ^ 40 * 1115573 * 2
def baseEnd_1115573 : Nat := 254588957412564021869813

theorem tailTrace_1115573 : CollatzResearch.WordTrace tailWord_1115573 prefixEnd_1115573 254588957412564021869813 := by
  unfold tailWord_1115573
  simp only [CollatzResearch.WordTrace]
  refine ⟨40688289987477020545063373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27125526658318013696708915 40688289987477020545063373)
  ·
    refine ⟨15258108745303882704398765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40688289987477020545063373 15258108745303882704398765)
    ·
      refine ⟨5721790779488956014149537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15258108745303882704398765 5721790779488956014149537)
      ·
        refine ⟨4291343084616717010612153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5721790779488956014149537 4291343084616717010612153)
        ·
          refine ⟨3218507313462537757959115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291343084616717010612153 3218507313462537757959115)
          ·
            refine ⟨4827760970193806636938673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3218507313462537757959115 4827760970193806636938673)
            ·
              refine ⟨3620820727645354977704005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4827760970193806636938673 3620820727645354977704005)
              ·
                refine ⟨678903886433504058319501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3620820727645354977704005 678903886433504058319501)
                ·
                  refine ⟨254588957412564021869813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678903886433504058319501 254588957412564021869813)
                  ·
                    rfl

theorem cell21_1115573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1115573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115573 prefixEnd_1115573 := by exact prefixLift 1115573
  have htrace : WordTrace (prefixWord ++ tailWord_1115573) baseStart_1115573 baseEnd_1115573 := by
    simpa [prefixWord, tailWord_1115573, baseEnd_1115573] using wordTrace_append hprefix tailTrace_1115573
  have hstable : (prefixWord ++ tailWord_1115573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115573).length < 2 ^ (prefixWord ++ tailWord_1115573).sum := by decide
  have hdescent : baseEnd_1115573 < baseStart_1115573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115632 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_1115632 : Nat := 118140960795 + 1115632 * 2 ^ 59
def prefixEnd_1115632 : Nat := 4983230072969 + 3 ^ 40 * 1115632 * 2
def baseEnd_1115632 : Nat := 254602422016393030386359

theorem tailTrace_1115632 : CollatzResearch.WordTrace tailWord_1115632 prefixEnd_1115632 254602422016393030386359 := by
  unfold tailWord_1115632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20345220947131636810730575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27126961262842182414307433 20345220947131636810730575)
  ·
    refine ⟨30517831420697455216095863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20345220947131636810730575 30517831420697455216095863)
    ·
      refine ⟨45776747131046182824143795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30517831420697455216095863 45776747131046182824143795)
      ·
        refine ⟨68665120696569274236215693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45776747131046182824143795 68665120696569274236215693)
        ·
          refine ⟨25749420261213477838580885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68665120696569274236215693 25749420261213477838580885)
          ·
            refine ⟨1207004074744381773683479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25749420261213477838580885 1207004074744381773683479)
            ·
              refine ⟨1810506112116572660525219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207004074744381773683479 1810506112116572660525219)
              ·
                refine ⟨2715759168174858990787829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1810506112116572660525219 2715759168174858990787829)
                ·
                  refine ⟨254602422016393030386359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715759168174858990787829 254602422016393030386359)
                  ·
                    rfl

theorem cell21_1115632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_1115632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115632 prefixEnd_1115632 := by exact prefixLift 1115632
  have htrace : WordTrace (prefixWord ++ tailWord_1115632) baseStart_1115632 baseEnd_1115632 := by
    simpa [prefixWord, tailWord_1115632, baseEnd_1115632] using wordTrace_append hprefix tailTrace_1115632
  have hstable : (prefixWord ++ tailWord_1115632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115632).length < 2 ^ (prefixWord ++ tailWord_1115632).sum := by decide
  have hdescent : baseEnd_1115632 < baseStart_1115632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115683 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 3]
def baseStart_1115683 : Nat := 118140960795 + 1115683 * 2 ^ 59
def prefixEnd_1115683 : Nat := 4983230072969 + 3 ^ 40 * 1115683 * 2
def baseEnd_1115683 : Nat := 254614060911228275036255

theorem tailTrace_1115683 : CollatzResearch.WordTrace tailWord_1115683 prefixEnd_1115683 254614060911228275036255 := by
  unfold tailWord_1115683
  simp only [CollatzResearch.WordTrace]
  refine ⟨40692302017078509331567703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27128201344719006221045135 40692302017078509331567703)
  ·
    refine ⟨61038453025617763997351555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40692302017078509331567703 61038453025617763997351555)
    ·
      refine ⟨91557679538426645996027333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61038453025617763997351555 91557679538426645996027333)
      ·
        refine ⟨17167064913454996124255125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91557679538426645996027333 17167064913454996124255125)
        ·
          refine ⟨804706167818202943324459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17167064913454996124255125 804706167818202943324459)
          ·
            refine ⟨1207059251727304414986689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804706167818202943324459 1207059251727304414986689)
            ·
              refine ⟨905294438795478311240017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207059251727304414986689 905294438795478311240017)
              ·
                refine ⟨678970829096608733430013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905294438795478311240017 678970829096608733430013)
                ·
                  refine ⟨254614060911228275036255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 678970829096608733430013 254614060911228275036255)
                  ·
                    rfl

theorem cell21_1115683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].length) (baseStart_1115683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115683 prefixEnd_1115683 := by exact prefixLift 1115683
  have htrace : WordTrace (prefixWord ++ tailWord_1115683) baseStart_1115683 baseEnd_1115683 := by
    simpa [prefixWord, tailWord_1115683, baseEnd_1115683] using wordTrace_append hprefix tailTrace_1115683
  have hstable : (prefixWord ++ tailWord_1115683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115683).length < 2 ^ (prefixWord ++ tailWord_1115683).sum := by decide
  have hdescent : baseEnd_1115683 < baseStart_1115683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115694 : List Nat := [4, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1115694 : Nat := 118140960795 + 1115694 * 2 ^ 59
def prefixEnd_1115694 : Nat := 4983230072969 + 3 ^ 40 * 1115694 * 2
def baseEnd_1115694 : Nat := 84872190420364900117633

theorem tailTrace_1115694 : CollatzResearch.WordTrace tailWord_1115694 prefixEnd_1115694 84872190420364900117633 := by
  unfold tailWord_1115694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086587902504832276277267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27128468813359105473478757 5086587902504832276277267)
  ·
    refine ⟨7629881853757248414415901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5086587902504832276277267 7629881853757248414415901)
    ·
      refine ⟨2861205695158968155405963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7629881853757248414415901 2861205695158968155405963)
      ·
        refine ⟨4291808542738452233108945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861205695158968155405963 4291808542738452233108945)
        ·
          refine ⟨3218856407053839174831709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291808542738452233108945 3218856407053839174831709)
          ·
            refine ⟨1207071152645189690561891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3218856407053839174831709 1207071152645189690561891)
            ·
              refine ⟨1810606728967784535842837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207071152645189690561891 1810606728967784535842837)
              ·
                refine ⟨84872190420364900117633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1810606728967784535842837 84872190420364900117633)
                ·
                  rfl

theorem cell21_1115694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1115694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115694 prefixEnd_1115694 := by exact prefixLift 1115694
  have htrace : WordTrace (prefixWord ++ tailWord_1115694) baseStart_1115694 baseEnd_1115694 := by
    simpa [prefixWord, tailWord_1115694, baseEnd_1115694] using wordTrace_append hprefix tailTrace_1115694
  have hstable : (prefixWord ++ tailWord_1115694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115694).length < 2 ^ (prefixWord ++ tailWord_1115694).sum := by decide
  have hdescent : baseEnd_1115694 < baseStart_1115694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115708 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_1115708 : Nat := 118140960795 + 1115708 * 2 ^ 59
def prefixEnd_1115708 : Nat := 4983230072969 + 3 ^ 40 * 1115708 * 2
def baseEnd_1115708 : Nat := 254619766251833787119537

theorem tailTrace_1115708 : CollatzResearch.WordTrace tailWord_1115708 prefixEnd_1115708 254619766251833787119537 := by
  unfold tailWord_1115708
  simp only [CollatzResearch.WordTrace]
  refine ⟨20346606920993969300613889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27128809227991959067485185 20346606920993969300613889)
  ·
    refine ⟨15259955190745476975460417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20346606920993969300613889 15259955190745476975460417)
    ·
      refine ⟨11444966393059107731595313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15259955190745476975460417 11444966393059107731595313)
      ·
        refine ⟨8583724794794330798696485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11444966393059107731595313 8583724794794330798696485)
        ·
          refine ⟨1609448399023937024755591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8583724794794330798696485 1609448399023937024755591)
          ·
            refine ⟨2414172598535905537133387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609448399023937024755591 2414172598535905537133387)
            ·
              refine ⟨3621258897803858305700081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414172598535905537133387 3621258897803858305700081)
              ·
                refine ⟨2715944173352893729275061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3621258897803858305700081 2715944173352893729275061)
                ·
                  refine ⟨254619766251833787119537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2715944173352893729275061 254619766251833787119537)
                  ·
                    rfl

theorem cell21_1115708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_1115708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115708 prefixEnd_1115708 := by exact prefixLift 1115708
  have htrace : WordTrace (prefixWord ++ tailWord_1115708) baseStart_1115708 baseEnd_1115708 := by
    simpa [prefixWord, tailWord_1115708, baseEnd_1115708] using wordTrace_append hprefix tailTrace_1115708
  have hstable : (prefixWord ++ tailWord_1115708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115708).length < 2 ^ (prefixWord ++ tailWord_1115708).sum := by decide
  have hdescent : baseEnd_1115708 < baseStart_1115708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115781 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1115781 : Nat := 118140960795 + 1115781 * 2 ^ 59
def prefixEnd_1115781 : Nat := 4983230072969 + 3 ^ 40 * 1115781 * 2
def baseEnd_1115781 : Nat := 254636425846401882402721

theorem tailTrace_1115781 : CollatzResearch.WordTrace tailWord_1115781 prefixEnd_1115781 254636425846401882402721 := by
  unfold tailWord_1115781
  simp only [CollatzResearch.WordTrace]
  refine ⟨40695876370723472068635197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27130584247148981379090131 40695876370723472068635197)
  ·
    refine ⟨15260953639021302025738199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40695876370723472068635197 15260953639021302025738199)
    ·
      refine ⟨22891430458531953038607299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15260953639021302025738199 22891430458531953038607299)
      ·
        refine ⟨34337145687797929557910949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22891430458531953038607299 34337145687797929557910949)
        ·
          refine ⟨6438214816462111792108303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34337145687797929557910949 6438214816462111792108303)
          ·
            refine ⟨9657322224693167688162455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6438214816462111792108303 9657322224693167688162455)
            ·
              refine ⟨14485983337039751532243683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9657322224693167688162455 14485983337039751532243683)
              ·
                refine ⟨21728975005559627298365525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14485983337039751532243683 21728975005559627298365525)
                ·
                  refine ⟨254636425846401882402721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21728975005559627298365525 254636425846401882402721)
                  ·
                    rfl

theorem cell21_1115781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1115781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115781 prefixEnd_1115781 := by exact prefixLift 1115781
  have htrace : WordTrace (prefixWord ++ tailWord_1115781) baseStart_1115781 baseEnd_1115781 := by
    simpa [prefixWord, tailWord_1115781, baseEnd_1115781] using wordTrace_append hprefix tailTrace_1115781
  have hstable : (prefixWord ++ tailWord_1115781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115781).length < 2 ^ (prefixWord ++ tailWord_1115781).sum := by decide
  have hdescent : baseEnd_1115781 < baseStart_1115781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115812 : List Nat := [2, 3, 1, 2, 2, 2, 1, 8]
def baseStart_1115812 : Nat := 118140960795 + 1115812 * 2 ^ 59
def prefixEnd_1115812 : Nat := 4983230072969 + 3 ^ 40 * 1115812 * 2
def baseEnd_1115812 : Nat := 84881166822917572461997

theorem tailTrace_1115812 : CollatzResearch.WordTrace tailWord_1115812 prefixEnd_1115812 84881166822917572461997 := by
  unfold tailWord_1115812
  simp only [CollatzResearch.WordTrace]
  refine ⟨20348503516805582181506845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27131338022407442908675793 20348503516805582181506845)
  ·
    refine ⟨7630688818802093318065067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20348503516805582181506845 7630688818802093318065067)
    ·
      refine ⟨11446033228203139977097601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630688818802093318065067 11446033228203139977097601)
      ·
        refine ⟨8584524921152354982823201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11446033228203139977097601 8584524921152354982823201)
        ·
          refine ⟨6438393690864266237117401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8584524921152354982823201 6438393690864266237117401)
          ·
            refine ⟨4828795268148199677838051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6438393690864266237117401 4828795268148199677838051)
            ·
              refine ⟨7243192902222299516757077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4828795268148199677838051 7243192902222299516757077)
              ·
                refine ⟨84881166822917572461997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7243192902222299516757077 84881166822917572461997)
                ·
                  rfl

theorem cell21_1115812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_1115812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115812 prefixEnd_1115812 := by exact prefixLift 1115812
  have htrace : WordTrace (prefixWord ++ tailWord_1115812) baseStart_1115812 baseEnd_1115812 := by
    simpa [prefixWord, tailWord_1115812, baseEnd_1115812] using wordTrace_append hprefix tailTrace_1115812
  have hstable : (prefixWord ++ tailWord_1115812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115812).length < 2 ^ (prefixWord ++ tailWord_1115812).sum := by decide
  have hdescent : baseEnd_1115812 < baseStart_1115812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115846 : List Nat := [6, 1, 2, 1, 1, 10]
def baseStart_1115846 : Nat := 118140960795 + 1115846 * 2 ^ 59
def prefixEnd_1115846 : Nat := 4983230072969 + 3 ^ 40 * 1115846 * 2
def baseEnd_1115846 : Nat := 9431528138221341252565

theorem tailTrace_1115846 : CollatzResearch.WordTrace tailWord_1115846 prefixEnd_1115846 9431528138221341252565 := by
  unfold tailWord_1115846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271820222358999630304731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27132164743658658779834261 1271820222358999630304731)
  ·
    refine ⟨1907730333538499445457097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271820222358999630304731 1907730333538499445457097)
    ·
      refine ⟨1430797750153874584092823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907730333538499445457097 1430797750153874584092823)
      ·
        refine ⟨2146196625230811876139235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430797750153874584092823 2146196625230811876139235)
        ·
          refine ⟨3219294937846217814208853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146196625230811876139235 3219294937846217814208853)
          ·
            refine ⟨9431528138221341252565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3219294937846217814208853 9431528138221341252565)
            ·
              rfl

theorem cell21_1115846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 10].length) (baseStart_1115846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115846 prefixEnd_1115846 := by exact prefixLift 1115846
  have htrace : WordTrace (prefixWord ++ tailWord_1115846) baseStart_1115846 baseEnd_1115846 := by
    simpa [prefixWord, tailWord_1115846, baseEnd_1115846] using wordTrace_append hprefix tailTrace_1115846
  have hstable : (prefixWord ++ tailWord_1115846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115846).length < 2 ^ (prefixWord ++ tailWord_1115846).sum := by decide
  have hdescent : baseEnd_1115846 < baseStart_1115846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115953 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 3]
def baseStart_1115953 : Nat := 118140960795 + 1115953 * 2 ^ 59
def prefixEnd_1115953 : Nat := 4983230072969 + 3 ^ 40 * 1115953 * 2
def baseEnd_1115953 : Nat := 254675678589767805535703

theorem tailTrace_1115953 : CollatzResearch.WordTrace tailWord_1115953 prefixEnd_1115953 254675678589767805535703 := by
  unfold tailWord_1115953
  simp only [CollatzResearch.WordTrace]
  refine ⟨40702149726100345443896513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27134766484066896962597675 40702149726100345443896513)
  ·
    refine ⟨30526612294575259082922385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40702149726100345443896513 30526612294575259082922385)
    ·
      refine ⟨22894959220931444312191789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30526612294575259082922385 22894959220931444312191789)
      ·
        refine ⟨8585609707849291617071921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22894959220931444312191789 8585609707849291617071921)
        ·
          refine ⟨6439207280886968712803941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8585609707849291617071921 6439207280886968712803941)
          ·
            refine ⟨1207351365166306633650739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6439207280886968712803941 1207351365166306633650739)
            ·
              refine ⟨1811027047749459950476109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207351365166306633650739 1811027047749459950476109)
              ·
                refine ⟨679135142906047481428541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811027047749459950476109 679135142906047481428541)
                ·
                  refine ⟨254675678589767805535703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679135142906047481428541 254675678589767805535703)
                  ·
                    rfl

theorem cell21_1115953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_1115953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115953 prefixEnd_1115953 := by exact prefixLift 1115953
  have htrace : WordTrace (prefixWord ++ tailWord_1115953) baseStart_1115953 baseEnd_1115953 := by
    simpa [prefixWord, tailWord_1115953, baseEnd_1115953] using wordTrace_append hprefix tailTrace_1115953
  have hstable : (prefixWord ++ tailWord_1115953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115953).length < 2 ^ (prefixWord ++ tailWord_1115953).sum := by decide
  have hdescent : baseEnd_1115953 < baseStart_1115953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115981 : List Nat := [1, 6, 1, 2, 1, 1, 1, 8]
def baseStart_1115981 : Nat := 118140960795 + 1115981 * 2 ^ 59
def prefixEnd_1115981 : Nat := 4983230072969 + 3 ^ 40 * 1115981 * 2
def baseEnd_1115981 : Nat := 84894022857081993022993

theorem tailTrace_1115981 : CollatzResearch.WordTrace tailWord_1115981 prefixEnd_1115981 84894022857081993022993 := by
  unfold tailWord_1115981
  simp only [CollatzResearch.WordTrace]
  refine ⟨40703170969998906225915797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27135447313332604150610531 40703170969998906225915797)
  ·
    refine ⟨1907961139218698729339803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40703170969998906225915797 1907961139218698729339803)
    ·
      refine ⟨2861941708828048094009705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907961139218698729339803 2861941708828048094009705)
      ·
        refine ⟨2146456281621036070507279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2861941708828048094009705 2146456281621036070507279)
        ·
          refine ⟨3219684422431554105760919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146456281621036070507279 3219684422431554105760919)
          ·
            refine ⟨4829526633647331158641379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3219684422431554105760919 4829526633647331158641379)
            ·
              refine ⟨7244289950470996737962069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829526633647331158641379 7244289950470996737962069)
              ·
                refine ⟨84894022857081993022993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7244289950470996737962069 84894022857081993022993)
                ·
                  rfl

theorem cell21_1115981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_1115981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1115981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1115981 prefixEnd_1115981 := by exact prefixLift 1115981
  have htrace : WordTrace (prefixWord ++ tailWord_1115981) baseStart_1115981 baseEnd_1115981 := by
    simpa [prefixWord, tailWord_1115981, baseEnd_1115981] using wordTrace_append hprefix tailTrace_1115981
  have hstable : (prefixWord ++ tailWord_1115981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115981).length < 2 ^ (prefixWord ++ tailWord_1115981).sum := by decide
  have hdescent : baseEnd_1115981 < baseStart_1115981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116116 : List Nat := [2, 4, 1, 2, 1, 1, 3, 7]
def baseStart_1116116 : Nat := 118140960795 + 1116116 * 2 ^ 59
def prefixEnd_1116116 : Nat := 4983230072969 + 3 ^ 40 * 1116116 * 2
def baseEnd_1116116 : Nat := 84904292470171914772901

theorem tailTrace_1116116 : CollatzResearch.WordTrace tailWord_1116116 prefixEnd_1116116 84904292470171914772901 := by
  unfold tailWord_1116116
  simp only [CollatzResearch.WordTrace]
  refine ⟨20354047412254912141040101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27138729883006549521386801 20354047412254912141040101)
  ·
    refine ⟨3816383889797796026445019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20354047412254912141040101 3816383889797796026445019)
    ·
      refine ⟨5724575834696694039667529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816383889797796026445019 5724575834696694039667529)
      ·
        refine ⟨4293431876022520529750647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5724575834696694039667529 4293431876022520529750647)
        ·
          refine ⟨6440147814033780794625971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293431876022520529750647 6440147814033780794625971)
          ·
            refine ⟨9660221721050671191938957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440147814033780794625971 9660221721050671191938957)
            ·
              refine ⟨3622583145394001696977109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9660221721050671191938957 3622583145394001696977109)
              ·
                refine ⟨84904292470171914772901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3622583145394001696977109 84904292470171914772901)
                ·
                  rfl

theorem cell21_1116116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_1116116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116116 prefixEnd_1116116 := by exact prefixLift 1116116
  have htrace : WordTrace (prefixWord ++ tailWord_1116116) baseStart_1116116 baseEnd_1116116 := by
    simpa [prefixWord, tailWord_1116116, baseEnd_1116116] using wordTrace_append hprefix tailTrace_1116116
  have hstable : (prefixWord ++ tailWord_1116116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116116).length < 2 ^ (prefixWord ++ tailWord_1116116).sum := by decide
  have hdescent : baseEnd_1116116 < baseStart_1116116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116122 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_1116122 : Nat := 118140960795 + 1116122 * 2 ^ 59
def prefixEnd_1116122 : Nat := 4983230072969 + 3 ^ 40 * 1116122 * 2
def baseEnd_1116122 : Nat := 254714246692261067218691

theorem tailTrace_1116122 : CollatzResearch.WordTrace tailWord_1116122 prefixEnd_1116122 254714246692261067218691 := by
  unfold tailWord_1116122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10177078415622021826699655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27138875774992058204532413 10177078415622021826699655)
  ·
    refine ⟨15265617623433032740049483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10177078415622021826699655 15265617623433032740049483)
    ·
      refine ⟨22898426435149549110074225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15265617623433032740049483 22898426435149549110074225)
      ·
        refine ⟨17173819826362161832555669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22898426435149549110074225 17173819826362161832555669)
        ·
          refine ⟨805022804360726335901047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17173819826362161832555669 805022804360726335901047)
          ·
            refine ⟨1207534206541089503851571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805022804360726335901047 1207534206541089503851571)
            ·
              refine ⟨1811301309811634255777357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207534206541089503851571 1811301309811634255777357)
              ·
                refine ⟨679237991179362845916509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811301309811634255777357 679237991179362845916509)
                ·
                  refine ⟨254714246692261067218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679237991179362845916509 254714246692261067218691)
                  ·
                    rfl

theorem cell21_1116122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_1116122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116122 prefixEnd_1116122 := by exact prefixLift 1116122
  have htrace : WordTrace (prefixWord ++ tailWord_1116122) baseStart_1116122 baseEnd_1116122 := by
    simpa [prefixWord, tailWord_1116122, baseEnd_1116122] using wordTrace_append hprefix tailTrace_1116122
  have hstable : (prefixWord ++ tailWord_1116122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116122).length < 2 ^ (prefixWord ++ tailWord_1116122).sum := by decide
  have hdescent : baseEnd_1116122 < baseStart_1116122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 3]
def baseStart_1116147 : Nat := 118140960795 + 1116147 * 2 ^ 59
def prefixEnd_1116147 : Nat := 4983230072969 + 3 ^ 40 * 1116147 * 2
def baseEnd_1116147 : Nat := 254719952032866579301973

theorem tailTrace_1116147 : CollatzResearch.WordTrace tailWord_1116147 prefixEnd_1116147 254719952032866579301973 := by
  unfold tailWord_1116147
  simp only [CollatzResearch.WordTrace]
  refine ⟨40709225487397516576458695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27139483658265011050972463 40709225487397516576458695)
  ·
    refine ⟨61063838231096274864688043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40709225487397516576458695 61063838231096274864688043)
    ·
      refine ⟨91595757346644412297032065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61063838231096274864688043 91595757346644412297032065)
      ·
        refine ⟨68696818009983309222774049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91595757346644412297032065 68696818009983309222774049)
        ·
          refine ⟨51522613507487481917080537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68696818009983309222774049 51522613507487481917080537)
          ·
            refine ⟨38641960130615611437810403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51522613507487481917080537 38641960130615611437810403)
            ·
              refine ⟨57962940195923417156715605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38641960130615611437810403 57962940195923417156715605)
              ·
                refine ⟨679253205420977544805261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 57962940195923417156715605 679253205420977544805261)
                ·
                  refine ⟨254719952032866579301973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679253205420977544805261 254719952032866579301973)
                  ·
                    rfl

theorem cell21_1116147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].length) (baseStart_1116147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116147 prefixEnd_1116147 := by exact prefixLift 1116147
  have htrace : WordTrace (prefixWord ++ tailWord_1116147) baseStart_1116147 baseEnd_1116147 := by
    simpa [prefixWord, tailWord_1116147, baseEnd_1116147] using wordTrace_append hprefix tailTrace_1116147
  have hstable : (prefixWord ++ tailWord_1116147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116147).length < 2 ^ (prefixWord ++ tailWord_1116147).sum := by decide
  have hdescent : baseEnd_1116147 < baseStart_1116147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116285 : List Nat := [1, 4, 1, 1, 3, 4, 2, 5]
def baseStart_1116285 : Nat := 118140960795 + 1116285 * 2 ^ 59
def prefixEnd_1116285 : Nat := 4983230072969 + 3 ^ 40 * 1116285 * 2
def baseEnd_1116285 : Nat := 84917148504336335333897

theorem tailTrace_1116285 : CollatzResearch.WordTrace tailWord_1116285 prefixEnd_1116285 84917148504336335333897 := by
  unfold tailWord_1116285
  simp only [CollatzResearch.WordTrace]
  refine ⟨40714258760897566144982309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27142839173931710763321539 40714258760897566144982309)
  ·
    refine ⟨7633923517668293652184183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40714258760897566144982309 7633923517668293652184183)
    ·
      refine ⟨11450885276502440478276275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633923517668293652184183 11450885276502440478276275)
      ·
        refine ⟨17176327914753660717414413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450885276502440478276275 17176327914753660717414413)
        ·
          refine ⟨6441122968032622769030405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17176327914753660717414413 6441122968032622769030405)
          ·
            refine ⟨1207710556506116769193201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6441122968032622769030405 1207710556506116769193201)
            ·
              refine ⟨905782917379587576894901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207710556506116769193201 905782917379587576894901)
              ·
                refine ⟨84917148504336335333897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 905782917379587576894901 84917148504336335333897)
                ·
                  rfl

theorem cell21_1116285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 5].length) (baseStart_1116285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116285 prefixEnd_1116285 := by exact prefixLift 1116285
  have htrace : WordTrace (prefixWord ++ tailWord_1116285) baseStart_1116285 baseEnd_1116285 := by
    simpa [prefixWord, tailWord_1116285, baseEnd_1116285] using wordTrace_append hprefix tailTrace_1116285
  have hstable : (prefixWord ++ tailWord_1116285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116285).length < 2 ^ (prefixWord ++ tailWord_1116285).sum := by decide
  have hdescent : baseEnd_1116285 < baseStart_1116285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116420 : List Nat := [2, 3, 2, 2, 3, 1, 8]
def baseStart_1116420 : Nat := 118140960795 + 1116420 * 2 ^ 59
def prefixEnd_1116420 : Nat := 4983230072969 + 3 ^ 40 * 1116420 * 2
def baseEnd_1116420 : Nat := 28309139372475419027935

theorem tailTrace_1116420 : CollatzResearch.WordTrace tailWord_1116420 prefixEnd_1116420 28309139372475419027935 := by
  unfold tailWord_1116420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20359591307704242100573357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27146121743605656134097809 20359591307704242100573357)
  ·
    refine ⟨7634846740389090787715009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20359591307704242100573357 7634846740389090787715009)
    ·
      refine ⟨5726135055291818090786257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7634846740389090787715009 5726135055291818090786257)
      ·
        refine ⟨4294601291468863568089693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5726135055291818090786257 4294601291468863568089693)
        ·
          refine ⟨1610475484300823838033635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4294601291468863568089693 1610475484300823838033635)
          ·
            refine ⟨2415713226451235757050453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610475484300823838033635 2415713226451235757050453)
            ·
              refine ⟨28309139372475419027935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2415713226451235757050453 28309139372475419027935)
              ·
                rfl

theorem cell21_1116420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 8].length) (baseStart_1116420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116420 prefixEnd_1116420 := by exact prefixLift 1116420
  have htrace : WordTrace (prefixWord ++ tailWord_1116420) baseStart_1116420 baseEnd_1116420 := by
    simpa [prefixWord, tailWord_1116420, baseEnd_1116420] using wordTrace_append hprefix tailTrace_1116420
  have hstable : (prefixWord ++ tailWord_1116420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116420).length < 2 ^ (prefixWord ++ tailWord_1116420).sum := by decide
  have hdescent : baseEnd_1116420 < baseStart_1116420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116541 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1116541 : Nat := 118140960795 + 1116541 * 2 ^ 59
def prefixEnd_1116541 : Nat := 4983230072969 + 3 ^ 40 * 1116541 * 2
def baseEnd_1116541 : Nat := 254809868200809449734501

theorem tailTrace_1116541 : CollatzResearch.WordTrace tailWord_1116541 prefixEnd_1116541 254809868200809449734501 := by
  unfold tailWord_1116541
  simp only [CollatzResearch.WordTrace]
  refine ⟨40723595847970121866301477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27149063898646747910867651 40723595847970121866301477)
  ·
    refine ⟨7635674221494397849931527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40723595847970121866301477 7635674221494397849931527)
    ·
      refine ⟨11453511332241596774897291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635674221494397849931527 11453511332241596774897291)
      ·
        refine ⟨17180266998362395162345937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11453511332241596774897291 17180266998362395162345937)
        ·
          refine ⟨12885200248771796371759453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17180266998362395162345937 12885200248771796371759453)
          ·
            refine ⟨4831950093289423639409795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12885200248771796371759453 4831950093289423639409795)
            ·
              refine ⟨7247925139934135459114693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831950093289423639409795 7247925139934135459114693)
              ·
                refine ⟨1358985963737650398584005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7247925139934135459114693 1358985963737650398584005)
                ·
                  refine ⟨254809868200809449734501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1358985963737650398584005 254809868200809449734501)
                  ·
                    rfl

theorem cell21_1116541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1116541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116541 prefixEnd_1116541 := by exact prefixLift 1116541
  have htrace : WordTrace (prefixWord ++ tailWord_1116541) baseStart_1116541 baseEnd_1116541 := by
    simpa [prefixWord, tailWord_1116541, baseEnd_1116541] using wordTrace_append hprefix tailTrace_1116541
  have hstable : (prefixWord ++ tailWord_1116541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116541).length < 2 ^ (prefixWord ++ tailWord_1116541).sum := by decide
  have hdescent : baseEnd_1116541 < baseStart_1116541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116555 : List Nat := [1, 1, 1, 1, 4, 4, 3, 6]
def baseStart_1116555 : Nat := 118140960795 + 1116555 * 2 ^ 59
def prefixEnd_1116555 : Nat := 4983230072969 + 3 ^ 40 * 1116555 * 2
def baseEnd_1116555 : Nat := 84937687730516178833713

theorem tailTrace_1116555 : CollatzResearch.WordTrace tailWord_1116555 prefixEnd_1116555 84937687730516178833713 := by
  unfold tailWord_1116555
  simp only [CollatzResearch.WordTrace]
  refine ⟨40724106469919402257311119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27149404313279601504874079 40724106469919402257311119)
  ·
    refine ⟨61086159704879103385966679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40724106469919402257311119 61086159704879103385966679)
    ·
      refine ⟨91629239557318655078950019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61086159704879103385966679 91629239557318655078950019)
      ·
        refine ⟨137443859335977982618425029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91629239557318655078950019 137443859335977982618425029)
        ·
          refine ⟨25770723625495871740954693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137443859335977982618425029 25770723625495871740954693)
          ·
            refine ⟨4832010679780475951429005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25770723625495871740954693 4832010679780475951429005)
            ·
              refine ⟨1812004004917678481785877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4832010679780475951429005 1812004004917678481785877)
              ·
                refine ⟨84937687730516178833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1812004004917678481785877 84937687730516178833713)
                ·
                  rfl

theorem cell21_1116555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_1116555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116555 prefixEnd_1116555 := by exact prefixLift 1116555
  have htrace : WordTrace (prefixWord ++ tailWord_1116555) baseStart_1116555 baseEnd_1116555 := by
    simpa [prefixWord, tailWord_1116555, baseEnd_1116555] using wordTrace_append hprefix tailTrace_1116555
  have hstable : (prefixWord ++ tailWord_1116555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116555).length < 2 ^ (prefixWord ++ tailWord_1116555).sum := by decide
  have hdescent : baseEnd_1116555 < baseStart_1116555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116558 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1116558 : Nat := 118140960795 + 1116558 * 2 ^ 59
def prefixEnd_1116558 : Nat := 4983230072969 + 3 ^ 40 * 1116558 * 2
def baseEnd_1116558 : Nat := 254813747832421197951133

theorem tailTrace_1116558 : CollatzResearch.WordTrace tailWord_1116558 prefixEnd_1116558 254813747832421197951133 := by
  unfold tailWord_1116558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090526986113566721208791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27149477259272355846446885 5090526986113566721208791)
  ·
    refine ⟨7635790479170350081813187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5090526986113566721208791 7635790479170350081813187)
    ·
      refine ⟨11453685718755525122719781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7635790479170350081813187 11453685718755525122719781)
      ·
        refine ⟨2147566072266660960509959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11453685718755525122719781 2147566072266660960509959)
        ·
          refine ⟨3221349108399991440764939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147566072266660960509959 3221349108399991440764939)
          ·
            refine ⟨4832023662599987161147409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221349108399991440764939 4832023662599987161147409)
            ·
              refine ⟨3624017746949990370860557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832023662599987161147409 3624017746949990370860557)
              ·
                refine ⟨1359006655106246389072709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624017746949990370860557 1359006655106246389072709)
                ·
                  refine ⟨254813747832421197951133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359006655106246389072709 254813747832421197951133)
                  ·
                    rfl

theorem cell21_1116558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1116558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116558 prefixEnd_1116558 := by exact prefixLift 1116558
  have htrace : WordTrace (prefixWord ++ tailWord_1116558) baseStart_1116558 baseEnd_1116558 := by
    simpa [prefixWord, tailWord_1116558, baseEnd_1116558] using wordTrace_append hprefix tailTrace_1116558
  have hstable : (prefixWord ++ tailWord_1116558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116558).length < 2 ^ (prefixWord ++ tailWord_1116558).sum := by decide
  have hdescent : baseEnd_1116558 < baseStart_1116558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116609 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 4]
def baseStart_1116609 : Nat := 118140960795 + 1116609 * 2 ^ 59
def prefixEnd_1116609 : Nat := 4983230072969 + 3 ^ 40 * 1116609 * 2
def baseEnd_1116609 : Nat := 254825386727256442601029

theorem tailTrace_1116609 : CollatzResearch.WordTrace tailWord_1116609 prefixEnd_1116609 254825386727256442601029 := by
  unfold tailWord_1116609
  simp only [CollatzResearch.WordTrace]
  refine ⟨40726076011723769479776881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27150717341149179653184587 40726076011723769479776881)
  ·
    refine ⟨30544557008792827109832661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40726076011723769479776881 30544557008792827109832661)
    ·
      refine ⟨715888054893581885386703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30544557008792827109832661 715888054893581885386703)
      ·
        refine ⟨1073832082340372828080055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715888054893581885386703 1073832082340372828080055)
        ·
          refine ⟨1610748123510559242120083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073832082340372828080055 1610748123510559242120083)
          ·
            refine ⟨2416122185265838863180125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610748123510559242120083 2416122185265838863180125)
            ·
              refine ⟨906045819474689573692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2416122185265838863180125 906045819474689573692547)
              ·
                refine ⟨1359068729212034360538821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906045819474689573692547 1359068729212034360538821)
                ·
                  refine ⟨254825386727256442601029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359068729212034360538821 254825386727256442601029)
                  ·
                    rfl

theorem cell21_1116609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_1116609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116609 prefixEnd_1116609 := by exact prefixLift 1116609
  have htrace : WordTrace (prefixWord ++ tailWord_1116609) baseStart_1116609 baseEnd_1116609 := by
    simpa [prefixWord, tailWord_1116609, baseEnd_1116609] using wordTrace_append hprefix tailTrace_1116609
  have hstable : (prefixWord ++ tailWord_1116609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116609).length < 2 ^ (prefixWord ++ tailWord_1116609).sum := by decide
  have hdescent : baseEnd_1116609 < baseStart_1116609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116769 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 4]
def baseStart_1116769 : Nat := 118140960795 + 1116769 * 2 ^ 59
def prefixEnd_1116769 : Nat := 4983230072969 + 3 ^ 40 * 1116769 * 2
def baseEnd_1116769 : Nat := 254861900907131719934035

theorem tailTrace_1116769 : CollatzResearch.WordTrace tailWord_1116769 prefixEnd_1116769 254861900907131719934035 := by
  unfold tailWord_1116769
  simp only [CollatzResearch.WordTrace]
  refine ⟨40731911691144116805601361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27154607794096077870400907 40731911691144116805601361)
  ·
    refine ⟨30548933768358087604201021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40731911691144116805601361 30548933768358087604201021)
    ·
      refine ⟨11455850163134282851575383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30548933768358087604201021 11455850163134282851575383)
      ·
        refine ⟨17183775244701424277363075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11455850163134282851575383 17183775244701424277363075)
        ·
          refine ⟨25775662867052136416044613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17183775244701424277363075 25775662867052136416044613)
          ·
            refine ⟨4832936787572275578008365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25775662867052136416044613 4832936787572275578008365)
            ·
              refine ⟨1812351295339603341753137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4832936787572275578008365 1812351295339603341753137)
              ·
                refine ⟨1359263471504702506314853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812351295339603341753137 1359263471504702506314853)
                ·
                  refine ⟨254861900907131719934035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1359263471504702506314853 254861900907131719934035)
                  ·
                    rfl

theorem cell21_1116769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_1116769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116769 prefixEnd_1116769 := by exact prefixLift 1116769
  have htrace : WordTrace (prefixWord ++ tailWord_1116769) baseStart_1116769 baseEnd_1116769 := by
    simpa [prefixWord, tailWord_1116769, baseEnd_1116769] using wordTrace_append hprefix tailTrace_1116769
  have hstable : (prefixWord ++ tailWord_1116769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116769).length < 2 ^ (prefixWord ++ tailWord_1116769).sum := by decide
  have hdescent : baseEnd_1116769 < baseStart_1116769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116800 : List Nat := [2, 1, 1, 2, 1, 7, 2, 5]
def baseStart_1116800 : Nat := 118140960795 + 1116800 * 2 ^ 59
def prefixEnd_1116800 : Nat := 4983230072969 + 3 ^ 40 * 1116800 * 2
def baseEnd_1116800 : Nat := 84956325176494184972435

theorem tailTrace_1116800 : CollatzResearch.WordTrace tailWord_1116800 prefixEnd_1116800 84956325176494184972435 := by
  unfold tailWord_1116800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366521177015904549989927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27155361569354539399986569 20366521177015904549989927)
  ·
    refine ⟨30549781765523856824984891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20366521177015904549989927 30549781765523856824984891)
    ·
      refine ⟨45824672648285785237477337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30549781765523856824984891 45824672648285785237477337)
      ·
        refine ⟨34368504486214338928108003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45824672648285785237477337 34368504486214338928108003)
        ·
          refine ⟨51552756729321508392162005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34368504486214338928108003 51552756729321508392162005)
          ·
            refine ⟨1208267735843472852941297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51552756729321508392162005 1208267735843472852941297)
            ·
              refine ⟨906200801882604639705973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208267735843472852941297 906200801882604639705973)
              ·
                refine ⟨84956325176494184972435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906200801882604639705973 84956325176494184972435)
                ·
                  rfl

theorem cell21_1116800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_1116800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116800 prefixEnd_1116800 := by exact prefixLift 1116800
  have htrace : WordTrace (prefixWord ++ tailWord_1116800) baseStart_1116800 baseEnd_1116800 := by
    simpa [prefixWord, tailWord_1116800, baseEnd_1116800] using wordTrace_append hprefix tailTrace_1116800
  have hstable : (prefixWord ++ tailWord_1116800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116800).length < 2 ^ (prefixWord ++ tailWord_1116800).sum := by decide
  have hdescent : baseEnd_1116800 < baseStart_1116800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116882 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1116882 : Nat := 118140960795 + 1116882 * 2 ^ 59
def prefixEnd_1116882 : Nat := 4983230072969 + 3 ^ 40 * 1116882 * 2
def baseEnd_1116882 : Nat := 254887689046668634550471

theorem tailTrace_1116882 : CollatzResearch.WordTrace tailWord_1116882 prefixEnd_1116882 254887689046668634550471 := by
  unfold tailWord_1116882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10184008284933684276116225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27157355426489824736309933 10184008284933684276116225)
  ·
    refine ⟨7638006213700263207087169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10184008284933684276116225 7638006213700263207087169)
    ·
      refine ⟨5728504660275197405315377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7638006213700263207087169 5728504660275197405315377)
      ·
        refine ⟨4296378495206398053986533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5728504660275197405315377 4296378495206398053986533)
        ·
          refine ⟨805570967851199635122475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4296378495206398053986533 805570967851199635122475)
          ·
            refine ⟨1208356451776799452683713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805570967851199635122475 1208356451776799452683713)
            ·
              refine ⟨906267338832599589512785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208356451776799452683713 906267338832599589512785)
              ·
                refine ⟨679700504124449692134589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906267338832599589512785 679700504124449692134589)
                ·
                  refine ⟨254887689046668634550471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679700504124449692134589 254887689046668634550471)
                  ·
                    rfl

theorem cell21_1116882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1116882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116882 prefixEnd_1116882 := by exact prefixLift 1116882
  have htrace : WordTrace (prefixWord ++ tailWord_1116882) baseStart_1116882 baseEnd_1116882 := by
    simpa [prefixWord, tailWord_1116882, baseEnd_1116882] using wordTrace_append hprefix tailTrace_1116882
  have hstable : (prefixWord ++ tailWord_1116882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116882).length < 2 ^ (prefixWord ++ tailWord_1116882).sum := by decide
  have hdescent : baseEnd_1116882 < baseStart_1116882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116935 : List Nat := [1, 1, 4, 4, 1, 2, 8]
def baseStart_1116935 : Nat := 118140960795 + 1116935 * 2 ^ 59
def prefixEnd_1116935 : Nat := 4983230072969 + 3 ^ 40 * 1116935 * 2
def baseEnd_1116935 : Nat := 28322198263194702240781

theorem tailTrace_1116935 : CollatzResearch.WordTrace tailWord_1116935 prefixEnd_1116935 28322198263194702240781 := by
  unfold tailWord_1116935
  simp only [CollatzResearch.WordTrace]
  refine ⟨40737966208542727156144259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27158644139028484770762839 40737966208542727156144259)
  ·
    refine ⟨61106949312814090734216389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40737966208542727156144259 61106949312814090734216389)
    ·
      refine ⟨11457552996152642012665573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61106949312814090734216389 11457552996152642012665573)
      ·
        refine ⟨2148291186778620377374795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11457552996152642012665573 2148291186778620377374795)
        ·
          refine ⟨3222436780167930566062193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2148291186778620377374795 3222436780167930566062193)
          ·
            refine ⟨2416827585125947924546645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3222436780167930566062193 2416827585125947924546645)
            ·
              refine ⟨28322198263194702240781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2416827585125947924546645 28322198263194702240781)
              ·
                rfl

theorem cell21_1116935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_1116935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1116935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1116935 prefixEnd_1116935 := by exact prefixLift 1116935
  have htrace : WordTrace (prefixWord ++ tailWord_1116935) baseStart_1116935 baseEnd_1116935 := by
    simpa [prefixWord, tailWord_1116935, baseEnd_1116935] using wordTrace_append hprefix tailTrace_1116935
  have hstable : (prefixWord ++ tailWord_1116935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116935).length < 2 ^ (prefixWord ++ tailWord_1116935).sum := by decide
  have hdescent : baseEnd_1116935 < baseStart_1116935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117039 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_1117039 : Nat := 118140960795 + 1117039 * 2 ^ 59
def prefixEnd_1117039 : Nat := 4983230072969 + 3 ^ 40 * 1117039 * 2
def baseEnd_1117039 : Nat := 254923518585671250433483

theorem tailTrace_1117039 : CollatzResearch.WordTrace tailWord_1117039 prefixEnd_1117039 254923518585671250433483 := by
  unfold tailWord_1117039
  simp only [CollatzResearch.WordTrace]
  refine ⟨40741759400165952917930171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27161172933443968611953447 40741759400165952917930171)
  ·
    refine ⟨61112639100248929376895257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40741759400165952917930171 61112639100248929376895257)
    ·
      refine ⟨45834479325186697032671443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61112639100248929376895257 45834479325186697032671443)
      ·
        refine ⟨68751718987780045549007165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45834479325186697032671443 68751718987780045549007165)
        ·
          refine ⟨25781894620417517080877687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68751718987780045549007165 25781894620417517080877687)
          ·
            refine ⟨38672841930626275621316531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25781894620417517080877687 38672841930626275621316531)
            ·
              refine ⟨58009262895939413431974797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38672841930626275621316531 58009262895939413431974797)
              ·
                refine ⟨21753473585977280036990549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58009262895939413431974797 21753473585977280036990549)
                ·
                  refine ⟨254923518585671250433483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21753473585977280036990549 254923518585671250433483)
                  ·
                    rfl

theorem cell21_1117039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_1117039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117039 prefixEnd_1117039 := by exact prefixLift 1117039
  have htrace : WordTrace (prefixWord ++ tailWord_1117039) baseStart_1117039 baseEnd_1117039 := by
    simpa [prefixWord, tailWord_1117039, baseEnd_1117039] using wordTrace_append hprefix tailTrace_1117039
  have hstable : (prefixWord ++ tailWord_1117039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117039).length < 2 ^ (prefixWord ++ tailWord_1117039).sum := by decide
  have hdescent : baseEnd_1117039 < baseStart_1117039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117118 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1117118 : Nat := 118140960795 + 1117118 * 2 ^ 59
def prefixEnd_1117118 : Nat := 4983230072969 + 3 ^ 40 * 1117118 * 2
def baseEnd_1117118 : Nat := 254941547461984668616655

theorem tailTrace_1117118 : CollatzResearch.WordTrace tailWord_1117118 prefixEnd_1117118 254941547461984668616655 := by
  unfold tailWord_1117118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093080095859968676257001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27163093844586499606704005 5093080095859968676257001)
  ·
    refine ⟨3819810071894976507192751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5093080095859968676257001 3819810071894976507192751)
    ·
      refine ⟨5729715107842464760789127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819810071894976507192751 5729715107842464760789127)
      ·
        refine ⟨8594572661763697141183691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729715107842464760789127 8594572661763697141183691)
        ·
          refine ⟨12891858992645545711775537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8594572661763697141183691 12891858992645545711775537)
          ·
            refine ⟨9668894244484159283831653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12891858992645545711775537 9668894244484159283831653)
            ·
              refine ⟨1812917670840779865718435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9668894244484159283831653 1812917670840779865718435)
              ·
                refine ⟨2719376506261169798577653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812917670840779865718435 2719376506261169798577653)
                ·
                  refine ⟨254941547461984668616655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2719376506261169798577653 254941547461984668616655)
                  ·
                    rfl

theorem cell21_1117118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1117118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117118 prefixEnd_1117118 := by exact prefixLift 1117118
  have htrace : WordTrace (prefixWord ++ tailWord_1117118) baseStart_1117118 baseEnd_1117118 := by
    simpa [prefixWord, tailWord_1117118, baseEnd_1117118] using wordTrace_append hprefix tailTrace_1117118
  have hstable : (prefixWord ++ tailWord_1117118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117118).length < 2 ^ (prefixWord ++ tailWord_1117118).sum := by decide
  have hdescent : baseEnd_1117118 < baseStart_1117118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117298 : List Nat := [3, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1117298 : Nat := 118140960795 + 1117298 * 2 ^ 59
def prefixEnd_1117298 : Nat := 4983230072969 + 3 ^ 40 * 1117298 * 2
def baseEnd_1117298 : Nat := 84994208638114785205429

theorem tailTrace_1117298 : CollatzResearch.WordTrace tailWord_1117298 prefixEnd_1117298 84994208638114785205429 := by
  unfold tailWord_1117298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187801476556910037902137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27167470604151760101072365 10187801476556910037902137)
  ·
    refine ⟨7640851107417682528426603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10187801476556910037902137 7640851107417682528426603)
    ·
      refine ⟨11461276661126523792639905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640851107417682528426603 11461276661126523792639905)
      ·
        refine ⟨8595957495844892844479929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11461276661126523792639905 8595957495844892844479929)
        ·
          refine ⟨6446968121883669633359947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8595957495844892844479929 6446968121883669633359947)
          ·
            refine ⟨9670452182825504450039921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6446968121883669633359947 9670452182825504450039921)
            ·
              refine ⟨7252839137119128337529941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9670452182825504450039921 7252839137119128337529941)
              ·
                refine ⟨84994208638114785205429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7252839137119128337529941 84994208638114785205429)
                ·
                  rfl

theorem cell21_1117298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1117298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117298 prefixEnd_1117298 := by exact prefixLift 1117298
  have htrace : WordTrace (prefixWord ++ tailWord_1117298) baseStart_1117298 baseEnd_1117298 := by
    simpa [prefixWord, tailWord_1117298, baseEnd_1117298] using wordTrace_append hprefix tailTrace_1117298
  have hstable : (prefixWord ++ tailWord_1117298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117298).length < 2 ^ (prefixWord ++ tailWord_1117298).sum := by decide
  have hdescent : baseEnd_1117298 < baseStart_1117298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117566 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1117566 : Nat := 118140960795 + 1117566 * 2 ^ 59
def prefixEnd_1117566 : Nat := 4983230072969 + 3 ^ 40 * 1117566 * 2
def baseEnd_1117566 : Nat := 255043787165635445149073

theorem tailTrace_1117566 : CollatzResearch.WordTrace tailWord_1117566 prefixEnd_1117566 255043787165635445149073 := by
  unfold tailWord_1117566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095122583657090240295569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27173987112837814614909701 5095122583657090240295569)
  ·
    refine ⟨3821341937742817680221677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5095122583657090240295569 3821341937742817680221677)
    ·
      refine ⟨1433003226653556630083129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3821341937742817680221677 1433003226653556630083129)
      ·
        refine ⟨1074752419990167472562347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1433003226653556630083129 1074752419990167472562347)
        ·
          refine ⟨1612128629985251208843521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074752419990167472562347 1612128629985251208843521)
          ·
            refine ⟨1209096472488938406632641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612128629985251208843521 1209096472488938406632641)
            ·
              refine ⟨906822354366703804974481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209096472488938406632641 906822354366703804974481)
              ·
                refine ⟨680116765775027853730861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906822354366703804974481 680116765775027853730861)
                ·
                  refine ⟨255043787165635445149073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680116765775027853730861 255043787165635445149073)
                  ·
                    rfl

theorem cell21_1117566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1117566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117566 prefixEnd_1117566 := by exact prefixLift 1117566
  have htrace : WordTrace (prefixWord ++ tailWord_1117566) baseStart_1117566 baseEnd_1117566 := by
    simpa [prefixWord, tailWord_1117566, baseEnd_1117566] using wordTrace_append hprefix tailTrace_1117566
  have hstable : (prefixWord ++ tailWord_1117566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117566).length < 2 ^ (prefixWord ++ tailWord_1117566).sum := by decide
  have hdescent : baseEnd_1117566 < baseStart_1117566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117608 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_1117608 : Nat := 118140960795 + 1117608 * 2 ^ 59
def prefixEnd_1117608 : Nat := 4983230072969 + 3 ^ 40 * 1117608 * 2
def baseEnd_1117608 : Nat := 255053372137852705448987

theorem tailTrace_1117608 : CollatzResearch.WordTrace tailWord_1117608 prefixEnd_1117608 255053372137852705448987 := by
  unfold tailWord_1117608
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381256267552281547696739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27175008356736375396928985 20381256267552281547696739)
  ·
    refine ⟨30571884401328422321545109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20381256267552281547696739 30571884401328422321545109)
    ·
      refine ⟨1433057081312269796322427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30571884401328422321545109 1433057081312269796322427)
      ·
        refine ⟨2149585621968404694483641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433057081312269796322427 2149585621968404694483641)
        ·
          refine ⟨1612189216476303520862731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2149585621968404694483641 1612189216476303520862731)
          ·
            refine ⟨2418283824714455281294097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612189216476303520862731 2418283824714455281294097)
            ·
              refine ⟨1813712868535841460970573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418283824714455281294097 1813712868535841460970573)
              ·
                refine ⟨680142325700940547863965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813712868535841460970573 680142325700940547863965)
                ·
                  refine ⟨255053372137852705448987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680142325700940547863965 255053372137852705448987)
                  ·
                    rfl

theorem cell21_1117608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_1117608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117608 prefixEnd_1117608 := by exact prefixLift 1117608
  have htrace : WordTrace (prefixWord ++ tailWord_1117608) baseStart_1117608 baseEnd_1117608 := by
    simpa [prefixWord, tailWord_1117608, baseEnd_1117608] using wordTrace_append hprefix tailTrace_1117608
  have hstable : (prefixWord ++ tailWord_1117608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117608).length < 2 ^ (prefixWord ++ tailWord_1117608).sum := by decide
  have hdescent : baseEnd_1117608 < baseStart_1117608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117647 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_1117647 : Nat := 118140960795 + 1117647 * 2 ^ 59
def prefixEnd_1117647 : Nat := 4983230072969 + 3 ^ 40 * 1117647 * 2
def baseEnd_1117647 : Nat := 255062272469197304298907

theorem tailTrace_1117647 : CollatzResearch.WordTrace tailWord_1117647 prefixEnd_1117647 255062272469197304298907 := by
  unfold tailWord_1117647
  simp only [CollatzResearch.WordTrace]
  refine ⟨40763934981963272756063195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27175956654642181837375463 40763934981963272756063195)
  ·
    refine ⟨61145902472944909134094793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40763934981963272756063195 61145902472944909134094793)
    ·
      refine ⟨45859426854708681850571095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61145902472944909134094793 45859426854708681850571095)
      ·
        refine ⟨68789140282063022775856643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45859426854708681850571095 68789140282063022775856643)
        ·
          refine ⟨103183710423094534163784965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68789140282063022775856643 103183710423094534163784965)
          ·
            refine ⟨19346945704330225155709681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103183710423094534163784965 19346945704330225155709681)
            ·
              refine ⟨14510209278247668866782261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19346945704330225155709681 14510209278247668866782261)
              ·
                refine ⟨1360332119835718956260837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14510209278247668866782261 1360332119835718956260837)
                ·
                  refine ⟨255062272469197304298907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360332119835718956260837 255062272469197304298907)
                  ·
                    rfl

theorem cell21_1117647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_1117647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117647 prefixEnd_1117647 := by exact prefixLift 1117647
  have htrace : WordTrace (prefixWord ++ tailWord_1117647) baseStart_1117647 baseEnd_1117647 := by
    simpa [prefixWord, tailWord_1117647, baseEnd_1117647] using wordTrace_append hprefix tailTrace_1117647
  have hstable : (prefixWord ++ tailWord_1117647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117647).length < 2 ^ (prefixWord ++ tailWord_1117647).sum := by decide
  have hdescent : baseEnd_1117647 < baseStart_1117647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117667 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 3]
def baseStart_1117667 : Nat := 118140960795 + 1117667 * 2 ^ 59
def prefixEnd_1117667 : Nat := 4983230072969 + 3 ^ 40 * 1117667 * 2
def baseEnd_1117667 : Nat := 255066836741681713965533

theorem tailTrace_1117667 : CollatzResearch.WordTrace tailWord_1117667 prefixEnd_1117667 255066836741681713965533 := by
  unfold tailWord_1117667
  simp only [CollatzResearch.WordTrace]
  refine ⟨40764664441890816171791255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27176442961260544114527503 40764664441890816171791255)
  ·
    refine ⟨61146996662836224257686883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40764664441890816171791255 61146996662836224257686883)
    ·
      refine ⟨91720494994254336386530325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61146996662836224257686883 91720494994254336386530325)
      ·
        refine ⟨4299398202855672018118609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91720494994254336386530325 4299398202855672018118609)
        ·
          refine ⟨3224548652141754013588957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299398202855672018118609 3224548652141754013588957)
          ·
            refine ⟨1209205744553157755095859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3224548652141754013588957 1209205744553157755095859)
            ·
              refine ⟨1813808616829736632643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209205744553157755095859 1813808616829736632643789)
              ·
                refine ⟨680178231311151237241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813808616829736632643789 680178231311151237241421)
                ·
                  refine ⟨255066836741681713965533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680178231311151237241421 255066836741681713965533)
                  ·
                    rfl

theorem cell21_1117667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].length) (baseStart_1117667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117667 prefixEnd_1117667 := by exact prefixLift 1117667
  have htrace : WordTrace (prefixWord ++ tailWord_1117667) baseStart_1117667 baseEnd_1117667 := by
    simpa [prefixWord, tailWord_1117667, baseEnd_1117667] using wordTrace_append hprefix tailTrace_1117667
  have hstable : (prefixWord ++ tailWord_1117667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117667).length < 2 ^ (prefixWord ++ tailWord_1117667).sum := by decide
  have hdescent : baseEnd_1117667 < baseStart_1117667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117698 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1117698 : Nat := 118140960795 + 1117698 * 2 ^ 59
def prefixEnd_1117698 : Nat := 4983230072969 + 3 ^ 40 * 1117698 * 2
def baseEnd_1117698 : Nat := 255073911364032548948803

theorem tailTrace_1117698 : CollatzResearch.WordTrace tailWord_1117698 prefixEnd_1117698 255073911364032548948803 := by
  unfold tailWord_1117698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10191448776194627116542437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27177196736519005644113165 10191448776194627116542437)
  ·
    refine ⟨1910896645536492584351707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10191448776194627116542437 1910896645536492584351707)
    ·
      refine ⟨2866344968304738876527561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910896645536492584351707 2866344968304738876527561)
      ·
        refine ⟨2149758726228554157395671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2866344968304738876527561 2149758726228554157395671)
        ·
          refine ⟨3224638089342831236093507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149758726228554157395671 3224638089342831236093507)
          ·
            refine ⟨4836957134014246854140261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224638089342831236093507 4836957134014246854140261)
            ·
              refine ⟨906929462627671285151299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4836957134014246854140261 906929462627671285151299)
              ·
                refine ⟨1360394193941506927726949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906929462627671285151299 1360394193941506927726949)
                ·
                  refine ⟨255073911364032548948803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360394193941506927726949 255073911364032548948803)
                  ·
                    rfl

theorem cell21_1117698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1117698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117698 prefixEnd_1117698 := by exact prefixLift 1117698
  have htrace : WordTrace (prefixWord ++ tailWord_1117698) baseStart_1117698 baseEnd_1117698 := by
    simpa [prefixWord, tailWord_1117698, baseEnd_1117698] using wordTrace_append hprefix tailTrace_1117698
  have hstable : (prefixWord ++ tailWord_1117698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117698).length < 2 ^ (prefixWord ++ tailWord_1117698).sum := by decide
  have hdescent : baseEnd_1117698 < baseStart_1117698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117802 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_1117802 : Nat := 118140960795 + 1117802 * 2 ^ 59
def prefixEnd_1117802 : Nat := 4983230072969 + 3 ^ 40 * 1117802 * 2
def baseEnd_1117802 : Nat := 255097645580951479215257

theorem tailTrace_1117802 : CollatzResearch.WordTrace tailWord_1117802 prefixEnd_1117802 255097645580951479215257 := by
  unfold tailWord_1117802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192397074100433556988915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27179725530934489485303773 10192397074100433556988915)
  ·
    refine ⟨15288595611150650335483373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10192397074100433556988915 15288595611150650335483373)
    ·
      refine ⟨5733223354181493875806265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15288595611150650335483373 5733223354181493875806265)
      ·
        refine ⟨4299917515636120406854699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733223354181493875806265 4299917515636120406854699)
        ·
          refine ⟨6449876273454180610282049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299917515636120406854699 6449876273454180610282049)
          ·
            refine ⟨4837407205090635457711537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6449876273454180610282049 4837407205090635457711537)
            ·
              refine ⟨3628055403817976593283653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837407205090635457711537 3628055403817976593283653)
              ·
                refine ⟨680260388215870611240685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3628055403817976593283653 680260388215870611240685)
                ·
                  refine ⟨255097645580951479215257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680260388215870611240685 255097645580951479215257)
                  ·
                    rfl

theorem cell21_1117802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_1117802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117802 prefixEnd_1117802 := by exact prefixLift 1117802
  have htrace : WordTrace (prefixWord ++ tailWord_1117802) baseStart_1117802 baseEnd_1117802 := by
    simpa [prefixWord, tailWord_1117802, baseEnd_1117802] using wordTrace_append hprefix tailTrace_1117802
  have hstable : (prefixWord ++ tailWord_1117802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117802).length < 2 ^ (prefixWord ++ tailWord_1117802).sum := by decide
  have hdescent : baseEnd_1117802 < baseStart_1117802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117861 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1117861 : Nat := 118140960795 + 1117861 * 2 ^ 59
def prefixEnd_1117861 : Nat := 4983230072969 + 3 ^ 40 * 1117861 * 2
def baseEnd_1117861 : Nat := 255111110184780487731803

theorem tailTrace_1117861 : CollatzResearch.WordTrace tailWord_1117861 prefixEnd_1117861 255111110184780487731803 := by
  unfold tailWord_1117861
  simp only [CollatzResearch.WordTrace]
  refine ⟨40771740203187987304353437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27181160135458658202902291 40771740203187987304353437)
  ·
    refine ⟨15289402576195495239132539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40771740203187987304353437 15289402576195495239132539)
    ·
      refine ⟨22934103864293242858698809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15289402576195495239132539 22934103864293242858698809)
      ·
        refine ⟨17200577898219932144024107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22934103864293242858698809 17200577898219932144024107)
        ·
          refine ⟨25800866847329898216036161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200577898219932144024107 25800866847329898216036161)
          ·
            refine ⟨19350650135497423662027121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25800866847329898216036161 19350650135497423662027121)
            ·
              refine ⟨14512987601623067746520341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19350650135497423662027121 14512987601623067746520341)
              ·
                refine ⟨680296293826081300618141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14512987601623067746520341 680296293826081300618141)
                ·
                  refine ⟨255111110184780487731803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680296293826081300618141 255111110184780487731803)
                  ·
                    rfl

theorem cell21_1117861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1117861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117861 prefixEnd_1117861 := by exact prefixLift 1117861
  have htrace : WordTrace (prefixWord ++ tailWord_1117861) baseStart_1117861 baseEnd_1117861 := by
    simpa [prefixWord, tailWord_1117861, baseEnd_1117861] using wordTrace_append hprefix tailTrace_1117861
  have hstable : (prefixWord ++ tailWord_1117861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117861).length < 2 ^ (prefixWord ++ tailWord_1117861).sum := by decide
  have hdescent : baseEnd_1117861 < baseStart_1117861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117875 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_1117875 : Nat := 118140960795 + 1117875 * 2 ^ 59
def prefixEnd_1117875 : Nat := 4983230072969 + 3 ^ 40 * 1117875 * 2
def baseEnd_1117875 : Nat := 255114305175519574498441

theorem tailTrace_1117875 : CollatzResearch.WordTrace tailWord_1117875 prefixEnd_1117875 255114305175519574498441 := by
  unfold tailWord_1117875
  simp only [CollatzResearch.WordTrace]
  refine ⟨40772250825137267695363079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27181500550091511796908719 40772250825137267695363079)
  ·
    refine ⟨61158376237705901543044619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40772250825137267695363079 61158376237705901543044619)
    ·
      refine ⟨91737564356558852314566929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61158376237705901543044619 91737564356558852314566929)
      ·
        refine ⟨68803173267419139235925197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91737564356558852314566929 68803173267419139235925197)
        ·
          refine ⟨25801189975282177213471949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68803173267419139235925197 25801189975282177213471949)
          ·
            refine ⟨9675446240730816455051981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25801189975282177213471949 9675446240730816455051981)
            ·
              refine ⟨3628292340274056170644493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9675446240730816455051981 3628292340274056170644493)
              ·
                refine ⟨1360609627602771063991685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628292340274056170644493 1360609627602771063991685)
                ·
                  refine ⟨255114305175519574498441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360609627602771063991685 255114305175519574498441)
                  ·
                    rfl

theorem cell21_1117875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_1117875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117875 prefixEnd_1117875 := by exact prefixLift 1117875
  have htrace : WordTrace (prefixWord ++ tailWord_1117875) baseStart_1117875 baseEnd_1117875 := by
    simpa [prefixWord, tailWord_1117875, baseEnd_1117875] using wordTrace_append hprefix tailTrace_1117875
  have hstable : (prefixWord ++ tailWord_1117875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117875).length < 2 ^ (prefixWord ++ tailWord_1117875).sum := by decide
  have hdescent : baseEnd_1117875 < baseStart_1117875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117923 : List Nat := [1, 1, 1, 7, 2, 2, 1, 6]
def baseStart_1117923 : Nat := 118140960795 + 1117923 * 2 ^ 59
def prefixEnd_1117923 : Nat := 4983230072969 + 3 ^ 40 * 1117923 * 2
def baseEnd_1117923 : Nat := 85041753143160719232781

theorem tailTrace_1117923 : CollatzResearch.WordTrace tailWord_1117923 prefixEnd_1117923 85041753143160719232781 := by
  unfold tailWord_1117923
  simp only [CollatzResearch.WordTrace]
  refine ⟨40774001528963371893110423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27182667685975581262073615 40774001528963371893110423)
  ·
    refine ⟨61161002293445057839665635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40774001528963371893110423 61161002293445057839665635)
    ·
      refine ⟨91741503440167586759498453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61161002293445057839665635 91741503440167586759498453)
      ·
        refine ⟨2150191486878927814675745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91741503440167586759498453 2150191486878927814675745)
        ·
          refine ⟨1612643615159195861006809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150191486878927814675745 1612643615159195861006809)
          ·
            refine ⟨1209482711369396895755107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612643615159195861006809 1209482711369396895755107)
            ·
              refine ⟨1814224067054095343632661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209482711369396895755107 1814224067054095343632661)
              ·
                refine ⟨85041753143160719232781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1814224067054095343632661 85041753143160719232781)
                ·
                  rfl

theorem cell21_1117923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 6].length) (baseStart_1117923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117923 prefixEnd_1117923 := by exact prefixLift 1117923
  have htrace : WordTrace (prefixWord ++ tailWord_1117923) baseStart_1117923 baseEnd_1117923 := by
    simpa [prefixWord, tailWord_1117923, baseEnd_1117923] using wordTrace_append hprefix tailTrace_1117923
  have hstable : (prefixWord ++ tailWord_1117923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117923).length < 2 ^ (prefixWord ++ tailWord_1117923).sum := by decide
  have hdescent : baseEnd_1117923 < baseStart_1117923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117979 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_1117979 : Nat := 118140960795 + 1117979 * 2 ^ 59
def prefixEnd_1117979 : Nat := 4983230072969 + 3 ^ 40 * 1117979 * 2
def baseEnd_1117979 : Nat := 255138039392438504764895

theorem tailTrace_1117979 : CollatzResearch.WordTrace tailWord_1117979 prefixEnd_1117979 255138039392438504764895 := by
  unfold tailWord_1117979
  simp only [CollatzResearch.WordTrace]
  refine ⟨40776044016760493457148991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27184029344506995638099327 40776044016760493457148991)
  ·
    refine ⟨61164066025140740185723487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40776044016760493457148991 61164066025140740185723487)
    ·
      refine ⟨91746099037711110278585231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61164066025140740185723487 91746099037711110278585231)
      ·
        refine ⟨137619148556566665417877847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91746099037711110278585231 137619148556566665417877847)
        ·
          refine ⟨206428722834849998126816771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137619148556566665417877847 206428722834849998126816771)
          ·
            refine ⟨309643084252274997190225157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206428722834849998126816771 309643084252274997190225157)
            ·
              refine ⟨58058078297301561973167217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309643084252274997190225157 58058078297301561973167217)
              ·
                refine ⟨43543558722976171479875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58058078297301561973167217 43543558722976171479875413)
                ·
                  refine ⟨255138039392438504764895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43543558722976171479875413 255138039392438504764895)
                  ·
                    rfl

theorem cell21_1117979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_1117979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117979 prefixEnd_1117979 := by exact prefixLift 1117979
  have htrace : WordTrace (prefixWord ++ tailWord_1117979) baseStart_1117979 baseEnd_1117979 := by
    simpa [prefixWord, tailWord_1117979, baseEnd_1117979] using wordTrace_append hprefix tailTrace_1117979
  have hstable : (prefixWord ++ tailWord_1117979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117979).length < 2 ^ (prefixWord ++ tailWord_1117979).sum := by decide
  have hdescent : baseEnd_1117979 < baseStart_1117979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117996 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1117996 : Nat := 118140960795 + 1117996 * 2 ^ 59
def prefixEnd_1117996 : Nat := 4983230072969 + 3 ^ 40 * 1117996 * 2
def baseEnd_1117996 : Nat := 255141919024050252981527

theorem tailTrace_1117996 : CollatzResearch.WordTrace tailWord_1117996 prefixEnd_1117996 255141919024050252981527 := by
  unfold tailWord_1117996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388332028849452680258921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27184442705132603573678561 20388332028849452680258921)
  ·
    refine ⟨15291249021637089510194191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20388332028849452680258921 15291249021637089510194191)
    ·
      refine ⟨22936873532455634265291287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15291249021637089510194191 22936873532455634265291287)
      ·
        refine ⟨34405310298683451397936931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22936873532455634265291287 34405310298683451397936931)
        ·
          refine ⟨51607965448025177096905397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34405310298683451397936931 51607965448025177096905397)
          ·
            refine ⟨4838246760752360352834881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51607965448025177096905397 4838246760752360352834881)
            ·
              refine ⟨3628685070564270264626161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838246760752360352834881 3628685070564270264626161)
              ·
                refine ⟨2721513802923202698469621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628685070564270264626161 2721513802923202698469621)
                ·
                  refine ⟨255141919024050252981527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2721513802923202698469621 255141919024050252981527)
                  ·
                    rfl

theorem cell21_1117996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1117996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1117996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1117996 prefixEnd_1117996 := by exact prefixLift 1117996
  have htrace : WordTrace (prefixWord ++ tailWord_1117996) baseStart_1117996 baseEnd_1117996 := by
    simpa [prefixWord, tailWord_1117996, baseEnd_1117996] using wordTrace_append hprefix tailTrace_1117996
  have hstable : (prefixWord ++ tailWord_1117996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117996).length < 2 ^ (prefixWord ++ tailWord_1117996).sum := by decide
  have hdescent : baseEnd_1117996 < baseStart_1117996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118041 : List Nat := [1, 2, 1, 2, 2, 3, 4, 6]
def baseStart_1118041 : Nat := 118140960795 + 1118041 * 2 ^ 59
def prefixEnd_1118041 : Nat := 4983230072969 + 3 ^ 40 * 1118041 * 2
def baseEnd_1118041 : Nat := 85050729545713391577145

theorem tailTrace_1118041 : CollatzResearch.WordTrace tailWord_1118041 prefixEnd_1118041 85050729545713391577145 := by
  unfold tailWord_1118041
  simp only [CollatzResearch.WordTrace]
  refine ⟨40778305342535878045905977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27185536895023918697270651 40778305342535878045905977)
  ·
    refine ⟨30583729006901908534429483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40778305342535878045905977 30583729006901908534429483)
    ·
      refine ⟨45875593510352862801644225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30583729006901908534429483 45875593510352862801644225)
      ·
        refine ⟨34406695132764647101233169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45875593510352862801644225 34406695132764647101233169)
        ·
          refine ⟨25805021349573485325924877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34406695132764647101233169 25805021349573485325924877)
          ·
            refine ⟨9676883006090056997221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25805021349573485325924877 9676883006090056997221829)
            ·
              refine ⟨1814415563641885686979093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9676883006090056997221829 1814415563641885686979093)
              ·
                refine ⟨85050729545713391577145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1814415563641885686979093 85050729545713391577145)
                ·
                  rfl

theorem cell21_1118041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_1118041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118041 prefixEnd_1118041 := by exact prefixLift 1118041
  have htrace : WordTrace (prefixWord ++ tailWord_1118041) baseStart_1118041 baseEnd_1118041 := by
    simpa [prefixWord, tailWord_1118041, baseEnd_1118041] using wordTrace_append hprefix tailTrace_1118041
  have hstable : (prefixWord ++ tailWord_1118041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118041).length < 2 ^ (prefixWord ++ tailWord_1118041).sum := by decide
  have hdescent : baseEnd_1118041 < baseStart_1118041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118081 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 3]
def baseStart_1118081 : Nat := 118140960795 + 1118081 * 2 ^ 59
def prefixEnd_1118081 : Nat := 4983230072969 + 3 ^ 40 * 1118081 * 2
def baseEnd_1118081 : Nat := 255161317182108994064687

theorem tailTrace_1118081 : CollatzResearch.WordTrace tailWord_1118081 prefixEnd_1118081 255161317182108994064687 := by
  unfold tailWord_1118081
  simp only [CollatzResearch.WordTrace]
  refine ⟨40779764262390964877362097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27186509508260643251574731 40779764262390964877362097)
  ·
    refine ⟨30584823196793223658021573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40779764262390964877362097 30584823196793223658021573)
    ·
      refine ⟨5734654349398729435879045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30584823196793223658021573 5734654349398729435879045)
      ·
        refine ⟨1075247690512261769227321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5734654349398729435879045 1075247690512261769227321)
        ·
          refine ⟨806435767884196326920491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075247690512261769227321 806435767884196326920491)
          ·
            refine ⟨1209653651826294490380737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806435767884196326920491 1209653651826294490380737)
            ·
              refine ⟨907240238869720867785553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209653651826294490380737 907240238869720867785553)
              ·
                refine ⟨680430179152290650839165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907240238869720867785553 680430179152290650839165)
                ·
                  refine ⟨255161317182108994064687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680430179152290650839165 255161317182108994064687)
                  ·
                    rfl

theorem cell21_1118081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_1118081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118081 prefixEnd_1118081 := by exact prefixLift 1118081
  have htrace : WordTrace (prefixWord ++ tailWord_1118081) baseStart_1118081 baseEnd_1118081 := by
    simpa [prefixWord, tailWord_1118081, baseEnd_1118081] using wordTrace_append hprefix tailTrace_1118081
  have hstable : (prefixWord ++ tailWord_1118081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118081).length < 2 ^ (prefixWord ++ tailWord_1118081).sum := by decide
  have hdescent : baseEnd_1118081 < baseStart_1118081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118089 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 3]
def baseStart_1118089 : Nat := 118140960795 + 1118089 * 2 ^ 59
def prefixEnd_1118089 : Nat := 4983230072969 + 3 ^ 40 * 1118089 * 2
def baseEnd_1118089 : Nat := 255163142891102757931337

theorem tailTrace_1118089 : CollatzResearch.WordTrace tailWord_1118089 prefixEnd_1118089 255163142891102757931337 := by
  unfold tailWord_1118089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40780056046361982243653321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27186704030907988162435547 40780056046361982243653321)
  ·
    refine ⟨30585042034771486682739991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40780056046361982243653321 30585042034771486682739991)
    ·
      refine ⟨45877563052157230024109987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30585042034771486682739991 45877563052157230024109987)
      ·
        refine ⟨68816344578235845036164981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45877563052157230024109987 68816344578235845036164981)
        ·
          refine ⟨6451532304209610472140467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68816344578235845036164981 6451532304209610472140467)
          ·
            refine ⟨9677298456314415708210701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451532304209610472140467 9677298456314415708210701)
            ·
              refine ⟨3628986921117905890579013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9677298456314415708210701 3628986921117905890579013)
              ·
                refine ⟨680435047709607354483565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3628986921117905890579013 680435047709607354483565)
                ·
                  refine ⟨255163142891102757931337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680435047709607354483565 255163142891102757931337)
                  ·
                    rfl

theorem cell21_1118089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_1118089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118089 prefixEnd_1118089 := by exact prefixLift 1118089
  have htrace : WordTrace (prefixWord ++ tailWord_1118089) baseStart_1118089 baseEnd_1118089 := by
    simpa [prefixWord, tailWord_1118089, baseEnd_1118089] using wordTrace_append hprefix tailTrace_1118089
  have hstable : (prefixWord ++ tailWord_1118089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118089).length < 2 ^ (prefixWord ++ tailWord_1118089).sum := by decide
  have hdescent : baseEnd_1118089 < baseStart_1118089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118103 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 4]
def baseStart_1118103 : Nat := 118140960795 + 1118103 * 2 ^ 59
def prefixEnd_1118103 : Nat := 4983230072969 + 3 ^ 40 * 1118103 * 2
def baseEnd_1118103 : Nat := 255166337881841844697975

theorem tailTrace_1118103 : CollatzResearch.WordTrace tailWord_1118103 prefixEnd_1118103 255166337881841844697975 := by
  unfold tailWord_1118103
  simp only [CollatzResearch.WordTrace]
  refine ⟨40780566668311262634662963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187044445540841756441975 40780566668311262634662963)
  ·
    refine ⟨61170850002466893951994445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40780566668311262634662963 61170850002466893951994445)
    ·
      refine ⟨22939068750925085231997917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61170850002466893951994445 22939068750925085231997917)
      ·
        refine ⟨8602150781596906961999219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22939068750925085231997917 8602150781596906961999219)
        ·
          refine ⟨12903226172395360442998829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8602150781596906961999219 12903226172395360442998829)
          ·
            refine ⟨4838709814648260166124561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12903226172395360442998829 4838709814648260166124561)
            ·
              refine ⟨3629032360986195124593421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838709814648260166124561 3629032360986195124593421)
              ·
                refine ⟨1360887135369823171722533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3629032360986195124593421 1360887135369823171722533)
                ·
                  refine ⟨255166337881841844697975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1360887135369823171722533 255166337881841844697975)
                  ·
                    rfl

theorem cell21_1118103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_1118103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118103 prefixEnd_1118103 := by exact prefixLift 1118103
  have htrace : WordTrace (prefixWord ++ tailWord_1118103) baseStart_1118103 baseEnd_1118103 := by
    simpa [prefixWord, tailWord_1118103, baseEnd_1118103] using wordTrace_append hprefix tailTrace_1118103
  have hstable : (prefixWord ++ tailWord_1118103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118103).length < 2 ^ (prefixWord ++ tailWord_1118103).sum := by decide
  have hdescent : baseEnd_1118103 < baseStart_1118103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118131 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_1118131 : Nat := 118140960795 + 1118131 * 2 ^ 59
def prefixEnd_1118131 : Nat := 4983230072969 + 3 ^ 40 * 1118131 * 2
def baseEnd_1118131 : Nat := 255172727863320018231251

theorem tailTrace_1118131 : CollatzResearch.WordTrace tailWord_1118131 prefixEnd_1118131 255172727863320018231251 := by
  unfold tailWord_1118131
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781587912209823416682247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187725274806548944454831 40781587912209823416682247)
  ·
    refine ⟨61172381868314735125023371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40781587912209823416682247 61172381868314735125023371)
    ·
      refine ⟨91758572802472102687535057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61172381868314735125023371 91758572802472102687535057)
      ·
        refine ⟨68818929601854077015651293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91758572802472102687535057 68818929601854077015651293)
        ·
          refine ⟨25807098600695278880869235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68818929601854077015651293 25807098600695278880869235)
          ·
            refine ⟨38710647901042918321303853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25807098600695278880869235 38710647901042918321303853)
            ·
              refine ⟨14516492962891094370488945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38710647901042918321303853 14516492962891094370488945)
              ·
                refine ⟨10887369722168320777866709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14516492962891094370488945 10887369722168320777866709)
                ·
                  refine ⟨255172727863320018231251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10887369722168320777866709 255172727863320018231251)
                  ·
                    rfl

theorem cell21_1118131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_1118131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118131 prefixEnd_1118131 := by exact prefixLift 1118131
  have htrace : WordTrace (prefixWord ++ tailWord_1118131) baseStart_1118131 baseEnd_1118131 := by
    simpa [prefixWord, tailWord_1118131, baseEnd_1118131] using wordTrace_append hprefix tailTrace_1118131
  have hstable : (prefixWord ++ tailWord_1118131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118131).length < 2 ^ (prefixWord ++ tailWord_1118131).sum := by decide
  have hdescent : baseEnd_1118131 < baseStart_1118131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118258 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_1118258 : Nat := 118140960795 + 1118258 * 2 ^ 59
def prefixEnd_1118258 : Nat := 4983230072969 + 3 ^ 40 * 1118258 * 2
def baseEnd_1118258 : Nat := 255201710993596019614325

theorem tailTrace_1118258 : CollatzResearch.WordTrace tailWord_1118258 prefixEnd_1118258 255201710993596019614325 := by
  unfold tailWord_1118258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196554995687431026638857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27190813321833149404370285 10196554995687431026638857)
  ·
    refine ⟨7647416246765573269979143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10196554995687431026638857 7647416246765573269979143)
    ·
      refine ⟨11471124370148359904968715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647416246765573269979143 11471124370148359904968715)
      ·
        refine ⟨17206686555222539857453073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11471124370148359904968715 17206686555222539857453073)
        ·
          refine ⟨12905014916416904893089805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17206686555222539857453073 12905014916416904893089805)
          ·
            refine ⟨4839380593656339334908677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12905014916416904893089805 4839380593656339334908677)
            ·
              refine ⟨907383861310563625295377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4839380593656339334908677 907383861310563625295377)
              ·
                refine ⟨680537895982922718971533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907383861310563625295377 680537895982922718971533)
                ·
                  refine ⟨255201710993596019614325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680537895982922718971533 255201710993596019614325)
                  ·
                    rfl

theorem cell21_1118258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_1118258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118258 prefixEnd_1118258 := by exact prefixLift 1118258
  have htrace : WordTrace (prefixWord ++ tailWord_1118258) baseStart_1118258 baseEnd_1118258 := by
    simpa [prefixWord, tailWord_1118258, baseEnd_1118258] using wordTrace_append hprefix tailTrace_1118258
  have hstable : (prefixWord ++ tailWord_1118258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118258).length < 2 ^ (prefixWord ++ tailWord_1118258).sum := by decide
  have hdescent : baseEnd_1118258 < baseStart_1118258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118283 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 5]
def baseStart_1118283 : Nat := 118140960795 + 1118283 * 2 ^ 59
def prefixEnd_1118283 : Nat := 4983230072969 + 3 ^ 40 * 1118283 * 2
def baseEnd_1118283 : Nat := 255207416334201531697607

theorem tailTrace_1118283 : CollatzResearch.WordTrace tailWord_1118283 prefixEnd_1118283 255207416334201531697607 := by
  unfold tailWord_1118283
  simp only [CollatzResearch.WordTrace]
  refine ⟨40787131807659153376215503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27191421205106102250810335 40787131807659153376215503)
  ·
    refine ⟨61180697711488730064323255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40787131807659153376215503 61180697711488730064323255)
    ·
      refine ⟨91771046567233095096484883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61180697711488730064323255 91771046567233095096484883)
      ·
        refine ⟨137656569850849642644727325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91771046567233095096484883 137656569850849642644727325)
        ·
          refine ⟨51621213694068615991772747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137656569850849642644727325 51621213694068615991772747)
          ·
            refine ⟨77431820541102923987659121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51621213694068615991772747 77431820541102923987659121)
            ·
              refine ⟨58073865405827192990744341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77431820541102923987659121 58073865405827192990744341)
              ·
                refine ⟨2722212440898149671441141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58073865405827192990744341 2722212440898149671441141)
                ·
                  refine ⟨255207416334201531697607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722212440898149671441141 255207416334201531697607)
                  ·
                    rfl

theorem cell21_1118283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_1118283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118283 prefixEnd_1118283 := by exact prefixLift 1118283
  have htrace : WordTrace (prefixWord ++ tailWord_1118283) baseStart_1118283 baseEnd_1118283 := by
    simpa [prefixWord, tailWord_1118283, baseEnd_1118283] using wordTrace_append hprefix tailTrace_1118283
  have hstable : (prefixWord ++ tailWord_1118283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118283).length < 2 ^ (prefixWord ++ tailWord_1118283).sum := by decide
  have hdescent : baseEnd_1118283 < baseStart_1118283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118286 : List Nat := [4, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1118286 : Nat := 118140960795 + 1118286 * 2 ^ 59
def prefixEnd_1118286 : Nat := 4983230072969 + 3 ^ 40 * 1118286 * 2
def baseEnd_1118286 : Nat := 85069366991691397715867

theorem tailTrace_1118286 : CollatzResearch.WordTrace tailWord_1118286 prefixEnd_1118286 85069366991691397715867 := by
  unfold tailWord_1118286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098405153331035611071839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27191494151098856592383141 5098405153331035611071839)
  ·
    refine ⟨7647607729996553416607759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5098405153331035611071839 7647607729996553416607759)
    ·
      refine ⟨11471411594994830124911639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7647607729996553416607759 11471411594994830124911639)
      ·
        refine ⟨17207117392492245187367459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11471411594994830124911639 17207117392492245187367459)
        ·
          refine ⟨25810676088738367781051189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17207117392492245187367459 25810676088738367781051189)
          ·
            refine ⟨2419750883319221979473549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25810676088738367781051189 2419750883319221979473549)
            ·
              refine ⟨907406581244708242302581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2419750883319221979473549 907406581244708242302581)
              ·
                refine ⟨85069366991691397715867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907406581244708242302581 85069366991691397715867)
                ·
                  rfl

theorem cell21_1118286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1118286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118286 prefixEnd_1118286 := by exact prefixLift 1118286
  have htrace : WordTrace (prefixWord ++ tailWord_1118286) baseStart_1118286 baseEnd_1118286 := by
    simpa [prefixWord, tailWord_1118286, baseEnd_1118286] using wordTrace_append hprefix tailTrace_1118286
  have hstable : (prefixWord ++ tailWord_1118286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118286).length < 2 ^ (prefixWord ++ tailWord_1118286).sum := by decide
  have hdescent : baseEnd_1118286 < baseStart_1118286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118306 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1118306 : Nat := 118140960795 + 1118306 * 2 ^ 59
def prefixEnd_1118306 : Nat := 4983230072969 + 3 ^ 40 * 1118306 * 2
def baseEnd_1118306 : Nat := 255212665247558602814227

theorem tailTrace_1118306 : CollatzResearch.WordTrace tailWord_1118306 prefixEnd_1118306 255212665247558602814227 := by
  unfold tailWord_1118306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196992671643957076075693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27191980457717218869535181 10196992671643957076075693)
  ·
    refine ⟨3823872251866483903528385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10196992671643957076075693 3823872251866483903528385)
    ·
      refine ⟨2867904188899862927646289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3823872251866483903528385 2867904188899862927646289)
      ·
        refine ⟨2150928141674897195734717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2867904188899862927646289 2150928141674897195734717)
        ·
          refine ⟨806598053128086448400519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2150928141674897195734717 806598053128086448400519)
          ·
            refine ⟨1209897079692129672600779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806598053128086448400519 1209897079692129672600779)
            ·
              refine ⟨1814845619538194508901169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209897079692129672600779 1814845619538194508901169)
              ·
                refine ⟨1361134214653645881675877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814845619538194508901169 1361134214653645881675877)
                ·
                  refine ⟨255212665247558602814227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361134214653645881675877 255212665247558602814227)
                  ·
                    rfl

theorem cell21_1118306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1118306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118306 prefixEnd_1118306 := by exact prefixLift 1118306
  have htrace : WordTrace (prefixWord ++ tailWord_1118306) baseStart_1118306 baseEnd_1118306 := by
    simpa [prefixWord, tailWord_1118306, baseEnd_1118306] using wordTrace_append hprefix tailTrace_1118306
  have hstable : (prefixWord ++ tailWord_1118306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118306).length < 2 ^ (prefixWord ++ tailWord_1118306).sum := by decide
  have hdescent : baseEnd_1118306 < baseStart_1118306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118317 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1118317 : Nat := 118140960795 + 1118317 * 2 ^ 59
def prefixEnd_1118317 : Nat := 4983230072969 + 3 ^ 40 * 1118317 * 2
def baseEnd_1118317 : Nat := 255215175597425028130871

theorem tailTrace_1118317 : CollatzResearch.WordTrace tailWord_1118317 prefixEnd_1118317 255215175597425028130871 := by
  unfold tailWord_1118317
  simp only [CollatzResearch.WordTrace]
  refine ⟨40788371889535977182953205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27192247926357318121968803 40788371889535977182953205)
  ·
    refine ⟨3823909864643997860901863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40788371889535977182953205 3823909864643997860901863)
    ·
      refine ⟨5735864796965996791352795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823909864643997860901863 5735864796965996791352795)
      ·
        refine ⟨8603797195448995187029193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735864796965996791352795 8603797195448995187029193)
        ·
          refine ⟨6452847896586746390271895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8603797195448995187029193 6452847896586746390271895)
          ·
            refine ⟨9679271844880119585407843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452847896586746390271895 9679271844880119585407843)
            ·
              refine ⟨14518907767320179378111765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679271844880119585407843 14518907767320179378111765)
              ·
                refine ⟨680573801593133408348989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14518907767320179378111765 680573801593133408348989)
                ·
                  refine ⟨255215175597425028130871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680573801593133408348989 255215175597425028130871)
                  ·
                    rfl

theorem cell21_1118317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1118317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118317 prefixEnd_1118317 := by exact prefixLift 1118317
  have htrace : WordTrace (prefixWord ++ tailWord_1118317) baseStart_1118317 baseEnd_1118317 := by
    simpa [prefixWord, tailWord_1118317, baseEnd_1118317] using wordTrace_append hprefix tailTrace_1118317
  have hstable : (prefixWord ++ tailWord_1118317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118317).length < 2 ^ (prefixWord ++ tailWord_1118317).sum := by decide
  have hdescent : baseEnd_1118317 < baseStart_1118317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118328 : List Nat := [2, 1, 2, 1, 1, 1, 3, 10]
def baseStart_1118328 : Nat := 118140960795 + 1118328 * 2 ^ 59
def prefixEnd_1118328 : Nat := 4983230072969 + 3 ^ 40 * 1118328 * 2
def baseEnd_1118328 : Nat := 85072561982430484482505

theorem tailTrace_1118328 : CollatzResearch.WordTrace tailWord_1118328 prefixEnd_1118328 85072561982430484482505 := by
  unfold tailWord_1118328
  simp only [CollatzResearch.WordTrace]
  refine ⟨20394386546248063030801819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27192515394997417374402425 20394386546248063030801819)
  ·
    refine ⟨30591579819372094546202729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20394386546248063030801819 30591579819372094546202729)
    ·
      refine ⟨22943684864529070909652047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30591579819372094546202729 22943684864529070909652047)
      ·
        refine ⟨34415527296793606364478071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22943684864529070909652047 34415527296793606364478071)
        ·
          refine ⟨51623290945190409546717107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34415527296793606364478071 51623290945190409546717107)
          ·
            refine ⟨77434936417785614320075661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51623290945190409546717107 77434936417785614320075661)
            ·
              refine ⟨29038101156669605370028373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77434936417785614320075661 29038101156669605370028373)
              ·
                refine ⟨85072561982430484482505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29038101156669605370028373 85072561982430484482505)
                ·
                  rfl

theorem cell21_1118328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_1118328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118328 prefixEnd_1118328 := by exact prefixLift 1118328
  have htrace : WordTrace (prefixWord ++ tailWord_1118328) baseStart_1118328 baseEnd_1118328 := by
    simpa [prefixWord, tailWord_1118328, baseEnd_1118328] using wordTrace_append hprefix tailTrace_1118328
  have hstable : (prefixWord ++ tailWord_1118328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118328).length < 2 ^ (prefixWord ++ tailWord_1118328).sum := by decide
  have hdescent : baseEnd_1118328 < baseStart_1118328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118362 : List Nat := [3, 1, 1, 5, 2, 2, 7]
def baseStart_1118362 : Nat := 118140960795 + 1118362 * 2 ^ 59
def prefixEnd_1118362 : Nat := 4983230072969 + 3 ^ 40 * 1118362 * 2
def baseEnd_1118362 : Nat := 28358382801168327764531

theorem tailTrace_1118362 : CollatzResearch.WordTrace tailWord_1118362 prefixEnd_1118362 28358382801168327764531 := by
  unfold tailWord_1118362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197503293593237467085335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27193342116248633245560893 10197503293593237467085335)
  ·
    refine ⟨15296254940389856200628003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10197503293593237467085335 15296254940389856200628003)
    ·
      refine ⟨22944382410584784300942005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296254940389856200628003 22944382410584784300942005)
      ·
        refine ⟨2151035850992323528213313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22944382410584784300942005 2151035850992323528213313)
        ·
          refine ⟨1613276888244242646159985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151035850992323528213313 1613276888244242646159985)
          ·
            refine ⟨1209957666183181984619989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613276888244242646159985 1209957666183181984619989)
            ·
              refine ⟨28358382801168327764531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1209957666183181984619989 28358382801168327764531)
              ·
                rfl

theorem cell21_1118362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 7].length) (baseStart_1118362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118362 prefixEnd_1118362 := by exact prefixLift 1118362
  have htrace : WordTrace (prefixWord ++ tailWord_1118362) baseStart_1118362 baseEnd_1118362 := by
    simpa [prefixWord, tailWord_1118362, baseEnd_1118362] using wordTrace_append hprefix tailTrace_1118362
  have hstable : (prefixWord ++ tailWord_1118362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118362).length < 2 ^ (prefixWord ++ tailWord_1118362).sum := by decide
  have hdescent : baseEnd_1118362 < baseStart_1118362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118421 : List Nat := [1, 3, 2, 4, 2, 9]
def baseStart_1118421 : Nat := 118140960795 + 1118421 * 2 ^ 59
def prefixEnd_1118421 : Nat := 4983230072969 + 3 ^ 40 * 1118421 * 2
def baseEnd_1118421 : Nat := 9453292956086813273975

theorem tailTrace_1118421 : CollatzResearch.WordTrace tailWord_1118421 prefixEnd_1118421 9453292956086813273975 := by
  unfold tailWord_1118421
  simp only [CollatzResearch.WordTrace]
  refine ⟨40792165081159202944739117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27194776720772801963159411 40792165081159202944739117)
  ·
    refine ⟨15297061905434701104277169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40792165081159202944739117 15297061905434701104277169)
    ·
      refine ⟨11472796429076025828207877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15297061905434701104277169 11472796429076025828207877)
      ·
        refine ⟨2151149330451754842788977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11472796429076025828207877 2151149330451754842788977)
        ·
          refine ⟨1613361997838816132091733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2151149330451754842788977 1613361997838816132091733)
          ·
            refine ⟨9453292956086813273975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1613361997838816132091733 9453292956086813273975)
            ·
              rfl

theorem cell21_1118421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 9].length) (baseStart_1118421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118421 prefixEnd_1118421 := by exact prefixLift 1118421
  have htrace : WordTrace (prefixWord ++ tailWord_1118421) baseStart_1118421 baseEnd_1118421 := by
    simpa [prefixWord, tailWord_1118421, baseEnd_1118421] using wordTrace_append hprefix tailTrace_1118421
  have hstable : (prefixWord ++ tailWord_1118421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118421).length < 2 ^ (prefixWord ++ tailWord_1118421).sum := by decide
  have hdescent : baseEnd_1118421 < baseStart_1118421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118500 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1118500 : Nat := 118140960795 + 1118500 * 2 ^ 59
def prefixEnd_1118500 : Nat := 4983230072969 + 3 ^ 40 * 1118500 * 2
def baseEnd_1118500 : Nat := 255256938690657376580497

theorem tailTrace_1118500 : CollatzResearch.WordTrace tailWord_1118500 prefixEnd_1118500 255256938690657376580497 := by
  unfold tailWord_1118500
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397523223936499718432477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27196697631915332957909969 20397523223936499718432477)
  ·
    refine ⟨7649071208976187394412179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20397523223936499718432477 7649071208976187394412179)
    ·
      refine ⟨11473606813464281091618269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7649071208976187394412179 11473606813464281091618269)
      ·
        refine ⟨4302602555049105409356851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11473606813464281091618269 4302602555049105409356851)
        ·
          refine ⟨6453903832573658114035277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302602555049105409356851 6453903832573658114035277)
          ·
            refine ⟨2420213937215121792763229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6453903832573658114035277 2420213937215121792763229)
            ·
              refine ⟨907580226455670672286211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2420213937215121792763229 907580226455670672286211)
              ·
                refine ⟨1361370339683506008429317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907580226455670672286211 1361370339683506008429317)
                ·
                  refine ⟨255256938690657376580497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361370339683506008429317 255256938690657376580497)
                  ·
                    rfl

theorem cell21_1118500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1118500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118500 prefixEnd_1118500 := by exact prefixLift 1118500
  have htrace : WordTrace (prefixWord ++ tailWord_1118500) baseStart_1118500 baseEnd_1118500 := by
    simpa [prefixWord, tailWord_1118500, baseEnd_1118500] using wordTrace_append hprefix tailTrace_1118500
  have hstable : (prefixWord ++ tailWord_1118500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118500).length < 2 ^ (prefixWord ++ tailWord_1118500).sum := by decide
  have hdescent : baseEnd_1118500 < baseStart_1118500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118511 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 5]
def baseStart_1118511 : Nat := 118140960795 + 1118511 * 2 ^ 59
def prefixEnd_1118511 : Nat := 4983230072969 + 3 ^ 40 * 1118511 * 2
def baseEnd_1118511 : Nat := 255259449040523801897141

theorem tailTrace_1118511 : CollatzResearch.WordTrace tailWord_1118511 prefixEnd_1118511 255259449040523801897141 := by
  unfold tailWord_1118511
  simp only [CollatzResearch.WordTrace]
  refine ⟨40795447650833148315515387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27196965100555432210343591 40795447650833148315515387)
  ·
    refine ⟨61193171476249722473273081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40795447650833148315515387 61193171476249722473273081)
    ·
      refine ⟨45894878607187291854954811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61193171476249722473273081 45894878607187291854954811)
      ·
        refine ⟨68842317910780937782432217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45894878607187291854954811 68842317910780937782432217)
        ·
          refine ⟨51631738433085703336824163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68842317910780937782432217 51631738433085703336824163)
          ·
            refine ⟨77447607649628555005236245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51631738433085703336824163 77447607649628555005236245)
            ·
              refine ⟨3630356608576338515870449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77447607649628555005236245 3630356608576338515870449)
              ·
                refine ⟨2722767456432253886902837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630356608576338515870449 2722767456432253886902837)
                ·
                  refine ⟨255259449040523801897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722767456432253886902837 255259449040523801897141)
                  ·
                    rfl

theorem cell21_1118511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_1118511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118511 prefixEnd_1118511 := by exact prefixLift 1118511
  have htrace : WordTrace (prefixWord ++ tailWord_1118511) baseStart_1118511 baseEnd_1118511 := by
    simpa [prefixWord, tailWord_1118511, baseEnd_1118511] using wordTrace_append hprefix tailTrace_1118511
  have hstable : (prefixWord ++ tailWord_1118511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118511).length < 2 ^ (prefixWord ++ tailWord_1118511).sum := by decide
  have hdescent : baseEnd_1118511 < baseStart_1118511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_1118528 : Nat := 118140960795 + 1118528 * 2 ^ 59
def prefixEnd_1118528 : Nat := 4983230072969 + 3 ^ 40 * 1118528 * 2
def baseEnd_1118528 : Nat := 255263328672135550113773

theorem tailTrace_1118528 : CollatzResearch.WordTrace tailWord_1118528 prefixEnd_1118528 255263328672135550113773 := by
  unfold tailWord_1118528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398033845885780109442119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27197378461181040145922825 20398033845885780109442119)
  ·
    refine ⟨30597050768828670164163179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20398033845885780109442119 30597050768828670164163179)
    ·
      refine ⟨45895576153243005246244769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30597050768828670164163179 45895576153243005246244769)
      ·
        refine ⟨34421682114932253934683577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45895576153243005246244769 34421682114932253934683577)
        ·
          refine ⟨25816261586199190451012683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34421682114932253934683577 25816261586199190451012683)
          ·
            refine ⟨38724392379298785676519025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25816261586199190451012683 38724392379298785676519025)
            ·
              refine ⟨29043294284474089257389269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38724392379298785676519025 29043294284474089257389269)
              ·
                refine ⟨680702209792361466970061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29043294284474089257389269 680702209792361466970061)
                ·
                  refine ⟨255263328672135550113773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680702209792361466970061 255263328672135550113773)
                  ·
                    rfl

theorem cell21_1118528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_1118528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118528 prefixEnd_1118528 := by exact prefixLift 1118528
  have htrace : WordTrace (prefixWord ++ tailWord_1118528) baseStart_1118528 baseEnd_1118528 := by
    simpa [prefixWord, tailWord_1118528, baseEnd_1118528] using wordTrace_append hprefix tailTrace_1118528
  have hstable : (prefixWord ++ tailWord_1118528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118528).length < 2 ^ (prefixWord ++ tailWord_1118528).sum := by decide
  have hdescent : baseEnd_1118528 < baseStart_1118528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118559 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 4]
def baseStart_1118559 : Nat := 118140960795 + 1118559 * 2 ^ 59
def prefixEnd_1118559 : Nat := 4983230072969 + 3 ^ 40 * 1118559 * 2
def baseEnd_1118559 : Nat := 255270403294486385097043

theorem tailTrace_1118559 : CollatzResearch.WordTrace tailWord_1118559 prefixEnd_1118559 255270403294486385097043 := by
  unfold tailWord_1118559
  simp only [CollatzResearch.WordTrace]
  refine ⟨40797198354659252513262731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27198132236439501675508487 40797198354659252513262731)
  ·
    refine ⟨61195797531988878769894097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40797198354659252513262731 61195797531988878769894097)
    ·
      refine ⟨45896848148991659077420573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61195797531988878769894097 45896848148991659077420573)
      ·
        refine ⟨17211318055871872154032715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45896848148991659077420573 17211318055871872154032715)
        ·
          refine ⟨25816977083807808231049073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17211318055871872154032715 25816977083807808231049073)
          ·
            refine ⟨19362732812855856173286805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25816977083807808231049073 19362732812855856173286805)
            ·
              refine ⟨907628100602618258122819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19362732812855856173286805 907628100602618258122819)
              ·
                refine ⟨1361442150903927387184229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907628100602618258122819 1361442150903927387184229)
                ·
                  refine ⟨255270403294486385097043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361442150903927387184229 255270403294486385097043)
                  ·
                    rfl

theorem cell21_1118559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_1118559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118559 prefixEnd_1118559 := by exact prefixLift 1118559
  have htrace : WordTrace (prefixWord ++ tailWord_1118559) baseStart_1118559 baseEnd_1118559 := by
    simpa [prefixWord, tailWord_1118559, baseEnd_1118559] using wordTrace_append hprefix tailTrace_1118559
  have hstable : (prefixWord ++ tailWord_1118559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118559).length < 2 ^ (prefixWord ++ tailWord_1118559).sum := by decide
  have hdescent : baseEnd_1118559 < baseStart_1118559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118652 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1118652 : Nat := 118140960795 + 1118652 * 2 ^ 59
def prefixEnd_1118652 : Nat := 4983230072969 + 3 ^ 40 * 1118652 * 2
def baseEnd_1118652 : Nat := 255291627161538890046853

theorem tailTrace_1118652 : CollatzResearch.WordTrace tailWord_1118652 prefixEnd_1118652 255291627161538890046853 := by
  unfold tailWord_1118652
  simp only [CollatzResearch.WordTrace]
  refine ⟨20400295171661164698199105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27200393562214886264265473 20400295171661164698199105)
  ·
    refine ⟨15300221378745873523649329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20400295171661164698199105 15300221378745873523649329)
    ·
      refine ⟨11475166034059405142736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15300221378745873523649329 11475166034059405142736997)
      ·
        refine ⟨2151593631386138464263187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11475166034059405142736997 2151593631386138464263187)
        ·
          refine ⟨3227390447079207696394781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151593631386138464263187 3227390447079207696394781)
          ·
            refine ⟨1210271417654702886148043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3227390447079207696394781 1210271417654702886148043)
            ·
              refine ⟨1815407126482054329222065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210271417654702886148043 1815407126482054329222065)
              ·
                refine ⟨1361555344861540746916549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815407126482054329222065 1361555344861540746916549)
                ·
                  refine ⟨255291627161538890046853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361555344861540746916549 255291627161538890046853)
                  ·
                    rfl

theorem cell21_1118652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1118652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118652 prefixEnd_1118652 := by exact prefixLift 1118652
  have htrace : WordTrace (prefixWord ++ tailWord_1118652) baseStart_1118652 baseEnd_1118652 := by
    simpa [prefixWord, tailWord_1118652, baseEnd_1118652] using wordTrace_append hprefix tailTrace_1118652
  have hstable : (prefixWord ++ tailWord_1118652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118652).length < 2 ^ (prefixWord ++ tailWord_1118652).sum := by decide
  have hdescent : baseEnd_1118652 < baseStart_1118652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118663 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_1118663 : Nat := 118140960795 + 1118663 * 2 ^ 59
def prefixEnd_1118663 : Nat := 4983230072969 + 3 ^ 40 * 1118663 * 2
def baseEnd_1118663 : Nat := 255294137511405315363497

theorem tailTrace_1118663 : CollatzResearch.WordTrace tailWord_1118663 prefixEnd_1118663 255294137511405315363497 := by
  unfold tailWord_1118663
  simp only [CollatzResearch.WordTrace]
  refine ⟨40800991546282478275048643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27200661030854985516699095 40800991546282478275048643)
  ·
    refine ⟨61201487319423717412572965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40800991546282478275048643 61201487319423717412572965)
    ·
      refine ⟨11475278872391947014857431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61201487319423717412572965 11475278872391947014857431)
      ·
        refine ⟨17212918308587920522286147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475278872391947014857431 17212918308587920522286147)
        ·
          refine ⟨25819377462881880783429221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17212918308587920522286147 25819377462881880783429221)
          ·
            refine ⟨4841133274290352646892979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25819377462881880783429221 4841133274290352646892979)
            ·
              refine ⟨7261699911435528970339469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841133274290352646892979 7261699911435528970339469)
              ·
                refine ⟨2723137466788323363877301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7261699911435528970339469 2723137466788323363877301)
                ·
                  refine ⟨255294137511405315363497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723137466788323363877301 255294137511405315363497)
                  ·
                    rfl

theorem cell21_1118663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_1118663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118663 prefixEnd_1118663 := by exact prefixLift 1118663
  have htrace : WordTrace (prefixWord ++ tailWord_1118663) baseStart_1118663 baseEnd_1118663 := by
    simpa [prefixWord, tailWord_1118663, baseEnd_1118663] using wordTrace_append hprefix tailTrace_1118663
  have hstable : (prefixWord ++ tailWord_1118663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118663).length < 2 ^ (prefixWord ++ tailWord_1118663).sum := by decide
  have hdescent : baseEnd_1118663 < baseStart_1118663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118765 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1118765 : Nat := 118140960795 + 1118765 * 2 ^ 59
def prefixEnd_1118765 : Nat := 4983230072969 + 3 ^ 40 * 1118765 * 2
def baseEnd_1118765 : Nat := 255317415301075804663289

theorem tailTrace_1118765 : CollatzResearch.WordTrace tailWord_1118765 prefixEnd_1118765 255317415301075804663289 := by
  unfold tailWord_1118765
  simp only [CollatzResearch.WordTrace]
  refine ⟨40804711791912949695261749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27203141194608633130174499 40804711791912949695261749)
  ·
    refine ⟨3825441730491839033930789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40804711791912949695261749 3825441730491839033930789)
    ·
      refine ⟨717270324467219818862023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3825441730491839033930789 717270324467219818862023)
      ·
        refine ⟨1075905486700829728293035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717270324467219818862023 1075905486700829728293035)
        ·
          refine ⟨1613858230051244592439553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075905486700829728293035 1613858230051244592439553)
          ·
            refine ⟨1210393672538433444329665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613858230051244592439553 1210393672538433444329665)
            ·
              refine ⟨907795254403825083247249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210393672538433444329665 907795254403825083247249)
              ·
                refine ⟨680846440802868812435437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907795254403825083247249 680846440802868812435437)
                ·
                  refine ⟨255317415301075804663289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680846440802868812435437 255317415301075804663289)
                  ·
                    rfl

theorem cell21_1118765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1118765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118765 prefixEnd_1118765 := by exact prefixLift 1118765
  have htrace : WordTrace (prefixWord ++ tailWord_1118765) baseStart_1118765 baseEnd_1118765 := by
    simpa [prefixWord, tailWord_1118765, baseEnd_1118765] using wordTrace_append hprefix tailTrace_1118765
  have hstable : (prefixWord ++ tailWord_1118765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118765).length < 2 ^ (prefixWord ++ tailWord_1118765).sum := by decide
  have hdescent : baseEnd_1118765 < baseStart_1118765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118770 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_1118770 : Nat := 118140960795 + 1118770 * 2 ^ 59
def prefixEnd_1118770 : Nat := 4983230072969 + 3 ^ 40 * 1118770 * 2
def baseEnd_1118770 : Nat := 255318556369196907079945

theorem tailTrace_1118770 : CollatzResearch.WordTrace tailWord_1118770 prefixEnd_1118770 255318556369196907079945 := by
  unfold tailWord_1118770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201223539223708887298441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27203262771263223699462509 10201223539223708887298441)
  ·
    refine ⟨7650917654417781665473831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10201223539223708887298441 7650917654417781665473831)
    ·
      refine ⟨11476376481626672498210747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650917654417781665473831 11476376481626672498210747)
      ·
        refine ⟨17214564722440008747316121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11476376481626672498210747 17214564722440008747316121)
        ·
          refine ⟨12910923541830006560487091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17214564722440008747316121 12910923541830006560487091)
          ·
            refine ⟨19366385312745009840730637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12910923541830006560487091 19366385312745009840730637)
            ·
              refine ⟨7262394492279378690273989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19366385312745009840730637 7262394492279378690273989)
              ·
                refine ⟨1361698967302383504426373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7262394492279378690273989 1361698967302383504426373)
                ·
                  refine ⟨255318556369196907079945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361698967302383504426373 255318556369196907079945)
                  ·
                    rfl

theorem cell21_1118770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_1118770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118770 prefixEnd_1118770 := by exact prefixLift 1118770
  have htrace : WordTrace (prefixWord ++ tailWord_1118770) baseStart_1118770 baseEnd_1118770 := by
    simpa [prefixWord, tailWord_1118770, baseEnd_1118770] using wordTrace_append hprefix tailTrace_1118770
  have hstable : (prefixWord ++ tailWord_1118770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118770).length < 2 ^ (prefixWord ++ tailWord_1118770).sum := by decide
  have hdescent : baseEnd_1118770 < baseStart_1118770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118784 : List Nat := [2, 1, 1, 2, 2, 2, 5, 6]
def baseStart_1118784 : Nat := 118140960795 + 1118784 * 2 ^ 59
def prefixEnd_1118784 : Nat := 4983230072969 + 3 ^ 40 * 1118784 * 2
def baseEnd_1118784 : Nat := 85107250453311997948861

theorem tailTrace_1118784 : CollatzResearch.WordTrace tailWord_1118784 prefixEnd_1118784 85107250453311997948861 := by
  unfold tailWord_1118784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20402702389422057970101703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27203603185896077293468937 20402702389422057970101703)
  ·
    refine ⟨30604053584133086955152555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20402702389422057970101703 30604053584133086955152555)
    ·
      refine ⟨45906080376199630432728833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30604053584133086955152555 45906080376199630432728833)
      ·
        refine ⟨34429560282149722824546625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45906080376199630432728833 34429560282149722824546625)
        ·
          refine ⟨25822170211612292118409969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34429560282149722824546625 25822170211612292118409969)
          ·
            refine ⟨19366627658709219088807477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25822170211612292118409969 19366627658709219088807477)
            ·
              refine ⟨1815621343003989289575701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19366627658709219088807477 1815621343003989289575701)
              ·
                refine ⟨85107250453311997948861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1815621343003989289575701 85107250453311997948861)
                ·
                  rfl

theorem cell21_1118784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_1118784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118784 prefixEnd_1118784 := by exact prefixLift 1118784
  have htrace : WordTrace (prefixWord ++ tailWord_1118784) baseStart_1118784 baseEnd_1118784 := by
    simpa [prefixWord, tailWord_1118784, baseEnd_1118784] using wordTrace_append hprefix tailTrace_1118784
  have hstable : (prefixWord ++ tailWord_1118784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118784).length < 2 ^ (prefixWord ++ tailWord_1118784).sum := by decide
  have hdescent : baseEnd_1118784 < baseStart_1118784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118801 : List Nat := [1, 2, 2, 1, 3, 4, 3, 5]
def baseStart_1118801 : Nat := 118140960795 + 1118801 * 2 ^ 59
def prefixEnd_1118801 : Nat := 4983230072969 + 3 ^ 40 * 1118801 * 2
def baseEnd_1118801 : Nat := 85108543663849247354405

theorem tailTrace_1118801 : CollatzResearch.WordTrace tailWord_1118801 prefixEnd_1118801 85108543663849247354405 := by
  unfold tailWord_1118801
  simp only [CollatzResearch.WordTrace]
  refine ⟨40806024819782527843572257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27204016546521685229048171 40806024819782527843572257)
  ·
    refine ⟨30604518614836895882679193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40806024819782527843572257 30604518614836895882679193)
    ·
      refine ⟨22953388961127671912009395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30604518614836895882679193 22953388961127671912009395)
      ·
        refine ⟨34430083441691507868014093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22953388961127671912009395 34430083441691507868014093)
        ·
          refine ⟨12911281290634315450505285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34430083441691507868014093 12911281290634315450505285)
          ·
            refine ⟨2420865241993934146969741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12911281290634315450505285 2420865241993934146969741)
            ·
              refine ⟨907824465747725305113653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2420865241993934146969741 907824465747725305113653)
              ·
                refine ⟨85108543663849247354405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 907824465747725305113653 85108543663849247354405)
                ·
                  rfl

theorem cell21_1118801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].length) (baseStart_1118801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118801 prefixEnd_1118801 := by exact prefixLift 1118801
  have htrace : WordTrace (prefixWord ++ tailWord_1118801) baseStart_1118801 baseEnd_1118801 := by
    simpa [prefixWord, tailWord_1118801, baseEnd_1118801] using wordTrace_append hprefix tailTrace_1118801
  have hstable : (prefixWord ++ tailWord_1118801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118801).length < 2 ^ (prefixWord ++ tailWord_1118801).sum := by decide
  have hdescent : baseEnd_1118801 < baseStart_1118801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118818 : List Nat := [3, 3, 2, 3, 1, 1, 8]
def baseStart_1118818 : Nat := 118140960795 + 1118818 * 2 ^ 59
def prefixEnd_1118818 : Nat := 4983230072969 + 3 ^ 40 * 1118818 * 2
def baseEnd_1118818 : Nat := 28369945624795498919983

theorem tailTrace_1118818 : CollatzResearch.WordTrace tailWord_1118818 prefixEnd_1118818 28369945624795498919983 := by
  unfold tailWord_1118818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201661215180234936735277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27204429907147293164627405 10201661215180234936735277)
  ·
    refine ⟨3825622955692588101275729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10201661215180234936735277 3825622955692588101275729)
    ·
      refine ⟨2869217216769441075956797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3825622955692588101275729 2869217216769441075956797)
      ·
        refine ⟨1075956456288540403483799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2869217216769441075956797 1075956456288540403483799)
        ·
          refine ⟨1613934684432810605225699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075956456288540403483799 1613934684432810605225699)
          ·
            refine ⟨2420902026649215907838549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613934684432810605225699 2420902026649215907838549)
            ·
              refine ⟨28369945624795498919983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2420902026649215907838549 28369945624795498919983)
              ·
                rfl

theorem cell21_1118818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 8].length) (baseStart_1118818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118818 prefixEnd_1118818 := by exact prefixLift 1118818
  have htrace : WordTrace (prefixWord ++ tailWord_1118818) baseStart_1118818 baseEnd_1118818 := by
    simpa [prefixWord, tailWord_1118818, baseEnd_1118818] using wordTrace_append hprefix tailTrace_1118818
  have hstable : (prefixWord ++ tailWord_1118818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118818).length < 2 ^ (prefixWord ++ tailWord_1118818).sum := by decide
  have hdescent : baseEnd_1118818 < baseStart_1118818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118832 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1118832 : Nat := 118140960795 + 1118832 * 2 ^ 59
def prefixEnd_1118832 : Nat := 4983230072969 + 3 ^ 40 * 1118832 * 2
def baseEnd_1118832 : Nat := 255332705613898577046485

theorem tailTrace_1118832 : CollatzResearch.WordTrace tailWord_1118832 prefixEnd_1118832 255332705613898577046485 := by
  unfold tailWord_1118832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20403577741335110068975375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27204770321780146758633833 20403577741335110068975375)
  ·
    refine ⟨30605366612002665103463063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20403577741335110068975375 30605366612002665103463063)
    ·
      refine ⟨45908049918003997655194595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30605366612002665103463063 45908049918003997655194595)
      ·
        refine ⟨68862074877005996482791893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45908049918003997655194595 68862074877005996482791893)
        ·
          refine ⟨1613954879929828042565435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68862074877005996482791893 1613954879929828042565435)
          ·
            refine ⟨2420932319894742063848153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613954879929828042565435 2420932319894742063848153)
            ·
              refine ⟨1815699239921056547886115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420932319894742063848153 1815699239921056547886115)
              ·
                refine ⟨2723548859881584821829173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1815699239921056547886115 2723548859881584821829173)
                ·
                  refine ⟨255332705613898577046485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723548859881584821829173 255332705613898577046485)
                  ·
                    rfl

theorem cell21_1118832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1118832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118832 prefixEnd_1118832 := by exact prefixLift 1118832
  have htrace : WordTrace (prefixWord ++ tailWord_1118832) baseStart_1118832 baseEnd_1118832 := by
    simpa [prefixWord, tailWord_1118832, baseEnd_1118832] using wordTrace_append hprefix tailTrace_1118832
  have hstable : (prefixWord ++ tailWord_1118832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118832).length < 2 ^ (prefixWord ++ tailWord_1118832).sum := by decide
  have hdescent : baseEnd_1118832 < baseStart_1118832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118866 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1118866 : Nat := 118140960795 + 1118866 * 2 ^ 59
def prefixEnd_1118866 : Nat := 4983230072969 + 3 ^ 40 * 1118866 * 2
def baseEnd_1118866 : Nat := 255340464877122073479749

theorem tailTrace_1118866 : CollatzResearch.WordTrace tailWord_1118866 prefixEnd_1118866 255340464877122073479749 := by
  unfold tailWord_1118866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202098891136760986172113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27205597043031362629792301 10202098891136760986172113)
  ·
    refine ⟨7651574168352570739629085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10202098891136760986172113 7651574168352570739629085)
    ·
      refine ⟨2869340313132214027360907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7651574168352570739629085 2869340313132214027360907)
      ·
        refine ⟨4304010469698321041041361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869340313132214027360907 4304010469698321041041361)
        ·
          refine ⟨3228007852273740780781021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304010469698321041041361 3228007852273740780781021)
          ·
            refine ⟨1210502944602652792792883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3228007852273740780781021 1210502944602652792792883)
            ·
              refine ⟨1815754416903979189189325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210502944602652792792883 1815754416903979189189325)
              ·
                refine ⟨680907906338992195945997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815754416903979189189325 680907906338992195945997)
                ·
                  refine ⟨255340464877122073479749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680907906338992195945997 255340464877122073479749)
                  ·
                    rfl

theorem cell21_1118866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1118866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118866 prefixEnd_1118866 := by exact prefixLift 1118866
  have htrace : WordTrace (prefixWord ++ tailWord_1118866) baseStart_1118866 baseEnd_1118866 := by
    simpa [prefixWord, tailWord_1118866, baseEnd_1118866] using wordTrace_append hprefix tailTrace_1118866
  have hstable : (prefixWord ++ tailWord_1118866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118866).length < 2 ^ (prefixWord ++ tailWord_1118866).sum := by decide
  have hdescent : baseEnd_1118866 < baseStart_1118866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118894 : List Nat := [4, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1118894 : Nat := 118140960795 + 1118894 * 2 ^ 59
def prefixEnd_1118894 : Nat := 4983230072969 + 3 ^ 40 * 1118894 * 2
def baseEnd_1118894 : Nat := 85115618286200082337675

theorem tailTrace_1118894 : CollatzResearch.WordTrace tailWord_1118894 prefixEnd_1118894 85115618286200082337675 := by
  unfold tailWord_1118894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101177101055700590838467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27206277872297069817805157 5101177101055700590838467)
  ·
    refine ⟨7651765651583550886257701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5101177101055700590838467 7651765651583550886257701)
    ·
      refine ⟨1434706059671915791173319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7651765651583550886257701 1434706059671915791173319)
      ·
        refine ⟨2152059089507873686759979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434706059671915791173319 2152059089507873686759979)
        ·
          refine ⟨3228088634261810530139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152059089507873686759979 3228088634261810530139969)
          ·
            refine ⟨2421066475696357897604977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228088634261810530139969 2421066475696357897604977)
            ·
              refine ⟨1815799856772268423203733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421066475696357897604977 1815799856772268423203733)
              ·
                refine ⟨85115618286200082337675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1815799856772268423203733 85115618286200082337675)
                ·
                  rfl

theorem cell21_1118894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1118894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118894 prefixEnd_1118894 := by exact prefixLift 1118894
  have htrace : WordTrace (prefixWord ++ tailWord_1118894) baseStart_1118894 baseEnd_1118894 := by
    simpa [prefixWord, tailWord_1118894, baseEnd_1118894] using wordTrace_append hprefix tailTrace_1118894
  have hstable : (prefixWord ++ tailWord_1118894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118894).length < 2 ^ (prefixWord ++ tailWord_1118894).sum := by decide
  have hdescent : baseEnd_1118894 < baseStart_1118894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118897 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 4]
def baseStart_1118897 : Nat := 118140960795 + 1118897 * 2 ^ 59
def prefixEnd_1118897 : Nat := 4983230072969 + 3 ^ 40 * 1118897 * 2
def baseEnd_1118897 : Nat := 255347539499472908463019

theorem tailTrace_1118897 : CollatzResearch.WordTrace tailWord_1118897 prefixEnd_1118897 255347539499472908463019 := by
  unfold tailWord_1118897
  simp only [CollatzResearch.WordTrace]
  refine ⟨40809526227434736239066945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27206350818289824159377963 40809526227434736239066945)
  ·
    refine ⟨30607144670576052179300209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40809526227434736239066945 30607144670576052179300209)
    ·
      refine ⟨22955358502932039134475157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30607144670576052179300209 22955358502932039134475157)
      ·
        refine ⟨1076032429824939334428523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22955358502932039134475157 1076032429824939334428523)
        ·
          refine ⟨1614048644737409001642785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076032429824939334428523 1614048644737409001642785)
          ·
            refine ⟨1210536483553056751232089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1614048644737409001642785 1210536483553056751232089)
            ·
              refine ⟨907902362664792563424067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210536483553056751232089 907902362664792563424067)
              ·
                refine ⟨1361853543997188845136101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907902362664792563424067 1361853543997188845136101)
                ·
                  refine ⟨255347539499472908463019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1361853543997188845136101 255347539499472908463019)
                  ·
                    rfl

theorem cell21_1118897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_1118897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118897 prefixEnd_1118897 := by exact prefixLift 1118897
  have htrace : WordTrace (prefixWord ++ tailWord_1118897) baseStart_1118897 baseEnd_1118897 := by
    simpa [prefixWord, tailWord_1118897, baseEnd_1118897] using wordTrace_append hprefix tailTrace_1118897
  have hstable : (prefixWord ++ tailWord_1118897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118897).length < 2 ^ (prefixWord ++ tailWord_1118897).sum := by decide
  have hdescent : baseEnd_1118897 < baseStart_1118897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118984 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_1118984 : Nat := 118140960795 + 1118984 * 2 ^ 59
def prefixEnd_1118984 : Nat := 4983230072969 + 3 ^ 40 * 1118984 * 2
def baseEnd_1118984 : Nat := 255367394084780090512841

theorem tailTrace_1118984 : CollatzResearch.WordTrace tailWord_1118984 prefixEnd_1118984 255367394084780090512841 := by
  unfold tailWord_1118984
  simp only [CollatzResearch.WordTrace]
  refine ⟨20406349689059775048742003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27208466252079700064989337 20406349689059775048742003)
  ·
    refine ⟨30609524533589662573113005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20406349689059775048742003 30609524533589662573113005)
    ·
      refine ⟨11478571700096123464917377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30609524533589662573113005 11478571700096123464917377)
      ·
        refine ⟨8608928775072092598688033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11478571700096123464917377 8608928775072092598688033)
        ·
          refine ⟨6456696581304069449016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8608928775072092598688033 6456696581304069449016025)
          ·
            refine ⟨4842522435978052086762019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456696581304069449016025 4842522435978052086762019)
            ·
              refine ⟨7263783653967078130143029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842522435978052086762019 7263783653967078130143029)
              ·
                refine ⟨680979717559413574700909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7263783653967078130143029 680979717559413574700909)
                ·
                  refine ⟨255367394084780090512841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 680979717559413574700909 255367394084780090512841)
                  ·
                    rfl

theorem cell21_1118984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_1118984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118984 prefixEnd_1118984 := by exact prefixLift 1118984
  have htrace : WordTrace (prefixWord ++ tailWord_1118984) baseStart_1118984 baseEnd_1118984 := by
    simpa [prefixWord, tailWord_1118984, baseEnd_1118984] using wordTrace_append hprefix tailTrace_1118984
  have hstable : (prefixWord ++ tailWord_1118984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118984).length < 2 ^ (prefixWord ++ tailWord_1118984).sum := by decide
  have hdescent : baseEnd_1118984 < baseStart_1118984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118995 : List Nat := [1, 1, 1, 2, 1, 3, 12]
def baseStart_1118995 : Nat := 118140960795 + 1118995 * 2 ^ 59
def prefixEnd_1118995 : Nat := 4983230072969 + 3 ^ 40 * 1118995 * 2
def baseEnd_1118995 : Nat := 28374433826071835092165

theorem tailTrace_1118995 : CollatzResearch.WordTrace tailWord_1118995 prefixEnd_1118995 28374433826071835092165 := by
  unfold tailWord_1118995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40813100581079698976134439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27208733720719799317422959 40813100581079698976134439)
  ·
    refine ⟨61219650871619548464201659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40813100581079698976134439 61219650871619548464201659)
    ·
      refine ⟨91829476307429322696302489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61219650871619548464201659 91829476307429322696302489)
      ·
        refine ⟨68872107230571992022226867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91829476307429322696302489 68872107230571992022226867)
        ·
          refine ⟨103308160845857988033340301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68872107230571992022226867 103308160845857988033340301)
          ·
            refine ⟨38740560317196745512502613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103308160845857988033340301 38740560317196745512502613)
            ·
              refine ⟨28374433826071835092165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 38740560317196745512502613 28374433826071835092165)
              ·
                rfl

theorem cell21_1118995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_1118995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1118995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1118995 prefixEnd_1118995 := by exact prefixLift 1118995
  have htrace : WordTrace (prefixWord ++ tailWord_1118995) baseStart_1118995 baseEnd_1118995 := by
    simpa [prefixWord, tailWord_1118995, baseEnd_1118995] using wordTrace_append hprefix tailTrace_1118995
  have hstable : (prefixWord ++ tailWord_1118995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118995).length < 2 ^ (prefixWord ++ tailWord_1118995).sum := by decide
  have hdescent : baseEnd_1118995 < baseStart_1118995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119029 : List Nat := [1, 3, 3, 1, 3, 1, 4, 5]
def baseStart_1119029 : Nat := 118140960795 + 1119029 * 2 ^ 59
def prefixEnd_1119029 : Nat := 4983230072969 + 3 ^ 40 * 1119029 * 2
def baseEnd_1119029 : Nat := 85125887899290004087583

theorem tailTrace_1119029 : CollatzResearch.WordTrace tailWord_1119029 prefixEnd_1119029 85125887899290004087583 := by
  unfold tailWord_1119029
  simp only [CollatzResearch.WordTrace]
  refine ⟨40814340662956522782872141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27209560441971015188581427 40814340662956522782872141)
  ·
    refine ⟨15305377748608696043577053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40814340662956522782872141 15305377748608696043577053)
    ·
      refine ⟨5739516655728261016341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15305377748608696043577053 5739516655728261016341395)
      ·
        refine ⟨8609274983592391524512093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739516655728261016341395 8609274983592391524512093)
        ·
          refine ⟨3228478118847146821692035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8609274983592391524512093 3228478118847146821692035)
          ·
            refine ⟨4842717178270720232538053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228478118847146821692035 4842717178270720232538053)
            ·
              refine ⟨908009470925760043600885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4842717178270720232538053 908009470925760043600885)
              ·
                refine ⟨85125887899290004087583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 908009470925760043600885 85125887899290004087583)
                ·
                  rfl

theorem cell21_1119029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].length) (baseStart_1119029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119029 prefixEnd_1119029 := by exact prefixLift 1119029
  have htrace : WordTrace (prefixWord ++ tailWord_1119029) baseStart_1119029 baseEnd_1119029 := by
    simpa [prefixWord, tailWord_1119029, baseEnd_1119029] using wordTrace_append hprefix tailTrace_1119029
  have hstable : (prefixWord ++ tailWord_1119029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119029).length < 2 ^ (prefixWord ++ tailWord_1119029).sum := by decide
  have hdescent : baseEnd_1119029 < baseStart_1119029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119122 : List Nat := [3, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1119122 : Nat := 118140960795 + 1119122 * 2 ^ 59
def prefixEnd_1119122 : Nat := 4983230072969 + 3 ^ 40 * 1119122 * 2
def baseEnd_1119122 : Nat := 85132962521640839070853

theorem tailTrace_1119122 : CollatzResearch.WordTrace tailWord_1119122 prefixEnd_1119122 85132962521640839070853 := by
  unfold tailWord_1119122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204433162904899916501905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27211821767746399777338413 10204433162904899916501905)
  ·
    refine ⟨7653324872178674937376429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10204433162904899916501905 7653324872178674937376429)
    ·
      refine ⟨2869996827067003101516161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7653324872178674937376429 2869996827067003101516161)
      ·
        refine ⟨2152497620300252326137121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2869996827067003101516161 2152497620300252326137121)
        ·
          refine ⟨1614373215225189244602841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2152497620300252326137121 1614373215225189244602841)
          ·
            refine ⟨1210779911418891933452131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1614373215225189244602841 1210779911418891933452131)
            ·
              refine ⟨1816169867128337900178197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210779911418891933452131 1816169867128337900178197)
              ·
                refine ⟨85132962521640839070853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816169867128337900178197 85132962521640839070853)
                ·
                  rfl

theorem cell21_1119122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1119122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119122 prefixEnd_1119122 := by exact prefixLift 1119122
  have htrace : WordTrace (prefixWord ++ tailWord_1119122) baseStart_1119122 baseEnd_1119122 := by
    simpa [prefixWord, tailWord_1119122, baseEnd_1119122] using wordTrace_append hprefix tailTrace_1119122
  have hstable : (prefixWord ++ tailWord_1119122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119122).length < 2 ^ (prefixWord ++ tailWord_1119122).sum := by decide
  have hdescent : baseEnd_1119122 < baseStart_1119122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119153 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 3]
def baseStart_1119153 : Nat := 118140960795 + 1119153 * 2 ^ 59
def prefixEnd_1119153 : Nat := 4983230072969 + 3 ^ 40 * 1119153 * 2
def baseEnd_1119153 : Nat := 255405962187273352195829

theorem tailTrace_1119153 : CollatzResearch.WordTrace tailWord_1119153 prefixEnd_1119153 255405962187273352195829 := by
  unfold tailWord_1119153
  simp only [CollatzResearch.WordTrace]
  refine ⟨40818863314507291960386113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27212575543004861306924075 40818863314507291960386113)
  ·
    refine ⟨30614147485880468970289585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40818863314507291960386113 30614147485880468970289585)
    ·
      refine ⟨22960610614410351727717189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30614147485880468970289585 22960610614410351727717189)
      ·
        refine ⟨4305114490201940948946973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22960610614410351727717189 4305114490201940948946973)
        ·
          refine ⟨1614417933825727855855115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4305114490201940948946973 1614417933825727855855115)
          ·
            refine ⟨2421626900738591783782673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614417933825727855855115 2421626900738591783782673)
            ·
              refine ⟨1816220175553943837837005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421626900738591783782673 1816220175553943837837005)
              ·
                refine ⟨681082565832728939188877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1816220175553943837837005 681082565832728939188877)
                ·
                  refine ⟨255405962187273352195829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681082565832728939188877 255405962187273352195829)
                  ·
                    rfl

theorem cell21_1119153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_1119153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119153 prefixEnd_1119153 := by exact prefixLift 1119153
  have htrace : WordTrace (prefixWord ++ tailWord_1119153) baseStart_1119153 baseEnd_1119153 := by
    simpa [prefixWord, tailWord_1119153, baseEnd_1119153] using wordTrace_append hprefix tailTrace_1119153
  have hstable : (prefixWord ++ tailWord_1119153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119153).length < 2 ^ (prefixWord ++ tailWord_1119153).sum := by decide
  have hdescent : baseEnd_1119153 < baseStart_1119153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119240 : List Nat := [2, 1, 3, 2, 1, 4, 2, 6]
def baseStart_1119240 : Nat := 118140960795 + 1119240 * 2 ^ 59
def prefixEnd_1119240 : Nat := 4983230072969 + 3 ^ 40 * 1119240 * 2
def baseEnd_1119240 : Nat := 85141938924193511415217

theorem tailTrace_1119240 : CollatzResearch.WordTrace tailWord_1119240 prefixEnd_1119240 85141938924193511415217 := by
  unfold tailWord_1119240
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411018232596052909401587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27214690976794737212535449 20411018232596052909401587)
  ·
    refine ⟨30616527348894079364102381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20411018232596052909401587 30616527348894079364102381)
    ·
      refine ⟨11481197755835279761538393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30616527348894079364102381 11481197755835279761538393)
      ·
        refine ⟨8610898316876459821153795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11481197755835279761538393 8610898316876459821153795)
        ·
          refine ⟨12916347475314689731730693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8610898316876459821153795 12916347475314689731730693)
          ·
            refine ⟨2421815151621504324699505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12916347475314689731730693 2421815151621504324699505)
            ·
              refine ⟨1816361363716128243524629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421815151621504324699505 1816361363716128243524629)
              ·
                refine ⟨85141938924193511415217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816361363716128243524629 85141938924193511415217)
                ·
                  rfl

theorem cell21_1119240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_1119240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119240 prefixEnd_1119240 := by exact prefixLift 1119240
  have htrace : WordTrace (prefixWord ++ tailWord_1119240) baseStart_1119240 baseEnd_1119240 := by
    simpa [prefixWord, tailWord_1119240, baseEnd_1119240] using wordTrace_append hprefix tailTrace_1119240
  have hstable : (prefixWord ++ tailWord_1119240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119240).length < 2 ^ (prefixWord ++ tailWord_1119240).sum := by decide
  have hdescent : baseEnd_1119240 < baseStart_1119240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119243 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 4]
def baseStart_1119243 : Nat := 118140960795 + 1119243 * 2 ^ 59
def prefixEnd_1119243 : Nat := 4983230072969 + 3 ^ 40 * 1119243 * 2
def baseEnd_1119243 : Nat := 255426501413453195695645

theorem tailTrace_1119243 : CollatzResearch.WordTrace tailWord_1119243 prefixEnd_1119243 255426501413453195695645 := by
  unfold tailWord_1119243
  simp only [CollatzResearch.WordTrace]
  refine ⟨40822145884181237331162383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27214763922787491554108255 40822145884181237331162383)
  ·
    refine ⟨61233218826271855996743575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40822145884181237331162383 61233218826271855996743575)
    ·
      refine ⟨91849828239407783995115363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61233218826271855996743575 91849828239407783995115363)
      ·
        refine ⟨137774742359111675992673045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91849828239407783995115363 137774742359111675992673045)
        ·
          refine ⟨6458191048083359812156549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137774742359111675992673045 6458191048083359812156549)
          ·
            refine ⟨1210910821515629964779353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6458191048083359812156549 1210910821515629964779353)
            ·
              refine ⟨908183116136722473584515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210910821515629964779353 908183116136722473584515)
              ·
                refine ⟨1362274674205083710376773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908183116136722473584515 1362274674205083710376773)
                ·
                  refine ⟨255426501413453195695645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362274674205083710376773 255426501413453195695645)
                  ·
                    rfl

theorem cell21_1119243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_1119243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119243 prefixEnd_1119243 := by exact prefixLift 1119243
  have htrace : WordTrace (prefixWord ++ tailWord_1119243) baseStart_1119243 baseEnd_1119243 := by
    simpa [prefixWord, tailWord_1119243, baseEnd_1119243] using wordTrace_append hprefix tailTrace_1119243
  have hstable : (prefixWord ++ tailWord_1119243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119243).length < 2 ^ (prefixWord ++ tailWord_1119243).sum := by decide
  have hdescent : baseEnd_1119243 < baseStart_1119243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119288 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_1119288 : Nat := 118140960795 + 1119288 * 2 ^ 59
def prefixEnd_1119288 : Nat := 4983230072969 + 3 ^ 40 * 1119288 * 2
def baseEnd_1119288 : Nat := 255436771026543117445553

theorem tailTrace_1119288 : CollatzResearch.WordTrace tailWord_1119288 prefixEnd_1119288 255436771026543117445553 := by
  unfold tailWord_1119288
  simp only [CollatzResearch.WordTrace]
  refine ⟨20411893584509105008275259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27215858112678806677700345 20411893584509105008275259)
  ·
    refine ⟨30617840376763657512412889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20411893584509105008275259 30617840376763657512412889)
    ·
      refine ⟨22963380282572743134309667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30617840376763657512412889 22963380282572743134309667)
      ·
        refine ⟨34445070423859114701464501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22963380282572743134309667 34445070423859114701464501)
        ·
          refine ⟨3229225352236792003262297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34445070423859114701464501 3229225352236792003262297)
          ·
            refine ⟨2421919014177594002446723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3229225352236792003262297 2421919014177594002446723)
            ·
              refine ⟨3632878521266391003670085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421919014177594002446723 3632878521266391003670085)
              ·
                refine ⟨681164722737448313188141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3632878521266391003670085 681164722737448313188141)
                ·
                  refine ⟨255436771026543117445553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681164722737448313188141 255436771026543117445553)
                  ·
                    rfl

theorem cell21_1119288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_1119288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119288 prefixEnd_1119288 := by exact prefixLift 1119288
  have htrace : WordTrace (prefixWord ++ tailWord_1119288) baseStart_1119288 baseEnd_1119288 := by
    simpa [prefixWord, tailWord_1119288, baseEnd_1119288] using wordTrace_append hprefix tailTrace_1119288
  have hstable : (prefixWord ++ tailWord_1119288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119288).length < 2 ^ (prefixWord ++ tailWord_1119288).sum := by decide
  have hdescent : baseEnd_1119288 < baseStart_1119288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119336 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_1119336 : Nat := 118140960795 + 1119336 * 2 ^ 59
def prefixEnd_1119336 : Nat := 4983230072969 + 3 ^ 40 * 1119336 * 2
def baseEnd_1119336 : Nat := 255447725280505700645455

theorem tailTrace_1119336 : CollatzResearch.WordTrace tailWord_1119336 prefixEnd_1119336 255447725280505700645455 := by
  unfold tailWord_1119336
  simp only [CollatzResearch.WordTrace]
  refine ⟨20412768936422157107148931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27217025248562876142865241 20412768936422157107148931)
  ·
    refine ⟨30619153404633235660723397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20412768936422157107148931 30619153404633235660723397)
    ·
      refine ⟨5741091263368731686385637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30619153404633235660723397 5741091263368731686385637)
      ·
        refine ⟨1076454611881637191197307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5741091263368731686385637 1076454611881637191197307)
        ·
          refine ⟨1614681917822455786795961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076454611881637191197307 1614681917822455786795961)
          ·
            refine ⟨1211011438366841840096971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1614681917822455786795961 1211011438366841840096971)
            ·
              refine ⟨1816517157550262760145457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211011438366841840096971 1816517157550262760145457)
              ·
                refine ⟨1362387868162697070109093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816517157550262760145457 1362387868162697070109093)
                ·
                  refine ⟨255447725280505700645455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362387868162697070109093 255447725280505700645455)
                  ·
                    rfl

theorem cell21_1119336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_1119336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119336 prefixEnd_1119336 := by exact prefixLift 1119336
  have htrace : WordTrace (prefixWord ++ tailWord_1119336) baseStart_1119336 baseEnd_1119336 := by
    simpa [prefixWord, tailWord_1119336, baseEnd_1119336] using wordTrace_append hprefix tailTrace_1119336
  have hstable : (prefixWord ++ tailWord_1119336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119336).length < 2 ^ (prefixWord ++ tailWord_1119336).sum := by decide
  have hdescent : baseEnd_1119336 < baseStart_1119336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119457 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 3]
def baseStart_1119457 : Nat := 118140960795 + 1119457 * 2 ^ 59
def prefixEnd_1119457 : Nat := 4983230072969 + 3 ^ 40 * 1119457 * 2
def baseEnd_1119457 : Nat := 255475339129036379128541

theorem tailTrace_1119457 : CollatzResearch.WordTrace tailWord_1119457 prefixEnd_1119457 255475339129036379128541 := by
  unfold tailWord_1119457
  simp only [CollatzResearch.WordTrace]
  refine ⟨40829951105405951879452625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27219967403603967919635083 40829951105405951879452625)
  ·
    refine ⟨30622463329054463909589469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40829951105405951879452625 30622463329054463909589469)
    ·
      refine ⟨11483423748395423966096051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30622463329054463909589469 11483423748395423966096051)
      ·
        refine ⟨17225135622593135949144077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11483423748395423966096051 17225135622593135949144077)
        ·
          refine ⟨6459425858472425980929029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17225135622593135949144077 6459425858472425980929029)
          ·
            refine ⟨1211142348463579871424193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6459425858472425980929029 1211142348463579871424193)
            ·
              refine ⟨908356761347684903568145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211142348463579871424193 908356761347684903568145)
              ·
                refine ⟨681267571010763677676109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908356761347684903568145 681267571010763677676109)
                ·
                  refine ⟨255475339129036379128541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681267571010763677676109 255475339129036379128541)
                  ·
                    rfl

theorem cell21_1119457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_1119457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119457 prefixEnd_1119457 := by exact prefixLift 1119457
  have htrace : WordTrace (prefixWord ++ tailWord_1119457) baseStart_1119457 baseEnd_1119457 := by
    simpa [prefixWord, tailWord_1119457, baseEnd_1119457] using wordTrace_append hprefix tailTrace_1119457
  have hstable : (prefixWord ++ tailWord_1119457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119457).length < 2 ^ (prefixWord ++ tailWord_1119457).sum := by decide
  have hdescent : baseEnd_1119457 < baseStart_1119457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119468 : List Nat := [2, 2, 1, 1, 2, 6, 1, 6]
def baseStart_1119468 : Nat := 118140960795 + 1119468 * 2 ^ 59
def prefixEnd_1119468 : Nat := 4983230072969 + 3 ^ 40 * 1119468 * 2
def baseEnd_1119468 : Nat := 85159283159634268148395

theorem tailTrace_1119468 : CollatzResearch.WordTrace tailWord_1119468 prefixEnd_1119468 85159283159634268148395 := by
  unfold tailWord_1119468
  simp only [CollatzResearch.WordTrace]
  refine ⟨20415176154183050379051529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27220234872244067172068705 20415176154183050379051529)
  ·
    refine ⟨15311382115637287784288647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20415176154183050379051529 15311382115637287784288647)
    ·
      refine ⟨22967073173455931676432971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15311382115637287784288647 22967073173455931676432971)
      ·
        refine ⟨34450609760183897514649457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22967073173455931676432971 34450609760183897514649457)
        ·
          refine ⟨25837957320137923135987093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34450609760183897514649457 25837957320137923135987093)
          ·
            refine ⟨1211154249381465146999395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25837957320137923135987093 1211154249381465146999395)
            ·
              refine ⟨1816731374072197720499093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211154249381465146999395 1816731374072197720499093)
              ·
                refine ⟨85159283159634268148395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1816731374072197720499093 85159283159634268148395)
                ·
                  rfl

theorem cell21_1119468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_1119468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119468 prefixEnd_1119468 := by exact prefixLift 1119468
  have htrace : WordTrace (prefixWord ++ tailWord_1119468) baseStart_1119468 baseEnd_1119468 := by
    simpa [prefixWord, tailWord_1119468, baseEnd_1119468] using wordTrace_append hprefix tailTrace_1119468
  have hstable : (prefixWord ++ tailWord_1119468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119468).length < 2 ^ (prefixWord ++ tailWord_1119468).sum := by decide
  have hdescent : baseEnd_1119468 < baseStart_1119468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119482 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1119482 : Nat := 118140960795 + 1119482 * 2 ^ 59
def prefixEnd_1119482 : Nat := 4983230072969 + 3 ^ 40 * 1119482 * 2
def baseEnd_1119482 : Nat := 255481044469641891211823

theorem tailTrace_1119482 : CollatzResearch.WordTrace tailWord_1119482 prefixEnd_1119482 255481044469641891211823 := by
  unfold tailWord_1119482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10207715732578845287278175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27220575286876920766075133 10207715732578845287278175)
  ·
    refine ⟨15311573598868267930917263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10207715732578845287278175 15311573598868267930917263)
    ·
      refine ⟨22967360398302401896375895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15311573598868267930917263 22967360398302401896375895)
      ·
        refine ⟨34451040597453602844563843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22967360398302401896375895 34451040597453602844563843)
        ·
          refine ⟨51676560896180404266845765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34451040597453602844563843 51676560896180404266845765)
          ·
            refine ⟨9689355168033825800033581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51676560896180404266845765 9689355168033825800033581)
            ·
              refine ⟨3633508188012684675012593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9689355168033825800033581 3633508188012684675012593)
              ·
                refine ⟨2725131141009513506259445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633508188012684675012593 2725131141009513506259445)
                ·
                  refine ⟨255481044469641891211823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2725131141009513506259445 255481044469641891211823)
                  ·
                    rfl

theorem cell21_1119482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1119482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119482 prefixEnd_1119482 := by exact prefixLift 1119482
  have htrace : WordTrace (prefixWord ++ tailWord_1119482) baseStart_1119482 baseEnd_1119482 := by
    simpa [prefixWord, tailWord_1119482, baseEnd_1119482] using wordTrace_append hprefix tailTrace_1119482
  have hstable : (prefixWord ++ tailWord_1119482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119482).length < 2 ^ (prefixWord ++ tailWord_1119482).sum := by decide
  have hdescent : baseEnd_1119482 < baseStart_1119482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119499 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 3]
def baseStart_1119499 : Nat := 118140960795 + 1119499 * 2 ^ 59
def prefixEnd_1119499 : Nat := 4983230072969 + 3 ^ 40 * 1119499 * 2
def baseEnd_1119499 : Nat := 255484924101253639428455

theorem tailTrace_1119499 : CollatzResearch.WordTrace tailWord_1119499 prefixEnd_1119499 255484924101253639428455 := by
  unfold tailWord_1119499
  simp only [CollatzResearch.WordTrace]
  refine ⟨40831482971253793052481551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27220988647502528701654367 40831482971253793052481551)
  ·
    refine ⟨61247224456880689578722327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40831482971253793052481551 61247224456880689578722327)
    ·
      refine ⟨91870836685321034368083491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61247224456880689578722327 91870836685321034368083491)
      ·
        refine ⟨137806255027981551552125237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91870836685321034368083491 137806255027981551552125237)
        ·
          refine ⟨12919336408873270458011741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137806255027981551552125237 12919336408873270458011741)
          ·
            refine ⟨4844751153327476421754403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12919336408873270458011741 4844751153327476421754403)
            ·
              refine ⟨7267126729991214632631605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844751153327476421754403 7267126729991214632631605)
              ·
                refine ⟨681293130936676371809213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7267126729991214632631605 681293130936676371809213)
                ·
                  refine ⟨255484924101253639428455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681293130936676371809213 255484924101253639428455)
                  ·
                    rfl

theorem cell21_1119499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].length) (baseStart_1119499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119499 prefixEnd_1119499 := by exact prefixLift 1119499
  have htrace : WordTrace (prefixWord ++ tailWord_1119499) baseStart_1119499 baseEnd_1119499 := by
    simpa [prefixWord, tailWord_1119499, baseEnd_1119499] using wordTrace_append hprefix tailTrace_1119499
  have hstable : (prefixWord ++ tailWord_1119499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119499).length < 2 ^ (prefixWord ++ tailWord_1119499).sum := by decide
  have hdescent : baseEnd_1119499 < baseStart_1119499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119575 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_1119575 : Nat := 118140960795 + 1119575 * 2 ^ 59
def prefixEnd_1119575 : Nat := 4983230072969 + 3 ^ 40 * 1119575 * 2
def baseEnd_1119575 : Nat := 255502268336694396161633

theorem tailTrace_1119575 : CollatzResearch.WordTrace tailWord_1119575 prefixEnd_1119575 255502268336694396161633 := by
  unfold tailWord_1119575
  simp only [CollatzResearch.WordTrace]
  refine ⟨40834254918978458032248179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27222836612652305354832119 40834254918978458032248179)
  ·
    refine ⟨61251382378467687048372269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40834254918978458032248179 61251382378467687048372269)
    ·
      refine ⟨22969268391925382643139601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61251382378467687048372269 22969268391925382643139601)
      ·
        refine ⟨17226951293944036982354701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22969268391925382643139601 17226951293944036982354701)
        ·
          refine ⟨6460106735229013868383013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17226951293944036982354701 6460106735229013868383013)
          ·
            refine ⟨1211270012855440100321815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6460106735229013868383013 1211270012855440100321815)
            ·
              refine ⟨1816905019283160150482723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211270012855440100321815 1816905019283160150482723)
              ·
                refine ⟨2725357528924740225724085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816905019283160150482723 2725357528924740225724085)
                ·
                  refine ⟨255502268336694396161633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2725357528924740225724085 255502268336694396161633)
                  ·
                    rfl

theorem cell21_1119575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_1119575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119575 prefixEnd_1119575 := by exact prefixLift 1119575
  have htrace : WordTrace (prefixWord ++ tailWord_1119575) baseStart_1119575 baseEnd_1119575 := by
    simpa [prefixWord, tailWord_1119575, baseEnd_1119575] using wordTrace_append hprefix tailTrace_1119575
  have hstable : (prefixWord ++ tailWord_1119575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119575).length < 2 ^ (prefixWord ++ tailWord_1119575).sum := by decide
  have hdescent : baseEnd_1119575 < baseStart_1119575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119589 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1119589 : Nat := 118140960795 + 1119589 * 2 ^ 59
def prefixEnd_1119589 : Nat := 4983230072969 + 3 ^ 40 * 1119589 * 2
def baseEnd_1119589 : Nat := 255505463327433482928271

theorem tailTrace_1119589 : CollatzResearch.WordTrace tailWord_1119589 prefixEnd_1119589 255505463327433482928271 := by
  unfold tailWord_1119589
  simp only [CollatzResearch.WordTrace]
  refine ⟨40834765540927738423257821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27223177027285158948838547 40834765540927738423257821)
  ·
    refine ⟨15313037077847901908721683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40834765540927738423257821 15313037077847901908721683)
    ·
      refine ⟨22969555616771852863082525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15313037077847901908721683 22969555616771852863082525)
      ·
        refine ⟨8613583356289444823655947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22969555616771852863082525 8613583356289444823655947)
        ·
          refine ⟨12920375034434167235483921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8613583356289444823655947 12920375034434167235483921)
          ·
            refine ⟨9690281275825625426612941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12920375034434167235483921 9690281275825625426612941)
            ·
              refine ⟨3633855478434609534979853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9690281275825625426612941 3633855478434609534979853)
              ·
                refine ⟨1362695804412978575617445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3633855478434609534979853 1362695804412978575617445)
                ·
                  refine ⟨255505463327433482928271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362695804412978575617445 255505463327433482928271)
                  ·
                    rfl

theorem cell21_1119589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1119589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119589 prefixEnd_1119589 := by exact prefixLift 1119589
  have htrace : WordTrace (prefixWord ++ tailWord_1119589) baseStart_1119589 baseEnd_1119589 := by
    simpa [prefixWord, tailWord_1119589, baseEnd_1119589] using wordTrace_append hprefix tailTrace_1119589
  have hstable : (prefixWord ++ tailWord_1119589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119589).length < 2 ^ (prefixWord ++ tailWord_1119589).sum := by decide
  have hdescent : baseEnd_1119589 < baseStart_1119589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119727 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 3]
def baseStart_1119727 : Nat := 118140960795 + 1119727 * 2 ^ 59
def prefixEnd_1119727 : Nat := 4983230072969 + 3 ^ 40 * 1119727 * 2
def baseEnd_1119727 : Nat := 255536956807575909627989

theorem tailTrace_1119727 : CollatzResearch.WordTrace tailWord_1119727 prefixEnd_1119727 255536956807575909627989 := by
  unfold tailWord_1119727
  simp only [CollatzResearch.WordTrace]
  refine ⟨40839798814427787991781435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27226532542951858661187623 40839798814427787991781435)
  ·
    refine ⟨61259698221641681987672153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40839798814427787991781435 61259698221641681987672153)
    ·
      refine ⟨45944773666231261490754115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61259698221641681987672153 45944773666231261490754115)
      ·
        refine ⟨68917160499346892236131173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45944773666231261490754115 68917160499346892236131173)
        ·
          refine ⟨12921967593627542294274595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68917160499346892236131173 12921967593627542294274595)
          ·
            refine ⟨19382951390441313441411893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12921967593627542294274595 19382951390441313441411893)
            ·
              refine ⟨1817151692853873135132365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19382951390441313441411893 1817151692853873135132365)
              ·
                refine ⟨681431884820202425674637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817151692853873135132365 681431884820202425674637)
                ·
                  refine ⟨255536956807575909627989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681431884820202425674637 255536956807575909627989)
                  ·
                    rfl

theorem cell21_1119727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 3].length) (baseStart_1119727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119727 prefixEnd_1119727 := by exact prefixLift 1119727
  have htrace : WordTrace (prefixWord ++ tailWord_1119727) baseStart_1119727 baseEnd_1119727 := by
    simpa [prefixWord, tailWord_1119727, baseEnd_1119727] using wordTrace_append hprefix tailTrace_1119727
  have hstable : (prefixWord ++ tailWord_1119727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119727).length < 2 ^ (prefixWord ++ tailWord_1119727).sum := by decide
  have hdescent : baseEnd_1119727 < baseStart_1119727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119750 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1119750 : Nat := 118140960795 + 1119750 * 2 ^ 59
def prefixEnd_1119750 : Nat := 4983230072969 + 3 ^ 40 * 1119750 * 2
def baseEnd_1119750 : Nat := 255542205720932980744609

theorem tailTrace_1119750 : CollatzResearch.WordTrace tailWord_1119750 prefixEnd_1119750 255542205720932980744609 := by
  unfold tailWord_1119750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276269927917014466245897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27227091795562975279912469 1276269927917014466245897)
  ·
    refine ⟨957202445937760849684423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1276269927917014466245897 957202445937760849684423)
    ·
      refine ⟨1435803668906641274526635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957202445937760849684423 1435803668906641274526635)
      ·
        refine ⟨2153705503359961911789953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435803668906641274526635 2153705503359961911789953)
        ·
          refine ⟨1615279127519971433842465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2153705503359961911789953 1615279127519971433842465)
          ·
            refine ⟨1211459345639978575381849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615279127519971433842465 1211459345639978575381849)
            ·
              refine ⟨908594509229983931536387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211459345639978575381849 908594509229983931536387)
              ·
                refine ⟨1362891763844975897304581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908594509229983931536387 1362891763844975897304581)
                ·
                  refine ⟨255542205720932980744609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362891763844975897304581 255542205720932980744609)
                  ·
                    rfl

theorem cell21_1119750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1119750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119750 prefixEnd_1119750 := by exact prefixLift 1119750
  have htrace : WordTrace (prefixWord ++ tailWord_1119750) baseStart_1119750 baseEnd_1119750 := by
    simpa [prefixWord, tailWord_1119750, baseEnd_1119750] using wordTrace_append hprefix tailTrace_1119750
  have hstable : (prefixWord ++ tailWord_1119750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119750).length < 2 ^ (prefixWord ++ tailWord_1119750).sum := by decide
  have hdescent : baseEnd_1119750 < baseStart_1119750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119758 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1119758 : Nat := 118140960795 + 1119758 * 2 ^ 59
def prefixEnd_1119758 : Nat := 4983230072969 + 3 ^ 40 * 1119758 * 2
def baseEnd_1119758 : Nat := 255544031429926744611259

theorem tailTrace_1119758 : CollatzResearch.WordTrace tailWord_1119758 prefixEnd_1119758 255544031429926744611259 := by
  unfold tailWord_1119758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5105116184664435035769991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27227286318210320190773285 5105116184664435035769991)
  ·
    refine ⟨7657674276996652553654987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5105116184664435035769991 7657674276996652553654987)
    ·
      refine ⟨11486511415494978830482481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657674276996652553654987 11486511415494978830482481)
      ·
        refine ⟨8614883561621234122861861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11486511415494978830482481 8614883561621234122861861)
        ·
          refine ⟨1615290667803981398036599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8614883561621234122861861 1615290667803981398036599)
          ·
            refine ⟨2422936001705972097054899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615290667803981398036599 2422936001705972097054899)
            ·
              refine ⟨3634404002558958145582349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422936001705972097054899 3634404002558958145582349)
              ·
                refine ⟨1362901500959609304593381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634404002558958145582349 1362901500959609304593381)
                ·
                  refine ⟨255544031429926744611259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1362901500959609304593381 255544031429926744611259)
                  ·
                    rfl

theorem cell21_1119758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1119758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119758 prefixEnd_1119758 := by exact prefixLift 1119758
  have htrace : WordTrace (prefixWord ++ tailWord_1119758) baseStart_1119758 baseEnd_1119758 := by
    simpa [prefixWord, tailWord_1119758, baseEnd_1119758] using wordTrace_append hprefix tailTrace_1119758
  have hstable : (prefixWord ++ tailWord_1119758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119758).length < 2 ^ (prefixWord ++ tailWord_1119758).sum := by decide
  have hdescent : baseEnd_1119758 < baseStart_1119758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119896 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_1119896 : Nat := 118140960795 + 1119896 * 2 ^ 59
def prefixEnd_1119896 : Nat := 4983230072969 + 3 ^ 40 * 1119896 * 2
def baseEnd_1119896 : Nat := 255575524910069171310977

theorem tailTrace_1119896 : CollatzResearch.WordTrace tailWord_1119896 prefixEnd_1119896 255575524910069171310977 := by
  unfold tailWord_1119896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20422981375407764927341771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27230641833877019903122361 20422981375407764927341771)
  ·
    refine ⟨30634472063111647391012657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20422981375407764927341771 30634472063111647391012657)
    ·
      refine ⟨22975854047333735543259493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30634472063111647391012657 22975854047333735543259493)
      ·
        refine ⟨4307972633875075414361155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22975854047333735543259493 4307972633875075414361155)
        ·
          refine ⟨6461958950812613121541733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307972633875075414361155 6461958950812613121541733)
          ·
            refine ⟨1211617303277364960289075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6461958950812613121541733 1211617303277364960289075)
            ·
              refine ⟨1817425954916047440433613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211617303277364960289075 1817425954916047440433613)
              ·
                refine ⟨681534733093517790162605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817425954916047440433613 681534733093517790162605)
                ·
                  refine ⟨255575524910069171310977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681534733093517790162605 255575524910069171310977)
                  ·
                    rfl

theorem cell21_1119896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_1119896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1119896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1119896 prefixEnd_1119896 := by exact prefixLift 1119896
  have htrace : WordTrace (prefixWord ++ tailWord_1119896) baseStart_1119896 baseEnd_1119896 := by
    simpa [prefixWord, tailWord_1119896, baseEnd_1119896] using wordTrace_append hprefix tailTrace_1119896
  have hstable : (prefixWord ++ tailWord_1119896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119896).length < 2 ^ (prefixWord ++ tailWord_1119896).sum := by decide
  have hdescent : baseEnd_1119896 < baseStart_1119896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120028 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1120028 : Nat := 118140960795 + 1120028 * 2 ^ 59
def prefixEnd_1120028 : Nat := 4983230072969 + 3 ^ 40 * 1120028 * 2
def baseEnd_1120028 : Nat := 255605649108466275110707

theorem tailTrace_1120028 : CollatzResearch.WordTrace tailWord_1120028 prefixEnd_1120028 255605649108466275110707 := by
  unfold tailWord_1120028
  simp only [CollatzResearch.WordTrace]
  refine ⟨20425388593168658199244369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27233851457558210932325825 20425388593168658199244369)
  ·
    refine ⟨15319041444876493649433277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20425388593168658199244369 15319041444876493649433277)
    ·
      refine ⟨5744640541828685118537479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15319041444876493649433277 5744640541828685118537479)
      ·
        refine ⟨8616960812743027677806219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744640541828685118537479 8616960812743027677806219)
        ·
          refine ⟨12925441219114541516709329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8616960812743027677806219 12925441219114541516709329)
          ·
            refine ⟨9694080914335906137531997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12925441219114541516709329 9694080914335906137531997)
            ·
              refine ⟨3635280342875964801574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9694080914335906137531997 3635280342875964801574499)
              ·
                refine ⟨5452920514313947202361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635280342875964801574499 5452920514313947202361749)
                ·
                  refine ⟨255605649108466275110707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5452920514313947202361749 255605649108466275110707)
                  ·
                    rfl

theorem cell21_1120028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1120028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120028 prefixEnd_1120028 := by exact prefixLift 1120028
  have htrace : WordTrace (prefixWord ++ tailWord_1120028) baseStart_1120028 baseEnd_1120028 := by
    simpa [prefixWord, tailWord_1120028, baseEnd_1120028] using wordTrace_append hprefix tailTrace_1120028
  have hstable : (prefixWord ++ tailWord_1120028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120028).length < 2 ^ (prefixWord ++ tailWord_1120028).sum := by decide
  have hdescent : baseEnd_1120028 < baseStart_1120028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120076 : List Nat := [2, 2, 1, 3, 5, 1, 7]
def baseStart_1120076 : Nat := 118140960795 + 1120076 * 2 ^ 59
def prefixEnd_1120076 : Nat := 4983230072969 + 3 ^ 40 * 1120076 * 2
def baseEnd_1120076 : Nat := 28401844818047650923401

theorem tailTrace_1120076 : CollatzResearch.WordTrace tailWord_1120076 prefixEnd_1120076 28401844818047650923401 := by
  unfold tailWord_1120076
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426263945081710298118041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27235018593442280397490721 20426263945081710298118041)
  ·
    refine ⟨15319697958811282723588531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20426263945081710298118041 15319697958811282723588531)
    ·
      refine ⟨22979546938216924085382797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15319697958811282723588531 22979546938216924085382797)
      ·
        refine ⟨8617330101831346532018549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22979546938216924085382797 8617330101831346532018549)
        ·
          refine ⟨807874697046688737376739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8617330101831346532018549 807874697046688737376739)
          ·
            refine ⟨1211812045570033106065109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807874697046688737376739 1211812045570033106065109)
            ·
              refine ⟨28401844818047650923401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1211812045570033106065109 28401844818047650923401)
              ·
                rfl

theorem cell21_1120076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 7].length) (baseStart_1120076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120076 prefixEnd_1120076 := by exact prefixLift 1120076
  have htrace : WordTrace (prefixWord ++ tailWord_1120076) baseStart_1120076 baseEnd_1120076 := by
    simpa [prefixWord, tailWord_1120076, baseEnd_1120076] using wordTrace_append hprefix tailTrace_1120076
  have hstable : (prefixWord ++ tailWord_1120076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120076).length < 2 ^ (prefixWord ++ tailWord_1120076).sum := by decide
  have hdescent : baseEnd_1120076 < baseStart_1120076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120135 : List Nat := [1, 1, 4, 2, 5, 8]
def baseStart_1120135 : Nat := 118140960795 + 1120135 * 2 ^ 59
def prefixEnd_1120135 : Nat := 4983230072969 + 3 ^ 40 * 1120135 * 2
def baseEnd_1120135 : Nat := 9467780295046587660265

theorem tailTrace_1120135 : CollatzResearch.WordTrace tailWord_1120135 prefixEnd_1120135 9467780295046587660265 := by
  unfold tailWord_1120135
  simp only [CollatzResearch.WordTrace]
  refine ⟨40854679796949673672633859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27236453197966449115089239 40854679796949673672633859)
  ·
    refine ⟨61282019695424510508950789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40854679796949673672633859 61282019695424510508950789)
    ·
      refine ⟨11490378692892095720428273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61282019695424510508950789 11490378692892095720428273)
      ·
        refine ⟨8617784019669071790321205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11490378692892095720428273 8617784019669071790321205)
        ·
          refine ⟨807917251843975480342613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8617784019669071790321205 807917251843975480342613)
          ·
            refine ⟨9467780295046587660265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 807917251843975480342613 9467780295046587660265)
            ·
              rfl

theorem cell21_1120135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 8].length) (baseStart_1120135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120135 prefixEnd_1120135 := by exact prefixLift 1120135
  have htrace : WordTrace (prefixWord ++ tailWord_1120135) baseStart_1120135 baseEnd_1120135 := by
    simpa [prefixWord, tailWord_1120135, baseEnd_1120135] using wordTrace_append hprefix tailTrace_1120135
  have hstable : (prefixWord ++ tailWord_1120135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120135).length < 2 ^ (prefixWord ++ tailWord_1120135).sum := by decide
  have hdescent : baseEnd_1120135 < baseStart_1120135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120138 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_1120138 : Nat := 118140960795 + 1120138 * 2 ^ 59
def prefixEnd_1120138 : Nat := 4983230072969 + 3 ^ 40 * 1120138 * 2
def baseEnd_1120138 : Nat := 255630752607130528277149

theorem tailTrace_1120138 : CollatzResearch.WordTrace tailWord_1120138 prefixEnd_1120138 255630752607130528277149 := by
  unfold tailWord_1120138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213697303984701296248267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27236526143959203456662045 10213697303984701296248267)
  ·
    refine ⟨15320545955977051944372401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10213697303984701296248267 15320545955977051944372401)
    ·
      refine ⟨11490409466982788958279301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15320545955977051944372401 11490409466982788958279301)
      ·
        refine ⟨2154451775059272929677369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11490409466982788958279301 2154451775059272929677369)
        ·
          refine ⟨1615838831294454697258027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154451775059272929677369 1615838831294454697258027)
          ·
            refine ⟨2423758246941682045887041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615838831294454697258027 2423758246941682045887041)
            ·
              refine ⟨1817818685206261534415281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423758246941682045887041 1817818685206261534415281)
              ·
                refine ⟨1363364013904696150811461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817818685206261534415281 1363364013904696150811461)
                ·
                  refine ⟨255630752607130528277149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363364013904696150811461 255630752607130528277149)
                  ·
                    rfl

theorem cell21_1120138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_1120138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120138 prefixEnd_1120138 := by exact prefixLift 1120138
  have htrace : WordTrace (prefixWord ++ tailWord_1120138) baseStart_1120138 baseEnd_1120138 := by
    simpa [prefixWord, tailWord_1120138, baseEnd_1120138] using wordTrace_append hprefix tailTrace_1120138
  have hstable : (prefixWord ++ tailWord_1120138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120138).length < 2 ^ (prefixWord ++ tailWord_1120138).sum := by decide
  have hdescent : baseEnd_1120138 < baseStart_1120138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120149 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1120149 : Nat := 118140960795 + 1120149 * 2 ^ 59
def prefixEnd_1120149 : Nat := 4983230072969 + 3 ^ 40 * 1120149 * 2
def baseEnd_1120149 : Nat := 255633262956996953593793

theorem tailTrace_1120149 : CollatzResearch.WordTrace tailWord_1120149 prefixEnd_1120149 255633262956996953593793 := by
  unfold tailWord_1120149
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855190418898954063643501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27236793612599302709095667 40855190418898954063643501)
  ·
    refine ⟨15320696407087107773866313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40855190418898954063643501 15320696407087107773866313)
    ·
      refine ⟨11490522305315330830399735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15320696407087107773866313 11490522305315330830399735)
      ·
        refine ⟨17235783457972996245599603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11490522305315330830399735 17235783457972996245599603)
        ·
          refine ⟨25853675186959494368399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17235783457972996245599603 25853675186959494368399405)
          ·
            refine ⟨9695128195109810388149777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25853675186959494368399405 9695128195109810388149777)
            ·
              refine ⟨7271346146332357791112333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9695128195109810388149777 7271346146332357791112333)
              ·
                refine ⟨2726754804874634171667125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7271346146332357791112333 2726754804874634171667125)
                ·
                  refine ⟨255633262956996953593793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2726754804874634171667125 255633262956996953593793)
                  ·
                    rfl

theorem cell21_1120149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1120149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120149 prefixEnd_1120149 := by exact prefixLift 1120149
  have htrace : WordTrace (prefixWord ++ tailWord_1120149) baseStart_1120149 baseEnd_1120149 := by
    simpa [prefixWord, tailWord_1120149, baseEnd_1120149] using wordTrace_append hprefix tailTrace_1120149
  have hstable : (prefixWord ++ tailWord_1120149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120149).length < 2 ^ (prefixWord ++ tailWord_1120149).sum := by decide
  have hdescent : baseEnd_1120149 < baseStart_1120149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120163 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_1120163 : Nat := 118140960795 + 1120163 * 2 ^ 59
def prefixEnd_1120163 : Nat := 4983230072969 + 3 ^ 40 * 1120163 * 2
def baseEnd_1120163 : Nat := 255636457947736040360431

theorem tailTrace_1120163 : CollatzResearch.WordTrace tailWord_1120163 prefixEnd_1120163 255636457947736040360431 := by
  unfold tailWord_1120163
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855701040848234454653143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27237134027232156303102095 40855701040848234454653143)
  ·
    refine ⟨61283551561272351681979715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40855701040848234454653143 61283551561272351681979715)
    ·
      refine ⟨91925327341908527522969573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61283551561272351681979715 91925327341908527522969573)
      ·
        refine ⟨17235998876607848910556795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91925327341908527522969573 17235998876607848910556795)
        ·
          refine ⟨25853998314911773365835193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17235998876607848910556795 25853998314911773365835193)
          ·
            refine ⟨19390498736183830024376395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25853998314911773365835193 19390498736183830024376395)
            ·
              refine ⟨29085748104275745036564593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19390498736183830024376395 29085748104275745036564593)
              ·
                refine ⟨21814311078206808777423445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29085748104275745036564593 21814311078206808777423445)
                ·
                  refine ⟨255636457947736040360431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21814311078206808777423445 255636457947736040360431)
                  ·
                    rfl

theorem cell21_1120163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_1120163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120163 prefixEnd_1120163 := by exact prefixLift 1120163
  have htrace : WordTrace (prefixWord ++ tailWord_1120163) baseStart_1120163 baseEnd_1120163 := by
    simpa [prefixWord, tailWord_1120163, baseEnd_1120163] using wordTrace_append hprefix tailTrace_1120163
  have hstable : (prefixWord ++ tailWord_1120163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120163).length < 2 ^ (prefixWord ++ tailWord_1120163).sum := by decide
  have hdescent : baseEnd_1120163 < baseStart_1120163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120225 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_1120225 : Nat := 118140960795 + 1120225 * 2 ^ 59
def prefixEnd_1120225 : Nat := 4983230072969 + 3 ^ 40 * 1120225 * 2
def baseEnd_1120225 : Nat := 255650607192437710326971

theorem tailTrace_1120225 : CollatzResearch.WordTrace tailWord_1120225 prefixEnd_1120225 255650607192437710326971 := by
  unfold tailWord_1120225
  simp only [CollatzResearch.WordTrace]
  refine ⟨40857962366623619043410129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27238641577749079362273419 40857962366623619043410129)
  ·
    refine ⟨30643471774967714282557597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40857962366623619043410129 30643471774967714282557597)
    ·
      refine ⟨11491301915612892855959099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30643471774967714282557597 11491301915612892855959099)
      ·
        refine ⟨17236952873419339283938649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491301915612892855959099 17236952873419339283938649)
        ·
          refine ⟨12927714655064504462953987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17236952873419339283938649 12927714655064504462953987)
          ·
            refine ⟨19391571982596756694430981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927714655064504462953987 19391571982596756694430981)
            ·
              refine ⟨3635919746736891880205809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19391571982596756694430981 3635919746736891880205809)
              ·
                refine ⟨2726939810052668910154357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635919746736891880205809 2726939810052668910154357)
                ·
                  refine ⟨255650607192437710326971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2726939810052668910154357 255650607192437710326971)
                  ·
                    rfl

theorem cell21_1120225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_1120225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120225 prefixEnd_1120225 := by exact prefixLift 1120225
  have htrace : WordTrace (prefixWord ++ tailWord_1120225) baseStart_1120225 baseEnd_1120225 := by
    simpa [prefixWord, tailWord_1120225, baseEnd_1120225] using wordTrace_append hprefix tailTrace_1120225
  have hstable : (prefixWord ++ tailWord_1120225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120225).length < 2 ^ (prefixWord ++ tailWord_1120225).sum := by decide
  have hdescent : baseEnd_1120225 < baseStart_1120225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120239 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_1120239 : Nat := 118140960795 + 1120239 * 2 ^ 59
def prefixEnd_1120239 : Nat := 4983230072969 + 3 ^ 40 * 1120239 * 2
def baseEnd_1120239 : Nat := 255653802183176797093609

theorem tailTrace_1120239 : CollatzResearch.WordTrace tailWord_1120239 prefixEnd_1120239 255653802183176797093609 := by
  unfold tailWord_1120239
  simp only [CollatzResearch.WordTrace]
  refine ⟨40858472988572899434419771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27238981992381932956279847 40858472988572899434419771)
  ·
    refine ⟨61287709482859349151629657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40858472988572899434419771 61287709482859349151629657)
    ·
      refine ⟨45965782112144511863722243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61287709482859349151629657 45965782112144511863722243)
      ·
        refine ⟨68948673168216767795583365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45965782112144511863722243 68948673168216767795583365)
        ·
          refine ⟨12927876219040643961671881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68948673168216767795583365 12927876219040643961671881)
          ·
            refine ⟨9695907164280482971253911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12927876219040643961671881 9695907164280482971253911)
            ·
              refine ⟨14543860746420724456880867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9695907164280482971253911 14543860746420724456880867)
              ·
                refine ⟨21815791119631086685321301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543860746420724456880867 21815791119631086685321301)
                ·
                  refine ⟨255653802183176797093609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21815791119631086685321301 255653802183176797093609)
                  ·
                    rfl

theorem cell21_1120239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_1120239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120239 prefixEnd_1120239 := by exact prefixLift 1120239
  have htrace : WordTrace (prefixWord ++ tailWord_1120239) baseStart_1120239 baseEnd_1120239 := by
    simpa [prefixWord, tailWord_1120239, baseEnd_1120239] using wordTrace_append hprefix tailTrace_1120239
  have hstable : (prefixWord ++ tailWord_1120239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120239).length < 2 ^ (prefixWord ++ tailWord_1120239).sum := by decide
  have hdescent : baseEnd_1120239 < baseStart_1120239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120332 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1120332 : Nat := 118140960795 + 1120332 * 2 ^ 59
def prefixEnd_1120332 : Nat := 4983230072969 + 3 ^ 40 * 1120332 * 2
def baseEnd_1120332 : Nat := 255675026050229302043419

theorem tailTrace_1120332 : CollatzResearch.WordTrace tailWord_1120332 prefixEnd_1120332 255675026050229302043419 := by
  unfold tailWord_1120332
  simp only [CollatzResearch.WordTrace]
  refine ⟨20430932488617988158777625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27241243318157317545036833 20430932488617988158777625)
  ·
    refine ⟨15323199366463491119083219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20430932488617988158777625 15323199366463491119083219)
    ·
      refine ⟨22984799049695236678624829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15323199366463491119083219 22984799049695236678624829)
      ·
        refine ⟨8619299643635713754484311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22984799049695236678624829 8619299643635713754484311)
        ·
          refine ⟨12928949465453570631726467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619299643635713754484311 12928949465453570631726467)
          ·
            refine ⟨19393424198180355947589701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12928949465453570631726467 19393424198180355947589701)
            ·
              refine ⟨3636267037158816740173069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19393424198180355947589701 3636267037158816740173069)
              ·
                refine ⟨1363600138934556277564901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3636267037158816740173069 1363600138934556277564901)
                ·
                  refine ⟨255675026050229302043419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363600138934556277564901 255675026050229302043419)
                  ·
                    rfl

theorem cell21_1120332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1120332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120332 prefixEnd_1120332 := by exact prefixLift 1120332
  have htrace : WordTrace (prefixWord ++ tailWord_1120332) baseStart_1120332 baseEnd_1120332 := by
    simpa [prefixWord, tailWord_1120332, baseEnd_1120332] using wordTrace_append hprefix tailTrace_1120332
  have hstable : (prefixWord ++ tailWord_1120332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120332).length < 2 ^ (prefixWord ++ tailWord_1120332).sum := by decide
  have hdescent : baseEnd_1120332 < baseStart_1120332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120377 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1120377 : Nat := 118140960795 + 1120377 * 2 ^ 59
def prefixEnd_1120377 : Nat := 4983230072969 + 3 ^ 40 * 1120377 * 2
def baseEnd_1120377 : Nat := 255685295663319223793327

theorem tailTrace_1120377 : CollatzResearch.WordTrace tailWord_1120377 prefixEnd_1120377 255685295663319223793327 := by
  unfold tailWord_1120377
  simp only [CollatzResearch.WordTrace]
  refine ⟨40863506262072949002943385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27242337508048632668628923 40863506262072949002943385)
  ·
    refine ⟨30647629696554711752207539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40863506262072949002943385 30647629696554711752207539)
    ·
      refine ⟨45971444544832067628311309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30647629696554711752207539 45971444544832067628311309)
      ·
        refine ⟨17239291704312025360616741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45971444544832067628311309 17239291704312025360616741)
        ·
          refine ⟨3232367194558504755115639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17239291704312025360616741 3232367194558504755115639)
          ·
            refine ⟨4848550791837757132673459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232367194558504755115639 4848550791837757132673459)
            ·
              refine ⟨7272826187756635699010189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848550791837757132673459 7272826187756635699010189)
              ·
                refine ⟨2727309820408738387128821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272826187756635699010189 2727309820408738387128821)
                ·
                  refine ⟨255685295663319223793327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727309820408738387128821 255685295663319223793327)
                  ·
                    rfl

theorem cell21_1120377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1120377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120377 prefixEnd_1120377 := by exact prefixLift 1120377
  have htrace : WordTrace (prefixWord ++ tailWord_1120377) baseStart_1120377 baseEnd_1120377 := by
    simpa [prefixWord, tailWord_1120377, baseEnd_1120377] using wordTrace_append hprefix tailTrace_1120377
  have hstable : (prefixWord ++ tailWord_1120377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120377).length < 2 ^ (prefixWord ++ tailWord_1120377).sum := by decide
  have hdescent : baseEnd_1120377 < baseStart_1120377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120487 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 3]
def baseStart_1120487 : Nat := 118140960795 + 1120487 * 2 ^ 59
def prefixEnd_1120487 : Nat := 4983230072969 + 3 ^ 40 * 1120487 * 2
def baseEnd_1120487 : Nat := 255710399161983476959769

theorem tailTrace_1120487 : CollatzResearch.WordTrace tailWord_1120487 prefixEnd_1120487 255710399161983476959769 := by
  unfold tailWord_1120487
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867518291674437789447715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27245012194449625192965143 40867518291674437789447715)
  ·
    refine ⟨61301277437511656684171573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40867518291674437789447715 61301277437511656684171573)
    ·
      refine ⟨5746994759766717814141085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61301277437511656684171573 5746994759766717814141085)
      ·
        refine ⟨2155123034912519180302907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5746994759766717814141085 2155123034912519180302907)
        ·
          refine ⟨3232684552368778770454361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155123034912519180302907 3232684552368778770454361)
          ·
            refine ⟨2424513414276584077840771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232684552368778770454361 2424513414276584077840771)
            ·
              refine ⟨3636770121414876116761157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424513414276584077840771 3636770121414876116761157)
              ·
                refine ⟨681894397765289271892717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3636770121414876116761157 681894397765289271892717)
                ·
                  refine ⟨255710399161983476959769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681894397765289271892717 255710399161983476959769)
                  ·
                    rfl

theorem cell21_1120487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].length) (baseStart_1120487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120487 prefixEnd_1120487 := by exact prefixLift 1120487
  have htrace : WordTrace (prefixWord ++ tailWord_1120487) baseStart_1120487 baseEnd_1120487 := by
    simpa [prefixWord, tailWord_1120487, baseEnd_1120487] using wordTrace_append hprefix tailTrace_1120487
  have hstable : (prefixWord ++ tailWord_1120487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120487).length < 2 ^ (prefixWord ++ tailWord_1120487).sum := by decide
  have hdescent : baseEnd_1120487 < baseStart_1120487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120512 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1120512 : Nat := 118140960795 + 1120512 * 2 ^ 59
def prefixEnd_1120512 : Nat := 4983230072969 + 3 ^ 40 * 1120512 * 2
def baseEnd_1120512 : Nat := 255716104502588989043051

theorem tailTrace_1120512 : CollatzResearch.WordTrace tailWord_1120512 prefixEnd_1120512 255716104502588989043051 := by
  unfold tailWord_1120512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20434215058291933529553895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27245620077722578039405193 20434215058291933529553895)
  ·
    refine ⟨30651322587437900294330843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20434215058291933529553895 30651322587437900294330843)
    ·
      refine ⟨45976983881156850441496265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30651322587437900294330843 45976983881156850441496265)
      ·
        refine ⟨34482737910867637831122199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45976983881156850441496265 34482737910867637831122199)
        ·
          refine ⟨51724106866301456746683299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34482737910867637831122199 51724106866301456746683299)
          ·
            refine ⟨77586160299452185120024949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51724106866301456746683299 77586160299452185120024949)
            ·
              refine ⟨7273702528073642355002339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77586160299452185120024949 7273702528073642355002339)
              ·
                refine ⟨10910553792110463532503509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273702528073642355002339 10910553792110463532503509)
                ·
                  refine ⟨255716104502588989043051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10910553792110463532503509 255716104502588989043051)
                  ·
                    rfl

theorem cell21_1120512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1120512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120512 prefixEnd_1120512 := by exact prefixLift 1120512
  have htrace : WordTrace (prefixWord ++ tailWord_1120512) baseStart_1120512 baseEnd_1120512 := by
    simpa [prefixWord, tailWord_1120512, baseEnd_1120512] using wordTrace_append hprefix tailTrace_1120512
  have hstable : (prefixWord ++ tailWord_1120512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120512).length < 2 ^ (prefixWord ++ tailWord_1120512).sum := by decide
  have hdescent : baseEnd_1120512 < baseStart_1120512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120546 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1120546 : Nat := 118140960795 + 1120546 * 2 ^ 59
def prefixEnd_1120546 : Nat := 4983230072969 + 3 ^ 40 * 1120546 * 2
def baseEnd_1120546 : Nat := 255723863765812485476315

theorem tailTrace_1120546 : CollatzResearch.WordTrace tailWord_1120546 prefixEnd_1120546 255723863765812485476315 := by
  unfold tailWord_1120546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217417549615172716461373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27246446798973793910563661 10217417549615172716461373)
  ·
    refine ⟨3831531581105689768673015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10217417549615172716461373 3831531581105689768673015)
    ·
      refine ⟨5747297371658534653009523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831531581105689768673015 5747297371658534653009523)
      ·
        refine ⟨8620946057487801979514285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747297371658534653009523 8620946057487801979514285)
        ·
          refine ⟨3232854771557925742317857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8620946057487801979514285 3232854771557925742317857)
          ·
            refine ⟨2424641078668444306738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3232854771557925742317857 2424641078668444306738393)
            ·
              refine ⟨1818480809001333230053795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424641078668444306738393 1818480809001333230053795)
              ·
                refine ⟨2727721213501999845080693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818480809001333230053795 2727721213501999845080693)
                ·
                  refine ⟨255723863765812485476315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727721213501999845080693 255723863765812485476315)
                  ·
                    rfl

theorem cell21_1120546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1120546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120546 prefixEnd_1120546 := by exact prefixLift 1120546
  have htrace : WordTrace (prefixWord ++ tailWord_1120546) baseStart_1120546 baseEnd_1120546 := by
    simpa [prefixWord, tailWord_1120546, baseEnd_1120546] using wordTrace_append hprefix tailTrace_1120546
  have hstable : (prefixWord ++ tailWord_1120546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120546).length < 2 ^ (prefixWord ++ tailWord_1120546).sum := by decide
  have hdescent : baseEnd_1120546 < baseStart_1120546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120619 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_1120619 : Nat := 118140960795 + 1120619 * 2 ^ 59
def prefixEnd_1120619 : Nat := 4983230072969 + 3 ^ 40 * 1120619 * 2
def baseEnd_1120619 : Nat := 255740523360380580759499

theorem tailTrace_1120619 : CollatzResearch.WordTrace tailWord_1120619 prefixEnd_1120619 255740523360380580759499 := by
  unfold tailWord_1120619
  simp only [CollatzResearch.WordTrace]
  refine ⟨40872332727196224333252911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27248221818130816222168607 40872332727196224333252911)
  ·
    refine ⟨61308499090794336499879367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40872332727196224333252911 61308499090794336499879367)
    ·
      refine ⟨91962748636191504749819051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61308499090794336499879367 91962748636191504749819051)
      ·
        refine ⟨137944122954287257124728577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91962748636191504749819051 137944122954287257124728577)
        ·
          refine ⟨103458092215715442843546433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137944122954287257124728577 103458092215715442843546433)
          ·
            refine ⟨77593569161786582132659825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103458092215715442843546433 77593569161786582132659825)
            ·
              refine ⟨58195176871339936599494869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77593569161786582132659825 58195176871339936599494869)
              ·
                refine ⟨1363949457922029764050661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58195176871339936599494869 1363949457922029764050661)
                ·
                  refine ⟨255740523360380580759499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363949457922029764050661 255740523360380580759499)
                  ·
                    rfl

theorem cell21_1120619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_1120619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120619 prefixEnd_1120619 := by exact prefixLift 1120619
  have htrace : WordTrace (prefixWord ++ tailWord_1120619) baseStart_1120619 baseEnd_1120619 := by
    simpa [prefixWord, tailWord_1120619, baseEnd_1120619] using wordTrace_append hprefix tailTrace_1120619
  have hstable : (prefixWord ++ tailWord_1120619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120619).length < 2 ^ (prefixWord ++ tailWord_1120619).sum := by decide
  have hdescent : baseEnd_1120619 < baseStart_1120619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120650 : List Nat := [3, 1, 2, 5, 10]
def baseStart_1120650 : Nat := 118140960795 + 1120650 * 2 ^ 59
def prefixEnd_1120650 : Nat := 4983230072969 + 3 ^ 40 * 1120650 * 2
def baseEnd_1120650 : Nat := 3157377752873227354849

theorem tailTrace_1120650 : CollatzResearch.WordTrace tailWord_1120650 prefixEnd_1120650 3157377752873227354849 := by
  unfold tailWord_1120650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218365847520979156907851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27248975593389277751754269 10218365847520979156907851)
  ·
    refine ⟨15327548771281468735361777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10218365847520979156907851 15327548771281468735361777)
    ·
      refine ⟨11495661578461101551521333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15327548771281468735361777 11495661578461101551521333)
      ·
        refine ⟨1077718272980728270455125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11495661578461101551521333 1077718272980728270455125)
        ·
          refine ⟨3157377752873227354849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1077718272980728270455125 3157377752873227354849)
          ·
            rfl

theorem cell21_1120650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 10].length) (baseStart_1120650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120650 prefixEnd_1120650 := by exact prefixLift 1120650
  have htrace : WordTrace (prefixWord ++ tailWord_1120650) baseStart_1120650 baseEnd_1120650 := by
    simpa [prefixWord, tailWord_1120650, baseEnd_1120650] using wordTrace_append hprefix tailTrace_1120650
  have hstable : (prefixWord ++ tailWord_1120650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120650).length < 2 ^ (prefixWord ++ tailWord_1120650).sum := by decide
  have hdescent : baseEnd_1120650 < baseStart_1120650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120712 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_1120712 : Nat := 118140960795 + 1120712 * 2 ^ 59
def prefixEnd_1120712 : Nat := 4983230072969 + 3 ^ 40 * 1120712 * 2
def baseEnd_1120712 : Nat := 255761747227433085709309

theorem tailTrace_1120712 : CollatzResearch.WordTrace tailWord_1120712 prefixEnd_1120712 255761747227433085709309 := by
  unfold tailWord_1120712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20437862357929650608194195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27250483143906200810925593 20437862357929650608194195)
  ·
    refine ⟨30656793536894475912291293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20437862357929650608194195 30656793536894475912291293)
    ·
      refine ⟨11496297576335428467109235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30656793536894475912291293 11496297576335428467109235)
      ·
        refine ⟨17244446364503142700663853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11496297576335428467109235 17244446364503142700663853)
        ·
          refine ⟨6466667386688678512748945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17244446364503142700663853 6466667386688678512748945)
          ·
            refine ⟨4850000540016508884561709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6466667386688678512748945 4850000540016508884561709)
            ·
              refine ⟨1818750202506190831710641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4850000540016508884561709 1818750202506190831710641)
              ·
                refine ⟨1364062651879643123782981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818750202506190831710641 1364062651879643123782981)
                ·
                  refine ⟨255761747227433085709309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364062651879643123782981 255761747227433085709309)
                  ·
                    rfl

theorem cell21_1120712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_1120712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120712 prefixEnd_1120712 := by exact prefixLift 1120712
  have htrace : WordTrace (prefixWord ++ tailWord_1120712) baseStart_1120712 baseEnd_1120712 := by
    simpa [prefixWord, tailWord_1120712, baseEnd_1120712] using wordTrace_append hprefix tailTrace_1120712
  have hstable : (prefixWord ++ tailWord_1120712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120712).length < 2 ^ (prefixWord ++ tailWord_1120712).sum := by decide
  have hdescent : baseEnd_1120712 < baseStart_1120712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120771 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_1120771 : Nat := 118140960795 + 1120771 * 2 ^ 59
def prefixEnd_1120771 : Nat := 4983230072969 + 3 ^ 40 * 1120771 * 2
def baseEnd_1120771 : Nat := 255775211831262094225855

theorem tailTrace_1120771 : CollatzResearch.WordTrace tailWord_1120771 prefixEnd_1120771 255775211831262094225855 := by
  unfold tailWord_1120771
  simp only [CollatzResearch.WordTrace]
  refine ⟨40877876622645554292786167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27251917748430369528524111 40877876622645554292786167)
  ·
    refine ⟨61316814933968331439179251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40877876622645554292786167 61316814933968331439179251)
    ·
      refine ⟨91975222400952497158768877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61316814933968331439179251 91975222400952497158768877)
      ·
        refine ⟨34490708400357186434538329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91975222400952497158768877 34490708400357186434538329)
        ·
          refine ⟨25868031300267889825903747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34490708400357186434538329 25868031300267889825903747)
          ·
            refine ⟨38802046950401834738855621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25868031300267889825903747 38802046950401834738855621)
            ·
              refine ⟨7275383803200344013535429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38802046950401834738855621 7275383803200344013535429)
              ·
                refine ⟨1364134463100064502537893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7275383803200344013535429 1364134463100064502537893)
                ·
                  refine ⟨255775211831262094225855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364134463100064502537893 255775211831262094225855)
                  ·
                    rfl

theorem cell21_1120771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_1120771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120771 prefixEnd_1120771 := by exact prefixLift 1120771
  have htrace : WordTrace (prefixWord ++ tailWord_1120771) baseStart_1120771 baseEnd_1120771 := by
    simpa [prefixWord, tailWord_1120771, baseEnd_1120771] using wordTrace_append hprefix tailTrace_1120771
  have hstable : (prefixWord ++ tailWord_1120771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120771).length < 2 ^ (prefixWord ++ tailWord_1120771).sum := by decide
  have hdescent : baseEnd_1120771 < baseStart_1120771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120847 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_1120847 : Nat := 118140960795 + 1120847 * 2 ^ 59
def prefixEnd_1120847 : Nat := 4983230072969 + 3 ^ 40 * 1120847 * 2
def baseEnd_1120847 : Nat := 255792556066702850959033

theorem tailTrace_1120847 : CollatzResearch.WordTrace tailWord_1120847 prefixEnd_1120847 255792556066702850959033 := by
  unfold tailWord_1120847
  simp only [CollatzResearch.WordTrace]
  refine ⟨40880648570370219272552795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27253765713580146181701863 40880648570370219272552795)
  ·
    refine ⟨61320972855555328908829193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40880648570370219272552795 61320972855555328908829193)
    ·
      refine ⟨45990729641666496681621895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61320972855555328908829193 45990729641666496681621895)
      ·
        refine ⟨68986094462499745022432843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45990729641666496681621895 68986094462499745022432843)
        ·
          refine ⟨103479141693749617533649265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68986094462499745022432843 103479141693749617533649265)
          ·
            refine ⟨77609356270312213150236949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103479141693749617533649265 77609356270312213150236949)
            ·
              refine ⟨3637938575170884991417357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77609356270312213150236949 3637938575170884991417357)
              ·
                refine ⟨1364226965689081871781509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3637938575170884991417357 1364226965689081871781509)
                ·
                  refine ⟨255792556066702850959033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364226965689081871781509 255792556066702850959033)
                  ·
                    rfl

theorem cell21_1120847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_1120847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120847 prefixEnd_1120847 := by exact prefixLift 1120847
  have htrace : WordTrace (prefixWord ++ tailWord_1120847) baseStart_1120847 baseEnd_1120847 := by
    simpa [prefixWord, tailWord_1120847, baseEnd_1120847] using wordTrace_append hprefix tailTrace_1120847
  have hstable : (prefixWord ++ tailWord_1120847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120847).length < 2 ^ (prefixWord ++ tailWord_1120847).sum := by decide
  have hdescent : baseEnd_1120847 < baseStart_1120847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120878 : List Nat := [4, 1, 2, 2, 2, 2, 8]
def baseStart_1120878 : Nat := 118140960795 + 1120878 * 2 ^ 59
def prefixEnd_1120878 : Nat := 4983230072969 + 3 ^ 40 * 1120878 * 2
def baseEnd_1120878 : Nat := 28422181187672631771367

theorem tailTrace_1120878 : CollatzResearch.WordTrace tailWord_1120878 prefixEnd_1120878 28422181187672631771367 := by
  unfold tailWord_1120878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110222404157238945866411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27254519488838607711287525 5110222404157238945866411)
  ·
    refine ⟨7665333606235858418799617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110222404157238945866411 7665333606235858418799617)
    ·
      refine ⟨5749000204676893814099713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7665333606235858418799617 5749000204676893814099713)
      ·
        refine ⟨4311750153507670360574785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5749000204676893814099713 4311750153507670360574785)
        ·
          refine ⟨3233812615130752770431089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4311750153507670360574785 3233812615130752770431089)
          ·
            refine ⟨2425359461348064577823317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3233812615130752770431089 2425359461348064577823317)
            ·
              refine ⟨28422181187672631771367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2425359461348064577823317 28422181187672631771367)
              ·
                rfl

theorem cell21_1120878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 8].length) (baseStart_1120878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120878 prefixEnd_1120878 := by exact prefixLift 1120878
  have htrace : WordTrace (prefixWord ++ tailWord_1120878) baseStart_1120878 baseEnd_1120878 := by
    simpa [prefixWord, tailWord_1120878, baseEnd_1120878] using wordTrace_append hprefix tailTrace_1120878
  have hstable : (prefixWord ++ tailWord_1120878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120878).length < 2 ^ (prefixWord ++ tailWord_1120878).sum := by decide
  have hdescent : baseEnd_1120878 < baseStart_1120878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120892 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1120892 : Nat := 118140960795 + 1120892 * 2 ^ 59
def prefixEnd_1120892 : Nat := 4983230072969 + 3 ^ 40 * 1120892 * 2
def baseEnd_1120892 : Nat := 255802825679792772708941

theorem tailTrace_1120892 : CollatzResearch.WordTrace tailWord_1120892 prefixEnd_1120892 255802825679792772708941 := by
  unfold tailWord_1120892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441144927603595978970465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27254859903471461305293953 20441144927603595978970465)
  ·
    refine ⟨15330858695702696984227849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20441144927603595978970465 15330858695702696984227849)
    ·
      refine ⟨11498144021777022738170887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15330858695702696984227849 11498144021777022738170887)
      ·
        refine ⟨17247216032665534107256331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11498144021777022738170887 17247216032665534107256331)
        ·
          refine ⟨25870824048998301160884497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17247216032665534107256331 25870824048998301160884497)
          ·
            refine ⟨19403118036748725870663373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25870824048998301160884497 19403118036748725870663373)
            ·
              refine ⟨7276169263780772201498765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19403118036748725870663373 7276169263780772201498765)
              ·
                refine ⟨2728563473917789575562037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7276169263780772201498765 2728563473917789575562037)
                ·
                  refine ⟨255802825679792772708941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2728563473917789575562037 255802825679792772708941)
                  ·
                    rfl

theorem cell21_1120892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1120892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120892 prefixEnd_1120892 := by exact prefixLift 1120892
  have htrace : WordTrace (prefixWord ++ tailWord_1120892) baseStart_1120892 baseEnd_1120892 := by
    simpa [prefixWord, tailWord_1120892, baseEnd_1120892] using wordTrace_append hprefix tailTrace_1120892
  have hstable : (prefixWord ++ tailWord_1120892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120892).length < 2 ^ (prefixWord ++ tailWord_1120892).sum := by decide
  have hdescent : baseEnd_1120892 < baseStart_1120892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120957 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1120957 : Nat := 118140960795 + 1120957 * 2 ^ 59
def prefixEnd_1120957 : Nat := 4983230072969 + 3 ^ 40 * 1120957 * 2
def baseEnd_1120957 : Nat := 255817659565367104125475

theorem tailTrace_1120957 : CollatzResearch.WordTrace tailWord_1120957 prefixEnd_1120957 255817659565367104125475 := by
  unfold tailWord_1120957
  simp only [CollatzResearch.WordTrace]
  refine ⟨40884660599971708059057125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256440399981138706038083 40884660599971708059057125)
  ·
    refine ⟨7665873862494695261073211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40884660599971708059057125 7665873862494695261073211)
    ·
      refine ⟨11498810793742042891609817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665873862494695261073211 11498810793742042891609817)
      ·
        refine ⟨8624108095306532168707363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11498810793742042891609817 8624108095306532168707363)
        ·
          refine ⟨12936162142959798253061045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624108095306532168707363 12936162142959798253061045)
          ·
            refine ⟨1212765200902481086224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12936162142959798253061045 1212765200902481086224473)
            ·
              refine ⟨909573900676860814668355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212765200902481086224473 909573900676860814668355)
              ·
                refine ⟨1364360851015291222002533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909573900676860814668355 1364360851015291222002533)
                ·
                  refine ⟨255817659565367104125475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364360851015291222002533 255817659565367104125475)
                  ·
                    rfl

theorem cell21_1120957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1120957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120957 prefixEnd_1120957 := by exact prefixLift 1120957
  have htrace : WordTrace (prefixWord ++ tailWord_1120957) baseStart_1120957 baseEnd_1120957 := by
    simpa [prefixWord, tailWord_1120957, baseEnd_1120957] using wordTrace_append hprefix tailTrace_1120957
  have hstable : (prefixWord ++ tailWord_1120957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120957).length < 2 ^ (prefixWord ++ tailWord_1120957).sum := by decide
  have hdescent : baseEnd_1120957 < baseStart_1120957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120985 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 3]
def baseStart_1120985 : Nat := 118140960795 + 1120985 * 2 ^ 59
def prefixEnd_1120985 : Nat := 4983230072969 + 3 ^ 40 * 1120985 * 2
def baseEnd_1120985 : Nat := 255824049546845277658751

theorem tailTrace_1120985 : CollatzResearch.WordTrace tailWord_1120985 prefixEnd_1120985 255824049546845277658751 := by
  unfold tailWord_1120985
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885681843870268841076409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27257121229246845894050939 40885681843870268841076409)
  ·
    refine ⟨30664261382902701630807307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40885681843870268841076409 30664261382902701630807307)
    ·
      refine ⟨45996392074354052446210961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30664261382902701630807307 45996392074354052446210961)
      ·
        refine ⟨34497294055765539334658221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45996392074354052446210961 34497294055765539334658221)
        ·
          refine ⟨12936485270912077250496833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34497294055765539334658221 12936485270912077250496833)
          ·
            refine ⟨9702363953184057937872625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936485270912077250496833 9702363953184057937872625)
            ·
              refine ⟨7276772964888043453404469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9702363953184057937872625 7276772964888043453404469)
              ·
                refine ⟨682197465458254073756669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7276772964888043453404469 682197465458254073756669)
                ·
                  refine ⟨255824049546845277658751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682197465458254073756669 255824049546845277658751)
                  ·
                    rfl

theorem cell21_1120985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_1120985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1120985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1120985 prefixEnd_1120985 := by exact prefixLift 1120985
  have htrace : WordTrace (prefixWord ++ tailWord_1120985) baseStart_1120985 baseEnd_1120985 := by
    simpa [prefixWord, tailWord_1120985, baseEnd_1120985] using wordTrace_append hprefix tailTrace_1120985
  have hstable : (prefixWord ++ tailWord_1120985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120985).length < 2 ^ (prefixWord ++ tailWord_1120985).sum := by decide
  have hdescent : baseEnd_1120985 < baseStart_1120985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121061 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1121061 : Nat := 118140960795 + 1121061 * 2 ^ 59
def prefixEnd_1121061 : Nat := 4983230072969 + 3 ^ 40 * 1121061 * 2
def baseEnd_1121061 : Nat := 255841393782286034391929

theorem tailTrace_1121061 : CollatzResearch.WordTrace tailWord_1121061 prefixEnd_1121061 255841393782286034391929 := by
  unfold tailWord_1121061
  simp only [CollatzResearch.WordTrace]
  refine ⟨40888453791594933820843037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27258969194396622547228691 40888453791594933820843037)
  ·
    refine ⟨15333170171848100182816139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40888453791594933820843037 15333170171848100182816139)
    ·
      refine ⟨22999755257772150274224209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15333170171848100182816139 22999755257772150274224209)
      ·
        refine ⟨17249816443329112705668157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22999755257772150274224209 17249816443329112705668157)
        ·
          refine ⟨6468681166248417264625559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17249816443329112705668157 6468681166248417264625559)
          ·
            refine ⟨9703021749372625896938339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468681166248417264625559 9703021749372625896938339)
            ·
              refine ⟨14554532624058938845407509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703021749372625896938339 14554532624058938845407509)
              ·
                refine ⟨682243716752762758378477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14554532624058938845407509 682243716752762758378477)
                ·
                  refine ⟨255841393782286034391929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682243716752762758378477 255841393782286034391929)
                  ·
                    rfl

theorem cell21_1121061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1121061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121061 prefixEnd_1121061 := by exact prefixLift 1121061
  have htrace : WordTrace (prefixWord ++ tailWord_1121061) baseStart_1121061 baseEnd_1121061 := by
    simpa [prefixWord, tailWord_1121061, baseEnd_1121061] using wordTrace_append hprefix tailTrace_1121061
  have hstable : (prefixWord ++ tailWord_1121061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121061).length < 2 ^ (prefixWord ++ tailWord_1121061).sum := by decide
  have hdescent : baseEnd_1121061 < baseStart_1121061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121210 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1121210 : Nat := 118140960795 + 1121210 * 2 ^ 59
def prefixEnd_1121210 : Nat := 4983230072969 + 3 ^ 40 * 1121210 * 2
def baseEnd_1121210 : Nat := 255875397612294886408291

theorem tailTrace_1121210 : CollatzResearch.WordTrace tailWord_1121210 prefixEnd_1121210 255875397612294886408291 := by
  unfold tailWord_1121210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223472067013783067004271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27262592178703421512011389 10223472067013783067004271)
  ·
    refine ⟨15335208100520674600506407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10223472067013783067004271 15335208100520674600506407)
    ·
      refine ⟨23002812150781011900759611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15335208100520674600506407 23002812150781011900759611)
      ·
        refine ⟨34504218226171517851139417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23002812150781011900759611 34504218226171517851139417)
        ·
          refine ⟨25878163669628638388354563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34504218226171517851139417 25878163669628638388354563)
          ·
            refine ⟨38817245504442957582531845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25878163669628638388354563 38817245504442957582531845)
            ·
              refine ⟨7278233532083054546724721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38817245504442957582531845 7278233532083054546724721)
              ·
                refine ⟨5458675149062290910043541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7278233532083054546724721 5458675149062290910043541)
                ·
                  refine ⟨255875397612294886408291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5458675149062290910043541 255875397612294886408291)
                  ·
                    rfl

theorem cell21_1121210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1121210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121210 prefixEnd_1121210 := by exact prefixLift 1121210
  have htrace : WordTrace (prefixWord ++ tailWord_1121210) baseStart_1121210 baseEnd_1121210 := by
    simpa [prefixWord, tailWord_1121210, baseEnd_1121210] using wordTrace_append hprefix tailTrace_1121210
  have hstable : (prefixWord ++ tailWord_1121210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121210).length < 2 ^ (prefixWord ++ tailWord_1121210).sum := by decide
  have hdescent : baseEnd_1121210 < baseStart_1121210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121227 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_1121227 : Nat := 118140960795 + 1121227 * 2 ^ 59
def prefixEnd_1121227 : Nat := 4983230072969 + 3 ^ 40 * 1121227 * 2
def baseEnd_1121227 : Nat := 255879277243906634624923

theorem tailTrace_1121227 : CollatzResearch.WordTrace tailWord_1121227 prefixEnd_1121227 255879277243906634624923 := by
  unfold tailWord_1121227
  simp only [CollatzResearch.WordTrace]
  refine ⟨40894508308993544171385935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27263005539329029447590623 40894508308993544171385935)
  ·
    refine ⟨61341762463490316257078903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40894508308993544171385935 61341762463490316257078903)
    ·
      refine ⟨92012643695235474385618355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61341762463490316257078903 92012643695235474385618355)
      ·
        refine ⟨138018965542853211578427533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92012643695235474385618355 138018965542853211578427533)
        ·
          refine ⟨51757112078569954341910325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138018965542853211578427533 51757112078569954341910325)
          ·
            refine ⟨4852229257365933219554093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51757112078569954341910325 4852229257365933219554093)
            ·
              refine ⟨1819585971512224957332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852229257365933219554093 1819585971512224957332785)
              ·
                refine ⟨1364689478634168717999589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819585971512224957332785 1364689478634168717999589)
                ·
                  refine ⟨255879277243906634624923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364689478634168717999589 255879277243906634624923)
                  ·
                    rfl

theorem cell21_1121227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_1121227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121227 prefixEnd_1121227 := by exact prefixLift 1121227
  have htrace : WordTrace (prefixWord ++ tailWord_1121227) baseStart_1121227 baseEnd_1121227 := by
    simpa [prefixWord, tailWord_1121227, baseEnd_1121227] using wordTrace_append hprefix tailTrace_1121227
  have hstable : (prefixWord ++ tailWord_1121227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121227).length < 2 ^ (prefixWord ++ tailWord_1121227).sum := by decide
  have hdescent : baseEnd_1121227 < baseStart_1121227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121258 : List Nat := [3, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1121258 : Nat := 118140960795 + 1121258 * 2 ^ 59
def prefixEnd_1121258 : Nat := 4983230072969 + 3 ^ 40 * 1121258 * 2
def baseEnd_1121258 : Nat := 85295450622085823202731

theorem tailTrace_1121258 : CollatzResearch.WordTrace tailWord_1121258 prefixEnd_1121258 85295450622085823202731 := by
  unfold tailWord_1121258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223909742970309116441107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27263759314587490977176285 10223909742970309116441107)
  ·
    refine ⟨15335864614455463674661661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10223909742970309116441107 15335864614455463674661661)
    ·
      refine ⟨5750949230420798877998123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15335864614455463674661661 5750949230420798877998123)
      ·
        refine ⟨8626423845631198316997185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750949230420798877998123 8626423845631198316997185)
        ·
          refine ⟨6469817884223398737747889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8626423845631198316997185 6469817884223398737747889)
          ·
            refine ⟨4852363413167549053310917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469817884223398737747889 4852363413167549053310917)
            ·
              refine ⟨909818139968915447495797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4852363413167549053310917 909818139968915447495797)
              ·
                refine ⟨85295450622085823202731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 909818139968915447495797 85295450622085823202731)
                ·
                  rfl

theorem cell21_1121258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1121258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121258 prefixEnd_1121258 := by exact prefixLift 1121258
  have htrace : WordTrace (prefixWord ++ tailWord_1121258) baseStart_1121258 baseEnd_1121258 := by
    simpa [prefixWord, tailWord_1121258, baseEnd_1121258] using wordTrace_append hprefix tailTrace_1121258
  have hstable : (prefixWord ++ tailWord_1121258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121258).length < 2 ^ (prefixWord ++ tailWord_1121258).sum := by decide
  have hdescent : baseEnd_1121258 < baseStart_1121258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121458 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_1121458 : Nat := 118140960795 + 1121458 * 2 ^ 59
def prefixEnd_1121458 : Nat := 4983230072969 + 3 ^ 40 * 1121458 * 2
def baseEnd_1121458 : Nat := 255931994591101566274451

theorem tailTrace_1121458 : CollatzResearch.WordTrace tailWord_1121458 prefixEnd_1121458 255931994591101566274451 := by
  unfold tailWord_1121458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225733392789167655761257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27268622380771113748696685 10225733392789167655761257)
  ·
    refine ⟨7669300044591875741820943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10225733392789167655761257 7669300044591875741820943)
    ·
      refine ⟨11503950066887813612731415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7669300044591875741820943 11503950066887813612731415)
      ·
        refine ⟨17255925100331720419097123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503950066887813612731415 17255925100331720419097123)
        ·
          refine ⟨25883887650497580628645685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17255925100331720419097123 25883887650497580628645685)
          ·
            refine ⟨2426614467234148183935533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25883887650497580628645685 2426614467234148183935533)
            ·
              refine ⟨909980425212805568975825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2426614467234148183935533 909980425212805568975825)
              ·
                refine ⟨682485318909604176731869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909980425212805568975825 682485318909604176731869)
                ·
                  refine ⟨255931994591101566274451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682485318909604176731869 255931994591101566274451)
                  ·
                    rfl

theorem cell21_1121458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_1121458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121458 prefixEnd_1121458 := by exact prefixLift 1121458
  have htrace : WordTrace (prefixWord ++ tailWord_1121458) baseStart_1121458 baseEnd_1121458 := by
    simpa [prefixWord, tailWord_1121458, baseEnd_1121458] using wordTrace_append hprefix tailTrace_1121458
  have hstable : (prefixWord ++ tailWord_1121458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121458).length < 2 ^ (prefixWord ++ tailWord_1121458).sum := by decide
  have hdescent : baseEnd_1121458 < baseStart_1121458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121545 : List Nat := [1, 2, 1, 1, 3, 3, 5, 5]
def baseStart_1121545 : Nat := 118140960795 + 1121545 * 2 ^ 59
def prefixEnd_1121545 : Nat := 4983230072969 + 3 ^ 40 * 1121545 * 2
def baseEnd_1121545 : Nat := 85317283058802916108091

theorem tailTrace_1121545 : CollatzResearch.WordTrace tailWord_1121545 prefixEnd_1121545 85317283058802916108091 := by
  unfold tailWord_1121545
  simp only [CollatzResearch.WordTrace]
  refine ⟨40906106721841484481462089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27270737814560989654308059 40906106721841484481462089)
  ·
    refine ⟨30679580041381113361096567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40906106721841484481462089 30679580041381113361096567)
    ·
      refine ⟨46019370062071670041644851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30679580041381113361096567 46019370062071670041644851)
      ·
        refine ⟨69029055093107505062467277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46019370062071670041644851 69029055093107505062467277)
        ·
          refine ⟨25885895659915314398425229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69029055093107505062467277 25885895659915314398425229)
          ·
            refine ⟨9707210872468242899409461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25885895659915314398425229 9707210872468242899409461)
            ·
              refine ⟨910051019293897771819637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9707210872468242899409461 910051019293897771819637)
              ·
                refine ⟨85317283058802916108091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910051019293897771819637 85317283058802916108091)
                ·
                  rfl

theorem cell21_1121545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].length) (baseStart_1121545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121545 prefixEnd_1121545 := by exact prefixLift 1121545
  have htrace : WordTrace (prefixWord ++ tailWord_1121545) baseStart_1121545 baseEnd_1121545 := by
    simpa [prefixWord, tailWord_1121545, baseEnd_1121545] using wordTrace_append hprefix tailTrace_1121545
  have hstable : (prefixWord ++ tailWord_1121545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121545).length < 2 ^ (prefixWord ++ tailWord_1121545).sum := by decide
  have hdescent : baseEnd_1121545 < baseStart_1121545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121559 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_1121559 : Nat := 118140960795 + 1121559 * 2 ^ 59
def prefixEnd_1121559 : Nat := 4983230072969 + 3 ^ 40 * 1121559 * 2
def baseEnd_1121559 : Nat := 255955044167147835090911

theorem tailTrace_1121559 : CollatzResearch.WordTrace tailWord_1121559 prefixEnd_1121559 255955044167147835090911 := by
  unfold tailWord_1121559
  simp only [CollatzResearch.WordTrace]
  refine ⟨40906617343790764872471731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27271078229193843248314487 40906617343790764872471731)
  ·
    refine ⟨61359926015686147308707597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40906617343790764872471731 61359926015686147308707597)
    ·
      refine ⟨23009972255882305240765349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61359926015686147308707597 23009972255882305240765349)
      ·
        refine ⟨4314369797977932232643503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23009972255882305240765349 4314369797977932232643503)
        ·
          refine ⟨6471554696966898348965255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314369797977932232643503 6471554696966898348965255)
          ·
            refine ⟨9707332045450347523447883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6471554696966898348965255 9707332045450347523447883)
            ·
              refine ⟨14560998068175521285171825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9707332045450347523447883 14560998068175521285171825)
              ·
                refine ⟨10920748551131640963878869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14560998068175521285171825 10920748551131640963878869)
                ·
                  refine ⟨255955044167147835090911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10920748551131640963878869 255955044167147835090911)
                  ·
                    rfl

theorem cell21_1121559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_1121559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121559 prefixEnd_1121559 := by exact prefixLift 1121559
  have htrace : WordTrace (prefixWord ++ tailWord_1121559) baseStart_1121559 baseEnd_1121559 := by
    simpa [prefixWord, tailWord_1121559, baseEnd_1121559] using wordTrace_append hprefix tailTrace_1121559
  have hstable : (prefixWord ++ tailWord_1121559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121559).length < 2 ^ (prefixWord ++ tailWord_1121559).sum := by decide
  have hdescent : baseEnd_1121559 < baseStart_1121559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121576 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1121576 : Nat := 118140960795 + 1121576 * 2 ^ 59
def prefixEnd_1121576 : Nat := 4983230072969 + 3 ^ 40 * 1121576 * 2
def baseEnd_1121576 : Nat := 255958923798759583307543

theorem tailTrace_1121576 : CollatzResearch.WordTrace tailWord_1121576 prefixEnd_1121576 255958923798759583307543 := by
  unfold tailWord_1121576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20453618692364588387920291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27271491589819451183893721 20453618692364588387920291)
  ·
    refine ⟨30680428038546882581880437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20453618692364588387920291 30680428038546882581880437)
    ·
      refine ⟨2876290128613770242051291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30680428038546882581880437 2876290128613770242051291)
      ·
        refine ⟨4314435192920655363076937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876290128613770242051291 4314435192920655363076937)
        ·
          refine ⟨3235826394690491522307703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4314435192920655363076937 3235826394690491522307703)
          ·
            refine ⟨4853739592035737283461555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235826394690491522307703 4853739592035737283461555)
            ·
              refine ⟨7280609388053605925192333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4853739592035737283461555 7280609388053605925192333)
              ·
                refine ⟨2730228520520102221947125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7280609388053605925192333 2730228520520102221947125)
                ·
                  refine ⟨255958923798759583307543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2730228520520102221947125 255958923798759583307543)
                  ·
                    rfl

theorem cell21_1121576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1121576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121576 prefixEnd_1121576 := by exact prefixLift 1121576
  have htrace : WordTrace (prefixWord ++ tailWord_1121576) baseStart_1121576 baseEnd_1121576 := by
    simpa [prefixWord, tailWord_1121576, baseEnd_1121576] using wordTrace_append hprefix tailTrace_1121576
  have hstable : (prefixWord ++ tailWord_1121576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121576).length < 2 ^ (prefixWord ++ tailWord_1121576).sum := by decide
  have hdescent : baseEnd_1121576 < baseStart_1121576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121621 : List Nat := [1, 3, 2, 2, 3, 3, 7]
def baseStart_1121621 : Nat := 118140960795 + 1121621 * 2 ^ 59
def prefixEnd_1121621 : Nat := 4983230072969 + 3 ^ 40 * 1121621 * 2
def baseEnd_1121621 : Nat := 28441021490205500561939

theorem tailTrace_1121621 : CollatzResearch.WordTrace tailWord_1121621 prefixEnd_1121621 28441021490205500561939 := by
  unfold tailWord_1121621
  simp only [CollatzResearch.WordTrace]
  refine ⟨40908878669566149461228717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27272585779710766307485811 40908878669566149461228717)
  ·
    refine ⟨15340829501087306047960769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40908878669566149461228717 15340829501087306047960769)
    ·
      refine ⟨11505622125815479535970577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15340829501087306047960769 11505622125815479535970577)
      ·
        refine ⟨8629216594361609651977933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11505622125815479535970577 8629216594361609651977933)
        ·
          refine ⟨3235956222885603619491725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8629216594361609651977933 3235956222885603619491725)
          ·
            refine ⟨1213483583582101357309397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3235956222885603619491725 1213483583582101357309397)
            ·
              refine ⟨28441021490205500561939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1213483583582101357309397 28441021490205500561939)
              ·
                rfl

theorem cell21_1121621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 7].length) (baseStart_1121621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121621 prefixEnd_1121621 := by exact prefixLift 1121621
  have htrace : WordTrace (prefixWord ++ tailWord_1121621) baseStart_1121621 baseEnd_1121621 := by
    simpa [prefixWord, tailWord_1121621, baseEnd_1121621] using wordTrace_append hprefix tailTrace_1121621
  have hstable : (prefixWord ++ tailWord_1121621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121621).length < 2 ^ (prefixWord ++ tailWord_1121621).sum := by decide
  have hdescent : baseEnd_1121621 < baseStart_1121621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121728 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 3]
def baseStart_1121728 : Nat := 118140960795 + 1121728 * 2 ^ 59
def prefixEnd_1121728 : Nat := 4983230072969 + 3 ^ 40 * 1121728 * 2
def baseEnd_1121728 : Nat := 255993612269641096773899

theorem tailTrace_1121728 : CollatzResearch.WordTrace tailWord_1121728 prefixEnd_1121728 255993612269641096773899 := by
  unfold tailWord_1121728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456390640089253367686919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27275187520119004490249225 20456390640089253367686919)
  ·
    refine ⟨30684585960133880051530379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20456390640089253367686919 30684585960133880051530379)
    ·
      refine ⟨46026878940200820077295569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30684585960133880051530379 46026878940200820077295569)
      ·
        refine ⟨34520159205150615057971677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46026878940200820077295569 34520159205150615057971677)
        ·
          refine ⟨12945059701931480646739379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34520159205150615057971677 12945059701931480646739379)
          ·
            refine ⟨19417589552897220970109069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12945059701931480646739379 19417589552897220970109069)
            ·
              refine ⟨7281596082336457863790901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19417589552897220970109069 7281596082336457863790901)
              ·
                refine ⟨682649632719042924730397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7281596082336457863790901 682649632719042924730397)
                ·
                  refine ⟨255993612269641096773899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682649632719042924730397 255993612269641096773899)
                  ·
                    rfl

theorem cell21_1121728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 3].length) (baseStart_1121728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121728 prefixEnd_1121728 := by exact prefixLift 1121728
  have htrace : WordTrace (prefixWord ++ tailWord_1121728) baseStart_1121728 baseEnd_1121728 := by
    simpa [prefixWord, tailWord_1121728, baseEnd_1121728] using wordTrace_append hprefix tailTrace_1121728
  have hstable : (prefixWord ++ tailWord_1121728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121728).length < 2 ^ (prefixWord ++ tailWord_1121728).sum := by decide
  have hdescent : baseEnd_1121728 < baseStart_1121728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121759 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 4]
def baseStart_1121759 : Nat := 118140960795 + 1121759 * 2 ^ 59
def prefixEnd_1121759 : Nat := 4983230072969 + 3 ^ 40 * 1121759 * 2
def baseEnd_1121759 : Nat := 256000686891991931757169

theorem tailTrace_1121759 : CollatzResearch.WordTrace tailWord_1121759 prefixEnd_1121759 256000686891991931757169 := by
  unfold tailWord_1121759
  simp only [CollatzResearch.WordTrace]
  refine ⟨40913911943066199029752331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27275941295377466019834887 40913911943066199029752331)
  ·
    refine ⟨61370867914599298544628497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40913911943066199029752331 61370867914599298544628497)
    ·
      refine ⟨46028150935949473908471373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61370867914599298544628497 46028150935949473908471373)
      ·
        refine ⟨17260556600981052715676765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46028150935949473908471373 17260556600981052715676765)
        ·
          refine ⟨6472708725367894768378787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17260556600981052715676765 6472708725367894768378787)
          ·
            refine ⟨9709063088051842152568181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472708725367894768378787 9709063088051842152568181)
            ·
              refine ⟨910224664504860201803267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9709063088051842152568181 910224664504860201803267)
              ·
                refine ⟨1365336996757290302704901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910224664504860201803267 1365336996757290302704901)
                ·
                  refine ⟨256000686891991931757169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365336996757290302704901 256000686891991931757169)
                  ·
                    rfl

theorem cell21_1121759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_1121759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121759 prefixEnd_1121759 := by exact prefixLift 1121759
  have htrace : WordTrace (prefixWord ++ tailWord_1121759) baseStart_1121759 baseEnd_1121759 := by
    simpa [prefixWord, tailWord_1121759, baseEnd_1121759] using wordTrace_append hprefix tailTrace_1121759
  have hstable : (prefixWord ++ tailWord_1121759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121759).length < 2 ^ (prefixWord ++ tailWord_1121759).sum := by decide
  have hdescent : baseEnd_1121759 < baseStart_1121759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121801 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_1121801 : Nat := 118140960795 + 1121801 * 2 ^ 59
def prefixEnd_1121801 : Nat := 4983230072969 + 3 ^ 40 * 1121801 * 2
def baseEnd_1121801 : Nat := 256010271864209192057083

theorem tailTrace_1121801 : CollatzResearch.WordTrace tailWord_1121801 prefixEnd_1121801 256010271864209192057083 := by
  unfold tailWord_1121801
  simp only [CollatzResearch.WordTrace]
  refine ⟨40915443808914040202781257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27276962539276026801854171 40915443808914040202781257)
  ·
    refine ⟨30686582856685530152085943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40915443808914040202781257 30686582856685530152085943)
    ·
      refine ⟨46029874285028295228128915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30686582856685530152085943 46029874285028295228128915)
      ·
        refine ⟨69044811427542442842193373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46029874285028295228128915 69044811427542442842193373)
        ·
          refine ⟨25891804285328416065822515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69044811427542442842193373 25891804285328416065822515)
          ·
            refine ⟨38837706427992624098733773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25891804285328416065822515 38837706427992624098733773)
            ·
              refine ⟨14564139910497234037025165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38837706427992624098733773 14564139910497234037025165)
              ·
                refine ⟨5461552466436462763884437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14564139910497234037025165 5461552466436462763884437)
                ·
                  refine ⟨256010271864209192057083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5461552466436462763884437 256010271864209192057083)
                  ·
                    rfl

theorem cell21_1121801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_1121801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121801 prefixEnd_1121801 := by exact prefixLift 1121801
  have htrace : WordTrace (prefixWord ++ tailWord_1121801) baseStart_1121801 baseEnd_1121801 := by
    simpa [prefixWord, tailWord_1121801, baseEnd_1121801] using wordTrace_append hprefix tailTrace_1121801
  have hstable : (prefixWord ++ tailWord_1121801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121801).length < 2 ^ (prefixWord ++ tailWord_1121801).sum := by decide
  have hdescent : baseEnd_1121801 < baseStart_1121801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121877 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1121877 : Nat := 118140960795 + 1121877 * 2 ^ 59
def prefixEnd_1121877 : Nat := 4983230072969 + 3 ^ 40 * 1121877 * 2
def baseEnd_1121877 : Nat := 256027616099649948790261

theorem tailTrace_1121877 : CollatzResearch.WordTrace tailWord_1121877 prefixEnd_1121877 256027616099649948790261 := by
  unfold tailWord_1121877
  simp only [CollatzResearch.WordTrace]
  refine ⟨40918215756638705182547885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27278810504425803455031923 40918215756638705182547885)
  ·
    refine ⟨15344330908739514443455457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40918215756638705182547885 15344330908739514443455457)
    ·
      refine ⟨11508248181554635832591593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15344330908739514443455457 11508248181554635832591593)
      ·
        refine ⟨8631186136165976874443695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11508248181554635832591593 8631186136165976874443695)
        ·
          refine ⟨12946779204248965311665543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631186136165976874443695 12946779204248965311665543)
          ·
            refine ⟨19420168806373447967498315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946779204248965311665543 19420168806373447967498315)
            ·
              refine ⟨29130253209560171951247473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19420168806373447967498315 29130253209560171951247473)
              ·
                refine ⟨21847689907170128963435605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29130253209560171951247473 21847689907170128963435605)
                ·
                  refine ⟨256027616099649948790261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21847689907170128963435605 256027616099649948790261)
                  ·
                    rfl

theorem cell21_1121877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1121877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121877 prefixEnd_1121877 := by exact prefixLift 1121877
  have htrace : WordTrace (prefixWord ++ tailWord_1121877) baseStart_1121877 baseEnd_1121877 := by
    simpa [prefixWord, tailWord_1121877, baseEnd_1121877] using wordTrace_append hprefix tailTrace_1121877
  have hstable : (prefixWord ++ tailWord_1121877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121877).length < 2 ^ (prefixWord ++ tailWord_1121877).sum := by decide
  have hdescent : baseEnd_1121877 < baseStart_1121877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121973 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1121973 : Nat := 118140960795 + 1121973 * 2 ^ 59
def prefixEnd_1121973 : Nat := 4983230072969 + 3 ^ 40 * 1121973 * 2
def baseEnd_1121973 : Nat := 256049524607575115190065

theorem tailTrace_1121973 : CollatzResearch.WordTrace tailWord_1121973 prefixEnd_1121973 256049524607575115190065 := by
  unfold tailWord_1121973
  simp only [CollatzResearch.WordTrace]
  refine ⟨40921717164290913578042573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27281144776193942385361715 40921717164290913578042573)
  ·
    refine ⟨15345643936609092591765965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40921717164290913578042573 15345643936609092591765965)
    ·
      refine ⟨5754616476228409721912237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15345643936609092591765965 5754616476228409721912237)
      ·
        refine ⟨2157981178585653645717089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5754616476228409721912237 2157981178585653645717089)
        ·
          refine ⟨1618485883939240234287817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157981178585653645717089 1618485883939240234287817)
          ·
            refine ⟨1213864412954430175715863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618485883939240234287817 1213864412954430175715863)
            ·
              refine ⟨1820796619431645263573795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213864412954430175715863 1820796619431645263573795)
              ·
                refine ⟨2731194929147467895360693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820796619431645263573795 2731194929147467895360693)
                ·
                  refine ⟨256049524607575115190065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2731194929147467895360693 256049524607575115190065)
                  ·
                    rfl

theorem cell21_1121973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1121973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121973 prefixEnd_1121973 := by exact prefixLift 1121973
  have htrace : WordTrace (prefixWord ++ tailWord_1121973) baseStart_1121973 baseEnd_1121973 := by
    simpa [prefixWord, tailWord_1121973, baseEnd_1121973] using wordTrace_append hprefix tailTrace_1121973
  have hstable : (prefixWord ++ tailWord_1121973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121973).length < 2 ^ (prefixWord ++ tailWord_1121973).sum := by decide
  have hdescent : baseEnd_1121973 < baseStart_1121973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121984 : List Nat := [2, 1, 1, 2, 4, 1, 4, 6]
def baseStart_1121984 : Nat := 118140960795 + 1121984 * 2 ^ 59
def prefixEnd_1121984 : Nat := 4983230072969 + 3 ^ 40 * 1121984 * 2
def baseEnd_1121984 : Nat := 85350678319147180168903

theorem tailTrace_1121984 : CollatzResearch.WordTrace tailWord_1121984 prefixEnd_1121984 85350678319147180168903 := by
  unfold tailWord_1121984
  simp only [CollatzResearch.WordTrace]
  refine ⟨20461059183625531228346503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27281412244834041637795337 20461059183625531228346503)
  ·
    refine ⟨30691588775438296842519755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20461059183625531228346503 30691588775438296842519755)
    ·
      refine ⟨46037383163157445263779633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30691588775438296842519755 46037383163157445263779633)
      ·
        refine ⟨34528037372368083947834725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46037383163157445263779633 34528037372368083947834725)
        ·
          refine ⟨6474007007319015740219011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34528037372368083947834725 6474007007319015740219011)
          ·
            refine ⟨9711010510978523610328517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6474007007319015740219011 9711010510978523610328517)
            ·
              refine ⟨1820814470808473176936597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9711010510978523610328517 1820814470808473176936597)
              ·
                refine ⟨85350678319147180168903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1820814470808473176936597 85350678319147180168903)
                ·
                  rfl

theorem cell21_1121984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_1121984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1121984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1121984 prefixEnd_1121984 := by exact prefixLift 1121984
  have htrace : WordTrace (prefixWord ++ tailWord_1121984) baseStart_1121984 baseEnd_1121984 := by
    simpa [prefixWord, tailWord_1121984, baseEnd_1121984] using wordTrace_append hprefix tailTrace_1121984
  have hstable : (prefixWord ++ tailWord_1121984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121984).length < 2 ^ (prefixWord ++ tailWord_1121984).sum := by decide
  have hdescent : baseEnd_1121984 < baseStart_1121984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122043 : List Nat := [1, 1, 1, 1, 1, 3, 1, 12]
def baseStart_1122043 : Nat := 118140960795 + 1122043 * 2 ^ 59
def prefixEnd_1122043 : Nat := 4983230072969 + 3 ^ 40 * 1122043 * 2
def baseEnd_1122043 : Nat := 85355166520423516341085

theorem tailTrace_1122043 : CollatzResearch.WordTrace tailWord_1122043 prefixEnd_1122043 85355166520423516341085 := by
  unfold tailWord_1122043
  simp only [CollatzResearch.WordTrace]
  refine ⟨40924270274037315533090783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27282846849358210355393855 40924270274037315533090783)
  ·
    refine ⟨61386405411055973299636175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40924270274037315533090783 61386405411055973299636175)
    ·
      refine ⟨92079608116583959949454263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61386405411055973299636175 92079608116583959949454263)
      ·
        refine ⟨138119412174875939924181395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92079608116583959949454263 138119412174875939924181395)
        ·
          refine ⟨207179118262313909886272093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138119412174875939924181395 207179118262313909886272093)
          ·
            refine ⟨77692169348367716207352035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207179118262313909886272093 77692169348367716207352035)
            ·
              refine ⟨116538254022551574311028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77692169348367716207352035 116538254022551574311028053)
              ·
                refine ⟨85355166520423516341085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 116538254022551574311028053 85355166520423516341085)
                ·
                  rfl

theorem cell21_1122043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_1122043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122043 prefixEnd_1122043 := by exact prefixLift 1122043
  have htrace : WordTrace (prefixWord ++ tailWord_1122043) baseStart_1122043 baseEnd_1122043 := by
    simpa [prefixWord, tailWord_1122043, baseEnd_1122043] using wordTrace_append hprefix tailTrace_1122043
  have hstable : (prefixWord ++ tailWord_1122043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122043).length < 2 ^ (prefixWord ++ tailWord_1122043).sum := by decide
  have hdescent : baseEnd_1122043 < baseStart_1122043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122066 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_1122066 : Nat := 118140960795 + 1122066 * 2 ^ 59
def prefixEnd_1122066 : Nat := 4983230072969 + 3 ^ 40 * 1122066 * 2
def baseEnd_1122066 : Nat := 256070748474627620139875

theorem tailTrace_1122066 : CollatzResearch.WordTrace tailWord_1122066 prefixEnd_1122066 256070748474627620139875 := by
  unfold tailWord_1122066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231277288238497615294513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27283406101969326974118701 10231277288238497615294513)
  ·
    refine ⟨7673457966178873211470885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10231277288238497615294513 7673457966178873211470885)
    ·
      refine ⟨1438773368658538727150791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7673457966178873211470885 1438773368658538727150791)
      ·
        refine ⟨2158160052987808090726187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438773368658538727150791 2158160052987808090726187)
        ·
          refine ⟨3237240079481712136089281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158160052987808090726187 3237240079481712136089281)
          ·
            refine ⟨2427930059611284102066961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3237240079481712136089281 2427930059611284102066961)
            ·
              refine ⟨1820947544708463076550221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427930059611284102066961 1820947544708463076550221)
              ·
                refine ⟨682855329265673653706333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820947544708463076550221 682855329265673653706333)
                ·
                  refine ⟨256070748474627620139875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682855329265673653706333 256070748474627620139875)
                  ·
                    rfl

theorem cell21_1122066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_1122066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122066 prefixEnd_1122066 := by exact prefixLift 1122066
  have htrace : WordTrace (prefixWord ++ tailWord_1122066) baseStart_1122066 baseEnd_1122066 := by
    simpa [prefixWord, tailWord_1122066, baseEnd_1122066] using wordTrace_append hprefix tailTrace_1122066
  have hstable : (prefixWord ++ tailWord_1122066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122066).length < 2 ^ (prefixWord ++ tailWord_1122066).sum := by decide
  have hdescent : baseEnd_1122066 < baseStart_1122066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122212 : List Nat := [2, 3, 1, 2, 1, 3, 3, 6]
def baseStart_1122212 : Nat := 118140960795 + 1122212 * 2 ^ 59
def prefixEnd_1122212 : Nat := 4983230072969 + 3 ^ 40 * 1122212 * 2
def baseEnd_1122212 : Nat := 85368022554587936902081

theorem tailTrace_1122212 : CollatzResearch.WordTrace tailWord_1122212 prefixEnd_1122212 85368022554587936902081 := by
  unfold tailWord_1122212
  simp only [CollatzResearch.WordTrace]
  refine ⟨20465217105212528697996445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27286956140283371597328593 20465217105212528697996445)
  ·
    refine ⟨7674456414454698261748667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20465217105212528697996445 7674456414454698261748667)
    ·
      refine ⟨11511684621682047392623001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7674456414454698261748667 11511684621682047392623001)
      ·
        refine ⟨8633763466261535544467251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11511684621682047392623001 8633763466261535544467251)
        ·
          refine ⟨12950645199392303316700877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633763466261535544467251 12950645199392303316700877)
          ·
            refine ⟨4856491949772113743762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12950645199392303316700877 4856491949772113743762829)
            ·
              refine ⟨1821184481164542653911061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4856491949772113743762829 1821184481164542653911061)
              ·
                refine ⟨85368022554587936902081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1821184481164542653911061 85368022554587936902081)
                ·
                  rfl

theorem cell21_1122212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_1122212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122212 prefixEnd_1122212 := by exact prefixLift 1122212
  have htrace : WordTrace (prefixWord ++ tailWord_1122212) baseStart_1122212 baseEnd_1122212 := by
    simpa [prefixWord, tailWord_1122212, baseEnd_1122212] using wordTrace_append hprefix tailTrace_1122212
  have hstable : (prefixWord ++ tailWord_1122212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122212).length < 2 ^ (prefixWord ++ tailWord_1122212).sum := by decide
  have hdescent : baseEnd_1122212 < baseStart_1122212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122229 : List Nat := [1, 3, 3, 2, 1, 3, 3, 5]
def baseStart_1122229 : Nat := 118140960795 + 1122229 * 2 ^ 59
def prefixEnd_1122229 : Nat := 4983230072969 + 3 ^ 40 * 1122229 * 2
def baseEnd_1122229 : Nat := 85369315765125186307625

theorem tailTrace_1122229 : CollatzResearch.WordTrace tailWord_1122229 prefixEnd_1122229 85369315765125186307625 := by
  unfold tailWord_1122229
  simp only [CollatzResearch.WordTrace]
  refine ⟨40931054251363469299361741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27287369500908979532907827 40931054251363469299361741)
  ·
    refine ⟨15349145344261300987260653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40931054251363469299361741 15349145344261300987260653)
    ·
      refine ⟨5755929504097987870222745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15349145344261300987260653 5755929504097987870222745)
      ·
        refine ⟨4316947128073490902667059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5755929504097987870222745 4316947128073490902667059)
        ·
          refine ⟨6475420692110236354000589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316947128073490902667059 6475420692110236354000589)
          ·
            refine ⟨2428282759541338632750221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6475420692110236354000589 2428282759541338632750221)
            ·
              refine ⟨910606034828001987281333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2428282759541338632750221 910606034828001987281333)
              ·
                refine ⟨85369315765125186307625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910606034828001987281333 85369315765125186307625)
                ·
                  rfl

theorem cell21_1122229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].length) (baseStart_1122229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122229 prefixEnd_1122229 := by exact prefixLift 1122229
  have htrace : WordTrace (prefixWord ++ tailWord_1122229) baseStart_1122229 baseEnd_1122229 := by
    simpa [prefixWord, tailWord_1122229, baseEnd_1122229] using wordTrace_append hprefix tailTrace_1122229
  have hstable : (prefixWord ++ tailWord_1122229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122229).length < 2 ^ (prefixWord ++ tailWord_1122229).sum := by decide
  have hdescent : baseEnd_1122229 < baseStart_1122229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122257 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_1122257 : Nat := 118140960795 + 1122257 * 2 ^ 59
def prefixEnd_1122257 : Nat := 4983230072969 + 3 ^ 40 * 1122257 * 2
def baseEnd_1122257 : Nat := 256114337276853732456151

theorem tailTrace_1122257 : CollatzResearch.WordTrace tailWord_1122257 prefixEnd_1122257 256114337276853732456151 := by
  unfold tailWord_1122257
  simp only [CollatzResearch.WordTrace]
  refine ⟨40932075495262030081381025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27288050330174686720920683 40932075495262030081381025)
  ·
    refine ⟨30699056621446522561035769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40932075495262030081381025 30699056621446522561035769)
    ·
      refine ⟨23024292466084891920776827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30699056621446522561035769 23024292466084891920776827)
      ·
        refine ⟨34536438699127337881165241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23024292466084891920776827 34536438699127337881165241)
        ·
          refine ⟨25902329024345503410873931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34536438699127337881165241 25902329024345503410873931)
          ·
            refine ⟨38853493536518255116310897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25902329024345503410873931 38853493536518255116310897)
            ·
              refine ⟨29140120152388691337233173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38853493536518255116310897 29140120152388691337233173)
              ·
                refine ⟨1365943132143219906432805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29140120152388691337233173 1365943132143219906432805)
                ·
                  refine ⟨256114337276853732456151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365943132143219906432805 256114337276853732456151)
                  ·
                    rfl

theorem cell21_1122257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_1122257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122257 prefixEnd_1122257 := by exact prefixLift 1122257
  have htrace : WordTrace (prefixWord ++ tailWord_1122257) baseStart_1122257 baseEnd_1122257 := by
    simpa [prefixWord, tailWord_1122257, baseEnd_1122257] using wordTrace_append hprefix tailTrace_1122257
  have hstable : (prefixWord ++ tailWord_1122257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122257).length < 2 ^ (prefixWord ++ tailWord_1122257).sum := by decide
  have hdescent : baseEnd_1122257 < baseStart_1122257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122260 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1122260 : Nat := 118140960795 + 1122260 * 2 ^ 59
def prefixEnd_1122260 : Nat := 4983230072969 + 3 ^ 40 * 1122260 * 2
def baseEnd_1122260 : Nat := 256115021917726393906145

theorem tailTrace_1122260 : CollatzResearch.WordTrace tailWord_1122260 prefixEnd_1122260 256115021917726393906145 := by
  unfold tailWord_1122260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466092457125580796870117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27288123276167441062493489 20466092457125580796870117)
  ·
    refine ⟨3837392335711046399413147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20466092457125580796870117 3837392335711046399413147)
    ·
      refine ⟨5756088503566569599119721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837392335711046399413147 5756088503566569599119721)
      ·
        refine ⟨4317066377674927199339791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5756088503566569599119721 4317066377674927199339791)
        ·
          refine ⟨6475599566512390799009687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317066377674927199339791 6475599566512390799009687)
          ·
            refine ⟨9713399349768586198514531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6475599566512390799009687 9713399349768586198514531)
            ·
              refine ⟨14570099024652879297771797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9713399349768586198514531 14570099024652879297771797)
              ·
                refine ⟨682973391780603717083053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14570099024652879297771797 682973391780603717083053)
                ·
                  refine ⟨256115021917726393906145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682973391780603717083053 256115021917726393906145)
                  ·
                    rfl

theorem cell21_1122260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1122260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122260 prefixEnd_1122260 := by exact prefixLift 1122260
  have htrace : WordTrace (prefixWord ++ tailWord_1122260) baseStart_1122260 baseEnd_1122260 := by
    simpa [prefixWord, tailWord_1122260, baseEnd_1122260] using wordTrace_append hprefix tailTrace_1122260
  have hstable : (prefixWord ++ tailWord_1122260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122260).length < 2 ^ (prefixWord ++ tailWord_1122260).sum := by decide
  have hdescent : baseEnd_1122260 < baseStart_1122260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122288 : List Nat := [2, 1, 1, 1, 3, 2, 6, 5]
def baseStart_1122288 : Nat := 118140960795 + 1122288 * 2 ^ 59
def prefixEnd_1122288 : Nat := 4983230072969 + 3 ^ 40 * 1122288 * 2
def baseEnd_1122288 : Nat := 85373803966401522479807

theorem tailTrace_1122288 : CollatzResearch.WordTrace tailWord_1122288 prefixEnd_1122288 85373803966401522479807 := by
  unfold tailWord_1122288
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466603079074861187879759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27288804105433148250506345 20466603079074861187879759)
  ·
    refine ⟨30699904618612291781819639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20466603079074861187879759 30699904618612291781819639)
    ·
      refine ⟨46049856927918437672729459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30699904618612291781819639 46049856927918437672729459)
      ·
        refine ⟨69074785391877656509094189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46049856927918437672729459 69074785391877656509094189)
        ·
          refine ⟨25903044521954121190910321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69074785391877656509094189 25903044521954121190910321)
          ·
            refine ⟨19427283391465590893182741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25903044521954121190910321 19427283391465590893182741)
            ·
              refine ⟨910653908974949573117941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19427283391465590893182741 910653908974949573117941)
              ·
                refine ⟨85373803966401522479807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910653908974949573117941 85373803966401522479807)
                ·
                  rfl

theorem cell21_1122288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_1122288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122288 prefixEnd_1122288 := by exact prefixLift 1122288
  have htrace : WordTrace (prefixWord ++ tailWord_1122288) baseStart_1122288 baseEnd_1122288 := by
    simpa [prefixWord, tailWord_1122288, baseEnd_1122288] using wordTrace_append hprefix tailTrace_1122288
  have hstable : (prefixWord ++ tailWord_1122288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122288).length < 2 ^ (prefixWord ++ tailWord_1122288).sum := by decide
  have hdescent : baseEnd_1122288 < baseStart_1122288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122294 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1122294 : Nat := 118140960795 + 1122294 * 2 ^ 59
def prefixEnd_1122294 : Nat := 4983230072969 + 3 ^ 40 * 1122294 * 2
def baseEnd_1122294 : Nat := 256122781180949890339409

theorem tailTrace_1122294 : CollatzResearch.WordTrace tailWord_1122294 prefixEnd_1122294 256122781180949890339409 := by
  unfold tailWord_1122294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2558339062257999087529871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27288949997418656933651957 2558339062257999087529871)
  ·
    refine ⟨3837508593386998631294807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2558339062257999087529871 3837508593386998631294807)
    ·
      refine ⟨5756262890080497946942211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837508593386998631294807 5756262890080497946942211)
      ·
        refine ⟨8634394335120746920413317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756262890080497946942211 8634394335120746920413317)
        ·
          refine ⟨1618948937835140047577497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8634394335120746920413317 1618948937835140047577497)
          ·
            refine ⟨1214211703376355035683123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618948937835140047577497 1214211703376355035683123)
            ·
              refine ⟨1821317555064532553524685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214211703376355035683123 1821317555064532553524685)
              ·
                refine ⟨682994083149199707571757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821317555064532553524685 682994083149199707571757)
                ·
                  refine ⟨256122781180949890339409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682994083149199707571757 256122781180949890339409)
                  ·
                    rfl

theorem cell21_1122294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1122294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122294 prefixEnd_1122294 := by exact prefixLift 1122294
  have htrace : WordTrace (prefixWord ++ tailWord_1122294) baseStart_1122294 baseEnd_1122294 := by
    simpa [prefixWord, tailWord_1122294, baseEnd_1122294] using wordTrace_append hprefix tailTrace_1122294
  have hstable : (prefixWord ++ tailWord_1122294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122294).length < 2 ^ (prefixWord ++ tailWord_1122294).sum := by decide
  have hdescent : baseEnd_1122294 < baseStart_1122294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122378 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1122378 : Nat := 118140960795 + 1122378 * 2 ^ 59
def prefixEnd_1122378 : Nat := 4983230072969 + 3 ^ 40 * 1122378 * 2
def baseEnd_1122378 : Nat := 256141951125384410939237

theorem tailTrace_1122378 : CollatzResearch.WordTrace tailWord_1122378 prefixEnd_1122378 256141951125384410939237 := by
  unfold tailWord_1122378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234122181955916936633947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27290992485215778497690525 10234122181955916936633947)
  ·
    refine ⟨15351183272933875404950921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10234122181955916936633947 15351183272933875404950921)
    ·
      refine ⟨11513387454700406553713191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15351183272933875404950921 11513387454700406553713191)
      ·
        refine ⟨17270081182050609830569787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513387454700406553713191 17270081182050609830569787)
        ·
          refine ⟨25905121773075914745854681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17270081182050609830569787 25905121773075914745854681)
          ·
            refine ⟨19428841329806936059391011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25905121773075914745854681 19428841329806936059391011)
            ·
              refine ⟨29143261994710404089086517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19428841329806936059391011 29143261994710404089086517)
              ·
                refine ⟨2732180812004100383351861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29143261994710404089086517 2732180812004100383351861)
                ·
                  refine ⟨256141951125384410939237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2732180812004100383351861 256141951125384410939237)
                  ·
                    rfl

theorem cell21_1122378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1122378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122378 prefixEnd_1122378 := by exact prefixLift 1122378
  have htrace : WordTrace (prefixWord ++ tailWord_1122378) baseStart_1122378 baseEnd_1122378 := by
    simpa [prefixWord, tailWord_1122378, baseEnd_1122378] using wordTrace_append hprefix tailTrace_1122378
  have hstable : (prefixWord ++ tailWord_1122378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122378).length < 2 ^ (prefixWord ++ tailWord_1122378).sum := by decide
  have hdescent : baseEnd_1122378 < baseStart_1122378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122412 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1122412 : Nat := 118140960795 + 1122412 * 2 ^ 59
def prefixEnd_1122412 : Nat := 4983230072969 + 3 ^ 40 * 1122412 * 2
def baseEnd_1122412 : Nat := 256149710388607907372501

theorem tailTrace_1122412 : CollatzResearch.WordTrace tailWord_1122412 prefixEnd_1122412 256149710388607907372501 := by
  unfold tailWord_1122412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468864404850245776636745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27291819206466994368848993 20468864404850245776636745)
  ·
    refine ⟨15351648303637684332477559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20468864404850245776636745 15351648303637684332477559)
    ·
      refine ⟨23027472455456526498716339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15351648303637684332477559 23027472455456526498716339)
      ·
        refine ⟨34541208683184789748074509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23027472455456526498716339 34541208683184789748074509)
        ·
          refine ⟨12952953256194296155527941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34541208683184789748074509 12952953256194296155527941)
          ·
            refine ⟨2428678735536430529161489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12952953256194296155527941 2428678735536430529161489)
            ·
              refine ⟨1821509051652322896871117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2428678735536430529161489 1821509051652322896871117)
              ·
                refine ⟨683065894369621086326669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821509051652322896871117 683065894369621086326669)
                ·
                  refine ⟨256149710388607907372501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683065894369621086326669 256149710388607907372501)
                  ·
                    rfl

theorem cell21_1122412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1122412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122412 prefixEnd_1122412 := by exact prefixLift 1122412
  have htrace : WordTrace (prefixWord ++ tailWord_1122412) baseStart_1122412 baseEnd_1122412 := by
    simpa [prefixWord, tailWord_1122412, baseEnd_1122412] using wordTrace_append hprefix tailTrace_1122412
  have hstable : (prefixWord ++ tailWord_1122412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122412).length < 2 ^ (prefixWord ++ tailWord_1122412).sum := by decide
  have hdescent : baseEnd_1122412 < baseStart_1122412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122423 : List Nat := [1, 1, 3, 1, 1, 6, 8]
def baseStart_1122423 : Nat := 118140960795 + 1122423 * 2 ^ 59
def prefixEnd_1122423 : Nat := 4983230072969 + 3 ^ 40 * 1122423 * 2
def baseEnd_1122423 : Nat := 28461357859830481409905

theorem tailTrace_1122423 : CollatzResearch.WordTrace tailWord_1122423 prefixEnd_1122423 28461357859830481409905 := by
  unfold tailWord_1122423
  simp only [CollatzResearch.WordTrace]
  refine ⟨40938130012660640431923923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27292086675107093621282615 40938130012660640431923923)
  ·
    refine ⟨61407195018990960647885885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40938130012660640431923923 61407195018990960647885885)
    ·
      refine ⟨23027698132121610242957207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61407195018990960647885885 23027698132121610242957207)
      ·
        refine ⟨34541547198182415364435811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23027698132121610242957207 34541547198182415364435811)
        ·
          refine ⟨51812320797273623046653717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34541547198182415364435811 51812320797273623046653717)
          ·
            refine ⟨2428702537372201080311893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51812320797273623046653717 2428702537372201080311893)
            ·
              refine ⟨28461357859830481409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2428702537372201080311893 28461357859830481409905)
              ·
                rfl

theorem cell21_1122423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 8].length) (baseStart_1122423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122423 prefixEnd_1122423 := by exact prefixLift 1122423
  have htrace : WordTrace (prefixWord ++ tailWord_1122423) baseStart_1122423 baseEnd_1122423 := by
    simpa [prefixWord, tailWord_1122423, baseEnd_1122423] using wordTrace_append hprefix tailTrace_1122423
  have hstable : (prefixWord ++ tailWord_1122423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122423).length < 2 ^ (prefixWord ++ tailWord_1122423).sum := by decide
  have hdescent : baseEnd_1122423 < baseStart_1122423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122474 : List Nat := [3, 1, 5, 1, 3, 1, 7]
def baseStart_1122474 : Nat := 118140960795 + 1122474 * 2 ^ 59
def prefixEnd_1122474 : Nat := 4983230072969 + 3 ^ 40 * 1122474 * 2
def baseEnd_1122474 : Nat := 28462651070367730815449

theorem tailTrace_1122474 : CollatzResearch.WordTrace tailWord_1122474 prefixEnd_1122474 28462651070367730815449 := by
  unfold tailWord_1122474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234997533868969035507619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27293326756983917428020317 10234997533868969035507619)
  ·
    refine ⟨15352496300803453553261429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10234997533868969035507619 15352496300803453553261429)
    ·
      refine ⟨1439296528200323770618259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15352496300803453553261429 1439296528200323770618259)
      ·
        refine ⟨2158944792300485655927389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439296528200323770618259 2158944792300485655927389)
        ·
          refine ⟨809604297112682120972771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2158944792300485655927389 809604297112682120972771)
          ·
            refine ⟨1214406445669023181459157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809604297112682120972771 1214406445669023181459157)
            ·
              refine ⟨28462651070367730815449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1214406445669023181459157 28462651070367730815449)
              ·
                rfl

theorem cell21_1122474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 7].length) (baseStart_1122474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122474 prefixEnd_1122474 := by exact prefixLift 1122474
  have htrace : WordTrace (prefixWord ++ tailWord_1122474) baseStart_1122474 baseEnd_1122474 := by
    simpa [prefixWord, tailWord_1122474, baseEnd_1122474] using wordTrace_append hprefix tailTrace_1122474
  have hstable : (prefixWord ++ tailWord_1122474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122474).length < 2 ^ (prefixWord ++ tailWord_1122474).sum := by decide
  have hdescent : baseEnd_1122474 < baseStart_1122474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122488 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_1122488 : Nat := 118140960795 + 1122488 * 2 ^ 59
def prefixEnd_1122488 : Nat := 4983230072969 + 3 ^ 40 * 1122488 * 2
def baseEnd_1122488 : Nat := 256167054624048664105679

theorem tailTrace_1122488 : CollatzResearch.WordTrace tailWord_1122488 prefixEnd_1122488 256167054624048664105679 := by
  unfold tailWord_1122488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470250378712578266520059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27293667171616771022026745 20470250378712578266520059)
  ·
    refine ⟨30705375568068867399780089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20470250378712578266520059 30705375568068867399780089)
    ·
      refine ⟨23029031676051650549835067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30705375568068867399780089 23029031676051650549835067)
      ·
        refine ⟨34543547514077475824752601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23029031676051650549835067 34543547514077475824752601)
        ·
          refine ⟨25907660635558106868564451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34543547514077475824752601 25907660635558106868564451)
          ·
            refine ⟨38861490953337160302846677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25907660635558106868564451 38861490953337160302846677)
            ·
              refine ⟨910816194218839694597969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38861490953337160302846677 910816194218839694597969)
              ·
                refine ⟨683112145664129770948477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910816194218839694597969 683112145664129770948477)
                ·
                  refine ⟨256167054624048664105679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683112145664129770948477 256167054624048664105679)
                  ·
                    rfl

theorem cell21_1122488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_1122488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122488 prefixEnd_1122488 := by exact prefixLift 1122488
  have htrace : WordTrace (prefixWord ++ tailWord_1122488) baseStart_1122488 baseEnd_1122488 := by
    simpa [prefixWord, tailWord_1122488, baseEnd_1122488] using wordTrace_append hprefix tailTrace_1122488
  have hstable : (prefixWord ++ tailWord_1122488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122488).length < 2 ^ (prefixWord ++ tailWord_1122488).sum := by decide
  have hdescent : baseEnd_1122488 < baseStart_1122488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122544 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1122544 : Nat := 118140960795 + 1122544 * 2 ^ 59
def prefixEnd_1122544 : Nat := 4983230072969 + 3 ^ 40 * 1122544 * 2
def baseEnd_1122544 : Nat := 256179834587005011172231

theorem tailTrace_1122544 : CollatzResearch.WordTrace tailWord_1122544 prefixEnd_1122544 256179834587005011172231 := by
  unfold tailWord_1122544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20471271622611139048539343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27295028830148185398052457 20471271622611139048539343)
  ·
    refine ⟨30706907433916708572809015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20471271622611139048539343 30706907433916708572809015)
    ·
      refine ⟨46060361150875062859213523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30706907433916708572809015 46060361150875062859213523)
      ·
        refine ⟨69090541726312594288820285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46060361150875062859213523 69090541726312594288820285)
        ·
          refine ⟨25908953147367222858307607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69090541726312594288820285 25908953147367222858307607)
          ·
            refine ⟨38863429721050834287461411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25908953147367222858307607 38863429721050834287461411)
            ·
              refine ⟨58295144581576251431192117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38863429721050834287461411 58295144581576251431192117)
              ·
                refine ⟨5465169804522773571674261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58295144581576251431192117 5465169804522773571674261)
                ·
                  refine ⟨256179834587005011172231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5465169804522773571674261 256179834587005011172231)
                  ·
                    rfl

theorem cell21_1122544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1122544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122544 prefixEnd_1122544 := by exact prefixLift 1122544
  have htrace : WordTrace (prefixWord ++ tailWord_1122544) baseStart_1122544 baseEnd_1122544 := by
    simpa [prefixWord, tailWord_1122544, baseEnd_1122544] using wordTrace_append hprefix tailTrace_1122544
  have hstable : (prefixWord ++ tailWord_1122544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122544).length < 2 ^ (prefixWord ++ tailWord_1122544).sum := by decide
  have hdescent : baseEnd_1122544 < baseStart_1122544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122547 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 3]
def baseStart_1122547 : Nat := 118140960795 + 1122547 * 2 ^ 59
def prefixEnd_1122547 : Nat := 4983230072969 + 3 ^ 40 * 1122547 * 2
def baseEnd_1122547 : Nat := 256180519227877672622225

theorem tailTrace_1122547 : CollatzResearch.WordTrace tailWord_1122547 prefixEnd_1122547 256180519227877672622225 := by
  unfold tailWord_1122547
  simp only [CollatzResearch.WordTrace]
  refine ⟨40942652664211409609437895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27295101776140939739625263 40942652664211409609437895)
  ·
    refine ⟨61413978996317114414156843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40942652664211409609437895 61413978996317114414156843)
    ·
      refine ⟨92120968494475671621235265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61413978996317114414156843 92120968494475671621235265)
      ·
        refine ⟨69090726370856753715926449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92120968494475671621235265 69090726370856753715926449)
        ·
          refine ⟨51818044778142565286944837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69090726370856753715926449 51818044778142565286944837)
          ·
            refine ⟨9715883395901730991302157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51818044778142565286944837 9715883395901730991302157)
            ·
              refine ⟨3643456273463149121738309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9715883395901730991302157 3643456273463149121738309)
              ·
                refine ⟨683148051274340460325933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3643456273463149121738309 683148051274340460325933)
                ·
                  refine ⟨256180519227877672622225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683148051274340460325933 256180519227877672622225)
                  ·
                    rfl

theorem cell21_1122547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 3].length) (baseStart_1122547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122547 prefixEnd_1122547 := by exact prefixLift 1122547
  have htrace : WordTrace (prefixWord ++ tailWord_1122547) baseStart_1122547 baseEnd_1122547 := by
    simpa [prefixWord, tailWord_1122547, baseEnd_1122547] using wordTrace_append hprefix tailTrace_1122547
  have hstable : (prefixWord ++ tailWord_1122547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122547).length < 2 ^ (prefixWord ++ tailWord_1122547).sum := by decide
  have hdescent : baseEnd_1122547 < baseStart_1122547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122561 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1122561 : Nat := 118140960795 + 1122561 * 2 ^ 59
def prefixEnd_1122561 : Nat := 4983230072969 + 3 ^ 40 * 1122561 * 2
def baseEnd_1122561 : Nat := 256183714218616759388863

theorem tailTrace_1122561 : CollatzResearch.WordTrace tailWord_1122561 prefixEnd_1122561 256183714218616759388863 := by
  unfold tailWord_1122561
  simp only [CollatzResearch.WordTrace]
  refine ⟨40943163286160690000447537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27295442190773793333631691 40943163286160690000447537)
  ·
    refine ⟨30707372464620517500335653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40943163286160690000447537 30707372464620517500335653)
    ·
      refine ⟨5757632337116347031312935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30707372464620517500335653 5757632337116347031312935)
      ·
        refine ⟨8636448505674520546969403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757632337116347031312935 8636448505674520546969403)
        ·
          refine ⟨12954672758511780820454105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8636448505674520546969403 12954672758511780820454105)
          ·
            refine ⟨9716004568883835615340579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12954672758511780820454105 9716004568883835615340579)
            ·
              refine ⟨14574006853325753423010869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9716004568883835615340579 14574006853325753423010869)
              ·
                refine ⟨1366313142499289383407269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14574006853325753423010869 1366313142499289383407269)
                ·
                  refine ⟨256183714218616759388863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366313142499289383407269 256183714218616759388863)
                  ·
                    rfl

theorem cell21_1122561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1122561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122561 prefixEnd_1122561 := by exact prefixLift 1122561
  have htrace : WordTrace (prefixWord ++ tailWord_1122561) baseStart_1122561 baseEnd_1122561 := by
    simpa [prefixWord, tailWord_1122561, baseEnd_1122561] using wordTrace_append hprefix tailTrace_1122561
  have hstable : (prefixWord ++ tailWord_1122561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122561).length < 2 ^ (prefixWord ++ tailWord_1122561).sum := by decide
  have hdescent : baseEnd_1122561 < baseStart_1122561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122640 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_1122640 : Nat := 118140960795 + 1122640 * 2 ^ 59
def prefixEnd_1122640 : Nat := 4983230072969 + 3 ^ 40 * 1122640 * 2
def baseEnd_1122640 : Nat := 256201743094930177572035

theorem tailTrace_1122640 : CollatzResearch.WordTrace tailWord_1122640 prefixEnd_1122640 256201743094930177572035 := by
  unfold tailWord_1122640
  simp only [CollatzResearch.WordTrace]
  refine ⟨20473022326437243246286687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27297363101916324328382249 20473022326437243246286687)
  ·
    refine ⟨30709533489655864869430031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20473022326437243246286687 30709533489655864869430031)
    ·
      refine ⟨46064300234483797304145047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30709533489655864869430031 46064300234483797304145047)
      ·
        refine ⟨69096450351725695956217571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46064300234483797304145047 69096450351725695956217571)
        ·
          refine ⟨103644675527588543934326357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69096450351725695956217571 103644675527588543934326357)
          ·
            refine ⟨1214586041338928249230387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 103644675527588543934326357 1214586041338928249230387)
            ·
              refine ⟨1821879062008392373845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214586041338928249230387 1821879062008392373845581)
              ·
                refine ⟨683204648253147140192093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821879062008392373845581 683204648253147140192093)
                ·
                  refine ⟨256201743094930177572035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683204648253147140192093 256201743094930177572035)
                  ·
                    rfl

theorem cell21_1122640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_1122640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122640 prefixEnd_1122640 := by exact prefixLift 1122640
  have htrace : WordTrace (prefixWord ++ tailWord_1122640) baseStart_1122640 baseEnd_1122640 := by
    simpa [prefixWord, tailWord_1122640, baseEnd_1122640] using wordTrace_append hprefix tailTrace_1122640
  have hstable : (prefixWord ++ tailWord_1122640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122640).length < 2 ^ (prefixWord ++ tailWord_1122640).sum := by decide
  have hdescent : baseEnd_1122640 < baseStart_1122640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122668 : List Nat := [2, 2, 1, 1, 6, 1, 2, 6]
def baseStart_1122668 : Nat := 118140960795 + 1122668 * 2 ^ 59
def prefixEnd_1122668 : Nat := 4983230072969 + 3 ^ 40 * 1122668 * 2
def baseEnd_1122668 : Nat := 85402711025469450368437

theorem tailTrace_1122668 : CollatzResearch.WordTrace tailWord_1122668 prefixEnd_1122668 85402711025469450368437 := by
  unfold tailWord_1122668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20473532948386523637296329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27298043931182031516395105 20473532948386523637296329)
  ·
    refine ⟨15355149711289892727972247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20473532948386523637296329 15355149711289892727972247)
    ·
      refine ⟨23032724566934839091958371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15355149711289892727972247 23032724566934839091958371)
      ·
        refine ⟨34549086850402258637937557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23032724566934839091958371 34549086850402258637937557)
        ·
          refine ⟨1619488446112605873653323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34549086850402258637937557 1619488446112605873653323)
          ·
            refine ⟨2429232669168908810479985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619488446112605873653323 2429232669168908810479985)
            ·
              refine ⟨1821924501876681607859989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2429232669168908810479985 1821924501876681607859989)
              ·
                refine ⟨85402711025469450368437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1821924501876681607859989 85402711025469450368437)
                ·
                  rfl

theorem cell21_1122668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_1122668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122668 prefixEnd_1122668 := by exact prefixLift 1122668
  have htrace : WordTrace (prefixWord ++ tailWord_1122668) baseStart_1122668 baseEnd_1122668 := by
    simpa [prefixWord, tailWord_1122668, baseEnd_1122668] using wordTrace_append hprefix tailTrace_1122668
  have hstable : (prefixWord ++ tailWord_1122668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122668).length < 2 ^ (prefixWord ++ tailWord_1122668).sum := by decide
  have hdescent : baseEnd_1122668 < baseStart_1122668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122713 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_1122713 : Nat := 118140960795 + 1122713 * 2 ^ 59
def prefixEnd_1122713 : Nat := 4983230072969 + 3 ^ 40 * 1122713 * 2
def baseEnd_1122713 : Nat := 256218402689498272855219

theorem tailTrace_1122713 : CollatzResearch.WordTrace tailWord_1122713 prefixEnd_1122713 256218402689498272855219 := by
  unfold tailWord_1122713
  simp only [CollatzResearch.WordTrace]
  refine ⟨40948707181610019959980793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27299138121073346639987195 40948707181610019959980793)
  ·
    refine ⟨30711530386207514969985595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40948707181610019959980793 30711530386207514969985595)
    ·
      refine ⟨46067295579311272454978393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30711530386207514969985595 46067295579311272454978393)
      ·
        refine ⟨34550471684483454341233795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46067295579311272454978393 34550471684483454341233795)
        ·
          refine ⟨51825707526725181511850693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34550471684483454341233795 51825707526725181511850693)
          ·
            refine ⟨9717320161260971533472005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51825707526725181511850693 9717320161260971533472005)
            ·
              refine ⟨1821997530236432162526001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9717320161260971533472005 1821997530236432162526001)
              ·
                refine ⟨1366498147677324121894501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821997530236432162526001 1366498147677324121894501)
                ·
                  refine ⟨256218402689498272855219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366498147677324121894501 256218402689498272855219)
                  ·
                    rfl

theorem cell21_1122713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_1122713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122713 prefixEnd_1122713 := by exact prefixLift 1122713
  have htrace : WordTrace (prefixWord ++ tailWord_1122713) baseStart_1122713 baseEnd_1122713 := by
    simpa [prefixWord, tailWord_1122713, baseEnd_1122713] using wordTrace_append hprefix tailTrace_1122713
  have hstable : (prefixWord ++ tailWord_1122713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122713).length < 2 ^ (prefixWord ++ tailWord_1122713).sum := by decide
  have hdescent : baseEnd_1122713 < baseStart_1122713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122820 : List Nat := [2, 3, 2, 3, 1, 3, 7]
def baseStart_1122820 : Nat := 118140960795 + 1122820 * 2 ^ 59
def prefixEnd_1122820 : Nat := 4983230072969 + 3 ^ 40 * 1122820 * 2
def baseEnd_1122820 : Nat := 28471424616365540507963

theorem tailTrace_1122820 : CollatzResearch.WordTrace tailWord_1122820 prefixEnd_1122820 28471424616365540507963 := by
  unfold tailWord_1122820
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476304896111188617062957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27301739861481584822750609 20476304896111188617062957)
  ·
    refine ⟨7678614336041695731398609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20476304896111188617062957 7678614336041695731398609)
    ·
      refine ⟨5758960752031271798548957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7678614336041695731398609 5758960752031271798548957)
      ·
        refine ⟨2159610282011726924455859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5758960752031271798548957 2159610282011726924455859)
        ·
          refine ⟨3239415423017590386683789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159610282011726924455859 3239415423017590386683789)
          ·
            refine ⟨1214780783631596395006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3239415423017590386683789 1214780783631596395006421)
            ·
              refine ⟨28471424616365540507963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1214780783631596395006421 28471424616365540507963)
              ·
                rfl

theorem cell21_1122820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 7].length) (baseStart_1122820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122820 prefixEnd_1122820 := by exact prefixLift 1122820
  have htrace : WordTrace (prefixWord ++ tailWord_1122820) baseStart_1122820 baseEnd_1122820 := by
    simpa [prefixWord, tailWord_1122820, baseEnd_1122820] using wordTrace_append hprefix tailTrace_1122820
  have hstable : (prefixWord ++ tailWord_1122820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122820).length < 2 ^ (prefixWord ++ tailWord_1122820).sum := by decide
  have hdescent : baseEnd_1122820 < baseStart_1122820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122941 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1122941 : Nat := 118140960795 + 1122941 * 2 ^ 59
def prefixEnd_1122941 : Nat := 4983230072969 + 3 ^ 40 * 1122941 * 2
def baseEnd_1122941 : Nat := 256270435395820543054753

theorem tailTrace_1122941 : CollatzResearch.WordTrace tailWord_1122941 prefixEnd_1122941 256270435395820543054753 := by
  unfold tailWord_1122941
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957023024784014899280677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27304682016522676599520451 40957023024784014899280677)
  ·
    refine ⟨7679441817147002793615127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40957023024784014899280677 7679441817147002793615127)
    ·
      refine ⟨11519162725720504190422691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679441817147002793615127 11519162725720504190422691)
      ·
        refine ⟨17278744088580756285634037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519162725720504190422691 17278744088580756285634037)
        ·
          refine ⟨1619882258304445901778191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17278744088580756285634037 1619882258304445901778191)
          ·
            refine ⟨2429823387456668852667287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619882258304445901778191 2429823387456668852667287)
            ·
              refine ⟨3644735081185003279000931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429823387456668852667287 3644735081185003279000931)
              ·
                refine ⟨5467102621777504918501397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644735081185003279000931 5467102621777504918501397)
                ·
                  refine ⟨256270435395820543054753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5467102621777504918501397 256270435395820543054753)
                  ·
                    rfl

theorem cell21_1122941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1122941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122941 prefixEnd_1122941 := by exact prefixLift 1122941
  have htrace : WordTrace (prefixWord ++ tailWord_1122941) baseStart_1122941 baseEnd_1122941 := by
    simpa [prefixWord, tailWord_1122941, baseEnd_1122941] using wordTrace_append hprefix tailTrace_1122941
  have hstable : (prefixWord ++ tailWord_1122941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122941).length < 2 ^ (prefixWord ++ tailWord_1122941).sum := by decide
  have hdescent : baseEnd_1122941 < baseStart_1122941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122958 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1122958 : Nat := 118140960795 + 1122958 * 2 ^ 59
def prefixEnd_1122958 : Nat := 4983230072969 + 3 ^ 40 * 1122958 * 2
def baseEnd_1122958 : Nat := 256274315027432291271385

theorem tailTrace_1122958 : CollatzResearch.WordTrace tailWord_1122958 prefixEnd_1122958 256274315027432291271385 := by
  unfold tailWord_1122958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119705383215303350331191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27305095377148284535099685 5119705383215303350331191)
  ·
    refine ⟨7679558074822955025496787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119705383215303350331191 7679558074822955025496787)
    ·
      refine ⟨11519337112234432538245181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679558074822955025496787 11519337112234432538245181)
      ·
        refine ⟨4319751417087912201841943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11519337112234432538245181 4319751417087912201841943)
        ·
          refine ⟨6479627125631868302762915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319751417087912201841943 6479627125631868302762915)
          ·
            refine ⟨9719440688447802454144373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479627125631868302762915 9719440688447802454144373)
            ·
              refine ⟨911197564541981480076035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9719440688447802454144373 911197564541981480076035)
              ·
                refine ⟨1366796346812972220114053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911197564541981480076035 1366796346812972220114053)
                ·
                  refine ⟨256274315027432291271385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366796346812972220114053 256274315027432291271385)
                  ·
                    rfl

theorem cell21_1122958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1122958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122958 prefixEnd_1122958 := by exact prefixLift 1122958
  have htrace : WordTrace (prefixWord ++ tailWord_1122958) baseStart_1122958 baseEnd_1122958 := by
    simpa [prefixWord, tailWord_1122958, baseEnd_1122958] using wordTrace_append hprefix tailTrace_1122958
  have hstable : (prefixWord ++ tailWord_1122958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122958).length < 2 ^ (prefixWord ++ tailWord_1122958).sum := by decide
  have hdescent : baseEnd_1122958 < baseStart_1122958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122969 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1122969 : Nat := 118140960795 + 1122969 * 2 ^ 59
def prefixEnd_1122969 : Nat := 4983230072969 + 3 ^ 40 * 1122969 * 2
def baseEnd_1122969 : Nat := 256276825377298716588029

theorem tailTrace_1122969 : CollatzResearch.WordTrace tailWord_1122969 prefixEnd_1122969 256276825377298716588029 := by
  unfold tailWord_1122969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40958044268682575681299961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27305362845788383787533307 40958044268682575681299961)
  ·
    refine ⟨30718533201511931760974971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40958044268682575681299961 30718533201511931760974971)
    ·
      refine ⟨46077799802267897641462457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30718533201511931760974971 46077799802267897641462457)
      ·
        refine ⟨34558349851700923231096843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46077799802267897641462457 34558349851700923231096843)
        ·
          refine ⟨51837524777551384846645265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34558349851700923231096843 51837524777551384846645265)
          ·
            refine ⟨38878143583163538634983949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51837524777551384846645265 38878143583163538634983949)
            ·
              refine ⟨14579303843686326988118981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38878143583163538634983949 14579303843686326988118981)
              ·
                refine ⟨2733619470691186310272309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14579303843686326988118981 2733619470691186310272309)
                ·
                  refine ⟨256276825377298716588029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733619470691186310272309 256276825377298716588029)
                  ·
                    rfl

theorem cell21_1122969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1122969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122969 prefixEnd_1122969 := by exact prefixLift 1122969
  have htrace : WordTrace (prefixWord ++ tailWord_1122969) baseStart_1122969 baseEnd_1122969 := by
    simpa [prefixWord, tailWord_1122969, baseEnd_1122969] using wordTrace_append hprefix tailTrace_1122969
  have hstable : (prefixWord ++ tailWord_1122969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122969).length < 2 ^ (prefixWord ++ tailWord_1122969).sum := by decide
  have hdescent : baseEnd_1122969 < baseStart_1122969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122972 : List Nat := [2, 2, 3, 2, 2, 1, 4, 5]
def baseStart_1122972 : Nat := 118140960795 + 1122972 * 2 ^ 59
def prefixEnd_1122972 : Nat := 4983230072969 + 3 ^ 40 * 1122972 * 2
def baseEnd_1122972 : Nat := 85425836672723792679341

theorem tailTrace_1122972 : CollatzResearch.WordTrace tailWord_1122972 prefixEnd_1122972 85425836672723792679341 := by
  unfold tailWord_1122972
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479076843835853596829585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27305435791781138129106113 20479076843835853596829585)
  ·
    refine ⟨15359307632876890197622189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20479076843835853596829585 15359307632876890197622189)
    ·
      refine ⟨5759740362328833824108321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15359307632876890197622189 5759740362328833824108321)
      ·
        refine ⟨4319805271746625368081241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5759740362328833824108321 4319805271746625368081241)
        ·
          refine ⟨3239853953809969026060931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4319805271746625368081241 3239853953809969026060931)
          ·
            refine ⟨4859780930714953539091397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239853953809969026060931 4859780930714953539091397)
            ·
              refine ⟨911208924509053788579637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4859780930714953539091397 911208924509053788579637)
              ·
                refine ⟨85425836672723792679341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 911208924509053788579637 85425836672723792679341)
                ·
                  rfl

theorem cell21_1122972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_1122972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1122972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1122972 prefixEnd_1122972 := by exact prefixLift 1122972
  have htrace : WordTrace (prefixWord ++ tailWord_1122972) baseStart_1122972 baseEnd_1122972 := by
    simpa [prefixWord, tailWord_1122972, baseEnd_1122972] using wordTrace_append hprefix tailTrace_1122972
  have hstable : (prefixWord ++ tailWord_1122972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122972).length < 2 ^ (prefixWord ++ tailWord_1122972).sum := by decide
  have hdescent : baseEnd_1122972 < baseStart_1122972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123009 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 4]
def baseStart_1123009 : Nat := 118140960795 + 1123009 * 2 ^ 59
def prefixEnd_1123009 : Nat := 4983230072969 + 3 ^ 40 * 1123009 * 2
def baseEnd_1123009 : Nat := 256285953922267535921281

theorem tailTrace_1123009 : CollatzResearch.WordTrace tailWord_1123009 prefixEnd_1123009 256285953922267535921281 := by
  unfold tailWord_1123009
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959503188537662512756081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27306335459025108341837387 40959503188537662512756081)
  ·
    refine ⟨30719627391403246884567061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40959503188537662512756081 30719627391403246884567061)
    ·
      refine ⟨1439982533972027197714081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30719627391403246884567061 1439982533972027197714081)
      ·
        refine ⟨1079986900479020398285561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1439982533972027197714081 1079986900479020398285561)
        ·
          refine ⟨809990175359265298714171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079986900479020398285561 809990175359265298714171)
          ·
            refine ⟨1214985263038897948071257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809990175359265298714171 1214985263038897948071257)
            ·
              refine ⟨911238947279173461053443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214985263038897948071257 911238947279173461053443)
              ·
                refine ⟨1366858420918760191580165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911238947279173461053443 1366858420918760191580165)
                ·
                  refine ⟨256285953922267535921281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366858420918760191580165 256285953922267535921281)
                  ·
                    rfl

theorem cell21_1123009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_1123009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123009 prefixEnd_1123009 := by exact prefixLift 1123009
  have htrace : WordTrace (prefixWord ++ tailWord_1123009) baseStart_1123009 baseEnd_1123009 := by
    simpa [prefixWord, tailWord_1123009, baseEnd_1123009] using wordTrace_append hprefix tailTrace_1123009
  have hstable : (prefixWord ++ tailWord_1123009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123009).length < 2 ^ (prefixWord ++ tailWord_1123009).sum := by decide
  have hdescent : baseEnd_1123009 < baseStart_1123009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123062 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1123062 : Nat := 118140960795 + 1123062 * 2 ^ 59
def prefixEnd_1123062 : Nat := 4983230072969 + 3 ^ 40 * 1123062 * 2
def baseEnd_1123062 : Nat := 256298049244351221537839

theorem tailTrace_1123062 : CollatzResearch.WordTrace tailWord_1123062 prefixEnd_1123062 256298049244351221537839 := by
  unfold tailWord_1123062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560089766084103285277215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27307624171563768376290293 2560089766084103285277215)
  ·
    refine ⟨3840134649126154927915823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560089766084103285277215 3840134649126154927915823)
    ·
      refine ⟨5760201973689232391873735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840134649126154927915823 5760201973689232391873735)
      ·
        refine ⟨8640302960533848587810603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760201973689232391873735 8640302960533848587810603)
        ·
          refine ⟨12960454440800772881715905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640302960533848587810603 12960454440800772881715905)
          ·
            refine ⟨9720340830600579661286929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12960454440800772881715905 9720340830600579661286929)
            ·
              refine ⟨7290255622950434745965197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9720340830600579661286929 7290255622950434745965197)
              ·
                refine ⟨2733845858606413029736949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7290255622950434745965197 2733845858606413029736949)
                ·
                  refine ⟨256298049244351221537839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733845858606413029736949 256298049244351221537839)
                  ·
                    rfl

theorem cell21_1123062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1123062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123062 prefixEnd_1123062 := by exact prefixLift 1123062
  have htrace : WordTrace (prefixWord ++ tailWord_1123062) baseStart_1123062 baseEnd_1123062 := by
    simpa [prefixWord, tailWord_1123062, baseEnd_1123062] using wordTrace_append hprefix tailTrace_1123062
  have hstable : (prefixWord ++ tailWord_1123062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123062).length < 2 ^ (prefixWord ++ tailWord_1123062).sum := by decide
  have hdescent : baseEnd_1123062 < baseStart_1123062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123172 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1123172 : Nat := 118140960795 + 1123172 * 2 ^ 59
def prefixEnd_1123172 : Nat := 4983230072969 + 3 ^ 40 * 1123172 * 2
def baseEnd_1123172 : Nat := 256323152743015474704281

theorem tailTrace_1123172 : CollatzResearch.WordTrace tailWord_1123172 prefixEnd_1123172 256323152743015474704281 := by
  unfold tailWord_1123172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20482724143473570675469885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27310298857964760900626513 20482724143473570675469885)
  ·
    refine ⟨7681021553802589003301207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20482724143473570675469885 7681021553802589003301207)
    ·
      refine ⟨11521532330703883504951811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681021553802589003301207 11521532330703883504951811)
      ·
        refine ⟨17282298496055825257427717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11521532330703883504951811 17282298496055825257427717)
        ·
          refine ⟨3240430968010467235767697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17282298496055825257427717 3240430968010467235767697)
          ·
            refine ⟨2430323226007850426825773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240430968010467235767697 2430323226007850426825773)
            ·
              refine ⟨911371209752943910059665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2430323226007850426825773 911371209752943910059665)
              ·
                refine ⟨683528407314707932544749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911371209752943910059665 683528407314707932544749)
                ·
                  refine ⟨256323152743015474704281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683528407314707932544749 256323152743015474704281)
                  ·
                    rfl

theorem cell21_1123172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1123172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123172 prefixEnd_1123172 := by exact prefixLift 1123172
  have htrace : WordTrace (prefixWord ++ tailWord_1123172) baseStart_1123172 baseEnd_1123172 := by
    simpa [prefixWord, tailWord_1123172, baseEnd_1123172] using wordTrace_append hprefix tailTrace_1123172
  have hstable : (prefixWord ++ tailWord_1123172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123172).length < 2 ^ (prefixWord ++ tailWord_1123172).sum := by decide
  have hdescent : baseEnd_1123172 < baseStart_1123172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123197 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1123197 : Nat := 118140960795 + 1123197 * 2 ^ 59
def prefixEnd_1123197 : Nat := 4983230072969 + 3 ^ 40 * 1123197 * 2
def baseEnd_1123197 : Nat := 256328858083620986787563

theorem tailTrace_1123197 : CollatzResearch.WordTrace tailWord_1123197 prefixEnd_1123197 256328858083620986787563 := by
  unfold tailWord_1123197
  simp only [CollatzResearch.WordTrace]
  refine ⟨40966360111856570620599845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27310906741237713747066563 40966360111856570620599845)
  ·
    refine ⟨7681192520973106991362471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40966360111856570620599845 7681192520973106991362471)
    ·
      refine ⟨11521788781459660487043707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7681192520973106991362471 11521788781459660487043707)
      ·
        refine ⟨17282683172189490730565561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11521788781459660487043707 17282683172189490730565561)
        ·
          refine ⟨12962012379142118047924171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17282683172189490730565561 12962012379142118047924171)
          ·
            refine ⟨19443018568713177071886257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12962012379142118047924171 19443018568713177071886257)
            ·
              refine ⟨14582263926534882803914693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443018568713177071886257 14582263926534882803914693)
              ·
                refine ⟨2734174486225290525734005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14582263926534882803914693 2734174486225290525734005)
                ·
                  refine ⟨256328858083620986787563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734174486225290525734005 256328858083620986787563)
                  ·
                    rfl

theorem cell21_1123197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1123197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123197 prefixEnd_1123197 := by exact prefixLift 1123197
  have htrace : WordTrace (prefixWord ++ tailWord_1123197) baseStart_1123197 baseEnd_1123197 := by
    simpa [prefixWord, tailWord_1123197, baseEnd_1123197] using wordTrace_append hprefix tailTrace_1123197
  have hstable : (prefixWord ++ tailWord_1123197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123197).length < 2 ^ (prefixWord ++ tailWord_1123197).sum := by decide
  have hdescent : baseEnd_1123197 < baseStart_1123197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123211 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_1123211 : Nat := 118140960795 + 1123211 * 2 ^ 59
def prefixEnd_1123211 : Nat := 4983230072969 + 3 ^ 40 * 1123211 * 2
def baseEnd_1123211 : Nat := 256332053074360073554201

theorem tailTrace_1123211 : CollatzResearch.WordTrace tailWord_1123211 prefixEnd_1123211 256332053074360073554201 := by
  unfold tailWord_1123211
  simp only [CollatzResearch.WordTrace]
  refine ⟨40966870733805851011609487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27311247155870567341072991 40966870733805851011609487)
  ·
    refine ⟨61450306100708776517414231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40966870733805851011609487 61450306100708776517414231)
    ·
      refine ⟨92175459151063164776121347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61450306100708776517414231 92175459151063164776121347)
      ·
        refine ⟨138263188726594747164182021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92175459151063164776121347 138263188726594747164182021)
        ·
          refine ⟨25924347886236515093284129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138263188726594747164182021 25924347886236515093284129)
          ·
            refine ⟨19443260914677386319963097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25924347886236515093284129 19443260914677386319963097)
            ·
              refine ⟨14582445686008039739972323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19443260914677386319963097 14582445686008039739972323)
              ·
                refine ⟨21873668529012059609958485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582445686008039739972323 21873668529012059609958485)
                ·
                  refine ⟨256332053074360073554201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21873668529012059609958485 256332053074360073554201)
                  ·
                    rfl

theorem cell21_1123211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_1123211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123211 prefixEnd_1123211 := by exact prefixLift 1123211
  have htrace : WordTrace (prefixWord ++ tailWord_1123211) baseStart_1123211 baseEnd_1123211 := by
    simpa [prefixWord, tailWord_1123211, baseEnd_1123211] using wordTrace_append hprefix tailTrace_1123211
  have hstable : (prefixWord ++ tailWord_1123211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123211).length < 2 ^ (prefixWord ++ tailWord_1123211).sum := by decide
  have hdescent : baseEnd_1123211 < baseStart_1123211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123231 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 3]
def baseStart_1123231 : Nat := 118140960795 + 1123231 * 2 ^ 59
def prefixEnd_1123231 : Nat := 4983230072969 + 3 ^ 40 * 1123231 * 2
def baseEnd_1123231 : Nat := 256336617346844483220827

theorem tailTrace_1123231 : CollatzResearch.WordTrace tailWord_1123231 prefixEnd_1123231 256336617346844483220827 := by
  unfold tailWord_1123231
  simp only [CollatzResearch.WordTrace]
  refine ⟨40967600193733394427337547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27311733462488929618225031 40967600193733394427337547)
  ·
    refine ⟨61451400290600091641006321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40967600193733394427337547 61451400290600091641006321)
    ·
      refine ⟨46088550217950068730754741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61451400290600091641006321 46088550217950068730754741)
      ·
        refine ⟨4320801582932818943508257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46088550217950068730754741 4320801582932818943508257)
        ·
          refine ⟨3240601187199614207631193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320801582932818943508257 3240601187199614207631193)
          ·
            refine ⟨2430450890399710655723395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240601187199614207631193 2430450890399710655723395)
            ·
              refine ⟨3645676335599565983585093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430450890399710655723395 3645676335599565983585093)
              ·
                refine ⟨683564312924918621922205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3645676335599565983585093 683564312924918621922205)
                ·
                  refine ⟨256336617346844483220827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683564312924918621922205 256336617346844483220827)
                  ·
                    rfl

theorem cell21_1123231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 3].length) (baseStart_1123231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123231 prefixEnd_1123231 := by exact prefixLift 1123231
  have htrace : WordTrace (prefixWord ++ tailWord_1123231) baseStart_1123231 baseEnd_1123231 := by
    simpa [prefixWord, tailWord_1123231, baseEnd_1123231] using wordTrace_append hprefix tailTrace_1123231
  have hstable : (prefixWord ++ tailWord_1123231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123231).length < 2 ^ (prefixWord ++ tailWord_1123231).sum := by decide
  have hdescent : baseEnd_1123231 < baseStart_1123231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123290 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1123290 : Nat := 118140960795 + 1123290 * 2 ^ 59
def prefixEnd_1123290 : Nat := 4983230072969 + 3 ^ 40 * 1123290 * 2
def baseEnd_1123290 : Nat := 256350081950673491737373

theorem tailTrace_1123290 : CollatzResearch.WordTrace tailWord_1123290 prefixEnd_1123290 256350081950673491737373 := by
  unfold tailWord_1123290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242438025129911875933831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27313168067013098335823549 10242438025129911875933831)
  ·
    refine ⟨15363657037694867813900747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10242438025129911875933831 15363657037694867813900747)
    ·
      refine ⟨23045485556542301720851121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15363657037694867813900747 23045485556542301720851121)
      ·
        refine ⟨17284114167406726290638341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23045485556542301720851121 17284114167406726290638341)
        ·
          refine ⟨3240771406388761179494689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17284114167406726290638341 3240771406388761179494689)
          ·
            refine ⟨2430578554791570884621017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240771406388761179494689 2430578554791570884621017)
            ·
              refine ⟨1822933916093678163465763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430578554791570884621017 1822933916093678163465763)
              ·
                refine ⟨2734400874140517245198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822933916093678163465763 2734400874140517245198645)
                ·
                  refine ⟨256350081950673491737373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734400874140517245198645 256350081950673491737373)
                  ·
                    rfl

theorem cell21_1123290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1123290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123290 prefixEnd_1123290 := by exact prefixLift 1123290
  have htrace : WordTrace (prefixWord ++ tailWord_1123290) baseStart_1123290 baseEnd_1123290 := by
    simpa [prefixWord, tailWord_1123290, baseEnd_1123290] using wordTrace_append hprefix tailTrace_1123290
  have hstable : (prefixWord ++ tailWord_1123290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123290).length < 2 ^ (prefixWord ++ tailWord_1123290).sum := by decide
  have hdescent : baseEnd_1123290 < baseStart_1123290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123304 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_1123304 : Nat := 118140960795 + 1123304 * 2 ^ 59
def prefixEnd_1123304 : Nat := 4983230072969 + 3 ^ 40 * 1123304 * 2
def baseEnd_1123304 : Nat := 256353276941412578504011

theorem tailTrace_1123304 : CollatzResearch.WordTrace tailWord_1123304 prefixEnd_1123304 256353276941412578504011 := by
  unfold tailWord_1123304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485131361234463947372483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27313508481645951929829977 20485131361234463947372483)
  ·
    refine ⟨30727697041851695921058725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20485131361234463947372483 30727697041851695921058725)
    ·
      refine ⟨5761443195347192985198511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30727697041851695921058725 5761443195347192985198511)
      ·
        refine ⟨8642164793020789477797767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761443195347192985198511 8642164793020789477797767)
        ·
          refine ⟨12963247189531184216696651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642164793020789477797767 12963247189531184216696651)
          ·
            refine ⟨19444870784296776325044977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12963247189531184216696651 19444870784296776325044977)
            ·
              refine ⟨14583653088222582243783733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19444870784296776325044977 14583653088222582243783733)
              ·
                refine ⟨1367217477020867085354725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14583653088222582243783733 1367217477020867085354725)
                ·
                  refine ⟨256353276941412578504011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367217477020867085354725 256353276941412578504011)
                  ·
                    rfl

theorem cell21_1123304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_1123304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123304 prefixEnd_1123304 := by exact prefixLift 1123304
  have htrace : WordTrace (prefixWord ++ tailWord_1123304) baseStart_1123304 baseEnd_1123304 := by
    simpa [prefixWord, tailWord_1123304, baseEnd_1123304] using wordTrace_append hprefix tailTrace_1123304
  have hstable : (prefixWord ++ tailWord_1123304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123304).length < 2 ^ (prefixWord ++ tailWord_1123304).sum := by decide
  have hdescent : baseEnd_1123304 < baseStart_1123304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123316 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1123316 : Nat := 118140960795 + 1123316 * 2 ^ 59
def prefixEnd_1123316 : Nat := 4983230072969 + 3 ^ 40 * 1123316 * 2
def baseEnd_1123316 : Nat := 256356015504903224303987

theorem tailTrace_1123316 : CollatzResearch.WordTrace tailWord_1123316 prefixEnd_1123316 256356015504903224303987 := by
  unfold tailWord_1123316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485350199212726972090901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27313800265616969296121201 20485350199212726972090901)
  ·
    refine ⟨960250790588096576816761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20485350199212726972090901 960250790588096576816761)
    ·
      refine ⟨720188092941072432612571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 960250790588096576816761 720188092941072432612571)
      ·
        refine ⟨1080282139411608648918857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720188092941072432612571 1080282139411608648918857)
        ·
          refine ⟨810211604558706486689143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080282139411608648918857 810211604558706486689143)
          ·
            refine ⟨1215317406838059730033715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810211604558706486689143 1215317406838059730033715)
            ·
              refine ⟨1822976110257089595050573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215317406838059730033715 1822976110257089595050573)
              ·
                refine ⟨683616041346408598143965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1822976110257089595050573 683616041346408598143965)
                ·
                  refine ⟨256356015504903224303987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683616041346408598143965 256356015504903224303987)
                  ·
                    rfl

theorem cell21_1123316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1123316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123316 prefixEnd_1123316 := by exact prefixLift 1123316
  have htrace : WordTrace (prefixWord ++ tailWord_1123316) baseStart_1123316 baseEnd_1123316 := by
    simpa [prefixWord, tailWord_1123316, baseEnd_1123316] using wordTrace_append hprefix tailTrace_1123316
  have hstable : (prefixWord ++ tailWord_1123316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123316).length < 2 ^ (prefixWord ++ tailWord_1123316).sum := by decide
  have hdescent : baseEnd_1123316 < baseStart_1123316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123408 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1123408 : Nat := 118140960795 + 1123408 * 2 ^ 59
def prefixEnd_1123408 : Nat := 4983230072969 + 3 ^ 40 * 1123408 * 2
def baseEnd_1123408 : Nat := 256377011158331508770465

theorem tailTrace_1123408 : CollatzResearch.WordTrace tailWord_1123408 prefixEnd_1123408 256377011158331508770465 := by
  unfold tailWord_1123408
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487027957046076828265439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27316037276061435771020585 20487027957046076828265439)
  ·
    refine ⟨30730541935569115242398159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20487027957046076828265439 30730541935569115242398159)
    ·
      refine ⟨46095812903353672863597239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30730541935569115242398159 46095812903353672863597239)
      ·
        refine ⟨69143719355030509295395859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46095812903353672863597239 69143719355030509295395859)
        ·
          refine ⟨103715579032545763943093789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69143719355030509295395859 103715579032545763943093789)
          ·
            refine ⟨38893342137204661478660171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103715579032545763943093789 38893342137204661478660171)
            ·
              refine ⟨58340013205806992217990257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38893342137204661478660171 58340013205806992217990257)
              ·
                refine ⟨43755009904355244163492693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58340013205806992217990257 43755009904355244163492693)
                ·
                  refine ⟨256377011158331508770465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43755009904355244163492693 256377011158331508770465)
                  ·
                    rfl

theorem cell21_1123408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1123408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123408 prefixEnd_1123408 := by exact prefixLift 1123408
  have htrace : WordTrace (prefixWord ++ tailWord_1123408) baseStart_1123408 baseEnd_1123408 := by
    simpa [prefixWord, tailWord_1123408, baseEnd_1123408] using wordTrace_append hprefix tailTrace_1123408
  have hstable : (prefixWord ++ tailWord_1123408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123408).length < 2 ^ (prefixWord ++ tailWord_1123408).sum := by decide
  have hdescent : baseEnd_1123408 < baseStart_1123408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123439 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_1123439 : Nat := 118140960795 + 1123439 * 2 ^ 59
def prefixEnd_1123439 : Nat := 4983230072969 + 3 ^ 40 * 1123439 * 2
def baseEnd_1123439 : Nat := 256384085780682343753735

theorem tailTrace_1123439 : CollatzResearch.WordTrace tailWord_1123439 prefixEnd_1123439 256384085780682343753735 := by
  unfold tailWord_1123439
  simp only [CollatzResearch.WordTrace]
  refine ⟨40975186576979845950909371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27316791051319897300606247 40975186576979845950909371)
  ·
    refine ⟨61462779865469768926364057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40975186576979845950909371 61462779865469768926364057)
    ·
      refine ⟨46097084899102326694773043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61462779865469768926364057 46097084899102326694773043)
      ·
        refine ⟨69145627348653490042159565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46097084899102326694773043 69145627348653490042159565)
        ·
          refine ⟨25929610255745058765809837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69145627348653490042159565 25929610255745058765809837)
          ·
            refine ⟨9723603845904397037178689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25929610255745058765809837 9723603845904397037178689)
            ·
              refine ⟨7292702884428297777884017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9723603845904397037178689 7292702884428297777884017)
              ·
                refine ⟨5469527163321223333413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7292702884428297777884017 5469527163321223333413013)
                ·
                  refine ⟨256384085780682343753735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5469527163321223333413013 256384085780682343753735)
                  ·
                    rfl

theorem cell21_1123439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_1123439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123439 prefixEnd_1123439 := by exact prefixLift 1123439
  have htrace : WordTrace (prefixWord ++ tailWord_1123439) baseStart_1123439 baseEnd_1123439 := by
    simpa [prefixWord, tailWord_1123439, baseEnd_1123439] using wordTrace_append hprefix tailTrace_1123439
  have hstable : (prefixWord ++ tailWord_1123439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123439).length < 2 ^ (prefixWord ++ tailWord_1123439).sum := by decide
  have hdescent : baseEnd_1123439 < baseStart_1123439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123456 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1123456 : Nat := 118140960795 + 1123456 * 2 ^ 59
def prefixEnd_1123456 : Nat := 4983230072969 + 3 ^ 40 * 1123456 * 2
def baseEnd_1123456 : Nat := 256387965412294091970367

theorem tailTrace_1123456 : CollatzResearch.WordTrace tailWord_1123456 prefixEnd_1123456 256387965412294091970367 := by
  unfold tailWord_1123456
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487903308959128927139111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27317204411945505236185481 20487903308959128927139111)
  ·
    refine ⟨30731854963438693390708667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20487903308959128927139111 30731854963438693390708667)
    ·
      refine ⟨46097782445158040086063001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30731854963438693390708667 46097782445158040086063001)
      ·
        refine ⟨34573336833868530064547251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46097782445158040086063001 34573336833868530064547251)
        ·
          refine ⟨51860005250802795096820877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34573336833868530064547251 51860005250802795096820877)
          ·
            refine ⟨19447501969051048161307829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51860005250802795096820877 19447501969051048161307829)
            ·
              refine ⟨1823203309598535765122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19447501969051048161307829 1823203309598535765122609)
              ·
                refine ⟨1367402482198901823841957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823203309598535765122609 1367402482198901823841957)
                ·
                  refine ⟨256387965412294091970367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367402482198901823841957 256387965412294091970367)
                  ·
                    rfl

theorem cell21_1123456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1123456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123456 prefixEnd_1123456 := by exact prefixLift 1123456
  have htrace : WordTrace (prefixWord ++ tailWord_1123456) baseStart_1123456 baseEnd_1123456 := by
    simpa [prefixWord, tailWord_1123456, baseEnd_1123456] using wordTrace_append hprefix tailTrace_1123456
  have hstable : (prefixWord ++ tailWord_1123456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123456).length < 2 ^ (prefixWord ++ tailWord_1123456).sum := by decide
  have hdescent : baseEnd_1123456 < baseStart_1123456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123487 : List Nat := [1, 1, 2, 6, 2, 1, 1, 7]
def baseStart_1123487 : Nat := 118140960795 + 1123487 * 2 ^ 59
def prefixEnd_1123487 : Nat := 4983230072969 + 3 ^ 40 * 1123487 * 2
def baseEnd_1123487 : Nat := 85465013344881642317879

theorem tailTrace_1123487 : CollatzResearch.WordTrace tailWord_1123487 prefixEnd_1123487 85465013344881642317879 := by
  unfold tailWord_1123487
  simp only [CollatzResearch.WordTrace]
  refine ⟨40976937280805950148656715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27317958187203966765771143 40976937280805950148656715)
  ·
    refine ⟨61465405921208925222985073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40976937280805950148656715 61465405921208925222985073)
    ·
      refine ⟨46099054440906693917238805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61465405921208925222985073 46099054440906693917238805)
      ·
        refine ⟨2160893176917501277370569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46099054440906693917238805 2160893176917501277370569)
        ·
          refine ⟨1620669882688125958027927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160893176917501277370569 1620669882688125958027927)
          ·
            refine ⟨2431004824032188937041891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620669882688125958027927 2431004824032188937041891)
            ·
              refine ⟨3646507236048283405562837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431004824032188937041891 3646507236048283405562837)
              ·
                refine ⟨85465013344881642317879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3646507236048283405562837 85465013344881642317879)
                ·
                  rfl

theorem cell21_1123487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_1123487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123487 prefixEnd_1123487 := by exact prefixLift 1123487
  have htrace : WordTrace (prefixWord ++ tailWord_1123487) baseStart_1123487 baseEnd_1123487 := by
    simpa [prefixWord, tailWord_1123487, baseEnd_1123487] using wordTrace_append hprefix tailTrace_1123487
  have hstable : (prefixWord ++ tailWord_1123487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123487).length < 2 ^ (prefixWord ++ tailWord_1123487).sum := by decide
  have hdescent : baseEnd_1123487 < baseStart_1123487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123510 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1123510 : Nat := 118140960795 + 1123510 * 2 ^ 59
def prefixEnd_1123510 : Nat := 4983230072969 + 3 ^ 40 * 1123510 * 2
def baseEnd_1123510 : Nat := 256400288948001998070257

theorem tailTrace_1123510 : CollatzResearch.WordTrace tailWord_1123510 prefixEnd_1123510 256400288948001998070257 := by
  unfold tailWord_1123510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561111009982664067296499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27318517439815083384495989 2561111009982664067296499)
  ·
    refine ⟨3841666514973996100944749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2561111009982664067296499 3841666514973996100944749)
    ·
      refine ⟨1440624943115248537854281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3841666514973996100944749 1440624943115248537854281)
      ·
        refine ⟨1080468707336436403390711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440624943115248537854281 1080468707336436403390711)
        ·
          refine ⟨1620703061004654605086067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080468707336436403390711 1620703061004654605086067)
          ·
            refine ⟨2431054591506981907629101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620703061004654605086067 2431054591506981907629101)
            ·
              refine ⟨911645471815118215360913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431054591506981907629101 911645471815118215360913)
              ·
                refine ⟨683734103861338661520685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911645471815118215360913 683734103861338661520685)
                ·
                  refine ⟨256400288948001998070257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683734103861338661520685 256400288948001998070257)
                  ·
                    rfl

theorem cell21_1123510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1123510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123510 prefixEnd_1123510 := by exact prefixLift 1123510
  have htrace : WordTrace (prefixWord ++ tailWord_1123510) baseStart_1123510 baseEnd_1123510 := by
    simpa [prefixWord, tailWord_1123510, baseEnd_1123510] using wordTrace_append hprefix tailTrace_1123510
  have hstable : (prefixWord ++ tailWord_1123510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123510).length < 2 ^ (prefixWord ++ tailWord_1123510).sum := by decide
  have hdescent : baseEnd_1123510 < baseStart_1123510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123518 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1123518 : Nat := 118140960795 + 1123518 * 2 ^ 59
def prefixEnd_1123518 : Nat := 4983230072969 + 3 ^ 40 * 1123518 * 2
def baseEnd_1123518 : Nat := 256402114656995761936907

theorem tailTrace_1123518 : CollatzResearch.WordTrace tailWord_1123518 prefixEnd_1123518 256402114656995761936907 := by
  unfold tailWord_1123518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122258492961705305379401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27318711962462428295356805 5122258492961705305379401)
  ·
    refine ⟨3841693869721278979034551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5122258492961705305379401 3841693869721278979034551)
    ·
      refine ⟨5762540804581918468551827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841693869721278979034551 5762540804581918468551827)
      ·
        refine ⟨8643811206872877702827741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5762540804581918468551827 8643811206872877702827741)
        ·
          refine ⟨3241429202577329138560403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8643811206872877702827741 3241429202577329138560403)
          ·
            refine ⟨4862143803865993707840605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241429202577329138560403 4862143803865993707840605)
            ·
              refine ⟨1823303926449747640440227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4862143803865993707840605 1823303926449747640440227)
              ·
                refine ⟨2734955889674621460660341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823303926449747640440227 2734955889674621460660341)
                ·
                  refine ⟨256402114656995761936907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734955889674621460660341 256402114656995761936907)
                  ·
                    rfl

theorem cell21_1123518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1123518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123518 prefixEnd_1123518 := by exact prefixLift 1123518
  have htrace : WordTrace (prefixWord ++ tailWord_1123518) baseStart_1123518 baseEnd_1123518 := by
    simpa [prefixWord, tailWord_1123518, baseEnd_1123518] using wordTrace_append hprefix tailTrace_1123518
  have hstable : (prefixWord ++ tailWord_1123518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123518).length < 2 ^ (prefixWord ++ tailWord_1123518).sum := by decide
  have hdescent : baseEnd_1123518 < baseStart_1123518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123580 : List Nat := [2, 2, 2, 1, 6, 1, 1, 6]
def baseStart_1123580 : Nat := 118140960795 + 1123580 * 2 ^ 59
def prefixEnd_1123580 : Nat := 4983230072969 + 3 ^ 40 * 1123580 * 2
def baseEnd_1123580 : Nat := 85472087967232477301149

theorem tailTrace_1123580 : CollatzResearch.WordTrace tailWord_1123580 prefixEnd_1123580 85472087967232477301149 := by
  unfold tailWord_1123580
  simp only [CollatzResearch.WordTrace]
  refine ⟨20490164634734513515896097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27320219512979351354528129 20490164634734513515896097)
  ·
    refine ⟨15367623476050885136922073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20490164634734513515896097 15367623476050885136922073)
    ·
      refine ⟨11525717607038163852691555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15367623476050885136922073 11525717607038163852691555)
      ·
        refine ⟨17288576410557245779037333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11525717607038163852691555 17288576410557245779037333)
        ·
          refine ⟨810402019244870895892375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17288576410557245779037333 810402019244870895892375)
          ·
            refine ⟨1215603028867306343838563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810402019244870895892375 1215603028867306343838563)
            ·
              refine ⟨1823404543300959515757845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215603028867306343838563 1823404543300959515757845)
              ·
                refine ⟨85472087967232477301149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1823404543300959515757845 85472087967232477301149)
                ·
                  rfl

theorem cell21_1123580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_1123580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123580 prefixEnd_1123580 := by exact prefixLift 1123580
  have htrace : WordTrace (prefixWord ++ tailWord_1123580) baseStart_1123580 baseEnd_1123580 := by
    simpa [prefixWord, tailWord_1123580, baseEnd_1123580] using wordTrace_append hprefix tailTrace_1123580
  have hstable : (prefixWord ++ tailWord_1123580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123580).length < 2 ^ (prefixWord ++ tailWord_1123580).sum := by decide
  have hdescent : baseEnd_1123580 < baseStart_1123580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123687 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 5]
def baseStart_1123687 : Nat := 118140960795 + 1123687 * 2 ^ 59
def prefixEnd_1123687 : Nat := 4983230072969 + 3 ^ 40 * 1123687 * 2
def baseEnd_1123687 : Nat := 256440682759489023619895

theorem tailTrace_1123687 : CollatzResearch.WordTrace tailWord_1123687 prefixEnd_1123687 256440682759489023619895 := by
  unfold tailWord_1123687
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984231880081384305937315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27322821253387589537291543 40984231880081384305937315)
  ·
    refine ⟨61476347820122076458905973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40984231880081384305937315 61476347820122076458905973)
    ·
      refine ⟨5763407608136444668022435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61476347820122076458905973 5763407608136444668022435)
      ·
        refine ⟨8645111412204667002033653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5763407608136444668022435 8645111412204667002033653)
        ·
          refine ⟨810479194894187531440655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8645111412204667002033653 810479194894187531440655)
          ·
            refine ⟨1215718792341281297160983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810479194894187531440655 1215718792341281297160983)
            ·
              refine ⟨1823578188511921945741475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215718792341281297160983 1823578188511921945741475)
              ·
                refine ⟨2735367282767882918612213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823578188511921945741475 2735367282767882918612213)
                ·
                  refine ⟨256440682759489023619895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735367282767882918612213 256440682759489023619895)
                  ·
                    rfl

theorem cell21_1123687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].length) (baseStart_1123687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123687 prefixEnd_1123687 := by exact prefixLift 1123687
  have htrace : WordTrace (prefixWord ++ tailWord_1123687) baseStart_1123687 baseEnd_1123687 := by
    simpa [prefixWord, tailWord_1123687, baseEnd_1123687] using wordTrace_append hprefix tailTrace_1123687
  have hstable : (prefixWord ++ tailWord_1123687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123687).length < 2 ^ (prefixWord ++ tailWord_1123687).sum := by decide
  have hdescent : baseEnd_1123687 < baseStart_1123687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123698 : List Nat := [3, 2, 1, 2, 1, 2, 4, 6]
def baseStart_1123698 : Nat := 118140960795 + 1123698 * 2 ^ 59
def prefixEnd_1123698 : Nat := 4983230072969 + 3 ^ 40 * 1123698 * 2
def baseEnd_1123698 : Nat := 85481064369785149645513

theorem tailTrace_1123698 : CollatzResearch.WordTrace tailWord_1123698 prefixEnd_1123698 85481064369785149645513 := by
  unfold tailWord_1123698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10246158270760383296146937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27323088722027688789725165 10246158270760383296146937)
  ·
    refine ⟨7684618703070287472110203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10246158270760383296146937 7684618703070287472110203)
    ·
      refine ⟨11526928054605431208165305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7684618703070287472110203 11526928054605431208165305)
      ·
        refine ⟨8645196040954073406123979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11526928054605431208165305 8645196040954073406123979)
        ·
          refine ⟨12967794061431110109185969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8645196040954073406123979 12967794061431110109185969)
          ·
            refine ⟨9725845546073332581889477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12967794061431110109185969 9725845546073332581889477)
            ·
              refine ⟨1823596039888749859104277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9725845546073332581889477 1823596039888749859104277)
              ·
                refine ⟨85481064369785149645513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1823596039888749859104277 85481064369785149645513)
                ·
                  rfl

theorem cell21_1123698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_1123698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123698 prefixEnd_1123698 := by exact prefixLift 1123698
  have htrace : WordTrace (prefixWord ++ tailWord_1123698) baseStart_1123698 baseEnd_1123698 := by
    simpa [prefixWord, tailWord_1123698, baseEnd_1123698] using wordTrace_append hprefix tailTrace_1123698
  have hstable : (prefixWord ++ tailWord_1123698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123698).length < 2 ^ (prefixWord ++ tailWord_1123698).sum := by decide
  have hdescent : baseEnd_1123698 < baseStart_1123698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123701 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1123701 : Nat := 118140960795 + 1123701 * 2 ^ 59
def prefixEnd_1123701 : Nat := 4983230072969 + 3 ^ 40 * 1123701 * 2
def baseEnd_1123701 : Nat := 256443877750228110386533

theorem tailTrace_1123701 : CollatzResearch.WordTrace tailWord_1123701 prefixEnd_1123701 256443877750228110386533 := by
  unfold tailWord_1123701
  simp only [CollatzResearch.WordTrace]
  refine ⟨40984742502030664696946957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27323161668020443131297971 40984742502030664696946957)
  ·
    refine ⟨15369278438261499261355109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40984742502030664696946957 15369278438261499261355109)
    ·
      refine ⟨2881739707174031111504083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15369278438261499261355109 2881739707174031111504083)
      ·
        refine ⟨4322609560761046667256125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881739707174031111504083 4322609560761046667256125)
        ·
          refine ⟨1620978585285392500221047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4322609560761046667256125 1620978585285392500221047)
          ·
            refine ⟨2431467877928088750331571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620978585285392500221047 2431467877928088750331571)
            ·
              refine ⟨3647201816892133125497357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431467877928088750331571 3647201816892133125497357)
              ·
                refine ⟨1367700681334549922061509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3647201816892133125497357 1367700681334549922061509)
                ·
                  refine ⟨256443877750228110386533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367700681334549922061509 256443877750228110386533)
                  ·
                    rfl

theorem cell21_1123701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1123701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123701 prefixEnd_1123701 := by exact prefixLift 1123701
  have htrace : WordTrace (prefixWord ++ tailWord_1123701) baseStart_1123701 baseEnd_1123701 := by
    simpa [prefixWord, tailWord_1123701, baseEnd_1123701] using wordTrace_append hprefix tailTrace_1123701
  have hstable : (prefixWord ++ tailWord_1123701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123701).length < 2 ^ (prefixWord ++ tailWord_1123701).sum := by decide
  have hdescent : baseEnd_1123701 < baseStart_1123701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123712 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1123712 : Nat := 118140960795 + 1123712 * 2 ^ 59
def prefixEnd_1123712 : Nat := 4983230072969 + 3 ^ 40 * 1123712 * 2
def baseEnd_1123712 : Nat := 256446388100094535703177

theorem tailTrace_1123712 : CollatzResearch.WordTrace tailWord_1123712 prefixEnd_1123712 256446388100094535703177 := by
  unfold tailWord_1123712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20492571852495406787798695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27323429136660542383731593 20492571852495406787798695)
  ·
    refine ⟨30738857778743110181698043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20492571852495406787798695 30738857778743110181698043)
    ·
      refine ⟨46108286668114665272547065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30738857778743110181698043 46108286668114665272547065)
      ·
        refine ⟨34581215001085998954410299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46108286668114665272547065 34581215001085998954410299)
        ·
          refine ⟨51871822501628998431615449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34581215001085998954410299 51871822501628998431615449)
          ·
            refine ⟨38903866876221748823711587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51871822501628998431615449 38903866876221748823711587)
            ·
              refine ⟨58355800314332623235567381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38903866876221748823711587 58355800314332623235567381)
              ·
                refine ⟨2735428139734341714167221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58355800314332623235567381 2735428139734341714167221)
                ·
                  refine ⟨256446388100094535703177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735428139734341714167221 256446388100094535703177)
                  ·
                    rfl

theorem cell21_1123712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1123712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123712 prefixEnd_1123712 := by exact prefixLift 1123712
  have htrace : WordTrace (prefixWord ++ tailWord_1123712) baseStart_1123712 baseEnd_1123712 := by
    simpa [prefixWord, tailWord_1123712, baseEnd_1123712] using wordTrace_append hprefix tailTrace_1123712
  have hstable : (prefixWord ++ tailWord_1123712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123712).length < 2 ^ (prefixWord ++ tailWord_1123712).sum := by decide
  have hdescent : baseEnd_1123712 < baseStart_1123712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123805 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1123805 : Nat := 118140960795 + 1123805 * 2 ^ 59
def prefixEnd_1123805 : Nat := 4983230072969 + 3 ^ 40 * 1123805 * 2
def baseEnd_1123805 : Nat := 256467611967147040652987

theorem tailTrace_1123805 : CollatzResearch.WordTrace tailWord_1123805 prefixEnd_1123805 256467611967147040652987 := by
  unfold tailWord_1123805
  simp only [CollatzResearch.WordTrace]
  refine ⟨40988535693653890458732869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27325690462435926972488579 40988535693653890458732869)
  ·
    refine ⟨7685350442560104461012413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40988535693653890458732869 7685350442560104461012413)
    ·
      refine ⟨2882006415960039172879655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7685350442560104461012413 2882006415960039172879655)
      ·
        refine ⟨4323009623940058759319483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882006415960039172879655 4323009623940058759319483)
        ·
          refine ⟨6484514435910088138979225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323009623940058759319483 6484514435910088138979225)
          ·
            refine ⟨4863385826932566104234419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6484514435910088138979225 4863385826932566104234419)
            ·
              refine ⟨7295078740398849156351629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863385826932566104234419 7295078740398849156351629)
              ·
                refine ⟨2735654527649568433631861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7295078740398849156351629 2735654527649568433631861)
                ·
                  refine ⟨256467611967147040652987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735654527649568433631861 256467611967147040652987)
                  ·
                    rfl

theorem cell21_1123805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1123805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123805 prefixEnd_1123805 := by exact prefixLift 1123805
  have htrace : WordTrace (prefixWord ++ tailWord_1123805) baseStart_1123805 baseEnd_1123805 := by
    simpa [prefixWord, tailWord_1123805, baseEnd_1123805] using wordTrace_append hprefix tailTrace_1123805
  have hstable : (prefixWord ++ tailWord_1123805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123805).length < 2 ^ (prefixWord ++ tailWord_1123805).sum := by decide
  have hdescent : baseEnd_1123805 < baseStart_1123805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123850 : List Nat := [3, 1, 2, 2, 2, 4, 7]
def baseStart_1123850 : Nat := 118140960795 + 1123850 * 2 ^ 59
def prefixEnd_1123850 : Nat := 4983230072969 + 3 ^ 40 * 1123850 * 2
def baseEnd_1123850 : Nat := 28497542397804106933655

theorem tailTrace_1123850 : CollatzResearch.WordTrace tailWord_1123850 prefixEnd_1123850 28497542397804106933655 := by
  unfold tailWord_1123850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247544244622715786030251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27326784652327242096080669 10247544244622715786030251)
  ·
    refine ⟨15371316366934073679045377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10247544244622715786030251 15371316366934073679045377)
    ·
      refine ⟨11528487275200555259284033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15371316366934073679045377 11528487275200555259284033)
      ·
        refine ⟨8646365456400416444463025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11528487275200555259284033 8646365456400416444463025)
        ·
          refine ⟨6484774092300312333347269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8646365456400416444463025 6484774092300312333347269)
          ·
            refine ⟨1215895142306308562502613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6484774092300312333347269 1215895142306308562502613)
            ·
              refine ⟨28497542397804106933655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1215895142306308562502613 28497542397804106933655)
              ·
                rfl

theorem cell21_1123850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 7].length) (baseStart_1123850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123850 prefixEnd_1123850 := by exact prefixLift 1123850
  have htrace : WordTrace (prefixWord ++ tailWord_1123850) baseStart_1123850 baseEnd_1123850 := by
    simpa [prefixWord, tailWord_1123850, baseEnd_1123850] using wordTrace_append hprefix tailTrace_1123850
  have hstable : (prefixWord ++ tailWord_1123850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123850).length < 2 ^ (prefixWord ++ tailWord_1123850).sum := by decide
  have hdescent : baseEnd_1123850 < baseStart_1123850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123940 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1123940 : Nat := 118140960795 + 1123940 * 2 ^ 59
def prefixEnd_1123940 : Nat := 4983230072969 + 3 ^ 40 * 1123940 * 2
def baseEnd_1123940 : Nat := 256498420806416805902711

theorem tailTrace_1123940 : CollatzResearch.WordTrace tailWord_1123940 prefixEnd_1123940 256498420806416805902711 := by
  unfold tailWord_1123940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20496729774082404257448637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27328973032109872343264849 20496729774082404257448637)
  ·
    refine ⟨7686273665280901596543239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20496729774082404257448637 7686273665280901596543239)
    ·
      refine ⟨11529410497921352394814859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7686273665280901596543239 11529410497921352394814859)
      ·
        refine ⟨17294115746882028592222289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11529410497921352394814859 17294115746882028592222289)
        ·
          refine ⟨12970586810161521444166717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17294115746882028592222289 12970586810161521444166717)
          ·
            refine ⟨4863970053810570541562519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12970586810161521444166717 4863970053810570541562519)
            ·
              refine ⟨7295955080715855812343779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863970053810570541562519 7295955080715855812343779)
              ·
                refine ⟨10943932621073783718515669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295955080715855812343779 10943932621073783718515669)
                ·
                  refine ⟨256498420806416805902711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10943932621073783718515669 256498420806416805902711)
                  ·
                    rfl

theorem cell21_1123940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1123940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1123940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1123940 prefixEnd_1123940 := by exact prefixLift 1123940
  have htrace : WordTrace (prefixWord ++ tailWord_1123940) baseStart_1123940 baseEnd_1123940 := by
    simpa [prefixWord, tailWord_1123940, baseEnd_1123940] using wordTrace_append hprefix tailTrace_1123940
  have hstable : (prefixWord ++ tailWord_1123940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123940).length < 2 ^ (prefixWord ++ tailWord_1123940).sum := by decide
  have hdescent : baseEnd_1123940 < baseStart_1123940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124084 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1124084 : Nat := 118140960795 + 1124084 * 2 ^ 59
def prefixEnd_1124084 : Nat := 4983230072969 + 3 ^ 40 * 1124084 * 2
def baseEnd_1124084 : Nat := 256531283568304555502417

theorem tailTrace_1124084 : CollatzResearch.WordTrace tailWord_1124084 prefixEnd_1124084 256531283568304555502417 := by
  unfold tailWord_1124084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499355829821560554069653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27332474439762080738759537 20499355829821560554069653)
  ·
    refine ⟨960907304522885650972015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20499355829821560554069653 960907304522885650972015)
    ·
      refine ⟨1441360956784328476458023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960907304522885650972015 1441360956784328476458023)
      ·
        refine ⟨2162041435176492714687035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441360956784328476458023 2162041435176492714687035)
        ·
          refine ⟨3243062152764739072030553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162041435176492714687035 3243062152764739072030553)
          ·
            refine ⟨2432296614573554304022915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243062152764739072030553 2432296614573554304022915)
            ·
              refine ⟨3648444921860331456034373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432296614573554304022915 3648444921860331456034373)
              ·
                refine ⟨684083422848812148006445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3648444921860331456034373 684083422848812148006445)
                ·
                  refine ⟨256531283568304555502417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684083422848812148006445 256531283568304555502417)
                  ·
                    rfl

theorem cell21_1124084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1124084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124084 prefixEnd_1124084 := by exact prefixLift 1124084
  have htrace : WordTrace (prefixWord ++ tailWord_1124084) baseStart_1124084 baseEnd_1124084 := by
    simpa [prefixWord, tailWord_1124084, baseEnd_1124084] using wordTrace_append hprefix tailTrace_1124084
  have hstable : (prefixWord ++ tailWord_1124084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124084).length < 2 ^ (prefixWord ++ tailWord_1124084).sum := by decide
  have hdescent : baseEnd_1124084 < baseStart_1124084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124092 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1124092 : Nat := 118140960795 + 1124092 * 2 ^ 59
def prefixEnd_1124092 : Nat := 4983230072969 + 3 ^ 40 * 1124092 * 2
def baseEnd_1124092 : Nat := 256533109277298319369067

theorem tailTrace_1124092 : CollatzResearch.WordTrace tailWord_1124092 prefixEnd_1124092 256533109277298319369067 := by
  unfold tailWord_1124092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20499501721807069237215265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27332668962409425649620353 20499501721807069237215265)
  ·
    refine ⟨15374626291355301927911449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20499501721807069237215265 15374626291355301927911449)
    ·
      refine ⟨11530969718516476445933587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15374626291355301927911449 11530969718516476445933587)
      ·
        refine ⟨17296454577774714668900381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11530969718516476445933587 17296454577774714668900381)
        ·
          refine ⟨6486170466665518000837643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17296454577774714668900381 6486170466665518000837643)
          ·
            refine ⟨9729255699998277001256465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486170466665518000837643 9729255699998277001256465)
            ·
              refine ⟨7296941774998707750942349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9729255699998277001256465 7296941774998707750942349)
              ·
                refine ⟨2736353165624515406603381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7296941774998707750942349 2736353165624515406603381)
                ·
                  refine ⟨256533109277298319369067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736353165624515406603381 256533109277298319369067)
                  ·
                    rfl

theorem cell21_1124092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1124092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124092 prefixEnd_1124092 := by exact prefixLift 1124092
  have htrace : WordTrace (prefixWord ++ tailWord_1124092) baseStart_1124092 baseEnd_1124092 := by
    simpa [prefixWord, tailWord_1124092, baseEnd_1124092] using wordTrace_append hprefix tailTrace_1124092
  have hstable : (prefixWord ++ tailWord_1124092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124092).length < 2 ^ (prefixWord ++ tailWord_1124092).sum := by decide
  have hdescent : baseEnd_1124092 < baseStart_1124092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124140 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1124140 : Nat := 118140960795 + 1124140 * 2 ^ 59
def prefixEnd_1124140 : Nat := 4983230072969 + 3 ^ 40 * 1124140 * 2
def baseEnd_1124140 : Nat := 256544063531260902568969

theorem tailTrace_1124140 : CollatzResearch.WordTrace tailWord_1124140 prefixEnd_1124140 256544063531260902568969 := by
  unfold tailWord_1124140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500377073720121336088937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27333836098293495114785249 20500377073720121336088937)
  ·
    refine ⟨15375282805290091002066703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20500377073720121336088937 15375282805290091002066703)
    ·
      refine ⟨23062924207935136503100055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15375282805290091002066703 23062924207935136503100055)
      ·
        refine ⟨34594386311902704754650083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23062924207935136503100055 34594386311902704754650083)
        ·
          refine ⟨51891579467854057131975125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34594386311902704754650083 51891579467854057131975125)
          ·
            refine ⟨1216208893777829464030667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51891579467854057131975125 1216208893777829464030667)
            ·
              refine ⟨1824313340666744196046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216208893777829464030667 1824313340666744196046001)
              ·
                refine ⟨1368235005500058147034501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824313340666744196046001 1368235005500058147034501)
                ·
                  refine ⟨256544063531260902568969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368235005500058147034501 256544063531260902568969)
                  ·
                    rfl

theorem cell21_1124140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1124140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124140 prefixEnd_1124140 := by exact prefixLift 1124140
  have htrace : WordTrace (prefixWord ++ tailWord_1124140) baseStart_1124140 baseEnd_1124140 := by
    simpa [prefixWord, tailWord_1124140, baseEnd_1124140] using wordTrace_append hprefix tailTrace_1124140
  have hstable : (prefixWord ++ tailWord_1124140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124140).length < 2 ^ (prefixWord ++ tailWord_1124140).sum := by decide
  have hdescent : baseEnd_1124140 < baseStart_1124140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124157 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1124157 : Nat := 118140960795 + 1124157 * 2 ^ 59
def prefixEnd_1124157 : Nat := 4983230072969 + 3 ^ 40 * 1124157 * 2
def baseEnd_1124157 : Nat := 256547943162872650785601

theorem tailTrace_1124157 : CollatzResearch.WordTrace tailWord_1124157 prefixEnd_1124157 256547943162872650785601 := by
  unfold tailWord_1124157
  simp only [CollatzResearch.WordTrace]
  refine ⟨41001374188378654575546725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27334249458919103050364483 41001374188378654575546725)
  ·
    refine ⟨7687757660320997732915011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41001374188378654575546725 7687757660320997732915011)
    ·
      refine ⟨11531636490481496599372517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687757660320997732915011 11531636490481496599372517)
      ·
        refine ⟨2162181841965280612382347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11531636490481496599372517 2162181841965280612382347)
        ·
          refine ⟨3243272762947920918573521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162181841965280612382347 3243272762947920918573521)
          ·
            refine ⟨2432454572210940688930141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243272762947920918573521 2432454572210940688930141)
            ·
              refine ⟨912170464579102758348803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2432454572210940688930141 912170464579102758348803)
              ·
                refine ⟨1368255696868654137523205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912170464579102758348803 1368255696868654137523205)
                ·
                  refine ⟨256547943162872650785601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368255696868654137523205 256547943162872650785601)
                  ·
                    rfl

theorem cell21_1124157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1124157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124157 prefixEnd_1124157 := by exact prefixLift 1124157
  have htrace : WordTrace (prefixWord ++ tailWord_1124157) baseStart_1124157 baseEnd_1124157 := by
    simpa [prefixWord, tailWord_1124157, baseEnd_1124157] using wordTrace_append hprefix tailTrace_1124157
  have hstable : (prefixWord ++ tailWord_1124157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124157).length < 2 ^ (prefixWord ++ tailWord_1124157).sum := by decide
  have hdescent : baseEnd_1124157 < baseStart_1124157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124168 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1124168 : Nat := 118140960795 + 1124168 * 2 ^ 59
def prefixEnd_1124168 : Nat := 4983230072969 + 3 ^ 40 * 1124168 * 2
def baseEnd_1124168 : Nat := 256550453512739076102245

theorem tailTrace_1124168 : CollatzResearch.WordTrace tailWord_1124168 prefixEnd_1124168 256550453512739076102245 := by
  unfold tailWord_1124168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500887695669401727098579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27334516927559202302798105 20500887695669401727098579)
  ·
    refine ⟨30751331543504102590647869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20500887695669401727098579 30751331543504102590647869)
    ·
      refine ⟨11531749328814038471492951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30751331543504102590647869 11531749328814038471492951)
      ·
        refine ⟨17297623993221057707239427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531749328814038471492951 17297623993221057707239427)
        ·
          refine ⟨25946435989831586560859141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17297623993221057707239427 25946435989831586560859141)
          ·
            refine ⟨4864956748093422480161089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25946435989831586560859141 4864956748093422480161089)
            ·
              refine ⟨3648717561070066860120817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864956748093422480161089 3648717561070066860120817)
              ·
                refine ⟨2736538170802550145090613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648717561070066860120817 2736538170802550145090613)
                ·
                  refine ⟨256550453512739076102245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736538170802550145090613 256550453512739076102245)
                  ·
                    rfl

theorem cell21_1124168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1124168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124168 prefixEnd_1124168 := by exact prefixLift 1124168
  have htrace : WordTrace (prefixWord ++ tailWord_1124168) baseStart_1124168 baseEnd_1124168 := by
    simpa [prefixWord, tailWord_1124168, baseEnd_1124168] using wordTrace_append hprefix tailTrace_1124168
  have hstable : (prefixWord ++ tailWord_1124168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124168).length < 2 ^ (prefixWord ++ tailWord_1124168).sum := by decide
  have hdescent : baseEnd_1124168 < baseStart_1124168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124199 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_1124199 : Nat := 118140960795 + 1124199 * 2 ^ 59
def prefixEnd_1124199 : Nat := 4983230072969 + 3 ^ 40 * 1124199 * 2
def baseEnd_1124199 : Nat := 256557528135089911085515

theorem tailTrace_1124199 : CollatzResearch.WordTrace tailWord_1124199 prefixEnd_1124199 256557528135089911085515 := by
  unfold tailWord_1124199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41002906054226495748575651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27335270702817663832383767 41002906054226495748575651)
  ·
    refine ⟨61504359081339743622863477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41002906054226495748575651 61504359081339743622863477)
    ·
      refine ⟨5766033663875600964643451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61504359081339743622863477 5766033663875600964643451)
      ·
        refine ⟨8649050495813401446965177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766033663875600964643451 8649050495813401446965177)
        ·
          refine ⟨6486787871860051085223883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649050495813401446965177 6486787871860051085223883)
          ·
            refine ⟨9730181807790076627835825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6486787871860051085223883 9730181807790076627835825)
            ·
              refine ⟨7297636355842557470876869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9730181807790076627835825 7297636355842557470876869)
              ·
                refine ⟨1368306816720479525789413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7297636355842557470876869 1368306816720479525789413)
                ·
                  refine ⟨256557528135089911085515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368306816720479525789413 256557528135089911085515)
                  ·
                    rfl

theorem cell21_1124199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_1124199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124199 prefixEnd_1124199 := by exact prefixLift 1124199
  have htrace : WordTrace (prefixWord ++ tailWord_1124199) baseStart_1124199 baseEnd_1124199 := by
    simpa [prefixWord, tailWord_1124199, baseEnd_1124199] using wordTrace_append hprefix tailTrace_1124199
  have hstable : (prefixWord ++ tailWord_1124199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124199).length < 2 ^ (prefixWord ++ tailWord_1124199).sum := by decide
  have hdescent : baseEnd_1124199 < baseStart_1124199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124264 : List Nat := [2, 1, 6, 2, 1, 2, 1, 6]
def baseStart_1124264 : Nat := 118140960795 + 1124264 * 2 ^ 59
def prefixEnd_1124264 : Nat := 4983230072969 + 3 ^ 40 * 1124264 * 2
def baseEnd_1124264 : Nat := 85524120673554747500683

theorem tailTrace_1124264 : CollatzResearch.WordTrace tailWord_1124264 prefixEnd_1124264 85524120673554747500683 := by
  unfold tailWord_1124264
  simp only [CollatzResearch.WordTrace]
  refine ⟨20502638399495505924845923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27336851199327341233127897 20502638399495505924845923)
  ·
    refine ⟨30753957599243258887268885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20502638399495505924845923 30753957599243258887268885)
    ·
      refine ⟨1441591762464527760340729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30753957599243258887268885 1441591762464527760340729)
      ·
        refine ⟨1081193821848395820255547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1441591762464527760340729 1081193821848395820255547)
        ·
          refine ⟨1621790732772593730383321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081193821848395820255547 1621790732772593730383321)
          ·
            refine ⟨1216343049579445297787491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621790732772593730383321 1216343049579445297787491)
            ·
              refine ⟨1824514574369167946681237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216343049579445297787491 1824514574369167946681237)
              ·
                refine ⟨85524120673554747500683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1824514574369167946681237 85524120673554747500683)
                ·
                  rfl

theorem cell21_1124264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_1124264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124264 prefixEnd_1124264 := by exact prefixLift 1124264
  have htrace : WordTrace (prefixWord ++ tailWord_1124264) baseStart_1124264 baseEnd_1124264 := by
    simpa [prefixWord, tailWord_1124264, baseEnd_1124264] using wordTrace_append hprefix tailTrace_1124264
  have hstable : (prefixWord ++ tailWord_1124264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124264).length < 2 ^ (prefixWord ++ tailWord_1124264).sum := by decide
  have hdescent : baseEnd_1124264 < baseStart_1124264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124303 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_1124303 : Nat := 118140960795 + 1124303 * 2 ^ 59
def prefixEnd_1124303 : Nat := 4983230072969 + 3 ^ 40 * 1124303 * 2
def baseEnd_1124303 : Nat := 256581262352008841351969

theorem tailTrace_1124303 : CollatzResearch.WordTrace tailWord_1124303 prefixEnd_1124303 256581262352008841351969 := by
  unfold tailWord_1124303
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006699245849721510361563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27337799497233147673574375 41006699245849721510361563)
  ·
    refine ⟨61510048868774582265542345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41006699245849721510361563 61510048868774582265542345)
    ·
      refine ⟨46132536651580936699156759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61510048868774582265542345 46132536651580936699156759)
      ·
        refine ⟨69198804977371405048735139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46132536651580936699156759 69198804977371405048735139)
        ·
          refine ⟨103798207466057107573102709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69198804977371405048735139 103798207466057107573102709)
          ·
            refine ⟨9731081949942853834978379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103798207466057107573102709 9731081949942853834978379)
            ·
              refine ⟨14596622924914280752467569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9731081949942853834978379 14596622924914280752467569)
              ·
                refine ⟨10947467193685710564350677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14596622924914280752467569 10947467193685710564350677)
                ·
                  refine ⟨256581262352008841351969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10947467193685710564350677 256581262352008841351969)
                  ·
                    rfl

theorem cell21_1124303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_1124303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124303 prefixEnd_1124303 := by exact prefixLift 1124303
  have htrace : WordTrace (prefixWord ++ tailWord_1124303) baseStart_1124303 baseEnd_1124303 := by
    simpa [prefixWord, tailWord_1124303, baseEnd_1124303] using wordTrace_append hprefix tailTrace_1124303
  have hstable : (prefixWord ++ tailWord_1124303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124303).length < 2 ^ (prefixWord ++ tailWord_1124303).sum := by decide
  have hdescent : baseEnd_1124303 < baseStart_1124303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124306 : List Nat := [3, 2, 2, 3, 2, 1, 8]
def baseStart_1124306 : Nat := 118140960795 + 1124306 * 2 ^ 59
def prefixEnd_1124306 : Nat := 4983230072969 + 3 ^ 40 * 1124306 * 2
def baseEnd_1124306 : Nat := 28509105221431278089107

theorem tailTrace_1124306 : CollatzResearch.WordTrace tailWord_1124306 prefixEnd_1124306 28509105221431278089107 := by
  unfold tailWord_1124306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251702166209713255680193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27337872443225902015147181 10251702166209713255680193)
  ·
    refine ⟨7688776624657284941760145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10251702166209713255680193 7688776624657284941760145)
    ·
      refine ⟨5766582468492963706320109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7688776624657284941760145 5766582468492963706320109)
      ·
        refine ⟨2162468425684861389870041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5766582468492963706320109 2162468425684861389870041)
        ·
          refine ⟨1621851319263646042402531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162468425684861389870041 1621851319263646042402531)
          ·
            refine ⟨2432776978895469063603797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621851319263646042402531 2432776978895469063603797)
            ·
              refine ⟨28509105221431278089107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2432776978895469063603797 28509105221431278089107)
              ·
                rfl

theorem cell21_1124306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 8].length) (baseStart_1124306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124306 prefixEnd_1124306 := by exact prefixLift 1124306
  have htrace : WordTrace (prefixWord ++ tailWord_1124306) baseStart_1124306 baseEnd_1124306 := by
    simpa [prefixWord, tailWord_1124306, baseEnd_1124306] using wordTrace_append hprefix tailTrace_1124306
  have hstable : (prefixWord ++ tailWord_1124306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124306).length < 2 ^ (prefixWord ++ tailWord_1124306).sum := by decide
  have hdescent : baseEnd_1124306 < baseStart_1124306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124379 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_1124379 : Nat := 118140960795 + 1124379 * 2 ^ 59
def prefixEnd_1124379 : Nat := 4983230072969 + 3 ^ 40 * 1124379 * 2
def baseEnd_1124379 : Nat := 256598606587449598085147

theorem tailTrace_1124379 : CollatzResearch.WordTrace tailWord_1124379 prefixEnd_1124379 256598606587449598085147 := by
  unfold tailWord_1124379
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009471193574386490128191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27339647462382924326752127 41009471193574386490128191)
  ·
    refine ⟨61514206790361579735192287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41009471193574386490128191 61514206790361579735192287)
    ·
      refine ⟨92271310185542369602788431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61514206790361579735192287 92271310185542369602788431)
      ·
        refine ⟨138406965278313554404182647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92271310185542369602788431 138406965278313554404182647)
        ·
          refine ⟨207610447917470331606273971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138406965278313554404182647 207610447917470331606273971)
          ·
            refine ⟨311415671876205497409410957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207610447917470331606273971 311415671876205497409410957)
            ·
              refine ⟨116780876953577061528529109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311415671876205497409410957 116780876953577061528529109)
              ·
                refine ⟨2737051803599462379574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116780876953577061528529109 2737051803599462379574901)
                ·
                  refine ⟨256598606587449598085147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737051803599462379574901 256598606587449598085147)
                  ·
                    rfl

theorem cell21_1124379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_1124379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124379 prefixEnd_1124379 := by exact prefixLift 1124379
  have htrace : WordTrace (prefixWord ++ tailWord_1124379) baseStart_1124379 baseEnd_1124379 := by
    simpa [prefixWord, tailWord_1124379, baseEnd_1124379] using wordTrace_append hprefix tailTrace_1124379
  have hstable : (prefixWord ++ tailWord_1124379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124379).length < 2 ^ (prefixWord ++ tailWord_1124379).sum := by decide
  have hdescent : baseEnd_1124379 < baseStart_1124379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124385 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 4]
def baseStart_1124385 : Nat := 118140960795 + 1124385 * 2 ^ 59
def prefixEnd_1124385 : Nat := 4983230072969 + 3 ^ 40 * 1124385 * 2
def baseEnd_1124385 : Nat := 256599975869194920985135

theorem tailTrace_1124385 : CollatzResearch.WordTrace tailWord_1124385 prefixEnd_1124385 256599975869194920985135 := by
  unfold tailWord_1124385
  simp only [CollatzResearch.WordTrace]
  refine ⟨41009690031552649514846609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27339793354368433009897739 41009690031552649514846609)
  ·
    refine ⟨30757267523664487136134957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41009690031552649514846609 30757267523664487136134957)
    ·
      refine ⟨11533975321374182676050609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30757267523664487136134957 11533975321374182676050609)
      ·
        refine ⟨8650481491030637007037957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11533975321374182676050609 8650481491030637007037957)
        ·
          refine ⟨1621965279568244438819617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8650481491030637007037957 1621965279568244438819617)
          ·
            refine ⟨1216473959676183329114713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621965279568244438819617 1216473959676183329114713)
            ·
              refine ⟨912355469757137496836035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216473959676183329114713 912355469757137496836035)
              ·
                refine ⟨1368533204635706245254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912355469757137496836035 1368533204635706245254053)
                ·
                  refine ⟨256599975869194920985135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368533204635706245254053 256599975869194920985135)
                  ·
                    rfl

theorem cell21_1124385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_1124385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124385 prefixEnd_1124385 := by exact prefixLift 1124385
  have htrace : WordTrace (prefixWord ++ tailWord_1124385) baseStart_1124385 baseEnd_1124385 := by
    simpa [prefixWord, tailWord_1124385, baseEnd_1124385] using wordTrace_append hprefix tailTrace_1124385
  have hstable : (prefixWord ++ tailWord_1124385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124385).length < 2 ^ (prefixWord ++ tailWord_1124385).sum := by decide
  have hdescent : baseEnd_1124385 < baseStart_1124385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124413 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1124413 : Nat := 118140960795 + 1124413 * 2 ^ 59
def prefixEnd_1124413 : Nat := 4983230072969 + 3 ^ 40 * 1124413 * 2
def baseEnd_1124413 : Nat := 256606365850673094518411

theorem tailTrace_1124413 : CollatzResearch.WordTrace tailWord_1124413 prefixEnd_1124413 256606365850673094518411 := by
  unfold tailWord_1124413
  simp only [CollatzResearch.WordTrace]
  refine ⟨41010711275451210296865893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27340474183634140197910595 41010711275451210296865893)
  ·
    refine ⟨7689508364147101930662355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41010711275451210296865893 7689508364147101930662355)
    ·
      refine ⟨11534262546220652895993533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689508364147101930662355 11534262546220652895993533)
      ·
        refine ⟨4325348454832744835997575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11534262546220652895993533 4325348454832744835997575)
        ·
          refine ⟨6488022682249117253996363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325348454832744835997575 6488022682249117253996363)
          ·
            refine ⟨9732034023373675880994545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488022682249117253996363 9732034023373675880994545)
            ·
              refine ⟨7299025517530256910745909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9732034023373675880994545 7299025517530256910745909)
              ·
                refine ⟨684283642268461585382429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7299025517530256910745909 684283642268461585382429)
                ·
                  refine ⟨256606365850673094518411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684283642268461585382429 256606365850673094518411)
                  ·
                    rfl

theorem cell21_1124413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1124413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124413 prefixEnd_1124413 := by exact prefixLift 1124413
  have htrace : WordTrace (prefixWord ++ tailWord_1124413) baseStart_1124413 baseEnd_1124413 := by
    simpa [prefixWord, tailWord_1124413, baseEnd_1124413] using wordTrace_append hprefix tailTrace_1124413
  have hstable : (prefixWord ++ tailWord_1124413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124413).length < 2 ^ (prefixWord ++ tailWord_1124413).sum := by decide
  have hdescent : baseEnd_1124413 < baseStart_1124413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124430 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1124430 : Nat := 118140960795 + 1124430 * 2 ^ 59
def prefixEnd_1124430 : Nat := 4983230072969 + 3 ^ 40 * 1124430 * 2
def baseEnd_1124430 : Nat := 256610245482284842735043

theorem tailTrace_1124430 : CollatzResearch.WordTrace tailWord_1124430 prefixEnd_1124430 256610245482284842735043 := by
  unfold tailWord_1124430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126416414548702775029343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27340887544259748133489829 5126416414548702775029343)
  ·
    refine ⟨7689624621823054162544015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126416414548702775029343 7689624621823054162544015)
    ·
      refine ⟨11534436932734581243816023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689624621823054162544015 11534436932734581243816023)
      ·
        refine ⟨17301655399101871865724035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11534436932734581243816023 17301655399101871865724035)
        ·
          refine ⟨25952483098652807798586053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17301655399101871865724035 25952483098652807798586053)
          ·
            refine ⟨4866090580997401462234885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25952483098652807798586053 4866090580997401462234885)
            ·
              refine ⟨912391983937012774169041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4866090580997401462234885 912391983937012774169041)
              ·
                refine ⟨684293987952759580626781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912391983937012774169041 684293987952759580626781)
                ·
                  refine ⟨256610245482284842735043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684293987952759580626781 256610245482284842735043)
                  ·
                    rfl

theorem cell21_1124430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1124430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124430 prefixEnd_1124430 := by exact prefixLift 1124430
  have htrace : WordTrace (prefixWord ++ tailWord_1124430) baseStart_1124430 baseEnd_1124430 := by
    simpa [prefixWord, tailWord_1124430, baseEnd_1124430] using wordTrace_append hprefix tailTrace_1124430
  have hstable : (prefixWord ++ tailWord_1124430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124430).length < 2 ^ (prefixWord ++ tailWord_1124430).sum := by decide
  have hdescent : baseEnd_1124430 < baseStart_1124430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124576 : List Nat := [2, 1, 1, 3, 1, 3, 1, 9]
def baseStart_1124576 : Nat := 118140960795 + 1124576 * 2 ^ 59
def prefixEnd_1124576 : Nat := 4983230072969 + 3 ^ 40 * 1124576 * 2
def baseEnd_1124576 : Nat := 85547854890473677767137

theorem tailTrace_1124576 : CollatzResearch.WordTrace tailWord_1124576 prefixEnd_1124576 85547854890473677767137 := by
  unfold tailWord_1124576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20508328186930344567524791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27344437582573792756699721 20508328186930344567524791)
  ·
    refine ⟨30762492280395516851287187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20508328186930344567524791 30762492280395516851287187)
    ·
      refine ⟨46143738420593275276930781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30762492280395516851287187 46143738420593275276930781)
      ·
        refine ⟨17303901907722478228849043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46143738420593275276930781 17303901907722478228849043)
        ·
          refine ⟨25955852861583717343273565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17303901907722478228849043 25955852861583717343273565)
          ·
            refine ⟨9733444823093894003727587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25955852861583717343273565 9733444823093894003727587)
            ·
              refine ⟨14600167234640841005591381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9733444823093894003727587 14600167234640841005591381)
              ·
                refine ⟨85547854890473677767137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14600167234640841005591381 85547854890473677767137)
                ·
                  rfl

theorem cell21_1124576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_1124576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124576 prefixEnd_1124576 := by exact prefixLift 1124576
  have htrace : WordTrace (prefixWord ++ tailWord_1124576) baseStart_1124576 baseEnd_1124576 := by
    simpa [prefixWord, tailWord_1124576, baseEnd_1124576] using wordTrace_append hprefix tailTrace_1124576
  have hstable : (prefixWord ++ tailWord_1124576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124576).length < 2 ^ (prefixWord ++ tailWord_1124576).sum := by decide
  have hdescent : baseEnd_1124576 < baseStart_1124576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124607 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_1124607 : Nat := 118140960795 + 1124607 * 2 ^ 59
def prefixEnd_1124607 : Nat := 4983230072969 + 3 ^ 40 * 1124607 * 2
def baseEnd_1124607 : Nat := 256650639293771868284681

theorem tailTrace_1124607 : CollatzResearch.WordTrace tailWord_1124607 prefixEnd_1124607 256650639293771868284681 := by
  unfold tailWord_1124607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41017787036748381429428075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27345191357832254286285383 41017787036748381429428075)
  ·
    refine ⟨61526680555122572144142113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41017787036748381429428075 61526680555122572144142113)
    ·
      refine ⟨46145010416341929108106585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61526680555122572144142113 46145010416341929108106585)
      ·
        refine ⟨34608757812256446831079939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46145010416341929108106585 34608757812256446831079939)
        ·
          refine ⟨51913136718384670246619909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34608757812256446831079939 51913136718384670246619909)
          ·
            refine ⟨9733713134697125671241233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51913136718384670246619909 9733713134697125671241233)
            ·
              refine ⟨7300284851022844253430925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9733713134697125671241233 7300284851022844253430925)
              ·
                refine ⟨2737606819133566595036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7300284851022844253430925 2737606819133566595036597)
                ·
                  refine ⟨256650639293771868284681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737606819133566595036597 256650639293771868284681)
                  ·
                    rfl

theorem cell21_1124607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_1124607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124607 prefixEnd_1124607 := by exact prefixLift 1124607
  have htrace : WordTrace (prefixWord ++ tailWord_1124607) baseStart_1124607 baseEnd_1124607 := by
    simpa [prefixWord, tailWord_1124607, baseEnd_1124607] using wordTrace_append hprefix tailTrace_1124607
  have hstable : (prefixWord ++ tailWord_1124607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124607).length < 2 ^ (prefixWord ++ tailWord_1124607).sum := by decide
  have hdescent : baseEnd_1124607 < baseStart_1124607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124610 : List Nat := [3, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1124610 : Nat := 118140960795 + 1124610 * 2 ^ 59
def prefixEnd_1124610 : Nat := 4983230072969 + 3 ^ 40 * 1124610 * 2
def baseEnd_1124610 : Nat := 85550441311548176578225

theorem tailTrace_1124610 : CollatzResearch.WordTrace tailWord_1124610 prefixEnd_1124610 85550441311548176578225 := by
  unfold tailWord_1124610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10254474113934378235446821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27345264303825008627858189 10254474113934378235446821)
  ·
    refine ⟨1922713896362695919146279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10254474113934378235446821 1922713896362695919146279)
    ·
      refine ⟨2884070844544043878719419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922713896362695919146279 2884070844544043878719419)
      ·
        refine ⟨4326106266816065818079129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884070844544043878719419 4326106266816065818079129)
        ·
          refine ⟨3244579700112049363559347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4326106266816065818079129 3244579700112049363559347)
          ·
            refine ⟨4866869550168074045339021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244579700112049363559347 4866869550168074045339021)
            ·
              refine ⟨1825076081313027767002133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4866869550168074045339021 1825076081313027767002133)
              ·
                refine ⟨85550441311548176578225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1825076081313027767002133 85550441311548176578225)
                ·
                  rfl

theorem cell21_1124610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1124610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124610 prefixEnd_1124610 := by exact prefixLift 1124610
  have htrace : WordTrace (prefixWord ++ tailWord_1124610) baseStart_1124610 baseEnd_1124610 := by
    simpa [prefixWord, tailWord_1124610, baseEnd_1124610] using wordTrace_append hprefix tailTrace_1124610
  have hstable : (prefixWord ++ tailWord_1124610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124610).length < 2 ^ (prefixWord ++ tailWord_1124610).sum := by decide
  have hdescent : baseEnd_1124610 < baseStart_1124610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124647 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 4]
def baseStart_1124647 : Nat := 118140960795 + 1124647 * 2 ^ 59
def prefixEnd_1124647 : Nat := 4983230072969 + 3 ^ 40 * 1124647 * 2
def baseEnd_1124647 : Nat := 256659767838740687617933

theorem tailTrace_1124647 : CollatzResearch.WordTrace tailWord_1124647 prefixEnd_1124647 256659767838740687617933 := by
  unfold tailWord_1124647
  simp only [CollatzResearch.WordTrace]
  refine ⟨41019245956603468260884195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27346163971068978840589463 41019245956603468260884195)
  ·
    refine ⟨61528868934905202391326293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41019245956603468260884195 61528868934905202391326293)
    ·
      refine ⟨721041432830920340523355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 61528868934905202391326293 721041432830920340523355)
      ·
        refine ⟨1081562149246380510785033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721041432830920340523355 1081562149246380510785033)
        ·
          refine ⟨811171611934785383088775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081562149246380510785033 811171611934785383088775)
          ·
            refine ⟨1216757417902178074633163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811171611934785383088775 1216757417902178074633163)
            ·
              refine ⟨1825136126853267111949745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216757417902178074633163 1825136126853267111949745)
              ·
                refine ⟨1368852095139950333962309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1825136126853267111949745 1368852095139950333962309)
                ·
                  refine ⟨256659767838740687617933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368852095139950333962309 256659767838740687617933)
                  ·
                    rfl

theorem cell21_1124647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].length) (baseStart_1124647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124647 prefixEnd_1124647 := by exact prefixLift 1124647
  have htrace : WordTrace (prefixWord ++ tailWord_1124647) baseStart_1124647 baseEnd_1124647 := by
    simpa [prefixWord, tailWord_1124647, baseEnd_1124647] using wordTrace_append hprefix tailTrace_1124647
  have hstable : (prefixWord ++ tailWord_1124647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124647).length < 2 ^ (prefixWord ++ tailWord_1124647).sum := by decide
  have hdescent : baseEnd_1124647 < baseStart_1124647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124731 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 4]
def baseStart_1124731 : Nat := 118140960795 + 1124731 * 2 ^ 59
def prefixEnd_1124731 : Nat := 4983230072969 + 3 ^ 40 * 1124731 * 2
def baseEnd_1124731 : Nat := 256678937783175208217761

theorem tailTrace_1124731 : CollatzResearch.WordTrace tailWord_1124731 prefixEnd_1124731 256678937783175208217761 := by
  unfold tailWord_1124731
  simp only [CollatzResearch.WordTrace]
  refine ⟨41022309688299150606942047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27348206458866100404628031 41022309688299150606942047)
  ·
    refine ⟨61533464532448725910413071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41022309688299150606942047 61533464532448725910413071)
    ·
      refine ⟨92300196798673088865619607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61533464532448725910413071 92300196798673088865619607)
      ·
        refine ⟨138450295198009633298429411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92300196798673088865619607 138450295198009633298429411)
        ·
          refine ⟨207675442797014449947644117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138450295198009633298429411 207675442797014449947644117)
          ·
            refine ⟨4867393190555026170647909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 207675442797014449947644117 4867393190555026170647909)
            ·
              refine ⟨912636223229067406996483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4867393190555026170647909 912636223229067406996483)
              ·
                refine ⟨1368954334843601110494725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912636223229067406996483 1368954334843601110494725)
                ·
                  refine ⟨256678937783175208217761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368954334843601110494725 256678937783175208217761)
                  ·
                    rfl

theorem cell21_1124731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_1124731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124731 prefixEnd_1124731 := by exact prefixLift 1124731
  have htrace : WordTrace (prefixWord ++ tailWord_1124731) baseStart_1124731 baseEnd_1124731 := by
    simpa [prefixWord, tailWord_1124731, baseEnd_1124731] using wordTrace_append hprefix tailTrace_1124731
  have hstable : (prefixWord ++ tailWord_1124731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124731).length < 2 ^ (prefixWord ++ tailWord_1124731).sum := by decide
  have hdescent : baseEnd_1124731 < baseStart_1124731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124900 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1124900 : Nat := 118140960795 + 1124900 * 2 ^ 59
def prefixEnd_1124900 : Nat := 4983230072969 + 3 ^ 40 * 1124900 * 2
def baseEnd_1124900 : Nat := 256717505885668469900749

theorem tailTrace_1124900 : CollatzResearch.WordTrace tailWord_1124900 prefixEnd_1124900 256717505885668469900749 := by
  unfold tailWord_1124900
  simp only [CollatzResearch.WordTrace]
  refine ⟨20514236812343446234922077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27352315749791261646562769 20514236812343446234922077)
  ·
    refine ⟨7692838804628792338095779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20514236812343446234922077 7692838804628792338095779)
    ·
      refine ⟨11539258206943188507143669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7692838804628792338095779 11539258206943188507143669)
      ·
        refine ⟨1081805456900923922544719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11539258206943188507143669 1081805456900923922544719)
        ·
          refine ⟨1622708185351385883817079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081805456900923922544719 1622708185351385883817079)
          ·
            refine ⟨2434062278027078825725619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622708185351385883817079 2434062278027078825725619)
            ·
              refine ⟨3651093417040618238588429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434062278027078825725619 3651093417040618238588429)
              ·
                refine ⟨1369160031390231839470661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3651093417040618238588429 1369160031390231839470661)
                ·
                  refine ⟨256717505885668469900749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369160031390231839470661 256717505885668469900749)
                  ·
                    rfl

theorem cell21_1124900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1124900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124900 prefixEnd_1124900 := by exact prefixLift 1124900
  have htrace : WordTrace (prefixWord ++ tailWord_1124900) baseStart_1124900 baseEnd_1124900 := by
    simpa [prefixWord, tailWord_1124900, baseEnd_1124900] using wordTrace_append hprefix tailTrace_1124900
  have hstable : (prefixWord ++ tailWord_1124900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124900).length < 2 ^ (prefixWord ++ tailWord_1124900).sum := by decide
  have hdescent : baseEnd_1124900 < baseStart_1124900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124942 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1124942 : Nat := 118140960795 + 1124942 * 2 ^ 59
def prefixEnd_1124942 : Nat := 4983230072969 + 3 ^ 40 * 1124942 * 2
def baseEnd_1124942 : Nat := 256727090857885730200663

theorem tailTrace_1124942 : CollatzResearch.WordTrace tailWord_1124942 prefixEnd_1124942 256727090857885730200663 := by
  unfold tailWord_1124942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128750686316841705359135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27353336993689822428582053 5128750686316841705359135)
  ·
    refine ⟨7693126029475262558038703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128750686316841705359135 7693126029475262558038703)
    ·
      refine ⟨11539689044212893837058055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7693126029475262558038703 11539689044212893837058055)
      ·
        refine ⟨17309533566319340755587083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11539689044212893837058055 17309533566319340755587083)
        ·
          refine ⟨25964300349479011133380625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17309533566319340755587083 25964300349479011133380625)
          ·
            refine ⟨19473225262109258350035469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964300349479011133380625 19473225262109258350035469)
            ·
              refine ⟨7302459473290971881263301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19473225262109258350035469 7302459473290971881263301)
              ·
                refine ⟨1369211151242057227736869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7302459473290971881263301 1369211151242057227736869)
                ·
                  refine ⟨256727090857885730200663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369211151242057227736869 256727090857885730200663)
                  ·
                    rfl

theorem cell21_1124942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1124942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124942 prefixEnd_1124942 := by exact prefixLift 1124942
  have htrace : WordTrace (prefixWord ++ tailWord_1124942) baseStart_1124942 baseEnd_1124942 := by
    simpa [prefixWord, tailWord_1124942, baseEnd_1124942] using wordTrace_append hprefix tailTrace_1124942
  have hstable : (prefixWord ++ tailWord_1124942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124942).length < 2 ^ (prefixWord ++ tailWord_1124942).sum := by decide
  have hdescent : baseEnd_1124942 < baseStart_1124942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124945 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 3]
def baseStart_1124945 : Nat := 118140960795 + 1124945 * 2 ^ 59
def prefixEnd_1124945 : Nat := 4983230072969 + 3 ^ 40 * 1124945 * 2
def baseEnd_1124945 : Nat := 256727775498758391650657

theorem tailTrace_1124945 : CollatzResearch.WordTrace tailWord_1124945 prefixEnd_1124945 256727775498758391650657 := by
  unfold tailWord_1124945
  simp only [CollatzResearch.WordTrace]
  refine ⟨41030114909523865155232289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27353409939682576770154859 41030114909523865155232289)
  ·
    refine ⟨30772586182142898866424217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41030114909523865155232289 30772586182142898866424217)
    ·
      refine ⟨23079439636607174149818163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30772586182142898866424217 23079439636607174149818163)
      ·
        refine ⟨34619159454910761224727245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23079439636607174149818163 34619159454910761224727245)
        ·
          refine ⟨12982184795591535459272717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34619159454910761224727245 12982184795591535459272717)
          ·
            refine ⟨4868319298346825797227269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12982184795591535459272717 4868319298346825797227269)
            ·
              refine ⟨912809868440029836980113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4868319298346825797227269 912809868440029836980113)
              ·
                refine ⟨684607401330022377735085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912809868440029836980113 684607401330022377735085)
                ·
                  refine ⟨256727775498758391650657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684607401330022377735085 256727775498758391650657)
                  ·
                    rfl

theorem cell21_1124945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_1124945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1124945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1124945 prefixEnd_1124945 := by exact prefixLift 1124945
  have htrace : WordTrace (prefixWord ++ tailWord_1124945) baseStart_1124945 baseEnd_1124945 := by
    simpa [prefixWord, tailWord_1124945, baseEnd_1124945] using wordTrace_append hprefix tailTrace_1124945
  have hstable : (prefixWord ++ tailWord_1124945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124945).length < 2 ^ (prefixWord ++ tailWord_1124945).sum := by decide
  have hdescent : baseEnd_1124945 < baseStart_1124945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125038 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_1125038 : Nat := 118140960795 + 1125038 * 2 ^ 59
def prefixEnd_1125038 : Nat := 4983230072969 + 3 ^ 40 * 1125038 * 2
def baseEnd_1125038 : Nat := 256748999365810896600467

theorem tailTrace_1125038 : CollatzResearch.WordTrace tailWord_1125038 prefixEnd_1125038 256748999365810896600467 := by
  unfold tailWord_1125038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129188362273367754795971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27355671265457961358911845 5129188362273367754795971)
  ·
    refine ⟨7693782543410051632193957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129188362273367754795971 7693782543410051632193957)
    ·
      refine ⟨1442584226889384681036367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7693782543410051632193957 1442584226889384681036367)
      ·
        refine ⟨2163876340334077021554551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442584226889384681036367 2163876340334077021554551)
        ·
          refine ⟨3245814510501115532331827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163876340334077021554551 3245814510501115532331827)
          ·
            refine ⟨4868721765751673298497741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245814510501115532331827 4868721765751673298497741)
            ·
              refine ⟨1825770662156877486936653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4868721765751673298497741 1825770662156877486936653)
              ·
                refine ⟨684663998308829057601245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1825770662156877486936653 684663998308829057601245)
                ·
                  refine ⟨256748999365810896600467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684663998308829057601245 256748999365810896600467)
                  ·
                    rfl

theorem cell21_1125038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_1125038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125038 prefixEnd_1125038 := by exact prefixLift 1125038
  have htrace : WordTrace (prefixWord ++ tailWord_1125038) baseStart_1125038 baseEnd_1125038 := by
    simpa [prefixWord, tailWord_1125038, baseEnd_1125038] using wordTrace_append hprefix tailTrace_1125038
  have hstable : (prefixWord ++ tailWord_1125038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125038).length < 2 ^ (prefixWord ++ tailWord_1125038).sum := by decide
  have hdescent : baseEnd_1125038 < baseStart_1125038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125153 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1125153 : Nat := 118140960795 + 1125153 * 2 ^ 59
def prefixEnd_1125153 : Nat := 4983230072969 + 3 ^ 40 * 1125153 * 2
def baseEnd_1125153 : Nat := 256775243932596252183565

theorem tailTrace_1125153 : CollatzResearch.WordTrace tailWord_1125153 prefixEnd_1125153 256775243932596252183565 := by
  unfold tailWord_1125153
  simp only [CollatzResearch.WordTrace]
  refine ⟨41037701292770316678804113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27358467528513544452536075 41037701292770316678804113)
  ·
    refine ⟨30778275969577737509103085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41037701292770316678804113 30778275969577737509103085)
    ·
      refine ⟨11541853488591651565913657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30778275969577737509103085 11541853488591651565913657)
      ·
        refine ⟨8656390116443738674435243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11541853488591651565913657 8656390116443738674435243)
        ·
          refine ⟨12984585174665608011652865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656390116443738674435243 12984585174665608011652865)
          ·
            refine ⟨9738438880999206008739649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12984585174665608011652865 9738438880999206008739649)
            ·
              refine ⟨7303829160749404506554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738438880999206008739649 7303829160749404506554737)
              ·
                refine ⟨5477871870562053379916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303829160749404506554737 5477871870562053379916053)
                ·
                  refine ⟨256775243932596252183565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5477871870562053379916053 256775243932596252183565)
                  ·
                    rfl

theorem cell21_1125153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1125153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125153 prefixEnd_1125153 := by exact prefixLift 1125153
  have htrace : WordTrace (prefixWord ++ tailWord_1125153) baseStart_1125153 baseEnd_1125153 := by
    simpa [prefixWord, tailWord_1125153, baseEnd_1125153] using wordTrace_append hprefix tailTrace_1125153
  have hstable : (prefixWord ++ tailWord_1125153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125153).length < 2 ^ (prefixWord ++ tailWord_1125153).sum := by decide
  have hdescent : baseEnd_1125153 < baseStart_1125153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125218 : List Nat := [3, 3, 2, 1, 4, 1, 7]
def baseStart_1125218 : Nat := 118140960795 + 1125218 * 2 ^ 59
def prefixEnd_1125218 : Nat := 4983230072969 + 3 ^ 40 * 1125218 * 2
def baseEnd_1125218 : Nat := 28532230868685620400011

theorem tailTrace_1125218 : CollatzResearch.WordTrace tailWord_1125218 prefixEnd_1125218 28532230868685620400011 := by
  unfold tailWord_1125218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260018009383708194980077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27360048025023221853280205 10260018009383708194980077)
  ·
    refine ⟨3847506753518890573117529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10260018009383708194980077 3847506753518890573117529)
    ·
      refine ⟨2885630065139167929838147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3847506753518890573117529 2885630065139167929838147)
      ·
        refine ⟨4328445097708751894757221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885630065139167929838147 4328445097708751894757221)
        ·
          refine ⟨811583455820390980266979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4328445097708751894757221 811583455820390980266979)
          ·
            refine ⟨1217375183730586470400469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811583455820390980266979 1217375183730586470400469)
            ·
              refine ⟨28532230868685620400011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1217375183730586470400469 28532230868685620400011)
              ·
                rfl

theorem cell21_1125218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 7].length) (baseStart_1125218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125218 prefixEnd_1125218 := by exact prefixLift 1125218
  have htrace : WordTrace (prefixWord ++ tailWord_1125218) baseStart_1125218 baseEnd_1125218 := by
    simpa [prefixWord, tailWord_1125218, baseEnd_1125218] using wordTrace_append hprefix tailTrace_1125218
  have hstable : (prefixWord ++ tailWord_1125218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125218).length < 2 ^ (prefixWord ++ tailWord_1125218).sum := by decide
  have hdescent : baseEnd_1125218 < baseStart_1125218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125243 : List Nat := [1, 1, 1, 1, 1, 5, 3, 8]
def baseStart_1125243 : Nat := 118140960795 + 1125243 * 2 ^ 59
def prefixEnd_1125243 : Nat := 4983230072969 + 3 ^ 40 * 1125243 * 2
def baseEnd_1125243 : Nat := 85598594386258698561127

theorem tailTrace_1125243 : CollatzResearch.WordTrace tailWord_1125243 prefixEnd_1125243 85598594386258698561127 := by
  unfold tailWord_1125243
  simp only [CollatzResearch.WordTrace]
  refine ⟨41040983862444262049580383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27360655908296174699720255 41040983862444262049580383)
  ·
    refine ⟨61561475793666393074370575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41040983862444262049580383 61561475793666393074370575)
    ·
      refine ⟨92342213690499589611555863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61561475793666393074370575 92342213690499589611555863)
      ·
        refine ⟨138513320535749384417333795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92342213690499589611555863 138513320535749384417333795)
        ·
          refine ⟨207769980803624076626000693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138513320535749384417333795 207769980803624076626000693)
          ·
            refine ⟨19478435700339757183687565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207769980803624076626000693 19478435700339757183687565)
            ·
              refine ⟨7304413387627408943882837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19478435700339757183687565 7304413387627408943882837)
              ·
                refine ⟨85598594386258698561127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7304413387627408943882837 85598594386258698561127)
                ·
                  rfl

theorem cell21_1125243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_1125243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125243 prefixEnd_1125243 := by exact prefixLift 1125243
  have htrace : WordTrace (prefixWord ++ tailWord_1125243) baseStart_1125243 baseEnd_1125243 := by
    simpa [prefixWord, tailWord_1125243, baseEnd_1125243] using wordTrace_append hprefix tailTrace_1125243
  have hstable : (prefixWord ++ tailWord_1125243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125243).length < 2 ^ (prefixWord ++ tailWord_1125243).sum := by decide
  have hdescent : baseEnd_1125243 < baseStart_1125243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125291 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 3]
def baseStart_1125291 : Nat := 118140960795 + 1125291 * 2 ^ 59
def prefixEnd_1125291 : Nat := 4983230072969 + 3 ^ 40 * 1125291 * 2
def baseEnd_1125291 : Nat := 256806737412738678883283

theorem tailTrace_1125291 : CollatzResearch.WordTrace tailWord_1125291 prefixEnd_1125291 256806737412738678883283 := by
  unfold tailWord_1125291
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042734566270366247327727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27361823044180244164885151 41042734566270366247327727)
  ·
    refine ⟨61564101849405549370991591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41042734566270366247327727 61564101849405549370991591)
    ·
      refine ⟨92346152774108324056487387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61564101849405549370991591 92346152774108324056487387)
      ·
        refine ⟨138519229161162486084731081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92346152774108324056487387 138519229161162486084731081)
        ·
          refine ⟨103889421870871864563548311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138519229161162486084731081 103889421870871864563548311)
          ·
            refine ⟨155834132806307796845322467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103889421870871864563548311 155834132806307796845322467)
            ·
              refine ⟨233751199209461695267983701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155834132806307796845322467 233751199209461695267983701)
              ·
                refine ⟨684817966433969810355421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 233751199209461695267983701 684817966433969810355421)
                ·
                  refine ⟨256806737412738678883283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684817966433969810355421 256806737412738678883283)
                  ·
                    rfl

theorem cell21_1125291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 3].length) (baseStart_1125291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125291 prefixEnd_1125291 := by exact prefixLift 1125291
  have htrace : WordTrace (prefixWord ++ tailWord_1125291) baseStart_1125291 baseEnd_1125291 := by
    simpa [prefixWord, tailWord_1125291, baseEnd_1125291] using wordTrace_append hprefix tailTrace_1125291
  have hstable : (prefixWord ++ tailWord_1125291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125291).length < 2 ^ (prefixWord ++ tailWord_1125291).sum := by decide
  have hdescent : baseEnd_1125291 < baseStart_1125291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125319 : List Nat := [1, 1, 4, 1, 1, 2, 2, 9]
def baseStart_1125319 : Nat := 118140960795 + 1125319 * 2 ^ 59
def prefixEnd_1125319 : Nat := 4983230072969 + 3 ^ 40 * 1125319 * 2
def baseEnd_1125319 : Nat := 85604375798072284138853

theorem tailTrace_1125319 : CollatzResearch.WordTrace tailWord_1125319 prefixEnd_1125319 85604375798072284138853 := by
  unfold tailWord_1125319
  simp only [CollatzResearch.WordTrace]
  refine ⟨41043755810168927029347011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27362503873445951352898007 41043755810168927029347011)
  ·
    refine ⟨61565633715253390544020517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41043755810168927029347011 61565633715253390544020517)
    ·
      refine ⟨11543556321610010727003847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61565633715253390544020517 11543556321610010727003847)
      ·
        refine ⟨17315334482415016090505771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11543556321610010727003847 17315334482415016090505771)
        ·
          refine ⟨25973001723622524135758657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17315334482415016090505771 25973001723622524135758657)
          ·
            refine ⟨19479751292716893101818993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25973001723622524135758657 19479751292716893101818993)
            ·
              refine ⟨14609813469537669826364245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19479751292716893101818993 14609813469537669826364245)
              ·
                refine ⟨85604375798072284138853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14609813469537669826364245 85604375798072284138853)
                ·
                  rfl

theorem cell21_1125319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_1125319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125319 prefixEnd_1125319 := by exact prefixLift 1125319
  have htrace : WordTrace (prefixWord ++ tailWord_1125319) baseStart_1125319 baseEnd_1125319 := by
    simpa [prefixWord, tailWord_1125319, baseEnd_1125319] using wordTrace_append hprefix tailTrace_1125319
  have hstable : (prefixWord ++ tailWord_1125319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125319).length < 2 ^ (prefixWord ++ tailWord_1125319).sum := by decide
  have hdescent : baseEnd_1125319 < baseStart_1125319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125384 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_1125384 : Nat := 118140960795 + 1125384 * 2 ^ 59
def prefixEnd_1125384 : Nat := 4983230072969 + 3 ^ 40 * 1125384 * 2
def baseEnd_1125384 : Nat := 256827961279791183833093

theorem tailTrace_1125384 : CollatzResearch.WordTrace tailWord_1125384 prefixEnd_1125384 256827961279791183833093 := by
  unfold tailWord_1125384
  simp only [CollatzResearch.WordTrace]
  refine ⟨20523063277466721565231603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27364084369955628753642137 20523063277466721565231603)
  ·
    refine ⟨30784594916200082347847405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20523063277466721565231603 30784594916200082347847405)
    ·
      refine ⟨11544223093575030880442777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30784594916200082347847405 11544223093575030880442777)
      ·
        refine ⟨8658167320181273160332083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11544223093575030880442777 8658167320181273160332083)
        ·
          refine ⟨12987250980271909740498125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8658167320181273160332083 12987250980271909740498125)
          ·
            refine ⟨4870219117601966152686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12987250980271909740498125 4870219117601966152686797)
            ·
              refine ⟨1826332169100737307257549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4870219117601966152686797 1826332169100737307257549)
              ·
                refine ⟨684874563412776490221581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1826332169100737307257549 684874563412776490221581)
                ·
                  refine ⟨256827961279791183833093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684874563412776490221581 256827961279791183833093)
                  ·
                    rfl

theorem cell21_1125384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_1125384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125384 prefixEnd_1125384 := by exact prefixLift 1125384
  have htrace : WordTrace (prefixWord ++ tailWord_1125384) baseStart_1125384 baseEnd_1125384 := by
    simpa [prefixWord, tailWord_1125384, baseEnd_1125384] using wordTrace_append hprefix tailTrace_1125384
  have hstable : (prefixWord ++ tailWord_1125384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125384).length < 2 ^ (prefixWord ++ tailWord_1125384).sum := by decide
  have hdescent : baseEnd_1125384 < baseStart_1125384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125412 : List Nat := [2, 3, 1, 4, 1, 1, 1, 8]
def baseStart_1125412 : Nat := 118140960795 + 1125412 * 2 ^ 59
def prefixEnd_1125412 : Nat := 4983230072969 + 3 ^ 40 * 1125412 * 2
def baseEnd_1125412 : Nat := 85611450420423119122123

theorem tailTrace_1125412 : CollatzResearch.WordTrace tailWord_1125412 prefixEnd_1125412 85611450420423119122123 := by
  unfold tailWord_1125412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20523573899416001956241245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27364765199221335941654993 20523573899416001956241245)
  ·
    refine ⟨7696340212281000733590467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20523573899416001956241245 7696340212281000733590467)
    ·
      refine ⟨11544510318421501100385701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7696340212281000733590467 11544510318421501100385701)
      ·
        refine ⟨2164595684704031456322319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11544510318421501100385701 2164595684704031456322319)
        ·
          refine ⟨3246893527056047184483479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164595684704031456322319 3246893527056047184483479)
          ·
            refine ⟨4870340290584070776725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246893527056047184483479 4870340290584070776725219)
            ·
              refine ⟨7305510435876106165087829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870340290584070776725219 7305510435876106165087829)
              ·
                refine ⟨85611450420423119122123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7305510435876106165087829 85611450420423119122123)
                ·
                  rfl

theorem cell21_1125412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_1125412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125412 prefixEnd_1125412 := by exact prefixLift 1125412
  have htrace : WordTrace (prefixWord ++ tailWord_1125412) baseStart_1125412 baseEnd_1125412 := by
    simpa [prefixWord, tailWord_1125412, baseEnd_1125412] using wordTrace_append hprefix tailTrace_1125412
  have hstable : (prefixWord ++ tailWord_1125412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125412).length < 2 ^ (prefixWord ++ tailWord_1125412).sum := by decide
  have hdescent : baseEnd_1125412 < baseStart_1125412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125415 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_1125415 : Nat := 118140960795 + 1125415 * 2 ^ 59
def prefixEnd_1125415 : Nat := 4983230072969 + 3 ^ 40 * 1125415 * 2
def baseEnd_1125415 : Nat := 256835035902142018816363

theorem tailTrace_1125415 : CollatzResearch.WordTrace tailWord_1125415 prefixEnd_1125415 256835035902142018816363 := by
  unfold tailWord_1125415
  simp only [CollatzResearch.WordTrace]
  refine ⟨41047257217821135424841699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27364838145214090283227799 41047257217821135424841699)
  ·
    refine ⟨61570885826731703137262549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41047257217821135424841699 61570885826731703137262549)
    ·
      refine ⟨1443067636564024292279591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 61570885826731703137262549 1443067636564024292279591)
      ·
        refine ⟨2164601454846036438419387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443067636564024292279591 2164601454846036438419387)
        ·
          refine ⟨3246902182269054657629081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164601454846036438419387 3246902182269054657629081)
          ·
            refine ⟨2435176636701790993221811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246902182269054657629081 2435176636701790993221811)
            ·
              refine ⟨3652764955052686489832717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435176636701790993221811 3652764955052686489832717)
              ·
                refine ⟨1369786858144757433687269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652764955052686489832717 1369786858144757433687269)
                ·
                  refine ⟨256835035902142018816363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369786858144757433687269 256835035902142018816363)
                  ·
                    rfl

theorem cell21_1125415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_1125415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125415 prefixEnd_1125415 := by exact prefixLift 1125415
  have htrace : WordTrace (prefixWord ++ tailWord_1125415) baseStart_1125415 baseEnd_1125415 := by
    simpa [prefixWord, tailWord_1125415, baseEnd_1125415] using wordTrace_append hprefix tailTrace_1125415
  have hstable : (prefixWord ++ tailWord_1125415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125415).length < 2 ^ (prefixWord ++ tailWord_1125415).sum := by decide
  have hdescent : baseEnd_1125415 < baseStart_1125415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125426 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1125426 : Nat := 118140960795 + 1125426 * 2 ^ 59
def prefixEnd_1125426 : Nat := 4983230072969 + 3 ^ 40 * 1125426 * 2
def baseEnd_1125426 : Nat := 256837546252008444133007

theorem tailTrace_1125426 : CollatzResearch.WordTrace tailWord_1125426 prefixEnd_1125426 256837546252008444133007 := by
  unfold tailWord_1125426
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261914605195321075873033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27365105613854189535661421 10261914605195321075873033)
  ·
    refine ⟨7696435953896490806904775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10261914605195321075873033 7696435953896490806904775)
    ·
      refine ⟨11544653930844736210357163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7696435953896490806904775 11544653930844736210357163)
      ·
        refine ⟨17316980896267104315535745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11544653930844736210357163 17316980896267104315535745)
        ·
          refine ⟨12987735672200328236651809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17316980896267104315535745 12987735672200328236651809)
          ·
            refine ⟨9740801754150246177488857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12987735672200328236651809 9740801754150246177488857)
            ·
              refine ⟨7305601315612684633116643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9740801754150246177488857 7305601315612684633116643)
              ·
                refine ⟨10958401973419026949674965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305601315612684633116643 10958401973419026949674965)
                ·
                  refine ⟨256837546252008444133007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10958401973419026949674965 256837546252008444133007)
                  ·
                    rfl

theorem cell21_1125426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1125426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125426 prefixEnd_1125426 := by exact prefixLift 1125426
  have htrace : WordTrace (prefixWord ++ tailWord_1125426) baseStart_1125426 baseEnd_1125426 := by
    simpa [prefixWord, tailWord_1125426, baseEnd_1125426] using wordTrace_append hprefix tailTrace_1125426
  have hstable : (prefixWord ++ tailWord_1125426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125426).length < 2 ^ (prefixWord ++ tailWord_1125426).sum := by decide
  have hdescent : baseEnd_1125426 < baseStart_1125426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125443 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 3]
def baseStart_1125443 : Nat := 118140960795 + 1125443 * 2 ^ 59
def prefixEnd_1125443 : Nat := 4983230072969 + 3 ^ 40 * 1125443 * 2
def baseEnd_1125443 : Nat := 256841425883620192349639

theorem tailTrace_1125443 : CollatzResearch.WordTrace tailWord_1125443 prefixEnd_1125443 256841425883620192349639 := by
  unfold tailWord_1125443
  simp only [CollatzResearch.WordTrace]
  refine ⟨41048278461719696206860983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27365518974479797471240655 41048278461719696206860983)
  ·
    refine ⟨61572417692579544310291475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41048278461719696206860983 61572417692579544310291475)
    ·
      refine ⟨92358626538869316465437213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61572417692579544310291475 92358626538869316465437213)
      ·
        refine ⟨34634484952075993674538955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92358626538869316465437213 34634484952075993674538955)
        ·
          refine ⟨51951727428113990511808433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34634484952075993674538955 51951727428113990511808433)
          ·
            refine ⟨38963795571085492883856325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51951727428113990511808433 38963795571085492883856325)
            ·
              refine ⟨7305711669578529915723061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38963795571085492883856325 7305711669578529915723061)
              ·
                refine ⟨684910469022987179599037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7305711669578529915723061 684910469022987179599037)
                ·
                  refine ⟨256841425883620192349639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684910469022987179599037 256841425883620192349639)
                  ·
                    rfl

theorem cell21_1125443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].length) (baseStart_1125443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125443 prefixEnd_1125443 := by exact prefixLift 1125443
  have htrace : WordTrace (prefixWord ++ tailWord_1125443) baseStart_1125443 baseEnd_1125443 := by
    simpa [prefixWord, tailWord_1125443, baseEnd_1125443] using wordTrace_append hprefix tailTrace_1125443
  have hstable : (prefixWord ++ tailWord_1125443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125443).length < 2 ^ (prefixWord ++ tailWord_1125443).sum := by decide
  have hdescent : baseEnd_1125443 < baseStart_1125443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125457 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_1125457 : Nat := 118140960795 + 1125457 * 2 ^ 59
def prefixEnd_1125457 : Nat := 4983230072969 + 3 ^ 40 * 1125457 * 2
def baseEnd_1125457 : Nat := 256844620874359279116277

theorem tailTrace_1125457 : CollatzResearch.WordTrace tailWord_1125457 prefixEnd_1125457 256844620874359279116277 := by
  unfold tailWord_1125457
  simp only [CollatzResearch.WordTrace]
  refine ⟨41048789083668976597870625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27365859389112651065247083 41048789083668976597870625)
  ·
    refine ⟨30786591812751732448402969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41048789083668976597870625 30786591812751732448402969)
    ·
      refine ⟨23089943859563799336302227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30786591812751732448402969 23089943859563799336302227)
      ·
        refine ⟨34634915789345699004453341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23089943859563799336302227 34634915789345699004453341)
        ·
          refine ⟨12988093421004637126670003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34634915789345699004453341 12988093421004637126670003)
          ·
            refine ⟨19482140131506955690005005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12988093421004637126670003 19482140131506955690005005)
            ·
              refine ⟨7305802549315108383751877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19482140131506955690005005 7305802549315108383751877)
              ·
                refine ⟨1369837977996582821953477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7305802549315108383751877 1369837977996582821953477)
                ·
                  refine ⟨256844620874359279116277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369837977996582821953477 256844620874359279116277)
                  ·
                    rfl

theorem cell21_1125457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_1125457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125457 prefixEnd_1125457 := by exact prefixLift 1125457
  have htrace : WordTrace (prefixWord ++ tailWord_1125457) baseStart_1125457 baseEnd_1125457 := by
    simpa [prefixWord, tailWord_1125457, baseEnd_1125457] using wordTrace_append hprefix tailTrace_1125457
  have hstable : (prefixWord ++ tailWord_1125457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125457).length < 2 ^ (prefixWord ++ tailWord_1125457).sum := by decide
  have hdescent : baseEnd_1125457 < baseStart_1125457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125488 : List Nat := [2, 1, 1, 1, 5, 1, 5, 5]
def baseStart_1125488 : Nat := 118140960795 + 1125488 * 2 ^ 59
def prefixEnd_1125488 : Nat := 4983230072969 + 3 ^ 40 * 1125488 * 2
def baseEnd_1125488 : Nat := 85617231832236704699849

theorem tailTrace_1125488 : CollatzResearch.WordTrace tailWord_1125488 prefixEnd_1125488 85617231832236704699849 := by
  unfold tailWord_1125488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20524959873278334446124559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27366613164371112594832745 20524959873278334446124559)
  ·
    refine ⟨30787439809917501669186839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20524959873278334446124559 30787439809917501669186839)
    ·
      refine ⟨46181159714876252503780259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30787439809917501669186839 46181159714876252503780259)
      ·
        refine ⟨69271739572314378755670389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46181159714876252503780259 69271739572314378755670389)
        ·
          refine ⟨6494225584904473008344099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69271739572314378755670389 6494225584904473008344099)
          ·
            refine ⟨9741338377356709512516149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494225584904473008344099 9741338377356709512516149)
            ·
              refine ⟨913250472877191516798389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9741338377356709512516149 913250472877191516798389)
              ·
                refine ⟨85617231832236704699849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 913250472877191516798389 85617231832236704699849)
                ·
                  rfl

theorem cell21_1125488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_1125488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125488 prefixEnd_1125488 := by exact prefixLift 1125488
  have htrace : WordTrace (prefixWord ++ tailWord_1125488) baseStart_1125488 baseEnd_1125488 := by
    simpa [prefixWord, tailWord_1125488, baseEnd_1125488] using wordTrace_append hprefix tailTrace_1125488
  have hstable : (prefixWord ++ tailWord_1125488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125488).length < 2 ^ (prefixWord ++ tailWord_1125488).sum := by decide
  have hdescent : baseEnd_1125488 < baseStart_1125488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125553 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 3]
def baseStart_1125553 : Nat := 118140960795 + 1125553 * 2 ^ 59
def prefixEnd_1125553 : Nat := 4983230072969 + 3 ^ 40 * 1125553 * 2
def baseEnd_1125553 : Nat := 256866529382284445516081

theorem tailTrace_1125553 : CollatzResearch.WordTrace tailWord_1125553 prefixEnd_1125553 256866529382284445516081 := by
  unfold tailWord_1125553
  simp only [CollatzResearch.WordTrace]
  refine ⟨41052290491321184993365313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27368193660880789995576875 41052290491321184993365313)
  ·
    refine ⟨30789217868490888745023985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41052290491321184993365313 30789217868490888745023985)
    ·
      refine ⟨23091913401368166558767989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30789217868490888745023985 23091913401368166558767989)
      ·
        refine ⟨2164866881378265614884499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23091913401368166558767989 2164866881378265614884499)
        ·
          refine ⟨3247300322067398422326749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164866881378265614884499 3247300322067398422326749)
          ·
            refine ⟨1217737620775274408372531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3247300322067398422326749 1217737620775274408372531)
            ·
              refine ⟨1826606431162911612558797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217737620775274408372531 1826606431162911612558797)
              ·
                refine ⟨684977411686091854709549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1826606431162911612558797 684977411686091854709549)
                ·
                  refine ⟨256866529382284445516081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684977411686091854709549 256866529382284445516081)
                  ·
                    rfl

theorem cell21_1125553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_1125553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125553 prefixEnd_1125553 := by exact prefixLift 1125553
  have htrace : WordTrace (prefixWord ++ tailWord_1125553) baseStart_1125553 baseEnd_1125553 := by
    simpa [prefixWord, tailWord_1125553, baseEnd_1125553] using wordTrace_append hprefix tailTrace_1125553
  have hstable : (prefixWord ++ tailWord_1125553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125553).length < 2 ^ (prefixWord ++ tailWord_1125553).sum := by decide
  have hdescent : baseEnd_1125553 < baseStart_1125553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125564 : List Nat := [2, 2, 2, 3, 2, 3, 7]
def baseStart_1125564 : Nat := 118140960795 + 1125564 * 2 ^ 59
def prefixEnd_1125564 : Nat := 4983230072969 + 3 ^ 40 * 1125564 * 2
def baseEnd_1125564 : Nat := 28541004414683430092525

theorem tailTrace_1125564 : CollatzResearch.WordTrace tailWord_1125564 prefixEnd_1125564 28541004414683430092525 := by
  unfold tailWord_1125564
  simp only [CollatzResearch.WordTrace]
  refine ⟨20526345847140666936007873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27368461129520889248010497 20526345847140666936007873)
  ·
    refine ⟨15394759385355500202005905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20526345847140666936007873 15394759385355500202005905)
    ·
      refine ⟨11546069539016625151504429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15394759385355500202005905 11546069539016625151504429)
      ·
        refine ⟨4329776077131234431814161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11546069539016625151504429 4329776077131234431814161)
        ·
          refine ⟨3247332057848425823860621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4329776077131234431814161 3247332057848425823860621)
          ·
            refine ⟨1217749521693159683947733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3247332057848425823860621 1217749521693159683947733)
            ·
              refine ⟨28541004414683430092525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1217749521693159683947733 28541004414683430092525)
              ·
                rfl

theorem cell21_1125564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 7].length) (baseStart_1125564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125564 prefixEnd_1125564 := by exact prefixLift 1125564
  have htrace : WordTrace (prefixWord ++ tailWord_1125564) baseStart_1125564 baseEnd_1125564 := by
    simpa [prefixWord, tailWord_1125564, baseEnd_1125564] using wordTrace_append hprefix tailTrace_1125564
  have hstable : (prefixWord ++ tailWord_1125564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125564).length < 2 ^ (prefixWord ++ tailWord_1125564).sum := by decide
  have hdescent : baseEnd_1125564 < baseStart_1125564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125570 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1125570 : Nat := 118140960795 + 1125570 * 2 ^ 59
def prefixEnd_1125570 : Nat := 4983230072969 + 3 ^ 40 * 1125570 * 2
def baseEnd_1125570 : Nat := 256870409013896193732713

theorem tailTrace_1125570 : CollatzResearch.WordTrace tailWord_1125570 prefixEnd_1125570 256870409013896193732713 := by
  unfold tailWord_1125570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10263227633064899224183541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27368607021506397931156109 10263227633064899224183541)
  ·
    refine ⟨962177590599834302267207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10263227633064899224183541 962177590599834302267207)
    ·
      refine ⟨1443266385899751453400811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962177590599834302267207 1443266385899751453400811)
      ·
        refine ⟨2164899578849627180101217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443266385899751453400811 2164899578849627180101217)
        ·
          refine ⟨1623674684137220385075913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164899578849627180101217 1623674684137220385075913)
          ·
            refine ⟨1217756013102915288806935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623674684137220385075913 1217756013102915288806935)
            ·
              refine ⟨1826634019654372933210403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217756013102915288806935 1826634019654372933210403)
              ·
                refine ⟨2739951029481559399815605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826634019654372933210403 2739951029481559399815605)
                ·
                  refine ⟨256870409013896193732713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739951029481559399815605 256870409013896193732713)
                  ·
                    rfl

theorem cell21_1125570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1125570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125570 prefixEnd_1125570 := by exact prefixLift 1125570
  have htrace : WordTrace (prefixWord ++ tailWord_1125570) baseStart_1125570 baseEnd_1125570 := by
    simpa [prefixWord, tailWord_1125570, baseEnd_1125570] using wordTrace_append hprefix tailTrace_1125570
  have hstable : (prefixWord ++ tailWord_1125570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125570).length < 2 ^ (prefixWord ++ tailWord_1125570).sum := by decide
  have hdescent : baseEnd_1125570 < baseStart_1125570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125685 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1125685 : Nat := 118140960795 + 1125685 * 2 ^ 59
def prefixEnd_1125685 : Nat := 4983230072969 + 3 ^ 40 * 1125685 * 2
def baseEnd_1125685 : Nat := 256896653580681549315811

theorem tailTrace_1125685 : CollatzResearch.WordTrace tailWord_1125685 prefixEnd_1125685 256896653580681549315811 := by
  unfold tailWord_1125685
  simp only [CollatzResearch.WordTrace]
  refine ⟨41057104926842971537170509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27371403284561981024780339 41057104926842971537170509)
  ·
    refine ⟨15396414347566114326438941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41057104926842971537170509 15396414347566114326438941)
    ·
      refine ⟨5773655380337292872414603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15396414347566114326438941 5773655380337292872414603)
      ·
        refine ⟨8660483070505939308621905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773655380337292872414603 8660483070505939308621905)
        ·
          refine ⟨6495362302879454481466429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8660483070505939308621905 6495362302879454481466429)
          ·
            refine ⟨2435760863579795430549911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6495362302879454481466429 2435760863579795430549911)
            ·
              refine ⟨3653641295369693145824867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435760863579795430549911 3653641295369693145824867)
              ·
                refine ⟨5480461943054539718737301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653641295369693145824867 5480461943054539718737301)
                ·
                  refine ⟨256896653580681549315811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5480461943054539718737301 256896653580681549315811)
                  ·
                    rfl

theorem cell21_1125685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1125685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125685 prefixEnd_1125685 := by exact prefixLift 1125685
  have htrace : WordTrace (prefixWord ++ tailWord_1125685) baseStart_1125685 baseEnd_1125685 := by
    simpa [prefixWord, tailWord_1125685, baseEnd_1125685] using wordTrace_append hprefix tailTrace_1125685
  have hstable : (prefixWord ++ tailWord_1125685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125685).length < 2 ^ (prefixWord ++ tailWord_1125685).sum := by decide
  have hdescent : baseEnd_1125685 < baseStart_1125685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125744 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1125744 : Nat := 118140960795 + 1125744 * 2 ^ 59
def prefixEnd_1125744 : Nat := 4983230072969 + 3 ^ 40 * 1125744 * 2
def baseEnd_1125744 : Nat := 256910118184510557832357

theorem tailTrace_1125744 : CollatzResearch.WordTrace tailWord_1125744 prefixEnd_1125744 256910118184510557832357 := by
  unfold tailWord_1125744
  simp only [CollatzResearch.WordTrace]
  refine ⟨20529628416814612306784143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27372837889086149742378857 20529628416814612306784143)
  ·
    refine ⟨30794442625221918460176215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20529628416814612306784143 30794442625221918460176215)
    ·
      refine ⟨46191663937832877690264323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30794442625221918460176215 46191663937832877690264323)
      ·
        refine ⟨69287495906749316535396485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46191663937832877690264323 69287495906749316535396485)
        ·
          refine ⟨12991405482515496850386841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69287495906749316535396485 12991405482515496850386841)
          ·
            refine ⟨9743554111886622637790131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12991405482515496850386841 9743554111886622637790131)
            ·
              refine ⟨14615331167829933956685197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9743554111886622637790131 14615331167829933956685197)
              ·
                refine ⟨5480749187936225233756949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14615331167829933956685197 5480749187936225233756949)
                ·
                  refine ⟨256910118184510557832357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5480749187936225233756949 256910118184510557832357)
                  ·
                    rfl

theorem cell21_1125744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1125744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125744 prefixEnd_1125744 := by exact prefixLift 1125744
  have htrace : WordTrace (prefixWord ++ tailWord_1125744) baseStart_1125744 baseEnd_1125744 := by
    simpa [prefixWord, tailWord_1125744, baseEnd_1125744] using wordTrace_append hprefix tailTrace_1125744
  have hstable : (prefixWord ++ tailWord_1125744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125744).length < 2 ^ (prefixWord ++ tailWord_1125744).sum := by decide
  have hdescent : baseEnd_1125744 < baseStart_1125744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125896 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1125896 : Nat := 118140960795 + 1125896 * 2 ^ 59
def prefixEnd_1125896 : Nat := 4983230072969 + 3 ^ 40 * 1125896 * 2
def baseEnd_1125896 : Nat := 256944806655392071298713

theorem tailTrace_1125896 : CollatzResearch.WordTrace tailWord_1125896 prefixEnd_1125896 256944806655392071298713 := by
  unfold tailWord_1125896
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532400364539277286550771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27376533819385703048734361 20532400364539277286550771)
  ·
    refine ⟨30798600546808915929826157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20532400364539277286550771 30798600546808915929826157)
    ·
      refine ⟨11549475205053343473684809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30798600546808915929826157 11549475205053343473684809)
      ·
        refine ⟨8662106403790007605263607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11549475205053343473684809 8662106403790007605263607)
        ·
          refine ⟨12993159605685011407895411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662106403790007605263607 12993159605685011407895411)
          ·
            refine ⟨19489739408527517111843117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993159605685011407895411 19489739408527517111843117)
            ·
              refine ⟨7308652278197818916941169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19489739408527517111843117 7308652278197818916941169)
              ·
                refine ⟨5481489208648364187705877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7308652278197818916941169 5481489208648364187705877)
                ·
                  refine ⟨256944806655392071298713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5481489208648364187705877 256944806655392071298713)
                  ·
                    rfl

theorem cell21_1125896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1125896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125896 prefixEnd_1125896 := by exact prefixLift 1125896
  have htrace : WordTrace (prefixWord ++ tailWord_1125896) baseStart_1125896 baseEnd_1125896 := by
    simpa [prefixWord, tailWord_1125896, baseEnd_1125896] using wordTrace_append hprefix tailTrace_1125896
  have hstable : (prefixWord ++ tailWord_1125896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125896).length < 2 ^ (prefixWord ++ tailWord_1125896).sum := by decide
  have hdescent : baseEnd_1125896 < baseStart_1125896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125916 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1125916 : Nat := 118140960795 + 1125916 * 2 ^ 59
def prefixEnd_1125916 : Nat := 4983230072969 + 3 ^ 40 * 1125916 * 2
def baseEnd_1125916 : Nat := 256949370927876480965339

theorem tailTrace_1125916 : CollatzResearch.WordTrace tailWord_1125916 prefixEnd_1125916 256949370927876480965339 := by
  unfold tailWord_1125916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532765094503048994414801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27377020126004065325886401 20532765094503048994414801)
  ·
    refine ⟨15399573820877286745811101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20532765094503048994414801 15399573820877286745811101)
    ·
      refine ⟨5774840182828982529679163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15399573820877286745811101 5774840182828982529679163)
      ·
        refine ⟨8662260274243473794518745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5774840182828982529679163 8662260274243473794518745)
        ·
          refine ⟨6496695205682605345889059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8662260274243473794518745 6496695205682605345889059)
          ·
            refine ⟨9745042808523908018833589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496695205682605345889059 9745042808523908018833589)
            ·
              refine ⟨913597763299116376765649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9745042808523908018833589 913597763299116376765649)
              ·
                refine ⟨685198322474337282574237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913597763299116376765649 685198322474337282574237)
                ·
                  refine ⟨256949370927876480965339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685198322474337282574237 256949370927876480965339)
                  ·
                    rfl

theorem cell21_1125916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1125916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125916 prefixEnd_1125916 := by exact prefixLift 1125916
  have htrace : WordTrace (prefixWord ++ tailWord_1125916) baseStart_1125916 baseEnd_1125916 := by
    simpa [prefixWord, tailWord_1125916, baseEnd_1125916] using wordTrace_append hprefix tailTrace_1125916
  have hstable : (prefixWord ++ tailWord_1125916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125916).length < 2 ^ (prefixWord ++ tailWord_1125916).sum := by decide
  have hdescent : baseEnd_1125916 < baseStart_1125916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125975 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 3]
def baseStart_1125975 : Nat := 118140960795 + 1125975 * 2 ^ 59
def prefixEnd_1125975 : Nat := 4983230072969 + 3 ^ 40 * 1125975 * 2
def baseEnd_1125975 : Nat := 256962835531705489481885

theorem tailTrace_1125975 : CollatzResearch.WordTrace tailWord_1125975 prefixEnd_1125975 256962835531705489481885 := by
  unfold tailWord_1125975
  simp only [CollatzResearch.WordTrace]
  refine ⟨41067682095792351065227379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27378454730528234043484919 41067682095792351065227379)
  ·
    refine ⟨61601523143688526597841069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41067682095792351065227379 61601523143688526597841069)
    ·
      refine ⟨23100571178883197474190401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61601523143688526597841069 23100571178883197474190401)
      ·
        refine ⟨17325428384162398105642801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23100571178883197474190401 17325428384162398105642801)
        ·
          refine ⟨12994071288121798579232101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17325428384162398105642801 12994071288121798579232101)
          ·
            refine ⟨2436388366522837233606019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12994071288121798579232101 2436388366522837233606019)
            ·
              refine ⟨3654582549784255850409029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436388366522837233606019 3654582549784255850409029)
              ·
                refine ⟨685234228084547971951693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3654582549784255850409029 685234228084547971951693)
                ·
                  refine ⟨256962835531705489481885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685234228084547971951693 256962835531705489481885)
                  ·
                    rfl

theorem cell21_1125975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 3].length) (baseStart_1125975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125975 prefixEnd_1125975 := by exact prefixLift 1125975
  have htrace : WordTrace (prefixWord ++ tailWord_1125975) baseStart_1125975 baseEnd_1125975 := by
    simpa [prefixWord, tailWord_1125975, baseEnd_1125975] using wordTrace_append hprefix tailTrace_1125975
  have hstable : (prefixWord ++ tailWord_1125975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125975).length < 2 ^ (prefixWord ++ tailWord_1125975).sum := by decide
  have hdescent : baseEnd_1125975 < baseStart_1125975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125989 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1125989 : Nat := 118140960795 + 1125989 * 2 ^ 59
def prefixEnd_1125989 : Nat := 4983230072969 + 3 ^ 40 * 1125989 * 2
def baseEnd_1125989 : Nat := 256966030522444576248523

theorem tailTrace_1125989 : CollatzResearch.WordTrace tailWord_1125989 prefixEnd_1125989 256966030522444576248523 := by
  unfold tailWord_1125989
  simp only [CollatzResearch.WordTrace]
  refine ⟨41068192717741631456237021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27378795145161087637491347 41068192717741631456237021)
  ·
    refine ⟨15400572269153111796088883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41068192717741631456237021 15400572269153111796088883)
    ·
      refine ⟨23100858403729667694133325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15400572269153111796088883 23100858403729667694133325)
      ·
        refine ⟨8662821901398625385299997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23100858403729667694133325 8662821901398625385299997)
        ·
          refine ⟨3248558213024484519487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8662821901398625385299997 3248558213024484519487499)
          ·
            refine ⟨4872837319536726779231249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248558213024484519487499 4872837319536726779231249)
            ·
              refine ⟨3654627989652545084423437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4872837319536726779231249 3654627989652545084423437)
              ·
                refine ⟨1370485496119704406658789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3654627989652545084423437 1370485496119704406658789)
                ·
                  refine ⟨256966030522444576248523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370485496119704406658789 256966030522444576248523)
                  ·
                    rfl

theorem cell21_1125989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1125989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1125989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1125989 prefixEnd_1125989 := by exact prefixLift 1125989
  have htrace : WordTrace (prefixWord ++ tailWord_1125989) baseStart_1125989 baseEnd_1125989 := by
    simpa [prefixWord, tailWord_1125989, baseEnd_1125989] using wordTrace_append hprefix tailTrace_1125989
  have hstable : (prefixWord ++ tailWord_1125989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125989).length < 2 ^ (prefixWord ++ tailWord_1125989).sum := by decide
  have hdescent : baseEnd_1125989 < baseStart_1125989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126200 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1126200 : Nat := 118140960795 + 1126200 * 2 ^ 59
def prefixEnd_1126200 : Nat := 4983230072969 + 3 ^ 40 * 1126200 * 2
def baseEnd_1126200 : Nat := 257014183597155098231425

theorem tailTrace_1126200 : CollatzResearch.WordTrace tailWord_1126200 prefixEnd_1126200 257014183597155098231425 := by
  unfold tailWord_1126200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20537944259988607246084027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27383925679984809661445369 20537944259988607246084027)
  ·
    refine ⟨30806916389982910869126041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20537944259988607246084027 30806916389982910869126041)
    ·
      refine ⟨23105187292487183151844531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30806916389982910869126041 23105187292487183151844531)
      ·
        refine ⟨34657780938730774727766797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23105187292487183151844531 34657780938730774727766797)
        ·
          refine ⟨12996667852024040522912549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34657780938730774727766797 12996667852024040522912549)
          ·
            refine ⟨2436875222254507598046103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12996667852024040522912549 2436875222254507598046103)
            ·
              refine ⟨3655312833381761397069155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436875222254507598046103 3655312833381761397069155)
              ·
                refine ⟨5482969250072642095603733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655312833381761397069155 5482969250072642095603733)
                ·
                  refine ⟨257014183597155098231425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5482969250072642095603733 257014183597155098231425)
                  ·
                    rfl

theorem cell21_1126200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1126200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126200 prefixEnd_1126200 := by exact prefixLift 1126200
  have htrace : WordTrace (prefixWord ++ tailWord_1126200) baseStart_1126200 baseEnd_1126200 := by
    simpa [prefixWord, tailWord_1126200, baseEnd_1126200] using wordTrace_append hprefix tailTrace_1126200
  have hstable : (prefixWord ++ tailWord_1126200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126200).length < 2 ^ (prefixWord ++ tailWord_1126200).sum := by decide
  have hdescent : baseEnd_1126200 < baseStart_1126200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126217 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 4]
def baseStart_1126217 : Nat := 118140960795 + 1126217 * 2 ^ 59
def prefixEnd_1126217 : Nat := 4983230072969 + 3 ^ 40 * 1126217 * 2
def baseEnd_1126217 : Nat := 257018063228766846448057

theorem tailTrace_1126217 : CollatzResearch.WordTrace tailWord_1126217 prefixEnd_1126217 257018063228766846448057 := by
  unfold tailWord_1126217
  simp only [CollatzResearch.WordTrace]
  refine ⟨41076508560915626395536905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27384339040610417597024603 41076508560915626395536905)
  ·
    refine ⟨30807381420686719796652679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41076508560915626395536905 30807381420686719796652679)
    ·
      refine ⟨46211072131030079694979019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30807381420686719796652679 46211072131030079694979019)
      ·
        refine ⟨69316608196545119542468529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46211072131030079694979019 69316608196545119542468529)
        ·
          refine ⟨51987456147408839656851397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69316608196545119542468529 51987456147408839656851397)
          ·
            refine ⟨9747648027639157435659637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51987456147408839656851397 9747648027639157435659637)
            ·
              refine ⟨913842002591171009593091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9747648027639157435659637 913842002591171009593091)
              ·
                refine ⟨1370763003886756514389637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913842002591171009593091 1370763003886756514389637)
                ·
                  refine ⟨257018063228766846448057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370763003886756514389637 257018063228766846448057)
                  ·
                    rfl

theorem cell21_1126217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_1126217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126217 prefixEnd_1126217 := by exact prefixLift 1126217
  have htrace : WordTrace (prefixWord ++ tailWord_1126217) baseStart_1126217 baseEnd_1126217 := by
    simpa [prefixWord, tailWord_1126217, baseEnd_1126217] using wordTrace_append hprefix tailTrace_1126217
  have hstable : (prefixWord ++ tailWord_1126217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126217).length < 2 ^ (prefixWord ++ tailWord_1126217).sum := by decide
  have hdescent : baseEnd_1126217 < baseStart_1126217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126231 : List Nat := [1, 1, 3, 2, 5, 1, 1, 7]
def baseStart_1126231 : Nat := 118140960795 + 1126231 * 2 ^ 59
def prefixEnd_1126231 : Nat := 4983230072969 + 3 ^ 40 * 1126231 * 2
def baseEnd_1126231 : Nat := 85673752739835311071565

theorem tailTrace_1126231 : CollatzResearch.WordTrace tailWord_1126231 prefixEnd_1126231 85673752739835311071565 := by
  unfold tailWord_1126231
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077019182864906786546547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27384679455243271191031031 41077019182864906786546547)
  ·
    refine ⟨61615528774297360179819821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41077019182864906786546547 61615528774297360179819821)
    ·
      refine ⟨23105823290361510067432433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61615528774297360179819821 23105823290361510067432433)
      ·
        refine ⟨17329367467771132550574325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23105823290361510067432433 17329367467771132550574325)
        ·
          refine ⟨1624628200103543676616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17329367467771132550574325 1624628200103543676616343)
          ·
            refine ⟨2436942300155315514924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624628200103543676616343 2436942300155315514924515)
            ·
              refine ⟨3655413450232973272386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436942300155315514924515 3655413450232973272386773)
              ·
                refine ⟨85673752739835311071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3655413450232973272386773 85673752739835311071565)
                ·
                  rfl

theorem cell21_1126231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_1126231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126231 prefixEnd_1126231 := by exact prefixLift 1126231
  have htrace : WordTrace (prefixWord ++ tailWord_1126231) baseStart_1126231 baseEnd_1126231 := by
    simpa [prefixWord, tailWord_1126231, baseEnd_1126231] using wordTrace_append hprefix tailTrace_1126231
  have hstable : (prefixWord ++ tailWord_1126231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126231).length < 2 ^ (prefixWord ++ tailWord_1126231).sum := by decide
  have hdescent : baseEnd_1126231 < baseStart_1126231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126397 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1126397 : Nat := 118140960795 + 1126397 * 2 ^ 59
def prefixEnd_1126397 : Nat := 4983230072969 + 3 ^ 40 * 1126397 * 2
def baseEnd_1126397 : Nat := 257059141681126533447689

theorem tailTrace_1126397 : CollatzResearch.WordTrace tailWord_1126397 prefixEnd_1126397 257059141681126533447689 := by
  unfold tailWord_1126397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083073700263517137089445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27388715800175678091392963 41083073700263517137089445)
  ·
    refine ⟨7703076318799409463204271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41083073700263517137089445 7703076318799409463204271)
    ·
      refine ⟨11554614478199114194806407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7703076318799409463204271 11554614478199114194806407)
      ·
        refine ⟨17331921717298671292209611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554614478199114194806407 17331921717298671292209611)
        ·
          refine ⟨25997882575948006938314417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17331921717298671292209611 25997882575948006938314417)
          ·
            refine ⟨19498411931961005203735813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25997882575948006938314417 19498411931961005203735813)
            ·
              refine ⟨3655952237242688475700465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19498411931961005203735813 3655952237242688475700465)
              ·
                refine ⟨2741964177932016356775349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655952237242688475700465 2741964177932016356775349)
                ·
                  refine ⟨257059141681126533447689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2741964177932016356775349 257059141681126533447689)
                  ·
                    rfl

theorem cell21_1126397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1126397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126397 prefixEnd_1126397 := by exact prefixLift 1126397
  have htrace : WordTrace (prefixWord ++ tailWord_1126397) baseStart_1126397 baseEnd_1126397 := by
    simpa [prefixWord, tailWord_1126397, baseEnd_1126397] using wordTrace_append hprefix tailTrace_1126397
  have hstable : (prefixWord ++ tailWord_1126397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126397).length < 2 ^ (prefixWord ++ tailWord_1126397).sum := by decide
  have hdescent : baseEnd_1126397 < baseStart_1126397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126411 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_1126411 : Nat := 118140960795 + 1126411 * 2 ^ 59
def prefixEnd_1126411 : Nat := 4983230072969 + 3 ^ 40 * 1126411 * 2
def baseEnd_1126411 : Nat := 257062336671865620214327

theorem tailTrace_1126411 : CollatzResearch.WordTrace tailWord_1126411 prefixEnd_1126411 257062336671865620214327 := by
  unfold tailWord_1126411
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083584322212797528099087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27389056214808531685399391 41083584322212797528099087)
  ·
    refine ⟨61625376483319196292148631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083584322212797528099087 61625376483319196292148631)
    ·
      refine ⟨92438064724978794438222947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61625376483319196292148631 92438064724978794438222947)
      ·
        refine ⟨138657097087468191657334421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92438064724978794438222947 138657097087468191657334421)
        ·
          refine ⟨6499551425975071483937551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138657097087468191657334421 6499551425975071483937551)
          ·
            refine ⟨9749327138962607225906327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499551425975071483937551 9749327138962607225906327)
            ·
              refine ⟨14623990708443910838859491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9749327138962607225906327 14623990708443910838859491)
              ·
                refine ⟨21935986062665866258289237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14623990708443910838859491 21935986062665866258289237)
                ·
                  refine ⟨257062336671865620214327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21935986062665866258289237 257062336671865620214327)
                  ·
                    rfl

theorem cell21_1126411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_1126411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126411 prefixEnd_1126411 := by exact prefixLift 1126411
  have htrace : WordTrace (prefixWord ++ tailWord_1126411) baseStart_1126411 baseEnd_1126411 := by
    simpa [prefixWord, tailWord_1126411, baseEnd_1126411] using wordTrace_append hprefix tailTrace_1126411
  have hstable : (prefixWord ++ tailWord_1126411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126411).length < 2 ^ (prefixWord ++ tailWord_1126411).sum := by decide
  have hdescent : baseEnd_1126411 < baseStart_1126411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126428 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1126428 : Nat := 118140960795 + 1126428 * 2 ^ 59
def prefixEnd_1126428 : Nat := 4983230072969 + 3 ^ 40 * 1126428 * 2
def baseEnd_1126428 : Nat := 257066216303477368430959

theorem tailTrace_1126428 : CollatzResearch.WordTrace tailWord_1126428 prefixEnd_1126428 257066216303477368430959 := by
  unfold tailWord_1126428
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542102181575604715733969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27389469575434139620978625 20542102181575604715733969)
  ·
    refine ⟨15406576636181703536800477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20542102181575604715733969 15406576636181703536800477)
    ·
      refine ⟨5777466238568138826300179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15406576636181703536800477 5777466238568138826300179)
      ·
        refine ⟨8666199357852208239450269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777466238568138826300179 8666199357852208239450269)
        ·
          refine ⟨3249824759194578089793851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8666199357852208239450269 3249824759194578089793851)
          ·
            refine ⟨4874737138791867134690777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249824759194578089793851 4874737138791867134690777)
            ·
              refine ⟨3656052854093900351018083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4874737138791867134690777 3656052854093900351018083)
              ·
                refine ⟨5484079281140850526527125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656052854093900351018083 5484079281140850526527125)
                ·
                  refine ⟨257066216303477368430959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5484079281140850526527125 257066216303477368430959)
                  ·
                    rfl

theorem cell21_1126428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1126428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126428 prefixEnd_1126428 := by exact prefixLift 1126428
  have htrace : WordTrace (prefixWord ++ tailWord_1126428) baseStart_1126428 baseEnd_1126428 := by
    simpa [prefixWord, tailWord_1126428, baseEnd_1126428] using wordTrace_append hprefix tailTrace_1126428
  have hstable : (prefixWord ++ tailWord_1126428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126428).length < 2 ^ (prefixWord ++ tailWord_1126428).sum := by decide
  have hdescent : baseEnd_1126428 < baseStart_1126428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126431 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 3]
def baseStart_1126431 : Nat := 118140960795 + 1126431 * 2 ^ 59
def prefixEnd_1126431 : Nat := 4983230072969 + 3 ^ 40 * 1126431 * 2
def baseEnd_1126431 : Nat := 257066900944350029880953

theorem tailTrace_1126431 : CollatzResearch.WordTrace tailWord_1126431 prefixEnd_1126431 257066900944350029880953 := by
  unfold tailWord_1126431
  simp only [CollatzResearch.WordTrace]
  refine ⟨41084313782140340943827147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27389542521426893962551431 41084313782140340943827147)
  ·
    refine ⟨61626470673210511415740721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41084313782140340943827147 61626470673210511415740721)
    ·
      refine ⟨46219853004907883561805541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61626470673210511415740721 46219853004907883561805541)
      ·
        refine ⟨8666222438420228167838539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46219853004907883561805541 8666222438420228167838539)
        ·
          refine ⟨12999333657630342251757809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666222438420228167838539 12999333657630342251757809)
          ·
            refine ⟨9749500243222756688818357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12999333657630342251757809 9749500243222756688818357)
            ·
              refine ⟨914015647802133439576721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9749500243222756688818357 914015647802133439576721)
              ·
                refine ⟨685511735851600079682541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914015647802133439576721 685511735851600079682541)
                ·
                  refine ⟨257066900944350029880953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685511735851600079682541 257066900944350029880953)
                  ·
                    rfl

theorem cell21_1126431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 3].length) (baseStart_1126431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126431 prefixEnd_1126431 := by exact prefixLift 1126431
  have htrace : WordTrace (prefixWord ++ tailWord_1126431) baseStart_1126431 baseEnd_1126431 := by
    simpa [prefixWord, tailWord_1126431, baseEnd_1126431] using wordTrace_append hprefix tailTrace_1126431
  have hstable : (prefixWord ++ tailWord_1126431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126431).length < 2 ^ (prefixWord ++ tailWord_1126431).sum := by decide
  have hdescent : baseEnd_1126431 < baseStart_1126431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126487 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_1126487 : Nat := 118140960795 + 1126487 * 2 ^ 59
def prefixEnd_1126487 : Nat := 4983230072969 + 3 ^ 40 * 1126487 * 2
def baseEnd_1126487 : Nat := 257079680907306376947505

theorem tailTrace_1126487 : CollatzResearch.WordTrace tailWord_1126487 prefixEnd_1126487 257079680907306376947505 := by
  unfold tailWord_1126487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41086356269937462507865715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27390904179958308338577143 41086356269937462507865715)
  ·
    refine ⟨61629534404906193761798573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41086356269937462507865715 61629534404906193761798573)
    ·
      refine ⟨23111075401839822660674465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61629534404906193761798573 23111075401839822660674465)
      ·
        refine ⟨17333306551379866995505849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23111075401839822660674465 17333306551379866995505849)
        ·
          refine ⟨12999979913534900246629387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17333306551379866995505849 12999979913534900246629387)
          ·
            refine ⟨19499969870302350369944081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12999979913534900246629387 19499969870302350369944081)
            ·
              refine ⟨14624977402726762777458061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19499969870302350369944081 14624977402726762777458061)
              ·
                refine ⟨5484366526022536041546773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14624977402726762777458061 5484366526022536041546773)
                ·
                  refine ⟨257079680907306376947505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5484366526022536041546773 257079680907306376947505)
                  ·
                    rfl

theorem cell21_1126487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_1126487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126487 prefixEnd_1126487 := by exact prefixLift 1126487
  have htrace : WordTrace (prefixWord ++ tailWord_1126487) baseStart_1126487 baseEnd_1126487 := by
    simpa [prefixWord, tailWord_1126487, baseEnd_1126487] using wordTrace_append hprefix tailTrace_1126487
  have hstable : (prefixWord ++ tailWord_1126487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126487).length < 2 ^ (prefixWord ++ tailWord_1126487).sum := by decide
  have hdescent : baseEnd_1126487 < baseStart_1126487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126490 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_1126490 : Nat := 118140960795 + 1126490 * 2 ^ 59
def prefixEnd_1126490 : Nat := 4983230072969 + 3 ^ 40 * 1126490 * 2
def baseEnd_1126490 : Nat := 257080365548179038397499

theorem tailTrace_1126490 : CollatzResearch.WordTrace tailWord_1126490 prefixEnd_1126490 257080365548179038397499 := by
  unfold tailWord_1126490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271616422231648505056231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27390977125951062680149949 10271616422231648505056231)
  ·
    refine ⟨15407424633347472757584347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10271616422231648505056231 15407424633347472757584347)
    ·
      refine ⟨23111136950021209136376521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15407424633347472757584347 23111136950021209136376521)
      ·
        refine ⟨17333352712515906852282391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23111136950021209136376521 17333352712515906852282391)
        ·
          refine ⟨26000029068773860278423587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17333352712515906852282391 26000029068773860278423587)
          ·
            refine ⟨39000043603160790417635381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26000029068773860278423587 39000043603160790417635381)
            ·
              refine ⟨3656254087796324101653317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39000043603160790417635381 3656254087796324101653317)
              ·
                refine ⟨685547641461810769059997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3656254087796324101653317 685547641461810769059997)
                ·
                  refine ⟨257080365548179038397499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685547641461810769059997 257080365548179038397499)
                  ·
                    rfl

theorem cell21_1126490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_1126490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126490 prefixEnd_1126490 := by exact prefixLift 1126490
  have htrace : WordTrace (prefixWord ++ tailWord_1126490) baseStart_1126490 baseEnd_1126490 := by
    simpa [prefixWord, tailWord_1126490, baseEnd_1126490] using wordTrace_append hprefix tailTrace_1126490
  have hstable : (prefixWord ++ tailWord_1126490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126490).length < 2 ^ (prefixWord ++ tailWord_1126490).sum := by decide
  have hdescent : baseEnd_1126490 < baseStart_1126490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126549 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1126549 : Nat := 118140960795 + 1126549 * 2 ^ 59
def prefixEnd_1126549 : Nat := 4983230072969 + 3 ^ 40 * 1126549 * 2
def baseEnd_1126549 : Nat := 257093830152008046914045

theorem tailTrace_1126549 : CollatzResearch.WordTrace tailWord_1126549 prefixEnd_1126549 257093830152008046914045 := by
  unfold tailWord_1126549
  simp only [CollatzResearch.WordTrace]
  refine ⟨41088617595712847096622701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27392411730475231397748467 41088617595712847096622701)
  ·
    refine ⟨15408231598392317661233513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41088617595712847096622701 15408231598392317661233513)
    ·
      refine ⟨11556173698794238245925135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15408231598392317661233513 11556173698794238245925135)
      ·
        refine ⟨17334260548191357368887703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556173698794238245925135 17334260548191357368887703)
        ·
          refine ⟨26001390822287036053331555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17334260548191357368887703 26001390822287036053331555)
          ·
            refine ⟨39002086233430554079997333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26001390822287036053331555 39002086233430554079997333)
            ·
              refine ⟨1828222792192057222499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39002086233430554079997333 1828222792192057222499875)
              ·
                refine ⟨2742334188288085833749813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828222792192057222499875 2742334188288085833749813)
                ·
                  refine ⟨257093830152008046914045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742334188288085833749813 257093830152008046914045)
                  ·
                    rfl

theorem cell21_1126549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1126549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126549 prefixEnd_1126549 := by exact prefixLift 1126549
  have htrace : WordTrace (prefixWord ++ tailWord_1126549) baseStart_1126549 baseEnd_1126549 := by
    simpa [prefixWord, tailWord_1126549, baseEnd_1126549] using wordTrace_append hprefix tailTrace_1126549
  have hstable : (prefixWord ++ tailWord_1126549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126549).length < 2 ^ (prefixWord ++ tailWord_1126549).sum := by decide
  have hdescent : baseEnd_1126549 < baseStart_1126549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126583 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 3]
def baseStart_1126583 : Nat := 118140960795 + 1126583 * 2 ^ 59
def prefixEnd_1126583 : Nat := 4983230072969 + 3 ^ 40 * 1126583 * 2
def baseEnd_1126583 : Nat := 257101589415231543347309

theorem tailTrace_1126583 : CollatzResearch.WordTrace tailWord_1126583 prefixEnd_1126583 257101589415231543347309 := by
  unfold tailWord_1126583
  simp only [CollatzResearch.WordTrace]
  refine ⟨41089857677589670903360403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27393238451726447268906935 41089857677589670903360403)
  ·
    refine ⟨61634786516384506355040605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41089857677589670903360403 61634786516384506355040605)
    ·
      refine ⟨23113044943644189883140227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61634786516384506355040605 23113044943644189883140227)
      ·
        refine ⟨34669567415466284824710341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23113044943644189883140227 34669567415466284824710341)
        ·
          refine ⟨6500543890399928404633189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34669567415466284824710341 6500543890399928404633189)
          ·
            refine ⟨1218851979449986575868723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6500543890399928404633189 1218851979449986575868723)
            ·
              refine ⟨1828277969174979863803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218851979449986575868723 1828277969174979863803085)
              ·
                refine ⟨685604238440617448926157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1828277969174979863803085 685604238440617448926157)
                ·
                  refine ⟨257101589415231543347309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685604238440617448926157 257101589415231543347309)
                  ·
                    rfl

theorem cell21_1126583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].length) (baseStart_1126583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126583 prefixEnd_1126583 := by exact prefixLift 1126583
  have htrace : WordTrace (prefixWord ++ tailWord_1126583) baseStart_1126583 baseEnd_1126583 := by
    simpa [prefixWord, tailWord_1126583, baseEnd_1126583] using wordTrace_append hprefix tailTrace_1126583
  have hstable : (prefixWord ++ tailWord_1126583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126583).length < 2 ^ (prefixWord ++ tailWord_1126583).sum := by decide
  have hdescent : baseEnd_1126583 < baseStart_1126583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126614 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1126614 : Nat := 118140960795 + 1126614 * 2 ^ 59
def prefixEnd_1126614 : Nat := 4983230072969 + 3 ^ 40 * 1126614 * 2
def baseEnd_1126614 : Nat := 257108664037582378330579

theorem tailTrace_1126614 : CollatzResearch.WordTrace tailWord_1126614 prefixEnd_1126614 257108664037582378330579 := by
  unfold tailWord_1126614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568186771279835199858681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27393992226984908798492597 2568186771279835199858681)
  ·
    refine ⟨1926140078459876399894011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568186771279835199858681 1926140078459876399894011)
    ·
      refine ⟨2889210117689814599841017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926140078459876399894011 2889210117689814599841017)
      ·
        refine ⟨2166907588267360949880763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2889210117689814599841017 2166907588267360949880763)
        ·
          refine ⟨3250361382401041424821145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166907588267360949880763 3250361382401041424821145)
          ·
            refine ⟨2437771036800781068615859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250361382401041424821145 2437771036800781068615859)
            ·
              refine ⟨3656656555201171602923789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437771036800781068615859 3656656555201171602923789)
              ·
                refine ⟨1371246208200439351096421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3656656555201171602923789 1371246208200439351096421)
                ·
                  refine ⟨257108664037582378330579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371246208200439351096421 257108664037582378330579)
                  ·
                    rfl

theorem cell21_1126614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1126614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126614 prefixEnd_1126614 := by exact prefixLift 1126614
  have htrace : WordTrace (prefixWord ++ tailWord_1126614) baseStart_1126614 baseEnd_1126614 := by
    simpa [prefixWord, tailWord_1126614, baseEnd_1126614] using wordTrace_append hprefix tailTrace_1126614
  have hstable : (prefixWord ++ tailWord_1126614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126614).length < 2 ^ (prefixWord ++ tailWord_1126614).sum := by decide
  have hdescent : baseEnd_1126614 < baseStart_1126614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126687 : List Nat := [1, 1, 2, 4, 3, 2, 3, 5]
def baseStart_1126687 : Nat := 118140960795 + 1126687 * 2 ^ 59
def prefixEnd_1126687 : Nat := 4983230072969 + 3 ^ 40 * 1126687 * 2
def baseEnd_1126687 : Nat := 85708441210716824537921

theorem tailTrace_1126687 : CollatzResearch.WordTrace tailWord_1126687 prefixEnd_1126687 85708441210716824537921 := by
  unfold tailWord_1126687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41093650869212896665146315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27395767246141931110097543 41093650869212896665146315)
  ·
    refine ⟨61640476303819344997719473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41093650869212896665146315 61640476303819344997719473)
    ·
      refine ⟨46230357227864508748289605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61640476303819344997719473 46230357227864508748289605)
      ·
        refine ⟨8668191980224595390304301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46230357227864508748289605 8668191980224595390304301)
        ·
          refine ⟨3250571992584223271364113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8668191980224595390304301 3250571992584223271364113)
          ·
            refine ⟨2437928994438167453523085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250571992584223271364113 2437928994438167453523085)
            ·
              refine ⟨914223372914312795071157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437928994438167453523085 914223372914312795071157)
              ·
                refine ⟨85708441210716824537921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 914223372914312795071157 85708441210716824537921)
                ·
                  rfl

theorem cell21_1126687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 5].length) (baseStart_1126687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126687 prefixEnd_1126687 := by exact prefixLift 1126687
  have htrace : WordTrace (prefixWord ++ tailWord_1126687) baseStart_1126687 baseEnd_1126687 := by
    simpa [prefixWord, tailWord_1126687, baseEnd_1126687] using wordTrace_append hprefix tailTrace_1126687
  have hstable : (prefixWord ++ tailWord_1126687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126687).length < 2 ^ (prefixWord ++ tailWord_1126687).sum := by decide
  have hdescent : baseEnd_1126687 < baseStart_1126687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126718 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1126718 : Nat := 118140960795 + 1126718 * 2 ^ 59
def prefixEnd_1126718 : Nat := 4983230072969 + 3 ^ 40 * 1126718 * 2
def baseEnd_1126718 : Nat := 257132398254501308597033

theorem tailTrace_1126718 : CollatzResearch.WordTrace tailWord_1126718 prefixEnd_1126718 257132398254501308597033 := by
  unfold tailWord_1126718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136847691512573619940601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27396521021400392639683205 5136847691512573619940601)
  ·
    refine ⟨3852635768634430214955451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5136847691512573619940601 3852635768634430214955451)
    ·
      refine ⟨5778953652951645322433177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852635768634430214955451 5778953652951645322433177)
      ·
        refine ⟨4334215239713733991824883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778953652951645322433177 4334215239713733991824883)
        ·
          refine ⟨6501322859570600987737325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334215239713733991824883 6501322859570600987737325)
          ·
            refine ⟨2437996072338975370401497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6501322859570600987737325 2437996072338975370401497)
            ·
              refine ⟨1828497054254231527801123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2437996072338975370401497 1828497054254231527801123)
              ·
                refine ⟨2742745581381347291701685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828497054254231527801123 2742745581381347291701685)
                ·
                  refine ⟨257132398254501308597033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742745581381347291701685 257132398254501308597033)
                  ·
                    rfl

theorem cell21_1126718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1126718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126718 prefixEnd_1126718 := by exact prefixLift 1126718
  have htrace : WordTrace (prefixWord ++ tailWord_1126718) baseStart_1126718 baseEnd_1126718 := by
    simpa [prefixWord, tailWord_1126718, baseEnd_1126718] using wordTrace_append hprefix tailTrace_1126718
  have hstable : (prefixWord ++ tailWord_1126718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126718).length < 2 ^ (prefixWord ++ tailWord_1126718).sum := by decide
  have hdescent : baseEnd_1126718 < baseStart_1126718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126729 : List Nat := [1, 2, 1, 1, 2, 3, 1, 10]
def baseStart_1126729 : Nat := 118140960795 + 1126729 * 2 ^ 59
def prefixEnd_1126729 : Nat := 4983230072969 + 3 ^ 40 * 1126729 * 2
def baseEnd_1126729 : Nat := 85711636201455911304559

theorem tailTrace_1126729 : CollatzResearch.WordTrace tailWord_1126729 prefixEnd_1126729 85711636201455911304559 := by
  unfold tailWord_1126729
  simp only [CollatzResearch.WordTrace]
  refine ⟨41095182735060737838175241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27396788490040491892116827 41095182735060737838175241)
  ·
    refine ⟨30821387051295553378631431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41095182735060737838175241 30821387051295553378631431)
    ·
      refine ⟨46232080576943330067947147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30821387051295553378631431 46232080576943330067947147)
      ·
        refine ⟨69348120865414995101920721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46232080576943330067947147 69348120865414995101920721)
        ·
          refine ⟨52011090649061246326440541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69348120865414995101920721 52011090649061246326440541)
          ·
            refine ⟨19504158993397967372415203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52011090649061246326440541 19504158993397967372415203)
            ·
              refine ⟨29256238490096951058622805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19504158993397967372415203 29256238490096951058622805)
              ·
                refine ⟨85711636201455911304559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29256238490096951058622805 85711636201455911304559)
                ·
                  rfl

theorem cell21_1126729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_1126729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126729 prefixEnd_1126729 := by exact prefixLift 1126729
  have htrace : WordTrace (prefixWord ++ tailWord_1126729) baseStart_1126729 baseEnd_1126729 := by
    simpa [prefixWord, tailWord_1126729, baseEnd_1126729] using wordTrace_append hprefix tailTrace_1126729
  have hstable : (prefixWord ++ tailWord_1126729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126729).length < 2 ^ (prefixWord ++ tailWord_1126729).sum := by decide
  have hdescent : baseEnd_1126729 < baseStart_1126729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126752 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_1126752 : Nat := 118140960795 + 1126752 * 2 ^ 59
def prefixEnd_1126752 : Nat := 4983230072969 + 3 ^ 40 * 1126752 * 2
def baseEnd_1126752 : Nat := 257140157517724805030297

theorem tailTrace_1126752 : CollatzResearch.WordTrace tailWord_1126752 prefixEnd_1126752 257140157517724805030297 := by
  unfold tailWord_1126752
  simp only [CollatzResearch.WordTrace]
  refine ⟨20548010806988706383131255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27397347742651608510841673 20548010806988706383131255)
  ·
    refine ⟨30822016210483059574696883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20548010806988706383131255 30822016210483059574696883)
    ·
      refine ⟨46233024315724589362045325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30822016210483059574696883 46233024315724589362045325)
      ·
        refine ⟨17337384118396721010766997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46233024315724589362045325 17337384118396721010766997)
        ·
          refine ⟨812689880549846297379703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17337384118396721010766997 812689880549846297379703)
          ·
            refine ⟨1219034820824769446069555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812689880549846297379703 1219034820824769446069555)
            ·
              refine ⟨1828552231237154169104333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219034820824769446069555 1828552231237154169104333)
              ·
                refine ⟨685707086713932813414125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1828552231237154169104333 685707086713932813414125)
                ·
                  refine ⟨257140157517724805030297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685707086713932813414125 257140157517724805030297)
                  ·
                    rfl

theorem cell21_1126752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_1126752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126752 prefixEnd_1126752 := by exact prefixLift 1126752
  have htrace : WordTrace (prefixWord ++ tailWord_1126752) baseStart_1126752 baseEnd_1126752 := by
    simpa [prefixWord, tailWord_1126752, baseEnd_1126752] using wordTrace_append hprefix tailTrace_1126752
  have hstable : (prefixWord ++ tailWord_1126752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126752).length < 2 ^ (prefixWord ++ tailWord_1126752).sum := by decide
  have hdescent : baseEnd_1126752 < baseStart_1126752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126881 : List Nat := [1, 2, 3, 1, 2, 2, 10]
def baseStart_1126881 : Nat := 118140960795 + 1126881 * 2 ^ 59
def prefixEnd_1126881 : Nat := 4983230072969 + 3 ^ 40 * 1126881 * 2
def baseEnd_1126881 : Nat := 28574399675027694153337

theorem tailTrace_1126881 : CollatzResearch.WordTrace tailWord_1126881 prefixEnd_1126881 28574399675027694153337 := by
  unfold tailWord_1126881
  simp only [CollatzResearch.WordTrace]
  refine ⟨41100726630510067797708497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27400484420340045198472331 41100726630510067797708497)
  ·
    refine ⟨30825544972882550848281373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41100726630510067797708497 30825544972882550848281373)
    ·
      refine ⟨11559579364830956568105515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30825544972882550848281373 11559579364830956568105515)
      ·
        refine ⟨17339369047246434852158273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11559579364830956568105515 17339369047246434852158273)
        ·
          refine ⟨13004526785434826139118705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17339369047246434852158273 13004526785434826139118705)
          ·
            refine ⟨9753395089076119604339029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13004526785434826139118705 9753395089076119604339029)
            ·
              refine ⟨28574399675027694153337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9753395089076119604339029 28574399675027694153337)
              ·
                rfl

theorem cell21_1126881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 10].length) (baseStart_1126881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126881 prefixEnd_1126881 := by exact prefixLift 1126881
  have htrace : WordTrace (prefixWord ++ tailWord_1126881) baseStart_1126881 baseEnd_1126881 := by
    simpa [prefixWord, tailWord_1126881, baseEnd_1126881] using wordTrace_append hprefix tailTrace_1126881
  have hstable : (prefixWord ++ tailWord_1126881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126881).length < 2 ^ (prefixWord ++ tailWord_1126881).sum := by decide
  have hdescent : baseEnd_1126881 < baseStart_1126881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126918 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1126918 : Nat := 118140960795 + 1126918 * 2 ^ 59
def prefixEnd_1126918 : Nat := 4983230072969 + 3 ^ 40 * 1126918 * 2
def baseEnd_1126918 : Nat := 257178040979345405263291

theorem tailTrace_1126918 : CollatzResearch.WordTrace tailWord_1126918 prefixEnd_1126918 257178040979345405263291 := by
  unfold tailWord_1126918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284439879105500722400169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27401384087584015411203605 1284439879105500722400169)
  ·
    refine ⟨963329909329125541800127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1284439879105500722400169 963329909329125541800127)
    ·
      refine ⟨1444994863993688312700191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963329909329125541800127 1444994863993688312700191)
      ·
        refine ⟨2167492295990532469050287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444994863993688312700191 2167492295990532469050287)
        ·
          refine ⟨3251238443985798703575431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167492295990532469050287 3251238443985798703575431)
          ·
            refine ⟨4876857665978698055363147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3251238443985798703575431 4876857665978698055363147)
            ·
              refine ⟨7315286498968047083044721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4876857665978698055363147 7315286498968047083044721)
              ·
                refine ⟨5486464874226035312283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7315286498968047083044721 5486464874226035312283541)
                ·
                  refine ⟨257178040979345405263291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5486464874226035312283541 257178040979345405263291)
                  ·
                    rfl

theorem cell21_1126918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1126918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126918 prefixEnd_1126918 := by exact prefixLift 1126918
  have htrace : WordTrace (prefixWord ++ tailWord_1126918) baseStart_1126918 baseEnd_1126918 := by
    simpa [prefixWord, tailWord_1126918, baseEnd_1126918] using wordTrace_append hprefix tailTrace_1126918
  have hstable : (prefixWord ++ tailWord_1126918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126918).length < 2 ^ (prefixWord ++ tailWord_1126918).sum := by decide
  have hdescent : baseEnd_1126918 < baseStart_1126918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126929 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 3]
def baseStart_1126929 : Nat := 118140960795 + 1126929 * 2 ^ 59
def prefixEnd_1126929 : Nat := 4983230072969 + 3 ^ 40 * 1126929 * 2
def baseEnd_1126929 : Nat := 257180551329211830579935

theorem tailTrace_1126929 : CollatzResearch.WordTrace tailWord_1126929 prefixEnd_1126929 257180551329211830579935 := by
  unfold tailWord_1126929
  simp only [CollatzResearch.WordTrace]
  refine ⟨41102477334336171995455841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27401651556224114663637227 41102477334336171995455841)
  ·
    refine ⟨30826858000752128996591881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41102477334336171995455841 30826858000752128996591881)
    ·
      refine ⟨23120143500564096747443911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30826858000752128996591881 23120143500564096747443911)
      ·
        refine ⟨34680215250846145121165867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23120143500564096747443911 34680215250846145121165867)
        ·
          refine ⟨52020322876269217681748801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34680215250846145121165867 52020322876269217681748801)
          ·
            refine ⟨39015242157201913261311601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52020322876269217681748801 39015242157201913261311601)
            ·
              refine ⟨29261431617901434945983701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39015242157201913261311601 29261431617901434945983701)
              ·
                refine ⟨685814803544564881546493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29261431617901434945983701 685814803544564881546493)
                ·
                  refine ⟨257180551329211830579935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685814803544564881546493 257180551329211830579935)
                  ·
                    rfl

theorem cell21_1126929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_1126929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126929 prefixEnd_1126929 := by exact prefixLift 1126929
  have htrace : WordTrace (prefixWord ++ tailWord_1126929) baseStart_1126929 baseEnd_1126929 := by
    simpa [prefixWord, tailWord_1126929, baseEnd_1126929] using wordTrace_append hprefix tailTrace_1126929
  have hstable : (prefixWord ++ tailWord_1126929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126929).length < 2 ^ (prefixWord ++ tailWord_1126929).sum := by decide
  have hdescent : baseEnd_1126929 < baseStart_1126929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126943 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_1126943 : Nat := 118140960795 + 1126943 * 2 ^ 59
def prefixEnd_1126943 : Nat := 4983230072969 + 3 ^ 40 * 1126943 * 2
def baseEnd_1126943 : Nat := 257183746319950917346573

theorem tailTrace_1126943 : CollatzResearch.WordTrace tailWord_1126943 prefixEnd_1126943 257183746319950917346573 := by
  unfold tailWord_1126943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41102987956285452386465483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27401991970856968257643655 41102987956285452386465483)
  ·
    refine ⟨61654481934428178579698225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41102987956285452386465483 61654481934428178579698225)
    ·
      refine ⟨46240861450821133934773669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61654481934428178579698225 46240861450821133934773669)
      ·
        refine ⟨8670161522028962612770063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46240861450821133934773669 8670161522028962612770063)
        ·
          refine ⟨13005242283043443919155095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670161522028962612770063 13005242283043443919155095)
          ·
            refine ⟨19507863424565165878732643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13005242283043443919155095 19507863424565165878732643)
            ·
              refine ⟨29261795136847748818098965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19507863424565165878732643 29261795136847748818098965)
              ·
                refine ⟨1371646647039738225848389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29261795136847748818098965 1371646647039738225848389)
                ·
                  refine ⟨257183746319950917346573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371646647039738225848389 257183746319950917346573)
                  ·
                    rfl

theorem cell21_1126943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_1126943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126943 prefixEnd_1126943 := by exact prefixLift 1126943
  have htrace : WordTrace (prefixWord ++ tailWord_1126943) baseStart_1126943 baseEnd_1126943 := by
    simpa [prefixWord, tailWord_1126943, baseEnd_1126943] using wordTrace_append hprefix tailTrace_1126943
  have hstable : (prefixWord ++ tailWord_1126943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126943).length < 2 ^ (prefixWord ++ tailWord_1126943).sum := by decide
  have hdescent : baseEnd_1126943 < baseStart_1126943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126960 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_1126960 : Nat := 118140960795 + 1126960 * 2 ^ 59
def prefixEnd_1126960 : Nat := 4983230072969 + 3 ^ 40 * 1126960 * 2
def baseEnd_1126960 : Nat := 257187625951562665563205

theorem tailTrace_1126960 : CollatzResearch.WordTrace tailWord_1126960 prefixEnd_1126960 257187625951562665563205 := by
  unfold tailWord_1126960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20551803998611932144917167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27402405331482576193222889 20551803998611932144917167)
  ·
    refine ⟨30827705997917898217375751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20551803998611932144917167 30827705997917898217375751)
    ·
      refine ⟨46241558996876847326063627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30827705997917898217375751 46241558996876847326063627)
      ·
        refine ⟨69362338495315270989095441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46241558996876847326063627 69362338495315270989095441)
        ·
          refine ⟨52021753871486453241821581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69362338495315270989095441 52021753871486453241821581)
          ·
            refine ⟨19508157701807419965683093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52021753871486453241821581 19508157701807419965683093)
            ·
              refine ⟨914444892272222810891395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19508157701807419965683093 914444892272222810891395)
              ·
                refine ⟨1371667338408334216337093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914444892272222810891395 1371667338408334216337093)
                ·
                  refine ⟨257187625951562665563205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371667338408334216337093 257187625951562665563205)
                  ·
                    rfl

theorem cell21_1126960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_1126960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1126960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1126960 prefixEnd_1126960 := by exact prefixLift 1126960
  have htrace : WordTrace (prefixWord ++ tailWord_1126960) baseStart_1126960 baseEnd_1126960 := by
    simpa [prefixWord, tailWord_1126960, baseEnd_1126960] using wordTrace_append hprefix tailTrace_1126960
  have hstable : (prefixWord ++ tailWord_1126960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126960).length < 2 ^ (prefixWord ++ tailWord_1126960).sum := by decide
  have hdescent : baseEnd_1126960 < baseStart_1126960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127050 : List Nat := [3, 1, 2, 3, 3, 1, 8]
def baseStart_1127050 : Nat := 118140960795 + 1127050 * 2 ^ 59
def prefixEnd_1127050 : Nat := 4983230072969 + 3 ^ 40 * 1127050 * 2
def baseEnd_1127050 : Nat := 28578685019749167673669

theorem tailTrace_1127050 : CollatzResearch.WordTrace tailWord_1127050 prefixEnd_1127050 28578685019749167673669 := by
  unfold tailWord_1127050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276722641724452415152651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27404593711265206440407069 10276722641724452415152651)
  ·
    refine ⟨15415083962586678622728977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10276722641724452415152651 15415083962586678622728977)
    ·
      refine ⟨11561312971940008967046733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15415083962586678622728977 11561312971940008967046733)
      ·
        refine ⟨4335492364477503362642525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11561312971940008967046733 4335492364477503362642525)
        ·
          refine ⟨1625809636679063760990947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4335492364477503362642525 1625809636679063760990947)
          ·
            refine ⟨2438714455018595641486421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625809636679063760990947 2438714455018595641486421)
            ·
              refine ⟨28578685019749167673669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2438714455018595641486421 28578685019749167673669)
              ·
                rfl

theorem cell21_1127050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 8].length) (baseStart_1127050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127050 prefixEnd_1127050 := by exact prefixLift 1127050
  have htrace : WordTrace (prefixWord ++ tailWord_1127050) baseStart_1127050 baseEnd_1127050 := by
    simpa [prefixWord, tailWord_1127050, baseEnd_1127050] using wordTrace_append hprefix tailTrace_1127050
  have hstable : (prefixWord ++ tailWord_1127050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127050).length < 2 ^ (prefixWord ++ tailWord_1127050).sum := by decide
  have hdescent : baseEnd_1127050 < baseStart_1127050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
