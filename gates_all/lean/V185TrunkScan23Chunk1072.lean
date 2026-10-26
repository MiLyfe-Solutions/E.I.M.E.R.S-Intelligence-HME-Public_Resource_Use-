import V185TrunkScan23Chunk1071

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6346191 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 1, 3, 2]
def baseStart_6346191 : Nat := 118140960795 + 6346191 * 2 ^ 59
def prefixEnd_6346191 : Nat := 4983230072969 + 3 ^ 40 * 6346191 * 2
def baseEnd_6346191 : Nat := 3258646308237285232226905

theorem tailTrace_6346191 : CollatzResearch.WordTrace tailWord_6346191 prefixEnd_6346191 3258646308237285232226905 := by
  unfold tailWord_6346191
  simp only [CollatzResearch.WordTrace]
  refine ⟨231464601351841324978750427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154309734234560883319166951 231464601351841324978750427)
  ·
    refine ⟨347196902027761987468125641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231464601351841324978750427 347196902027761987468125641)
    ·
      refine ⟨260397676520821490601094231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347196902027761987468125641 260397676520821490601094231)
      ·
        refine ⟨390596514781232235901641347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260397676520821490601094231 390596514781232235901641347)
        ·
          refine ⟨585894772171848353852462021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390596514781232235901641347 585894772171848353852462021)
          ·
            refine ⟨109855269782221566347336629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585894772171848353852462021 109855269782221566347336629)
            ·
              refine ⟨10298931542083271845062809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109855269782221566347336629 10298931542083271845062809)
              ·
                refine ⟨7724198656562453883797107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10298931542083271845062809 7724198656562453883797107)
                ·
                  refine ⟨11586297984843680825695661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7724198656562453883797107 11586297984843680825695661)
                  ·
                    refine ⟨4344861744316380309635873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11586297984843680825695661 4344861744316380309635873)
                    ·
                      refine ⟨3258646308237285232226905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4344861744316380309635873 3258646308237285232226905)
                      ·
                        rfl

theorem cell23_6346191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3, 2].length) (baseStart_6346191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346191 prefixEnd_6346191 := by exact prefixLift 6346191
  have htrace : WordTrace (prefixWord ++ tailWord_6346191) baseStart_6346191 baseEnd_6346191 := by
    simpa [prefixWord, tailWord_6346191, baseEnd_6346191] using wordTrace_append hprefix tailTrace_6346191
  have hstable : (prefixWord ++ tailWord_6346191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346191).length < 2 ^ (prefixWord ++ tailWord_6346191).sum := by decide
  have hdescent : baseEnd_6346191 < baseStart_6346191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346207 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_6346207 : Nat := 118140960795 + 6346207 * 2 ^ 59
def prefixEnd_6346207 : Nat := 4983230072969 + 3 ^ 40 * 6346207 * 2
def baseEnd_6346207 : Nat := 3258654523927757169626831

theorem tailTrace_6346207 : CollatzResearch.WordTrace tailWord_6346207 prefixEnd_6346207 3258654523927757169626831 := by
  unfold tailWord_6346207
  simp only [CollatzResearch.WordTrace]
  refine ⟨231465184919783359711332875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154310123279855573140888583 231465184919783359711332875)
  ·
    refine ⟨347197777379675039566999313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231465184919783359711332875 347197777379675039566999313)
    ·
      refine ⟨260398333034756279675249485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347197777379675039566999313 260398333034756279675249485)
      ·
        refine ⟨97649374888033604878218557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260398333034756279675249485 97649374888033604878218557)
        ·
          refine ⟨36618515583012601829331959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97649374888033604878218557 36618515583012601829331959)
          ·
            refine ⟨54927773374518902743997939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36618515583012601829331959 54927773374518902743997939)
            ·
              refine ⟨82391660061778354115996909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54927773374518902743997939 82391660061778354115996909)
              ·
                refine ⟨30896872523166882793498841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82391660061778354115996909 30896872523166882793498841)
                ·
                  refine ⟨23172654392375162095124131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30896872523166882793498841 23172654392375162095124131)
                  ·
                    refine ⟨34758981588562743142686197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23172654392375162095124131 34758981588562743142686197)
                    ·
                      refine ⟨3258654523927757169626831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34758981588562743142686197 3258654523927757169626831)
                      ·
                        rfl

theorem cell23_6346207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_6346207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346207 prefixEnd_6346207 := by exact prefixLift 6346207
  have htrace : WordTrace (prefixWord ++ tailWord_6346207) baseStart_6346207 baseEnd_6346207 := by
    simpa [prefixWord, tailWord_6346207, baseEnd_6346207] using wordTrace_append hprefix tailTrace_6346207
  have hstable : (prefixWord ++ tailWord_6346207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346207).length < 2 ^ (prefixWord ++ tailWord_6346207).sum := by decide
  have hdescent : baseEnd_6346207 < baseStart_6346207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346257 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 7]
def baseStart_6346257 : Nat := 118140960795 + 6346257 * 2 ^ 59
def prefixEnd_6346257 : Nat := 4983230072969 + 3 ^ 40 * 6346257 * 2
def baseEnd_6346257 : Nat := 1086226732653493991333867

theorem tailTrace_6346257 : CollatzResearch.WordTrace tailWord_6346257 prefixEnd_6346257 1086226732653493991333867 := by
  unfold tailWord_6346257
  simp only [CollatzResearch.WordTrace]
  refine ⟨231467008569602218250653025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154311339046401478833768683 231467008569602218250653025)
  ·
    refine ⟨173600256427201663687989769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231467008569602218250653025 173600256427201663687989769)
    ·
      refine ⟨130200192320401247765992327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173600256427201663687989769 130200192320401247765992327)
      ·
        refine ⟨195300288480601871648988491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130200192320401247765992327 195300288480601871648988491)
        ·
          refine ⟨292950432720902807473482737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195300288480601871648988491 292950432720902807473482737)
          ·
            refine ⟨219712824540677105605112053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292950432720902807473482737 219712824540677105605112053)
            ·
              refine ⟨20598077300688478650479255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219712824540677105605112053 20598077300688478650479255)
              ·
                refine ⟨30897115951032717975718883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20598077300688478650479255 30897115951032717975718883)
                ·
                  refine ⟨46345673926549076963578325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30897115951032717975718883 46345673926549076963578325)
                  ·
                    refine ⟨1086226732653493991333867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46345673926549076963578325 1086226732653493991333867)
                    ·
                      rfl

theorem cell23_6346257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_6346257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346257 prefixEnd_6346257 := by exact prefixLift 6346257
  have htrace : WordTrace (prefixWord ++ tailWord_6346257) baseStart_6346257 baseEnd_6346257 := by
    simpa [prefixWord, tailWord_6346257, baseEnd_6346257] using wordTrace_append hprefix tailTrace_6346257
  have hstable : (prefixWord ++ tailWord_6346257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346257).length < 2 ^ (prefixWord ++ tailWord_6346257).sum := by decide
  have hdescent : baseEnd_6346257 < baseStart_6346257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346261 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 5]
def baseStart_6346261 : Nat := 118140960795 + 6346261 * 2 ^ 59
def prefixEnd_6346261 : Nat := 4983230072969 + 3 ^ 40 * 6346261 * 2
def baseEnd_6346261 : Nat := 362075805764788884261287

theorem tailTrace_6346261 : CollatzResearch.WordTrace tailWord_6346261 prefixEnd_6346261 362075805764788884261287 := by
  unfold tailWord_6346261
  simp only [CollatzResearch.WordTrace]
  refine ⟨231467154461587726933798637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154311436307725151289199091 231467154461587726933798637)
  ·
    refine ⟨86800182923095397600174489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231467154461587726933798637 86800182923095397600174489)
    ·
      refine ⟨65100137192321548200130867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86800182923095397600174489 65100137192321548200130867)
      ·
        refine ⟨97650205788482322300196301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65100137192321548200130867 97650205788482322300196301)
        ·
          refine ⟨36618827170680870862573613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97650205788482322300196301 36618827170680870862573613)
          ·
            refine ⟨13732060189005326573465105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36618827170680870862573613 13732060189005326573465105)
            ·
              refine ⟨10299045141753994930098829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13732060189005326573465105 10299045141753994930098829)
              ·
                refine ⟨3862141928157748098787061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10299045141753994930098829 3862141928157748098787061)
                ·
                  refine ⟨362075805764788884261287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3862141928157748098787061 362075805764788884261287)
                  ·
                    rfl

theorem cell23_6346261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_6346261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346261 prefixEnd_6346261 := by exact prefixLift 6346261
  have htrace : WordTrace (prefixWord ++ tailWord_6346261) baseStart_6346261 baseEnd_6346261 := by
    simpa [prefixWord, tailWord_6346261, baseEnd_6346261] using wordTrace_append hprefix tailTrace_6346261
  have hstable : (prefixWord ++ tailWord_6346261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346261).length < 2 ^ (prefixWord ++ tailWord_6346261).sum := by decide
  have hdescent : baseEnd_6346261 < baseStart_6346261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346274 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6346274 : Nat := 118140960795 + 6346274 * 2 ^ 59
def prefixEnd_6346274 : Nat := 4983230072969 + 3 ^ 40 * 6346274 * 2
def baseEnd_6346274 : Nat := 1086229642377202802496341

theorem tailTrace_6346274 : CollatzResearch.WordTrace tailWord_6346274 prefixEnd_6346274 1086229642377202802496341 := by
  unfold tailWord_6346274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57866907152635157538505469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154311752407027086769347917 57866907152635157538505469)
  ·
    refine ⟨21700090182238184076939551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57866907152635157538505469 21700090182238184076939551)
    ·
      refine ⟨32550135273357276115409327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21700090182238184076939551 32550135273357276115409327)
      ·
        refine ⟨48825202910035914173113991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32550135273357276115409327 48825202910035914173113991)
        ·
          refine ⟨73237804365053871259670987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48825202910035914173113991 73237804365053871259670987)
          ·
            refine ⟨109856706547580806889506481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73237804365053871259670987 109856706547580806889506481)
            ·
              refine ⟨82392529910685605167129861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109856706547580806889506481 82392529910685605167129861)
              ·
                refine ⟨15448599358253550968836849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82392529910685605167129861 15448599358253550968836849)
                ·
                  refine ⟨11586449518690163226627637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15448599358253550968836849 11586449518690163226627637)
                  ·
                    refine ⟨1086229642377202802496341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11586449518690163226627637 1086229642377202802496341)
                    ·
                      rfl

theorem cell23_6346274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6346274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346274 prefixEnd_6346274 := by exact prefixLift 6346274
  have htrace : WordTrace (prefixWord ++ tailWord_6346274) baseStart_6346274 baseEnd_6346274 := by
    simpa [prefixWord, tailWord_6346274, baseEnd_6346274] using wordTrace_append hprefix tailTrace_6346274
  have hstable : (prefixWord ++ tailWord_6346274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346274).length < 2 ^ (prefixWord ++ tailWord_6346274).sum := by decide
  have hdescent : baseEnd_6346274 < baseStart_6346274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346314 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_6346314 : Nat := 118140960795 + 6346314 * 2 ^ 59
def prefixEnd_6346314 : Nat := 4983230072969 + 3 ^ 40 * 6346314 * 2
def baseEnd_6346314 : Nat := 3258709466357788250988839

theorem tailTrace_6346314 : CollatzResearch.WordTrace tailWord_6346314 prefixEnd_6346314 3258709466357788250988839 := by
  unfold tailWord_6346314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867271882598929246369499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154312725020263811323651997 57867271882598929246369499)
  ·
    refine ⟨86800907823898393869554249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57867271882598929246369499 86800907823898393869554249)
    ·
      refine ⟨65100680867923795402165687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86800907823898393869554249 65100680867923795402165687)
      ·
        refine ⟨97651021301885693103248531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65100680867923795402165687 97651021301885693103248531)
        ·
          refine ⟨146476531952828539654872797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97651021301885693103248531 146476531952828539654872797)
          ·
            refine ⟨54928699482310702370577299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146476531952828539654872797 54928699482310702370577299)
            ·
              refine ⟨82393049223466053555865949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54928699482310702370577299 82393049223466053555865949)
              ·
                refine ⟨30897393458799770083449731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82393049223466053555865949 30897393458799770083449731)
                ·
                  refine ⟨46346090188199655125174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30897393458799770083449731 46346090188199655125174597)
                  ·
                    refine ⟨8689891910287435335970237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46346090188199655125174597 8689891910287435335970237)
                    ·
                      refine ⟨3258709466357788250988839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689891910287435335970237 3258709466357788250988839)
                      ·
                        rfl

theorem cell23_6346314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_6346314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346314 prefixEnd_6346314 := by exact prefixLift 6346314
  have htrace : WordTrace (prefixWord ++ tailWord_6346314) baseStart_6346314 baseEnd_6346314 := by
    simpa [prefixWord, tailWord_6346314, baseEnd_6346314] using wordTrace_append hprefix tailTrace_6346314
  have hstable : (prefixWord ++ tailWord_6346314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346314).length < 2 ^ (prefixWord ++ tailWord_6346314).sum := by decide
  have hdescent : baseEnd_6346314 < baseStart_6346314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346361 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_6346361 : Nat := 118140960795 + 6346361 * 2 ^ 59
def prefixEnd_6346361 : Nat := 4983230072969 + 3 ^ 40 * 6346361 * 2
def baseEnd_6346361 : Nat := 3258733599948549567101123

theorem tailTrace_6346361 : CollatzResearch.WordTrace tailWord_6346361 prefixEnd_6346361 3258733599948549567101123 := by
  unfold tailWord_6346361
  simp only [CollatzResearch.WordTrace]
  refine ⟨231470801761225444012438937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154313867840816962674959291 231470801761225444012438937)
  ·
    refine ⟨173603101320919083009329203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231470801761225444012438937 173603101320919083009329203)
    ·
      refine ⟨260404651981378624513993805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173603101320919083009329203 260404651981378624513993805)
      ·
        refine ⟨97651744493016984192747677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260404651981378624513993805 97651744493016984192747677)
        ·
          refine ⟨36619404184881369072280379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97651744493016984192747677 36619404184881369072280379)
          ·
            refine ⟨54929106277322053608420569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36619404184881369072280379 54929106277322053608420569)
            ·
              refine ⟨41196829707991540206315427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54929106277322053608420569 41196829707991540206315427)
              ·
                refine ⟨61795244561987310309473141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41196829707991540206315427 61795244561987310309473141)
                ·
                  refine ⟨5793304177686310341513107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61795244561987310309473141 5793304177686310341513107)
                  ·
                    refine ⟨8689956266529465512269661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793304177686310341513107 8689956266529465512269661)
                    ·
                      refine ⟨3258733599948549567101123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8689956266529465512269661 3258733599948549567101123)
                      ·
                        rfl

theorem cell23_6346361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_6346361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346361 prefixEnd_6346361 := by exact prefixLift 6346361
  have htrace : WordTrace (prefixWord ++ tailWord_6346361) baseStart_6346361 baseEnd_6346361 := by
    simpa [prefixWord, tailWord_6346361, baseEnd_6346361] using wordTrace_append hprefix tailTrace_6346361
  have hstable : (prefixWord ++ tailWord_6346361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346361).length < 2 ^ (prefixWord ++ tailWord_6346361).sum := by decide
  have hdescent : baseEnd_6346361 < baseStart_6346361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346401 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6346401 : Nat := 118140960795 + 6346401 * 2 ^ 59
def prefixEnd_6346401 : Nat := 4983230072969 + 3 ^ 40 * 6346401 * 2
def baseEnd_6346401 : Nat := 3258754139174729410600939

theorem tailTrace_6346401 : CollatzResearch.WordTrace tailWord_6346401 prefixEnd_6346401 3258754139174729410600939 := by
  unfold tailWord_6346401
  simp only [CollatzResearch.WordTrace]
  refine ⟨231472260681080530843895057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154314840454053687229263371 231472260681080530843895057)
  ·
    refine ⟨173604195510810398132921293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231472260681080530843895057 173604195510810398132921293)
    ·
      refine ⟨65101573316553899299845485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173604195510810398132921293 65101573316553899299845485)
      ·
        refine ⟨24413089993707712237442057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65101573316553899299845485 24413089993707712237442057)
        ·
          refine ⟨18309817495280784178081543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24413089993707712237442057 18309817495280784178081543)
          ·
            refine ⟨27464726242921176267122315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18309817495280784178081543 27464726242921176267122315)
            ·
              refine ⟨41197089364381764400683473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27464726242921176267122315 41197089364381764400683473)
              ·
                refine ⟨30897817023286323300512605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41197089364381764400683473 30897817023286323300512605)
                ·
                  refine ⟨11586681383732371237692227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30897817023286323300512605 11586681383732371237692227)
                  ·
                    refine ⟨17380022075598556856538341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11586681383732371237692227 17380022075598556856538341)
                    ·
                      refine ⟨3258754139174729410600939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17380022075598556856538341 3258754139174729410600939)
                      ·
                        rfl

theorem cell23_6346401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6346401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346401 prefixEnd_6346401 := by exact prefixLift 6346401
  have htrace : WordTrace (prefixWord ++ tailWord_6346401) baseStart_6346401 baseEnd_6346401 := by
    simpa [prefixWord, tailWord_6346401, baseEnd_6346401] using wordTrace_append hprefix tailTrace_6346401
  have hstable : (prefixWord ++ tailWord_6346401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346401).length < 2 ^ (prefixWord ++ tailWord_6346401).sum := by decide
  have hdescent : baseEnd_6346401 < baseStart_6346401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346418 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_6346418 : Nat := 118140960795 + 6346418 * 2 ^ 59
def prefixEnd_6346418 : Nat := 4983230072969 + 3 ^ 40 * 6346418 * 2
def baseEnd_6346418 : Nat := 3258762868345855844088361

theorem tailTrace_6346418 : CollatzResearch.WordTrace tailWord_6346418 prefixEnd_6346418 3258762868345855844088361 := by
  unfold tailWord_6346418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57868220180504735686815977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154315253814679295164842605 57868220180504735686815977)
  ·
    refine ⟨43401165135378551765111983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57868220180504735686815977 43401165135378551765111983)
    ·
      refine ⟨65101747703067827647667975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43401165135378551765111983 65101747703067827647667975)
      ·
        refine ⟨97652621554601741471501963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65101747703067827647667975 97652621554601741471501963)
        ·
          refine ⟨146478932331902612207252945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97652621554601741471501963 146478932331902612207252945)
          ·
            refine ⟨109859199248926959155439709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146478932331902612207252945 109859199248926959155439709)
            ·
              refine ⟨41197199718347609683289891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109859199248926959155439709 41197199718347609683289891)
              ·
                refine ⟨61795799577521414524934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41197199718347609683289891 61795799577521414524934837)
                ·
                  refine ⟨5793356210392632611712641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61795799577521414524934837 5793356210392632611712641)
                  ·
                    refine ⟨4345017157794474458784481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793356210392632611712641 4345017157794474458784481)
                    ·
                      refine ⟨3258762868345855844088361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345017157794474458784481 3258762868345855844088361)
                      ·
                        rfl

theorem cell23_6346418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_6346418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346418 prefixEnd_6346418 := by exact prefixLift 6346418
  have htrace : WordTrace (prefixWord ++ tailWord_6346418) baseStart_6346418 baseEnd_6346418 := by
    simpa [prefixWord, tailWord_6346418, baseEnd_6346418] using wordTrace_append hprefix tailTrace_6346418
  have hstable : (prefixWord ++ tailWord_6346418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346418).length < 2 ^ (prefixWord ++ tailWord_6346418).sum := by decide
  have hdescent : baseEnd_6346418 < baseStart_6346418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346422 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6346422 : Nat := 118140960795 + 6346422 * 2 ^ 59
def prefixEnd_6346422 : Nat := 4983230072969 + 3 ^ 40 * 6346422 * 2
def baseEnd_6346422 : Nat := 3258764922268473828438343

theorem tailTrace_6346422 : CollatzResearch.WordTrace tailWord_6346422 prefixEnd_6346422 3258764922268473828438343 := by
  unfold tailWord_6346422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467064163375278214400595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154315351076002967620273013 14467064163375278214400595)
  ·
    refine ⟨21700596245062917321600893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467064163375278214400595 21700596245062917321600893)
    ·
      refine ⟨8137723591898593995600335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21700596245062917321600893 8137723591898593995600335)
      ·
        refine ⟨12206585387847890993400503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137723591898593995600335 12206585387847890993400503)
        ·
          refine ⟨18309878081771836490100755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206585387847890993400503 18309878081771836490100755)
          ·
            refine ⟨27464817122657754735151133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18309878081771836490100755 27464817122657754735151133)
            ·
              refine ⟨10299306420996658025681675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27464817122657754735151133 10299306420996658025681675)
              ·
                refine ⟨15448959631494987038522513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299306420996658025681675 15448959631494987038522513)
                ·
                  refine ⟨11586719723621240278891885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15448959631494987038522513 11586719723621240278891885)
                  ·
                    refine ⟨4345019896357965104584457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11586719723621240278891885 4345019896357965104584457)
                    ·
                      refine ⟨3258764922268473828438343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345019896357965104584457 3258764922268473828438343)
                      ·
                        rfl

theorem cell23_6346422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6346422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346422 prefixEnd_6346422 := by exact prefixLift 6346422
  have htrace : WordTrace (prefixWord ++ tailWord_6346422) baseStart_6346422 baseEnd_6346422 := by
    simpa [prefixWord, tailWord_6346422, baseEnd_6346422] using wordTrace_append hprefix tailTrace_6346422
  have hstable : (prefixWord ++ tailWord_6346422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346422).length < 2 ^ (prefixWord ++ tailWord_6346422).sum := by decide
  have hdescent : baseEnd_6346422 < baseStart_6346422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346445 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6346445 : Nat := 118140960795 + 6346445 * 2 ^ 59
def prefixEnd_6346445 : Nat := 4983230072969 + 3 ^ 40 * 6346445 * 2
def baseEnd_6346445 : Nat := 1086258910774509079483579

theorem tailTrace_6346445 : CollatzResearch.WordTrace tailWord_6346445 prefixEnd_6346445 1086258910774509079483579 := by
  unfold tailWord_6346445
  simp only [CollatzResearch.WordTrace]
  refine ⟨231473865492921126358496789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154315910328614084238997859 231473865492921126358496789)
  ·
    refine ⟨10850337444980677798054537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231473865492921126358496789 10850337444980677798054537)
    ·
      refine ⟨8137753083735508348540903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10850337444980677798054537 8137753083735508348540903)
      ·
        refine ⟨12206629625603262522811355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137753083735508348540903 12206629625603262522811355)
        ·
          refine ⟨18309944438404893784217033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206629625603262522811355 18309944438404893784217033)
          ·
            refine ⟨13732458328803670338162775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18309944438404893784217033 13732458328803670338162775)
            ·
              refine ⟨20598687493205505507244163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13732458328803670338162775 20598687493205505507244163)
              ·
                refine ⟨30898031239808258260866245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20598687493205505507244163 30898031239808258260866245)
                ·
                  refine ⟨5793380857464048423912421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30898031239808258260866245 5793380857464048423912421)
                  ·
                    refine ⟨1086258910774509079483579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793380857464048423912421 1086258910774509079483579)
                    ·
                      rfl

theorem cell23_6346445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6346445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346445 prefixEnd_6346445 := by exact prefixLift 6346445
  have htrace : WordTrace (prefixWord ++ tailWord_6346445) baseStart_6346445 baseEnd_6346445 := by
    simpa [prefixWord, tailWord_6346445, baseEnd_6346445] using wordTrace_append hprefix tailTrace_6346445
  have hstable : (prefixWord ++ tailWord_6346445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346445).length < 2 ^ (prefixWord ++ tailWord_6346445).sum := by decide
  have hdescent : baseEnd_6346445 < baseStart_6346445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346452 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6346452 : Nat := 118140960795 + 6346452 * 2 ^ 59
def prefixEnd_6346452 : Nat := 4983230072969 + 3 ^ 40 * 6346452 * 2
def baseEnd_6346452 : Nat := 3258780326688108711063205

theorem tailTrace_6346452 : CollatzResearch.WordTrace tailWord_6346452 prefixEnd_6346452 3258780326688108711063205 := by
  unfold tailWord_6346452
  simp only [CollatzResearch.WordTrace]
  refine ⟨115737060401947883277000805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154316080535930511036001073 115737060401947883277000805)
  ·
    refine ⟨21700698825365228114437651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115737060401947883277000805 21700698825365228114437651)
    ·
      refine ⟨32551048238047842171656477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21700698825365228114437651 32551048238047842171656477)
      ·
        refine ⟨12206643089267940814371179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32551048238047842171656477 12206643089267940814371179)
        ·
          refine ⟨18309964633901911221556769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206643089267940814371179 18309964633901911221556769)
          ·
            refine ⟨13732473475426433416167577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18309964633901911221556769 13732473475426433416167577)
            ·
              refine ⟨10299355106569825062125683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13732473475426433416167577 10299355106569825062125683)
              ·
                refine ⟨15449032659854737593188525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299355106569825062125683 15449032659854737593188525)
                ·
                  refine ⟨5793387247445526597445697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15449032659854737593188525 5793387247445526597445697)
                  ·
                    refine ⟨4345040435584144948084273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793387247445526597445697 4345040435584144948084273)
                    ·
                      refine ⟨3258780326688108711063205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345040435584144948084273 3258780326688108711063205)
                      ·
                        rfl

theorem cell23_6346452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6346452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346452 prefixEnd_6346452 := by exact prefixLift 6346452
  have htrace : WordTrace (prefixWord ++ tailWord_6346452) baseStart_6346452 baseEnd_6346452 := by
    simpa [prefixWord, tailWord_6346452, baseEnd_6346452] using wordTrace_append hprefix tailTrace_6346452
  have hstable : (prefixWord ++ tailWord_6346452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346452).length < 2 ^ (prefixWord ++ tailWord_6346452).sum := by decide
  have hdescent : baseEnd_6346452 < baseStart_6346452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346465 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_6346465 : Nat := 118140960795 + 6346465 * 2 ^ 59
def prefixEnd_6346465 : Nat := 4983230072969 + 3 ^ 40 * 6346465 * 2
def baseEnd_6346465 : Nat := 3258787001936617160200645

theorem tailTrace_6346465 : CollatzResearch.WordTrace tailWord_6346465 prefixEnd_6346465 3258787001936617160200645 := by
  unfold tailWord_6346465
  simp only [CollatzResearch.WordTrace]
  refine ⟨231474594952848669774224849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154316396635232446516149899 231474594952848669774224849)
  ·
    refine ⟨173605946214636502330668637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231474594952848669774224849 173605946214636502330668637)
    ·
      refine ⟨65102229830488688374000739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173605946214636502330668637 65102229830488688374000739)
      ·
        refine ⟨97653344745733032561001109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65102229830488688374000739 97653344745733032561001109)
        ·
          refine ⟨4577500534956235901296927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97653344745733032561001109 4577500534956235901296927)
          ·
            refine ⟨6866250802434353851945391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577500534956235901296927 6866250802434353851945391)
            ·
              refine ⟨10299376203651530777918087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866250802434353851945391 10299376203651530777918087)
              ·
                refine ⟨15449064305477296166877131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299376203651530777918087 15449064305477296166877131)
                ·
                  refine ⟨23173596458215944250315697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15449064305477296166877131 23173596458215944250315697)
                  ·
                    refine ⟨17380197343661958187736773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23173596458215944250315697 17380197343661958187736773)
                    ·
                      refine ⟨3258787001936617160200645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17380197343661958187736773 3258787001936617160200645)
                      ·
                        rfl

theorem cell23_6346465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_6346465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346465 prefixEnd_6346465 := by exact prefixLift 6346465
  have htrace : WordTrace (prefixWord ++ tailWord_6346465) baseStart_6346465 baseEnd_6346465 := by
    simpa [prefixWord, tailWord_6346465, baseEnd_6346465] using wordTrace_append hprefix tailTrace_6346465
  have hstable : (prefixWord ++ tailWord_6346465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346465).length < 2 ^ (prefixWord ++ tailWord_6346465).sum := by decide
  have hdescent : baseEnd_6346465 < baseStart_6346465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346542 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6346542 : Nat := 118140960795 + 6346542 * 2 ^ 59
def prefixEnd_6346542 : Nat := 4983230072969 + 3 ^ 40 * 6346542 * 2
def baseEnd_6346542 : Nat := 3258826539947013358937791

theorem tailTrace_6346542 : CollatzResearch.WordTrace tailWord_6346542 prefixEnd_6346542 3258826539947013358937791 := by
  unfold tailWord_6346542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934675421696213990597235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154318268915713141283185253 28934675421696213990597235)
  ·
    refine ⟨43402013132544320985895853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28934675421696213990597235 43402013132544320985895853)
    ·
      refine ⟨16275754924704120369710945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43402013132544320985895853 16275754924704120369710945)
      ·
        refine ⟨12206816193528090277283209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16275754924704120369710945 12206816193528090277283209)
        ·
          refine ⟨9155112145146067707962407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12206816193528090277283209 9155112145146067707962407)
          ·
            refine ⟨13732668217719101561943611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155112145146067707962407 13732668217719101561943611)
            ·
              refine ⟨20599002326578652342915417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13732668217719101561943611 20599002326578652342915417)
              ·
                refine ⟨15449251744933989257186563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20599002326578652342915417 15449251744933989257186563)
                ·
                  refine ⟨23173877617400983885779845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15449251744933989257186563 23173877617400983885779845)
                  ·
                    refine ⟨4345102053262684478583721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23173877617400983885779845 4345102053262684478583721)
                    ·
                      refine ⟨3258826539947013358937791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345102053262684478583721 3258826539947013358937791)
                      ·
                        rfl

theorem cell23_6346542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6346542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346542 prefixEnd_6346542 := by exact prefixLift 6346542
  have htrace : WordTrace (prefixWord ++ tailWord_6346542) baseStart_6346542 baseEnd_6346542 := by
    simpa [prefixWord, tailWord_6346542, baseEnd_6346542] using wordTrace_append hprefix tailTrace_6346542
  have hstable : (prefixWord ++ tailWord_6346542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346542).length < 2 ^ (prefixWord ++ tailWord_6346542).sum := by decide
  have hdescent : baseEnd_6346542 < baseStart_6346542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346568 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_6346568 : Nat := 118140960795 + 6346568 * 2 ^ 59
def prefixEnd_6346568 : Nat := 4983230072969 + 3 ^ 40 * 6346568 * 2
def baseEnd_6346568 : Nat := 3258839890444030257212671

theorem tailTrace_6346568 : CollatzResearch.WordTrace tailWord_6346568 prefixEnd_6346568 3258839890444030257212671 := by
  unfold tailWord_6346568
  simp only [CollatzResearch.WordTrace]
  refine ⟨115739175835737759182612179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154318901114317012243482905 115739175835737759182612179)
  ·
    refine ⟨173608763753606638773918269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115739175835737759182612179 173608763753606638773918269)
    ·
      refine ⟨65103286407602489540219351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173608763753606638773918269 65103286407602489540219351)
      ·
        refine ⟨97654929611403734310329027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65103286407602489540219351 97654929611403734310329027)
        ·
          refine ⟨146482394417105601465493541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97654929611403734310329027 146482394417105601465493541)
          ·
            refine ⟨27465448953207300274780039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146482394417105601465493541 27465448953207300274780039)
            ·
              refine ⟨41198173429810950412170059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27465448953207300274780039 41198173429810950412170059)
              ·
                refine ⟨61797260144716425618255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41198173429810950412170059 61797260144716425618255089)
                ·
                  refine ⟨46347945108537319213691317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61797260144716425618255089 46347945108537319213691317)
                  ·
                    refine ⟨4345119853925373676283561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46347945108537319213691317 4345119853925373676283561)
                    ·
                      refine ⟨3258839890444030257212671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345119853925373676283561 3258839890444030257212671)
                      ·
                        rfl

theorem cell23_6346568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_6346568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346568 prefixEnd_6346568 := by exact prefixLift 6346568
  have htrace : WordTrace (prefixWord ++ tailWord_6346568) baseStart_6346568 baseEnd_6346568 := by
    simpa [prefixWord, tailWord_6346568, baseEnd_6346568] using wordTrace_append hprefix tailTrace_6346568
  have hstable : (prefixWord ++ tailWord_6346568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346568).length < 2 ^ (prefixWord ++ tailWord_6346568).sum := by decide
  have hdescent : baseEnd_6346568 < baseStart_6346568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346595 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 2, 5]
def baseStart_6346595 : Nat := 118140960795 + 6346595 * 2 ^ 59
def prefixEnd_6346595 : Nat := 4983230072969 + 3 ^ 40 * 6346595 * 2
def baseEnd_6346595 : Nat := 1086284584807233883858349

theorem tailTrace_6346595 : CollatzResearch.WordTrace tailWord_6346595 prefixEnd_6346595 1086284584807233883858349 := by
  unfold tailWord_6346595
  simp only [CollatzResearch.WordTrace]
  refine ⟨231479336442377701976457239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154319557628251801317638159 231479336442377701976457239)
  ·
    refine ⟨347219004663566552964685859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231479336442377701976457239 347219004663566552964685859)
    ·
      refine ⟨520828506995349829447028789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347219004663566552964685859 520828506995349829447028789)
      ·
        refine ⟨48827672530814046510658949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 520828506995349829447028789 48827672530814046510658949)
        ·
          refine ⟨9155188599527633720748553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48827672530814046510658949 9155188599527633720748553)
          ·
            refine ⟨6866391449645725290561415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155188599527633720748553 6866391449645725290561415)
            ·
              refine ⟨10299587174468587935842123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866391449645725290561415 10299587174468587935842123)
              ·
                refine ⟨15449380761702881903763185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299587174468587935842123 15449380761702881903763185)
                ·
                  refine ⟨11587035571277161427822389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15449380761702881903763185 11587035571277161427822389)
                  ·
                    refine ⟨1086284584807233883858349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11587035571277161427822389 1086284584807233883858349)
                    ·
                      rfl

theorem cell23_6346595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 5].length) (baseStart_6346595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346595 prefixEnd_6346595 := by exact prefixLift 6346595
  have htrace : WordTrace (prefixWord ++ tailWord_6346595) baseStart_6346595 baseEnd_6346595 := by
    simpa [prefixWord, tailWord_6346595, baseEnd_6346595] using wordTrace_append hprefix tailTrace_6346595
  have hstable : (prefixWord ++ tailWord_6346595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346595).length < 2 ^ (prefixWord ++ tailWord_6346595).sum := by decide
  have hdescent : baseEnd_6346595 < baseStart_6346595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346618 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_6346618 : Nat := 118140960795 + 6346618 * 2 ^ 59
def prefixEnd_6346618 : Nat := 4983230072969 + 3 ^ 40 * 6346618 * 2
def baseEnd_6346618 : Nat := 3258865564476755061587441

theorem tailTrace_6346618 : CollatzResearch.WordTrace tailWord_6346618 prefixEnd_6346618 3258865564476755061587441 := by
  unfold tailWord_6346618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57870043830323594226136127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154320116880862917936363005 57870043830323594226136127)
  ·
    refine ⟨86805065745485391339204191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57870043830323594226136127 86805065745485391339204191)
    ·
      refine ⟨130207598618228087008806287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86805065745485391339204191 130207598618228087008806287)
      ·
        refine ⟨195311397927342130513209431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130207598618228087008806287 195311397927342130513209431)
        ·
          refine ⟨292967096891013195769814147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195311397927342130513209431 292967096891013195769814147)
          ·
            refine ⟨439450645336519793654721221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292967096891013195769814147 439450645336519793654721221)
            ·
              refine ⟨82396996000597461310260229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439450645336519793654721221 82396996000597461310260229)
              ·
                refine ⟨15449436750112023995673793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82396996000597461310260229 15449436750112023995673793)
                ·
                  refine ⟨11587077562584017996755345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15449436750112023995673793 11587077562584017996755345)
                  ·
                    refine ⟨8690308171938013497566509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11587077562584017996755345 8690308171938013497566509)
                    ·
                      refine ⟨3258865564476755061587441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8690308171938013497566509 3258865564476755061587441)
                      ·
                        rfl

theorem cell23_6346618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_6346618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346618 prefixEnd_6346618 := by exact prefixLift 6346618
  have htrace : WordTrace (prefixWord ++ tailWord_6346618) baseStart_6346618 baseEnd_6346618 := by
    simpa [prefixWord, tailWord_6346618, baseEnd_6346618] using wordTrace_append hprefix tailTrace_6346618
  have hstable : (prefixWord ++ tailWord_6346618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346618).length < 2 ^ (prefixWord ++ tailWord_6346618).sum := by decide
  have hdescent : baseEnd_6346618 < baseStart_6346618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346675 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 2, 3, 2]
def baseStart_6346675 : Nat := 118140960795 + 6346675 * 2 ^ 59
def prefixEnd_6346675 : Nat := 4983230072969 + 3 ^ 40 * 6346675 * 2
def baseEnd_6346675 : Nat := 3258894832874061338574679

theorem tailTrace_6346675 : CollatzResearch.WordTrace tailWord_6346675 prefixEnd_6346675 3258894832874061338574679 := by
  unfold tailWord_6346675
  simp only [CollatzResearch.WordTrace]
  refine ⟨231482254282087875639369479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154321502854725250426246319 231482254282087875639369479)
  ·
    refine ⟨347223381423131813459054219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231482254282087875639369479 347223381423131813459054219)
    ·
      refine ⟨520835072134697720188581329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347223381423131813459054219 520835072134697720188581329)
      ·
        refine ⟨390626304101023290141435997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520835072134697720188581329 390626304101023290141435997)
        ·
          refine ⟨146484864037883733803038499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390626304101023290141435997 146484864037883733803038499)
          ·
            refine ⟨219727296056825600704557749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146484864037883733803038499 219727296056825600704557749)
            ·
              refine ⟨20599434005327400066052289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219727296056825600704557749 20599434005327400066052289)
              ·
                refine ⟨15449575503995550049539217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20599434005327400066052289 15449575503995550049539217)
                ·
                  refine ⟨11587181627996662537154413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15449575503995550049539217 11587181627996662537154413)
                  ·
                    refine ⟨4345193110498748451432905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11587181627996662537154413 4345193110498748451432905)
                    ·
                      refine ⟨3258894832874061338574679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345193110498748451432905 3258894832874061338574679)
                      ·
                        rfl

theorem cell23_6346675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3, 2].length) (baseStart_6346675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346675 prefixEnd_6346675 := by exact prefixLift 6346675
  have htrace : WordTrace (prefixWord ++ tailWord_6346675) baseStart_6346675 baseEnd_6346675 := by
    simpa [prefixWord, tailWord_6346675, baseEnd_6346675] using wordTrace_append hprefix tailTrace_6346675
  have hstable : (prefixWord ++ tailWord_6346675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346675).length < 2 ^ (prefixWord ++ tailWord_6346675).sum := by decide
  have hdescent : baseEnd_6346675 < baseStart_6346675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346676 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6346676 : Nat := 118140960795 + 6346676 * 2 ^ 59
def prefixEnd_6346676 : Nat := 4983230072969 + 3 ^ 40 * 6346676 * 2
def baseEnd_6346676 : Nat := 1086298448784905278220725

theorem tailTrace_6346676 : CollatzResearch.WordTrace tailWord_6346676 prefixEnd_6346676 1086298448784905278220725 := by
  unfold tailWord_6346676
  simp only [CollatzResearch.WordTrace]
  refine ⟨115741145377542126405077941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154321527170056168540103921 115741145377542126405077941)
  ·
    refine ⟨10850732379144574350476057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115741145377542126405077941 10850732379144574350476057)
    ·
      refine ⟨8138049284358430762857043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10850732379144574350476057 8138049284358430762857043)
      ·
        refine ⟨12207073926537646144285565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138049284358430762857043 12207073926537646144285565)
        ·
          refine ⟨4577652722451617304107087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12207073926537646144285565 4577652722451617304107087)
          ·
            refine ⟨6866479083677425956160631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577652722451617304107087 6866479083677425956160631)
            ·
              refine ⟨10299718625516138934240947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866479083677425956160631 10299718625516138934240947)
              ·
                refine ⟨15449577938274208401361421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299718625516138934240947 15449577938274208401361421)
                ·
                  refine ⟨5793591726852828150510533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15449577938274208401361421 5793591726852828150510533)
                  ·
                    refine ⟨1086298448784905278220725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793591726852828150510533 1086298448784905278220725)
                    ·
                      rfl

theorem cell23_6346676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6346676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346676 prefixEnd_6346676 := by exact prefixLift 6346676
  have htrace : WordTrace (prefixWord ++ tailWord_6346676) baseStart_6346676 baseEnd_6346676 := by
    simpa [prefixWord, tailWord_6346676, baseEnd_6346676] using wordTrace_append hprefix tailTrace_6346676
  have hstable : (prefixWord ++ tailWord_6346676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346676).length < 2 ^ (prefixWord ++ tailWord_6346676).sum := by decide
  have hdescent : baseEnd_6346676 < baseStart_6346676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346688 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_6346688 : Nat := 118140960795 + 6346688 * 2 ^ 59
def prefixEnd_6346688 : Nat := 4983230072969 + 3 ^ 40 * 6346688 * 2
def baseEnd_6346688 : Nat := 3258901508122569787712119

theorem tailTrace_6346688 : CollatzResearch.WordTrace tailWord_6346688 prefixEnd_6346688 3258901508122569787712119 := by
  unfold tailWord_6346688
  simp only [CollatzResearch.WordTrace]
  refine ⟨115741364215520389429796359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154321818954027185906395145 115741364215520389429796359)
  ·
    refine ⟨173612046323280584144694539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115741364215520389429796359 173612046323280584144694539)
    ·
      refine ⟨260418069484920876217041809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173612046323280584144694539 260418069484920876217041809)
      ·
        refine ⟨195313552113690657162781357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260418069484920876217041809 195313552113690657162781357)
        ·
          refine ⟨73242582042633996436043009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195313552113690657162781357 73242582042633996436043009)
          ·
            refine ⟨54931936531975497327032257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73242582042633996436043009 54931936531975497327032257)
            ·
              refine ⟨41198952398981622995274193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54931936531975497327032257 41198952398981622995274193)
              ·
                refine ⟨30899214299236217246455645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41198952398981622995274193 30899214299236217246455645)
                ·
                  refine ⟨11587205362213581467420867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30899214299236217246455645 11587205362213581467420867)
                  ·
                    refine ⟨17380808043320372201131301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11587205362213581467420867 17380808043320372201131301)
                    ·
                      refine ⟨3258901508122569787712119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17380808043320372201131301 3258901508122569787712119)
                      ·
                        rfl

theorem cell23_6346688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_6346688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346688 prefixEnd_6346688 := by exact prefixLift 6346688
  have htrace : WordTrace (prefixWord ++ tailWord_6346688) baseStart_6346688 baseEnd_6346688 := by
    simpa [prefixWord, tailWord_6346688, baseEnd_6346688] using wordTrace_append hprefix tailTrace_6346688
  have hstable : (prefixWord ++ tailWord_6346688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346688).length < 2 ^ (prefixWord ++ tailWord_6346688).sum := by decide
  have hdescent : baseEnd_6346688 < baseStart_6346688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346711 : List Nat := [1, 1, 3, 2, 1, 1, 3, 11]
def baseStart_6346711 : Nat := 118140960795 + 6346711 * 2 ^ 59
def prefixEnd_6346711 : Nat := 4983230072969 + 3 ^ 40 * 6346711 * 2
def baseEnd_6346711 : Nat := 120700493265837896212019

theorem tailTrace_6346711 : CollatzResearch.WordTrace tailWord_6346711 prefixEnd_6346711 120700493265837896212019 := by
  unfold tailWord_6346711
  simp only [CollatzResearch.WordTrace]
  refine ⟨231483567309957453787679987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154322378206638302525119991 231483567309957453787679987)
  ·
    refine ⟨347225350964936180681519981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231483567309957453787679987 347225350964936180681519981)
    ·
      refine ⟨130209506611851067755569993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347225350964936180681519981 130209506611851067755569993)
      ·
        refine ⟨97657129958888300816677495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130209506611851067755569993 97657129958888300816677495)
        ·
          refine ⟨146485694938332451225016243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97657129958888300816677495 146485694938332451225016243)
          ·
            refine ⟨219728542407498676837524365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146485694938332451225016243 219728542407498676837524365)
            ·
              refine ⟨82398203402812003814071637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219728542407498676837524365 82398203402812003814071637)
              ·
                refine ⟨120700493265837896212019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82398203402812003814071637 120700493265837896212019)
                ·
                  rfl

theorem cell23_6346711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 11].length) (baseStart_6346711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346711 prefixEnd_6346711 := by exact prefixLift 6346711
  have htrace : WordTrace (prefixWord ++ tailWord_6346711) baseStart_6346711 baseEnd_6346711 := by
    simpa [prefixWord, tailWord_6346711, baseEnd_6346711] using wordTrace_append hprefix tailTrace_6346711
  have hstable : (prefixWord ++ tailWord_6346711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346711).length < 2 ^ (prefixWord ++ tailWord_6346711).sum := by decide
  have hdescent : baseEnd_6346711 < baseStart_6346711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346756 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6346756 : Nat := 118140960795 + 6346756 * 2 ^ 59
def prefixEnd_6346756 : Nat := 4983230072969 + 3 ^ 40 * 6346756 * 2
def baseEnd_6346756 : Nat := 3258936424807075521661807

theorem tailTrace_6346756 : CollatzResearch.WordTrace tailWord_6346756 prefixEnd_6346756 3258936424807075521661807 := by
  unfold tailWord_6346756
  simp only [CollatzResearch.WordTrace]
  refine ⟨115742604297397213236534061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154323472396529617648712081 115742604297397213236534061)
  ·
    refine ⟨43403476611523954963700273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115742604297397213236534061 43403476611523954963700273)
    ·
      refine ⟨32552607458642966222775205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43403476611523954963700273 32552607458642966222775205)
      ·
        refine ⟨6103613898495556166770351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32552607458642966222775205 6103613898495556166770351)
        ·
          refine ⟨9155420847743334250155527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103613898495556166770351 9155420847743334250155527)
          ·
            refine ⟨13733131271615001375233291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155420847743334250155527 13733131271615001375233291)
            ·
              refine ⟨20599696907422502062849937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13733131271615001375233291 20599696907422502062849937)
              ·
                refine ⟨15449772680566876547137453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20599696907422502062849937 15449772680566876547137453)
                ·
                  refine ⟨5793664755212578705176545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15449772680566876547137453 5793664755212578705176545)
                  ·
                    refine ⟨4345248566409434028882409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793664755212578705176545 4345248566409434028882409)
                    ·
                      refine ⟨3258936424807075521661807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345248566409434028882409 3258936424807075521661807)
                      ·
                        rfl

theorem cell23_6346756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6346756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346756 prefixEnd_6346756 := by exact prefixLift 6346756
  have htrace : WordTrace (prefixWord ++ tailWord_6346756) baseStart_6346756 baseEnd_6346756 := by
    simpa [prefixWord, tailWord_6346756, baseEnd_6346756] using wordTrace_append hprefix tailTrace_6346756
  have hstable : (prefixWord ++ tailWord_6346756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346756).length < 2 ^ (prefixWord ++ tailWord_6346756).sum := by decide
  have hdescent : baseEnd_6346756 < baseStart_6346756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346789 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 3]
def baseStart_6346789 : Nat := 118140960795 + 6346789 * 2 ^ 59
def prefixEnd_6346789 : Nat := 4983230072969 + 3 ^ 40 * 6346789 * 2
def baseEnd_6346789 : Nat := 3258953369668673892549155

theorem tailTrace_6346789 : CollatzResearch.WordTrace tailWord_6346789 prefixEnd_6346789 3258953369668673892549155 := by
  unfold tailWord_6346789
  simp only [CollatzResearch.WordTrace]
  refine ⟨231486412203674873109019421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154324274802449915406012947 231486412203674873109019421)
  ·
    refine ⟨86807404576378077415882283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231486412203674873109019421 86807404576378077415882283)
    ·
      refine ⟨130211106864567116123823425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86807404576378077415882283 130211106864567116123823425)
      ·
        refine ⟨97658330148425337092867569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130211106864567116123823425 97658330148425337092867569)
        ·
          refine ⟨73243747611319002819650677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97658330148425337092867569 73243747611319002819650677)
          ·
            refine ⟨6866601338561156514342251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73243747611319002819650677 6866601338561156514342251)
            ·
              refine ⟨10299902007841734771513377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866601338561156514342251 10299902007841734771513377)
              ·
                refine ⟨7724926505881301078635033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10299902007841734771513377 7724926505881301078635033)
                ·
                  refine ⟨5793694879410975808976275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7724926505881301078635033 5793694879410975808976275)
                  ·
                    refine ⟨8690542319116463713464413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793694879410975808976275 8690542319116463713464413)
                    ·
                      refine ⟨3258953369668673892549155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8690542319116463713464413 3258953369668673892549155)
                      ·
                        rfl

theorem cell23_6346789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_6346789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346789 prefixEnd_6346789 := by exact prefixLift 6346789
  have htrace : WordTrace (prefixWord ++ tailWord_6346789) baseStart_6346789 baseEnd_6346789 := by
    simpa [prefixWord, tailWord_6346789, baseEnd_6346789] using wordTrace_append hprefix tailTrace_6346789
  have hstable : (prefixWord ++ tailWord_6346789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346789).length < 2 ^ (prefixWord ++ tailWord_6346789).sum := by decide
  have hdescent : baseEnd_6346789 < baseStart_6346789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346806 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6346806 : Nat := 118140960795 + 6346806 * 2 ^ 59
def prefixEnd_6346806 : Nat := 4983230072969 + 3 ^ 40 * 6346806 * 2
def baseEnd_6346806 : Nat := 3258962098839800326036577

theorem tailTrace_6346806 : CollatzResearch.WordTrace tailWord_6346806 prefixEnd_6346806 3258962098839800326036577 := by
  unfold tailWord_6346806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467939515288330313274267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154324688163075523341592181 14467939515288330313274267)
  ·
    refine ⟨21701909272932495469911401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467939515288330313274267 21701909272932495469911401)
    ·
      refine ⟨16276431954699371602433551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21701909272932495469911401 16276431954699371602433551)
      ·
        refine ⟨24414647932049057403650327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16276431954699371602433551 24414647932049057403650327)
        ·
          refine ⟨36621971898073586105475491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24414647932049057403650327 36621971898073586105475491)
          ·
            refine ⟨54932957847110379158213237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36621971898073586105475491 54932957847110379158213237)
            ·
              refine ⟨5149964798166598046082491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54932957847110379158213237 5149964798166598046082491)
              ·
                refine ⟨7724947197249897069123737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149964798166598046082491 7724947197249897069123737)
                ·
                  refine ⟨5793710397937422801842803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7724947197249897069123737 5793710397937422801842803)
                  ·
                    refine ⟨8690565596906134202764205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793710397937422801842803 8690565596906134202764205)
                    ·
                      refine ⟨3258962098839800326036577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8690565596906134202764205 3258962098839800326036577)
                      ·
                        rfl

theorem cell23_6346806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6346806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346806 prefixEnd_6346806 := by exact prefixLift 6346806
  have htrace : WordTrace (prefixWord ++ tailWord_6346806) baseStart_6346806 baseEnd_6346806 := by
    simpa [prefixWord, tailWord_6346806, baseEnd_6346806] using wordTrace_append hprefix tailTrace_6346806
  have hstable : (prefixWord ++ tailWord_6346806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346806).length < 2 ^ (prefixWord ++ tailWord_6346806).sum := by decide
  have hdescent : baseEnd_6346806 < baseStart_6346806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346829 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6346829 : Nat := 118140960795 + 6346829 * 2 ^ 59
def prefixEnd_6346829 : Nat := 4983230072969 + 3 ^ 40 * 6346829 * 2
def baseEnd_6346829 : Nat := 3258973908894853736048971

theorem tailTrace_6346829 : CollatzResearch.WordTrace tailWord_6346829 prefixEnd_6346829 3258973908894853736048971 := by
  unfold tailWord_6346829
  simp only [CollatzResearch.WordTrace]
  refine ⟨231487871123529959940475541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154325247415686639960317027 231487871123529959940475541)
  ·
    refine ⟨10850993958915466872209791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231487871123529959940475541 10850993958915466872209791)
    ·
      refine ⟨16276490938373200308314687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850993958915466872209791 16276490938373200308314687)
      ·
        refine ⟨24414736407559800462472031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16276490938373200308314687 24414736407559800462472031)
        ·
          refine ⟨36622104611339700693708047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24414736407559800462472031 36622104611339700693708047)
          ·
            refine ⟨54933156917009551040562071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36622104611339700693708047 54933156917009551040562071)
            ·
              refine ⟨82399735375514326560843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54933156917009551040562071 82399735375514326560843107)
              ·
                refine ⟨123599603063271489841264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82399735375514326560843107 123599603063271489841264661)
                ·
                  refine ⟨5793731393590851086309281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123599603063271489841264661 5793731393590851086309281)
                  ·
                    refine ⟨4345298545193138314731961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793731393590851086309281 4345298545193138314731961)
                    ·
                      refine ⟨3258973908894853736048971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345298545193138314731961 3258973908894853736048971)
                      ·
                        rfl

theorem cell23_6346829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6346829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346829 prefixEnd_6346829 := by exact prefixLift 6346829
  have htrace : WordTrace (prefixWord ++ tailWord_6346829) baseStart_6346829 baseEnd_6346829 := by
    simpa [prefixWord, tailWord_6346829, baseEnd_6346829] using wordTrace_append hprefix tailTrace_6346829
  have hstable : (prefixWord ++ tailWord_6346829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346829).length < 2 ^ (prefixWord ++ tailWord_6346829).sum := by decide
  have hdescent : baseEnd_6346829 < baseStart_6346829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346929 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 3, 4]
def baseStart_6346929 : Nat := 118140960795 + 6346929 * 2 ^ 59
def prefixEnd_6346929 : Nat := 4983230072969 + 3 ^ 40 * 6346929 * 2
def baseEnd_6346929 : Nat := 1086341752320101114932837

theorem tailTrace_6346929 : CollatzResearch.WordTrace tailWord_6346929 prefixEnd_6346929 1086341752320101114932837 := by
  unfold tailWord_6346929
  simp only [CollatzResearch.WordTrace]
  refine ⟨231491518423167677019115841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154327678948778451346077227 231491518423167677019115841)
  ·
    refine ⟨173618638817375757764336881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231491518423167677019115841 173618638817375757764336881)
    ·
      refine ⟨130213979113031818323252661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173618638817375757764336881 130213979113031818323252661)
      ·
        refine ⟨12207560541846732967804937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130213979113031818323252661 12207560541846732967804937)
        ·
          refine ⟨9155670406385049725853703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12207560541846732967804937 9155670406385049725853703)
          ·
            refine ⟨13733505609577574588780555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155670406385049725853703 13733505609577574588780555)
            ·
              refine ⟨20600258414366361883170833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13733505609577574588780555 20600258414366361883170833)
              ·
                refine ⟨15450193810774771412378125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20600258414366361883170833 15450193810774771412378125)
                ·
                  refine ⟨5793822679040539279641797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15450193810774771412378125 5793822679040539279641797)
                  ·
                    refine ⟨1086341752320101114932837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793822679040539279641797 1086341752320101114932837)
                    ·
                      rfl

theorem cell23_6346929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_6346929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346929 prefixEnd_6346929 := by exact prefixLift 6346929
  have htrace : WordTrace (prefixWord ++ tailWord_6346929) baseStart_6346929 baseEnd_6346929 := by
    simpa [prefixWord, tailWord_6346929, baseEnd_6346929] using wordTrace_append hprefix tailTrace_6346929
  have hstable : (prefixWord ++ tailWord_6346929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346929).length < 2 ^ (prefixWord ++ tailWord_6346929).sum := by decide
  have hdescent : baseEnd_6346929 < baseStart_6346929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346952 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_6346952 : Nat := 118140960795 + 6346952 * 2 ^ 59
def prefixEnd_6346952 : Nat := 4983230072969 + 3 ^ 40 * 6346952 * 2
def baseEnd_6346952 : Nat := 3259037067015356754810905

theorem tailTrace_6346952 : CollatzResearch.WordTrace tailWord_6346952 prefixEnd_6346952 3259037067015356754810905 := by
  unfold tailWord_6346952
  simp only [CollatzResearch.WordTrace]
  refine ⟨115746178651042175973601555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154328238201389567964802073 115746178651042175973601555)
  ·
    refine ⟨173619267976563263960402333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115746178651042175973601555 173619267976563263960402333)
    ·
      refine ⟨65107225491211223985150875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173619267976563263960402333 65107225491211223985150875)
      ·
        refine ⟨97660838236816835977726313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65107225491211223985150875 97660838236816835977726313)
        ·
          refine ⟨73245628677612626983294735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97660838236816835977726313 73245628677612626983294735)
          ·
            refine ⟨109868443016418940474942103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73245628677612626983294735 109868443016418940474942103)
            ·
              refine ⟨164802664524628410712413155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109868443016418940474942103 164802664524628410712413155)
              ·
                refine ⟨247203996786942616068619733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164802664524628410712413155 247203996786942616068619733)
                ·
                  refine ⟨5793843674693967564108275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 247203996786942616068619733 5793843674693967564108275)
                  ·
                    refine ⟨8690765512040951346162413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793843674693967564108275 8690765512040951346162413)
                    ·
                      refine ⟨3259037067015356754810905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8690765512040951346162413 3259037067015356754810905)
                      ·
                        rfl

theorem cell23_6346952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_6346952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346952 prefixEnd_6346952 := by exact prefixLift 6346952
  have htrace : WordTrace (prefixWord ++ tailWord_6346952) baseStart_6346952 baseEnd_6346952 := by
    simpa [prefixWord, tailWord_6346952, baseEnd_6346952] using wordTrace_append hprefix tailTrace_6346952
  have hstable : (prefixWord ++ tailWord_6346952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346952).length < 2 ^ (prefixWord ++ tailWord_6346952).sum := by decide
  have hdescent : baseEnd_6346952 < baseStart_6346952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6346995 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_6346995 : Nat := 118140960795 + 6346995 * 2 ^ 59
def prefixEnd_6346995 : Nat := 4983230072969 + 3 ^ 40 * 6346995 * 2
def baseEnd_6346995 : Nat := 3259059146683500086573207

theorem tailTrace_6346995 : CollatzResearch.WordTrace tailWord_6346995 prefixEnd_6346995 3259059146683500086573207 := by
  unfold tailWord_6346995
  simp only [CollatzResearch.WordTrace]
  refine ⟨231493925640928570291018439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154329283760619046860678959 231493925640928570291018439)
  ·
    refine ⟨347240888461392855436527659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231493925640928570291018439 347240888461392855436527659)
    ·
      refine ⟨520861332692089283154791489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347240888461392855436527659 520861332692089283154791489)
      ·
        refine ⟨390645999519066962366093617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520861332692089283154791489 390645999519066962366093617)
        ·
          refine ⟨292984499639300221774570213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390645999519066962366093617 292984499639300221774570213)
          ·
            refine ⟨54934593682368791582731915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292984499639300221774570213 54934593682368791582731915)
            ·
              refine ⟨82401890523553187374097873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54934593682368791582731915 82401890523553187374097873)
              ·
                refine ⟨61801417892664890530573405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82401890523553187374097873 61801417892664890530573405)
                ·
                  refine ⟨23175531709749333948965027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61801417892664890530573405 23175531709749333948965027)
                  ·
                    refine ⟨34763297564624000923447541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23175531709749333948965027 34763297564624000923447541)
                    ·
                      refine ⟨3259059146683500086573207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34763297564624000923447541 3259059146683500086573207)
                      ·
                        rfl

theorem cell23_6346995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_6346995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6346995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6346995 prefixEnd_6346995 := by exact prefixLift 6346995
  have htrace : WordTrace (prefixWord ++ tailWord_6346995) baseStart_6346995 baseEnd_6346995 := by
    simpa [prefixWord, tailWord_6346995, baseEnd_6346995] using wordTrace_append hprefix tailTrace_6346995
  have hstable : (prefixWord ++ tailWord_6346995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6346995).length < 2 ^ (prefixWord ++ tailWord_6346995).sum := by decide
  have hdescent : baseEnd_6346995 < baseStart_6346995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6346995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347002 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_6347002 : Nat := 118140960795 + 6347002 * 2 ^ 59
def prefixEnd_6347002 : Nat := 4983230072969 + 3 ^ 40 * 6347002 * 2
def baseEnd_6347002 : Nat := 1086354247016027186395225

theorem tailTrace_6347002 : CollatzResearch.WordTrace tailWord_6347002 prefixEnd_6347002 1086354247016027186395225 := by
  unfold tailWord_6347002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57873545237975802621630815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154329453967935473657682173 57873545237975802621630815)
  ·
    refine ⟨86810317856963703932446223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57873545237975802621630815 86810317856963703932446223)
    ·
      refine ⟨130215476785445555898669335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86810317856963703932446223 130215476785445555898669335)
      ·
        refine ⟨195323215178168333848004003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130215476785445555898669335 195323215178168333848004003)
        ·
          refine ⟨292984822767252500772006005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195323215178168333848004003 292984822767252500772006005)
          ·
            refine ⟨27467327134429921947375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292984822767252500772006005 27467327134429921947375563)
            ·
              refine ⟨41200990701644882921063345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27467327134429921947375563 41200990701644882921063345)
              ·
                refine ⟨30900743026233662190797509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41200990701644882921063345 30900743026233662190797509)
                ·
                  refine ⟨5793889317418811660774533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30900743026233662190797509 5793889317418811660774533)
                  ·
                    refine ⟨1086354247016027186395225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5793889317418811660774533 1086354247016027186395225)
                    ·
                      rfl

theorem cell23_6347002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_6347002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347002 prefixEnd_6347002 := by exact prefixLift 6347002
  have htrace : WordTrace (prefixWord ++ tailWord_6347002) baseStart_6347002 baseEnd_6347002 := by
    simpa [prefixWord, tailWord_6347002, baseEnd_6347002] using wordTrace_append hprefix tailTrace_6347002
  have hstable : (prefixWord ++ tailWord_6347002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347002).length < 2 ^ (prefixWord ++ tailWord_6347002).sum := by decide
  have hdescent : baseEnd_6347002 < baseStart_6347002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347055 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_6347055 : Nat := 118140960795 + 6347055 * 2 ^ 59
def prefixEnd_6347055 : Nat := 4983230072969 + 3 ^ 40 * 6347055 * 2
def baseEnd_6347055 : Nat := 3259089955522769851822931

theorem tailTrace_6347055 : CollatzResearch.WordTrace tailWord_6347055 prefixEnd_6347055 3259089955522769851822931 := by
  unfold tailWord_6347055
  simp only [CollatzResearch.WordTrace]
  refine ⟨231496114020711200538202619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154330742680474133692135079 231496114020711200538202619)
  ·
    refine ⟨347244171031066800807303929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231496114020711200538202619 347244171031066800807303929)
    ·
      refine ⟨260433128273300100605477947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347244171031066800807303929 260433128273300100605477947)
      ·
        refine ⟨390649692409950150908216921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260433128273300100605477947 390649692409950150908216921)
        ·
          refine ⟨292987269307462613181162691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390649692409950150908216921 292987269307462613181162691)
          ·
            refine ⟨439480903961193919771744037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292987269307462613181162691 439480903961193919771744037)
            ·
              refine ⟨82402669492723859957202007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439480903961193919771744037 82402669492723859957202007)
              ·
                refine ⟨123604004239085789935803011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82402669492723859957202007 123604004239085789935803011)
                ·
                  refine ⟨185406006358628684903704517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123604004239085789935803011 185406006358628684903704517)
                  ·
                    refine ⟨34763626192242878419444597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185406006358628684903704517 34763626192242878419444597)
                    ·
                      refine ⟨3259089955522769851822931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34763626192242878419444597 3259089955522769851822931)
                      ·
                        rfl

theorem cell23_6347055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_6347055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347055 prefixEnd_6347055 := by exact prefixLift 6347055
  have htrace : WordTrace (prefixWord ++ tailWord_6347055) baseStart_6347055 baseEnd_6347055 := by
    simpa [prefixWord, tailWord_6347055, baseEnd_6347055] using wordTrace_append hprefix tailTrace_6347055
  have hstable : (prefixWord ++ tailWord_6347055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347055).length < 2 ^ (prefixWord ++ tailWord_6347055).sum := by decide
  have hdescent : baseEnd_6347055 < baseStart_6347055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347092 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_6347092 : Nat := 118140960795 + 6347092 * 2 ^ 59
def prefixEnd_6347092 : Nat := 4983230072969 + 3 ^ 40 * 6347092 * 2
def baseEnd_6347092 : Nat := 1086369651435662069020087

theorem tailTrace_6347092 : CollatzResearch.WordTrace tailWord_6347092 prefixEnd_6347092 1086369651435662069020087 := by
  unfold tailWord_6347092
  simp only [CollatzResearch.WordTrace]
  refine ⟨115748731760788577928649765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154331642347718103904866353 115748731760788577928649765)
  ·
    refine ⟨21702887205147858361621831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115748731760788577928649765 21702887205147858361621831)
    ·
      refine ⟨32554330807721787542432747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21702887205147858361621831 32554330807721787542432747)
      ·
        refine ⟨48831496211582681313649121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32554330807721787542432747 48831496211582681313649121)
        ·
          refine ⟨36623622158687010985236841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48831496211582681313649121 36623622158687010985236841)
          ·
            refine ⟨27467716619015258238927631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36623622158687010985236841 27467716619015258238927631)
            ·
              refine ⟨41201574928522887358391447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27467716619015258238927631 41201574928522887358391447)
              ·
                refine ⟨61802362392784331037587171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41201574928522887358391447 61802362392784331037587171)
                ·
                  refine ⟨92703543589176496556380757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61802362392784331037587171 92703543589176496556380757)
                  ·
                    refine ⟨1086369651435662069020087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92703543589176496556380757 1086369651435662069020087)
                    ·
                      rfl

theorem cell23_6347092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_6347092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347092 prefixEnd_6347092 := by exact prefixLift 6347092
  have htrace : WordTrace (prefixWord ++ tailWord_6347092) baseStart_6347092 baseEnd_6347092 := by
    simpa [prefixWord, tailWord_6347092, baseEnd_6347092] using wordTrace_append hprefix tailTrace_6347092
  have hstable : (prefixWord ++ tailWord_6347092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347092).length < 2 ^ (prefixWord ++ tailWord_6347092).sum := by decide
  have hdescent : baseEnd_6347092 < baseStart_6347092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347133 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_6347133 : Nat := 118140960795 + 6347133 * 2 ^ 59
def prefixEnd_6347133 : Nat := 4983230072969 + 3 ^ 40 * 6347133 * 2
def baseEnd_6347133 : Nat := 3259130007013820546647573

theorem tailTrace_6347133 : CollatzResearch.WordTrace tailWord_6347133 prefixEnd_6347133 3259130007013820546647573 := by
  unfold tailWord_6347133
  simp only [CollatzResearch.WordTrace]
  refine ⟨231498958914428619859542053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154332639276285746573028035 231498958914428619859542053)
  ·
    refine ⟨43406054796455366223664135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231498958914428619859542053 43406054796455366223664135)
    ·
      refine ⟨65109082194683049335496203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43406054796455366223664135 65109082194683049335496203)
      ·
        refine ⟨97663623292024574003244305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65109082194683049335496203 97663623292024574003244305)
        ·
          refine ⟨73247717469018430502433229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97663623292024574003244305 73247717469018430502433229)
          ·
            refine ⟨27467894050881911438412461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73247717469018430502433229 27467894050881911438412461)
            ·
              refine ⟨10300460269080716789404673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27467894050881911438412461 10300460269080716789404673)
              ·
                refine ⟨7725345201810537592053505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300460269080716789404673 7725345201810537592053505)
                ·
                  refine ⟨5794008901357903194040129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725345201810537592053505 5794008901357903194040129)
                  ·
                    refine ⟨4345506676018427395530097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794008901357903194040129 4345506676018427395530097)
                    ·
                      refine ⟨3259130007013820546647573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345506676018427395530097 3259130007013820546647573)
                      ·
                        rfl

theorem cell23_6347133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_6347133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347133 prefixEnd_6347133 := by exact prefixLift 6347133
  have htrace : WordTrace (prefixWord ++ tailWord_6347133) baseStart_6347133 baseEnd_6347133 := by
    simpa [prefixWord, tailWord_6347133, baseEnd_6347133] using wordTrace_append hprefix tailTrace_6347133
  have hstable : (prefixWord ++ tailWord_6347133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347133).length < 2 ^ (prefixWord ++ tailWord_6347133).sum := by decide
  have hdescent : baseEnd_6347133 < baseStart_6347133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347139 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 7]
def baseStart_6347139 : Nat := 118140960795 + 6347139 * 2 ^ 59
def prefixEnd_6347139 : Nat := 4983230072969 + 3 ^ 40 * 6347139 * 2
def baseEnd_6347139 : Nat := 362125898655305280352505

theorem tailTrace_6347139 : CollatzResearch.WordTrace tailWord_6347139 prefixEnd_6347139 362125898655305280352505 := by
  unfold tailWord_6347139
  simp only [CollatzResearch.WordTrace]
  refine ⟨231499177752406882884260471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154332785168271255256173647 231499177752406882884260471)
  ·
    refine ⟨347248766628610324326390707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231499177752406882884260471 347248766628610324326390707)
    ·
      refine ⟨520873149942915486489586061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347248766628610324326390707 520873149942915486489586061)
      ·
        refine ⟨195327431228593307433594773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520873149942915486489586061 195327431228593307433594773)
        ·
          refine ⟨9155973338840311285949755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195327431228593307433594773 9155973338840311285949755)
          ·
            refine ⟨13733960008260466928924633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155973338840311285949755 13733960008260466928924633)
            ·
              refine ⟨10300470006195350196693475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13733960008260466928924633 10300470006195350196693475)
              ·
                refine ⟨15450705009293025295040213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10300470006195350196693475 15450705009293025295040213)
                ·
                  refine ⟨362125898655305280352505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15450705009293025295040213 362125898655305280352505)
                  ·
                    rfl

theorem cell23_6347139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 7].length) (baseStart_6347139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347139 prefixEnd_6347139 := by exact prefixLift 6347139
  have htrace : WordTrace (prefixWord ++ tailWord_6347139) baseStart_6347139 baseEnd_6347139 := by
    simpa [prefixWord, tailWord_6347139, baseEnd_6347139] using wordTrace_append hprefix tailTrace_6347139
  have hstable : (prefixWord ++ tailWord_6347139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347139).length < 2 ^ (prefixWord ++ tailWord_6347139).sum := by decide
  have hdescent : baseEnd_6347139 < baseStart_6347139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347159 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 5, 2]
def baseStart_6347159 : Nat := 118140960795 + 6347159 * 2 ^ 59
def prefixEnd_6347159 : Nat := 4983230072969 + 3 ^ 40 * 6347159 * 2
def baseEnd_6347159 : Nat := 3259143357510837444922453

theorem tailTrace_6347159 : CollatzResearch.WordTrace tailWord_6347159 prefixEnd_6347159 3259143357510837444922453 := by
  unfold tailWord_6347159
  simp only [CollatzResearch.WordTrace]
  refine ⟨231499907212334426299988531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154333271474889617533325687 231499907212334426299988531)
  ·
    refine ⟨347249860818501639449982797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231499907212334426299988531 347249860818501639449982797)
    ·
      refine ⟨130218697806938114793743549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347249860818501639449982797 130218697806938114793743549)
      ·
        refine ⟨48832011677601793047653831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130218697806938114793743549 48832011677601793047653831)
        ·
          refine ⟨73248017516402689571480747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48832011677601793047653831 73248017516402689571480747)
          ·
            refine ⟨109872026274604034357221121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73248017516402689571480747 109872026274604034357221121)
            ·
              refine ⟨82404019705953025767915841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109872026274604034357221121 82404019705953025767915841)
              ·
                refine ⟨61803014779464769325936881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82404019705953025767915841 61803014779464769325936881)
                ·
                  refine ⟨46352261084598576994452661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61803014779464769325936881 46352261084598576994452661)
                  ·
                    refine ⟨4345524476681116593229937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46352261084598576994452661 4345524476681116593229937)
                    ·
                      refine ⟨3259143357510837444922453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345524476681116593229937 3259143357510837444922453)
                      ·
                        rfl

theorem cell23_6347159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_6347159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347159 prefixEnd_6347159 := by exact prefixLift 6347159
  have htrace : WordTrace (prefixWord ++ tailWord_6347159) baseStart_6347159 baseEnd_6347159 := by
    simpa [prefixWord, tailWord_6347159, baseEnd_6347159] using wordTrace_append hprefix tailTrace_6347159
  have hstable : (prefixWord ++ tailWord_6347159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347159).length < 2 ^ (prefixWord ++ tailWord_6347159).sum := by decide
  have hdescent : baseEnd_6347159 < baseStart_6347159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347201 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6347201 : Nat := 118140960795 + 6347201 * 2 ^ 59
def prefixEnd_6347201 : Nat := 4983230072969 + 3 ^ 40 * 6347201 * 2
def baseEnd_6347201 : Nat := 3259164923698326280597261

theorem tailTrace_6347201 : CollatzResearch.WordTrace tailWord_6347201 prefixEnd_6347201 3259164923698326280597261 := by
  unfold tailWord_6347201
  simp only [CollatzResearch.WordTrace]
  refine ⟨231501439078182267473017457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154334292718788178315344971 231501439078182267473017457)
  ·
    refine ⟨173626079308636700604763093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231501439078182267473017457 173626079308636700604763093)
    ·
      refine ⟨4069361233796172670424135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 173626079308636700604763093 4069361233796172670424135)
      ·
        refine ⟨6104041850694259005636203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069361233796172670424135 6104041850694259005636203)
        ·
          refine ⟨9156062776041388508454305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104041850694259005636203 9156062776041388508454305)
          ·
            refine ⟨6867047082031041381340729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156062776041388508454305 6867047082031041381340729)
            ·
              refine ⟨5150285311523281036005547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6867047082031041381340729 5150285311523281036005547)
              ·
                refine ⟨7725427967284921554008321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150285311523281036005547 7725427967284921554008321)
                ·
                  refine ⟨5794070975463691165506241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725427967284921554008321 5794070975463691165506241)
                  ·
                    refine ⟨4345553231597768374129681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794070975463691165506241 4345553231597768374129681)
                    ·
                      refine ⟨3259164923698326280597261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345553231597768374129681 3259164923698326280597261)
                      ·
                        rfl

theorem cell23_6347201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6347201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347201 prefixEnd_6347201 := by exact prefixLift 6347201
  have htrace : WordTrace (prefixWord ++ tailWord_6347201) baseStart_6347201 baseEnd_6347201 := by
    simpa [prefixWord, tailWord_6347201, baseEnd_6347201] using wordTrace_append hprefix tailTrace_6347201
  have hstable : (prefixWord ++ tailWord_6347201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347201).length < 2 ^ (prefixWord ++ tailWord_6347201).sum := by decide
  have hdescent : baseEnd_6347201 < baseStart_6347201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347226 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_6347226 : Nat := 118140960795 + 6347226 * 2 ^ 59
def prefixEnd_6347226 : Nat := 4983230072969 + 3 ^ 40 * 6347226 * 2
def baseEnd_6347226 : Nat := 3259177760714688682784645

theorem tailTrace_6347226 : CollatzResearch.WordTrace tailWord_6347226 prefixEnd_6347226 3259177760714688682784645 := by
  unfold tailWord_6347226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57875587725772924185669383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154334900602061131161785021 57875587725772924185669383)
  ·
    refine ⟨86813381588659386278504075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57875587725772924185669383 86813381588659386278504075)
    ·
      refine ⟨130220072382989079417756113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86813381588659386278504075 130220072382989079417756113)
      ·
        refine ⟨97665054287241809563317085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130220072382989079417756113 97665054287241809563317085)
        ·
          refine ⟨36624395357715678586243907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97665054287241809563317085 36624395357715678586243907)
          ·
            refine ⟨54936593036573517879365861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36624395357715678586243907 54936593036573517879365861)
            ·
              refine ⟨10300611194357534602381099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54936593036573517879365861 10300611194357534602381099)
              ·
                refine ⟨15450916791536301903571649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10300611194357534602381099 15450916791536301903571649)
                ·
                  refine ⟨11588187593652226427678737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15450916791536301903571649 11588187593652226427678737)
                  ·
                    refine ⟨8691140695239169820759053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588187593652226427678737 8691140695239169820759053)
                    ·
                      refine ⟨3259177760714688682784645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691140695239169820759053 3259177760714688682784645)
                      ·
                        rfl

theorem cell23_6347226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_6347226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347226 prefixEnd_6347226 := by exact prefixLift 6347226
  have htrace : WordTrace (prefixWord ++ tailWord_6347226) baseStart_6347226 baseEnd_6347226 := by
    simpa [prefixWord, tailWord_6347226, baseEnd_6347226] using wordTrace_append hprefix tailTrace_6347226
  have hstable : (prefixWord ++ tailWord_6347226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347226).length < 2 ^ (prefixWord ++ tailWord_6347226).sum := by decide
  have hdescent : baseEnd_6347226 < baseStart_6347226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347246 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_6347246 : Nat := 118140960795 + 6347246 * 2 ^ 59
def prefixEnd_6347246 : Nat := 4983230072969 + 3 ^ 40 * 6347246 * 2
def baseEnd_6347246 : Nat := 362132003369753178281617

theorem tailTrace_6347246 : CollatzResearch.WordTrace tailWord_6347246 prefixEnd_6347246 362132003369753178281617 := by
  unfold tailWord_6347246
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937885045377405019800699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154335386908679493438937061 28937885045377405019800699)
  ·
    refine ⟨43406827568066107529701049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28937885045377405019800699 43406827568066107529701049)
    ·
      refine ⟨32555120676049580647275787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43406827568066107529701049 32555120676049580647275787)
      ·
        refine ⟨48832681014074370970913681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32555120676049580647275787 48832681014074370970913681)
        ·
          refine ⟨36624510760555778228185261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48832681014074370970913681 36624510760555778228185261)
          ·
            refine ⟨13734191535208416835569473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36624510760555778228185261 13734191535208416835569473)
            ·
              refine ⟨10300643651406312626677105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13734191535208416835569473 10300643651406312626677105)
              ·
                refine ⟨7725482738554734470007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300643651406312626677105 7725482738554734470007829)
                ·
                  refine ⟨362132003369753178281617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7725482738554734470007829 362132003369753178281617)
                  ·
                    rfl

theorem cell23_6347246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_6347246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347246 prefixEnd_6347246 := by exact prefixLift 6347246
  have htrace : WordTrace (prefixWord ++ tailWord_6347246) baseStart_6347246 baseEnd_6347246 := by
    simpa [prefixWord, tailWord_6347246, baseEnd_6347246] using wordTrace_append hprefix tailTrace_6347246
  have hstable : (prefixWord ++ tailWord_6347246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347246).length < 2 ^ (prefixWord ++ tailWord_6347246).sum := by decide
  have hdescent : baseEnd_6347246 < baseStart_6347246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347250 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_6347250 : Nat := 118140960795 + 6347250 * 2 ^ 59
def prefixEnd_6347250 : Nat := 4983230072969 + 3 ^ 40 * 6347250 * 2
def baseEnd_6347250 : Nat := 1086396694750132196294845

theorem tailTrace_6347250 : CollatzResearch.WordTrace tailWord_6347250 prefixEnd_6347250 1086396694750132196294845 := by
  unfold tailWord_6347250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57875806563751187210387801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154335484170003165894367469 57875806563751187210387801)
  ·
    refine ⟨43406854922813390407790851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57875806563751187210387801 43406854922813390407790851)
    ·
      refine ⟨65110282384220085611686277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43406854922813390407790851 65110282384220085611686277)
      ·
        refine ⟨12208177947041266052191177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65110282384220085611686277 12208177947041266052191177)
        ·
          refine ⟨9156133460280949539143383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12208177947041266052191177 9156133460280949539143383)
          ·
            refine ⟨13734200190421424308715075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156133460280949539143383 13734200190421424308715075)
            ·
              refine ⟨20601300285632136463072613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13734200190421424308715075 20601300285632136463072613)
              ·
                refine ⟨3862743803556025586826115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20601300285632136463072613 3862743803556025586826115)
                ·
                  refine ⟨5794115705334038380239173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862743803556025586826115 5794115705334038380239173)
                  ·
                    refine ⟨1086396694750132196294845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794115705334038380239173 1086396694750132196294845)
                    ·
                      rfl

theorem cell23_6347250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_6347250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347250 prefixEnd_6347250 := by exact prefixLift 6347250
  have htrace : WordTrace (prefixWord ++ tailWord_6347250) baseStart_6347250 baseEnd_6347250 := by
    simpa [prefixWord, tailWord_6347250, baseEnd_6347250] using wordTrace_append hprefix tailTrace_6347250
  have hstable : (prefixWord ++ tailWord_6347250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347250).length < 2 ^ (prefixWord ++ tailWord_6347250).sum := by decide
  have hdescent : baseEnd_6347250 < baseStart_6347250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347256 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_6347256 : Nat := 118140960795 + 6347256 * 2 ^ 59
def prefixEnd_6347256 : Nat := 4983230072969 + 3 ^ 40 * 6347256 * 2
def baseEnd_6347256 : Nat := 3259193165134323565409507

theorem tailTrace_6347256 : CollatzResearch.WordTrace tailWord_6347256 prefixEnd_6347256 3259193165134323565409507 := by
  unfold tailWord_6347256
  simp only [CollatzResearch.WordTrace]
  refine ⟨115751722546491505933134811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154335630061988674577513081 115751722546491505933134811)
  ·
    refine ⟨173627583819737258899702217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115751722546491505933134811 173627583819737258899702217)
    ·
      refine ⟨130220687864802944174776663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173627583819737258899702217 130220687864802944174776663)
      ·
        refine ⟨195331031797204416262164995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130220687864802944174776663 195331031797204416262164995)
        ·
          refine ⟨292996547695806624393247493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195331031797204416262164995 292996547695806624393247493)
          ·
            refine ⟨54936852692963742073733905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292996547695806624393247493 54936852692963742073733905)
            ·
              refine ⟨41202639519722806555300429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54936852692963742073733905 41202639519722806555300429)
              ·
                refine ⟨15450989819896052458237661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41202639519722806555300429 15450989819896052458237661)
                ·
                  refine ⟨5794121182461019671839123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15450989819896052458237661 5794121182461019671839123)
                  ·
                    refine ⟨8691181773691529507758685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794121182461019671839123 8691181773691529507758685)
                    ·
                      refine ⟨3259193165134323565409507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691181773691529507758685 3259193165134323565409507)
                      ·
                        rfl

theorem cell23_6347256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_6347256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347256 prefixEnd_6347256 := by exact prefixLift 6347256
  have htrace : WordTrace (prefixWord ++ tailWord_6347256) baseStart_6347256 baseEnd_6347256 := by
    simpa [prefixWord, tailWord_6347256, baseEnd_6347256] using wordTrace_append hprefix tailTrace_6347256
  have hstable : (prefixWord ++ tailWord_6347256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347256).length < 2 ^ (prefixWord ++ tailWord_6347256).sum := by decide
  have hdescent : baseEnd_6347256 < baseStart_6347256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347277 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6347277 : Nat := 118140960795 + 6347277 * 2 ^ 59
def prefixEnd_6347277 : Nat := 4983230072969 + 3 ^ 40 * 6347277 * 2
def baseEnd_6347277 : Nat := 3259203948228067983246911

theorem tailTrace_6347277 : CollatzResearch.WordTrace tailWord_6347277 prefixEnd_6347277 3259203948228067983246911 := by
  unfold tailWord_6347277
  simp only [CollatzResearch.WordTrace]
  refine ⟨231504211025906932452784085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154336140683937954968522723 231504211025906932452784085)
  ·
    refine ⟨5425879945919693729362127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 231504211025906932452784085 5425879945919693729362127)
    ·
      refine ⟨8138819918879540594043191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425879945919693729362127 8138819918879540594043191)
      ·
        refine ⟨12208229878319310891064787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138819918879540594043191 12208229878319310891064787)
        ·
          refine ⟨18312344817478966336597181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12208229878319310891064787 18312344817478966336597181)
          ·
            refine ⟨6867129306554612376223943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18312344817478966336597181 6867129306554612376223943)
            ·
              refine ⟨10300693959831918564335915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867129306554612376223943 10300693959831918564335915)
              ·
                refine ⟨15451040939747877846503873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10300693959831918564335915 15451040939747877846503873)
                ·
                  refine ⟨11588280704810908384877905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15451040939747877846503873 11588280704810908384877905)
                  ·
                    refine ⟨8691210528608181288658429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588280704810908384877905 8691210528608181288658429)
                    ·
                      refine ⟨3259203948228067983246911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691210528608181288658429 3259203948228067983246911)
                      ·
                        rfl

theorem cell23_6347277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6347277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347277 prefixEnd_6347277 := by exact prefixLift 6347277
  have htrace : WordTrace (prefixWord ++ tailWord_6347277) baseStart_6347277 baseEnd_6347277 := by
    simpa [prefixWord, tailWord_6347277, baseEnd_6347277] using wordTrace_append hprefix tailTrace_6347277
  have hstable : (prefixWord ++ tailWord_6347277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347277).length < 2 ^ (prefixWord ++ tailWord_6347277).sum := by decide
  have hdescent : baseEnd_6347277 < baseStart_6347277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347289 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 6, 4]
def baseStart_6347289 : Nat := 118140960795 + 6347289 * 2 ^ 59
def prefixEnd_6347289 : Nat := 4983230072969 + 3 ^ 40 * 6347289 * 2
def baseEnd_6347289 : Nat := 1086403369998640645432285

theorem tailTrace_6347289 : CollatzResearch.WordTrace tailWord_6347289 prefixEnd_6347289 1086403369998640645432285 := by
  unfold tailWord_6347289
  simp only [CollatzResearch.WordTrace]
  refine ⟨231504648701863458502220921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154336432467908972334813947 231504648701863458502220921)
  ·
    refine ⟨173628486526397593876665691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231504648701863458502220921 173628486526397593876665691)
    ·
      refine ⟨260442729789596390814998537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173628486526397593876665691 260442729789596390814998537)
      ·
        refine ⟨195332047342197293111248903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260442729789596390814998537 195332047342197293111248903)
        ·
          refine ⟨292998071013295939666873355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195332047342197293111248903 292998071013295939666873355)
          ·
            refine ⟨439497106519943909500310033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292998071013295939666873355 439497106519943909500310033)
            ·
              refine ⟨329622829889957932125232525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439497106519943909500310033 329622829889957932125232525)
              ·
                refine ⟨123608561208734224546962197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329622829889957932125232525 123608561208734224546962197)
                ·
                  refine ⟨5794151306659416775638853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123608561208734224546962197 5794151306659416775638853)
                  ·
                    refine ⟨1086403369998640645432285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794151306659416775638853 1086403369998640645432285)
                    ·
                      rfl

theorem cell23_6347289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_6347289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347289 prefixEnd_6347289 := by exact prefixLift 6347289
  have htrace : WordTrace (prefixWord ++ tailWord_6347289) baseStart_6347289 baseEnd_6347289 := by
    simpa [prefixWord, tailWord_6347289, baseEnd_6347289] using wordTrace_append hprefix tailTrace_6347289
  have hstable : (prefixWord ++ tailWord_6347289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347289).length < 2 ^ (prefixWord ++ tailWord_6347289).sum := by decide
  have hdescent : baseEnd_6347289 < baseStart_6347289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347293 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_6347293 : Nat := 118140960795 + 6347293 * 2 ^ 59
def prefixEnd_6347293 : Nat := 4983230072969 + 3 ^ 40 * 6347293 * 2
def baseEnd_6347293 : Nat := 1086404054639513306882279

theorem tailTrace_6347293 : CollatzResearch.WordTrace tailWord_6347293 prefixEnd_6347293 1086404054639513306882279 := by
  unfold tailWord_6347293
  simp only [CollatzResearch.WordTrace]
  refine ⟨231504794593848967185366533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154336529729232644790244355 231504794593848967185366533)
  ·
    refine ⟨43407148986346681347256225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231504794593848967185366533 43407148986346681347256225)
    ·
      refine ⟨32555361739760011010442169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43407148986346681347256225 32555361739760011010442169)
      ·
        refine ⟨24416521304820008257831627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32555361739760011010442169 24416521304820008257831627)
        ·
          refine ⟨36624781957230012386747441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416521304820008257831627 36624781957230012386747441)
          ·
            refine ⟨27468586467922509290060581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36624781957230012386747441 27468586467922509290060581)
            ·
              refine ⟨5150359962735470491886359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27468586467922509290060581 5150359962735470491886359)
              ·
                refine ⟨7725539944103205737829539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150359962735470491886359 7725539944103205737829539)
                ·
                  refine ⟨11588309916154808606744309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725539944103205737829539 11588309916154808606744309)
                  ·
                    refine ⟨1086404054639513306882279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11588309916154808606744309 1086404054639513306882279)
                    ·
                      rfl

theorem cell23_6347293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_6347293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347293 prefixEnd_6347293 := by exact prefixLift 6347293
  have htrace : WordTrace (prefixWord ++ tailWord_6347293) baseStart_6347293 baseEnd_6347293 := by
    simpa [prefixWord, tailWord_6347293, baseEnd_6347293] using wordTrace_append hprefix tailTrace_6347293
  have hstable : (prefixWord ++ tailWord_6347293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347293).length < 2 ^ (prefixWord ++ tailWord_6347293).sum := by decide
  have hdescent : baseEnd_6347293 < baseStart_6347293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347313 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_6347313 : Nat := 118140960795 + 6347313 * 2 ^ 59
def prefixEnd_6347313 : Nat := 4983230072969 + 3 ^ 40 * 6347313 * 2
def baseEnd_6347313 : Nat := 3259222433531629842396745

theorem tailTrace_6347313 : CollatzResearch.WordTrace tailWord_6347313 prefixEnd_6347313 3259222433531629842396745 := by
  unfold tailWord_6347313
  simp only [CollatzResearch.WordTrace]
  refine ⟨231505524053776510601094593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154337016035851007067396395 231505524053776510601094593)
  ·
    refine ⟨173629143040332382950820945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231505524053776510601094593 173629143040332382950820945)
    ·
      refine ⟨130221857280249287213115709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173629143040332382950820945 130221857280249287213115709)
      ·
        refine ⟨48833196480093482704918391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130221857280249287213115709 48833196480093482704918391)
        ·
          refine ⟨73249794720140224057377587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48833196480093482704918391 73249794720140224057377587)
          ·
            refine ⟨109874692080210336086066381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73249794720140224057377587 109874692080210336086066381)
            ·
              refine ⟨41203009530078876032274893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109874692080210336086066381 41203009530078876032274893)
              ·
                refine ⟨15451128573779578512103085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41203009530078876032274893 15451128573779578512103085)
                ·
                  refine ⟨5794173215167341942038657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15451128573779578512103085 5794173215167341942038657)
                  ·
                    refine ⟨4345629911375506456528993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794173215167341942038657 4345629911375506456528993)
                    ·
                      refine ⟨3259222433531629842396745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345629911375506456528993 3259222433531629842396745)
                      ·
                        rfl

theorem cell23_6347313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_6347313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347313 prefixEnd_6347313 := by exact prefixLift 6347313
  have htrace : WordTrace (prefixWord ++ tailWord_6347313) baseStart_6347313 baseEnd_6347313 := by
    simpa [prefixWord, tailWord_6347313, baseEnd_6347313] using wordTrace_append hprefix tailTrace_6347313
  have hstable : (prefixWord ++ tailWord_6347313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347313).length < 2 ^ (prefixWord ++ tailWord_6347313).sum := by decide
  have hdescent : baseEnd_6347313 < baseStart_6347313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347333 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 3]
def baseStart_6347333 : Nat := 118140960795 + 6347333 * 2 ^ 59
def prefixEnd_6347333 : Nat := 4983230072969 + 3 ^ 40 * 6347333 * 2
def baseEnd_6347333 : Nat := 3259232703144719764146653

theorem tailTrace_6347333 : CollatzResearch.WordTrace tailWord_6347333 prefixEnd_6347333 3259232703144719764146653 := by
  unfold tailWord_6347333
  simp only [CollatzResearch.WordTrace]
  refine ⟨231506253513704054016822653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154337502342469369344548435 231506253513704054016822653)
  ·
    refine ⟨86814845067639020256308495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231506253513704054016822653 86814845067639020256308495)
    ·
      refine ⟨130222267601458530384462743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86814845067639020256308495 130222267601458530384462743)
      ·
        refine ⟨195333401402187795576694115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130222267601458530384462743 195333401402187795576694115)
        ·
          refine ⟨293000102103281693365041173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195333401402187795576694115 293000102103281693365041173)
          ·
            refine ⟨13734379786091329376486305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 293000102103281693365041173 13734379786091329376486305)
            ·
              refine ⟨10300784839568497032364729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13734379786091329376486305 10300784839568497032364729)
              ·
                refine ⟨7725588629676372774273547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300784839568497032364729 7725588629676372774273547)
                ·
                  refine ⟨11588382944514559161410321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725588629676372774273547 11588382944514559161410321)
                  ·
                    refine ⟨8691287208385919371057741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588382944514559161410321 8691287208385919371057741)
                    ·
                      refine ⟨3259232703144719764146653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691287208385919371057741 3259232703144719764146653)
                      ·
                        rfl

theorem cell23_6347333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_6347333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347333 prefixEnd_6347333 := by exact prefixLift 6347333
  have htrace : WordTrace (prefixWord ++ tailWord_6347333) baseStart_6347333 baseEnd_6347333 := by
    simpa [prefixWord, tailWord_6347333, baseEnd_6347333] using wordTrace_append hprefix tailTrace_6347333
  have hstable : (prefixWord ++ tailWord_6347333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347333).length < 2 ^ (prefixWord ++ tailWord_6347333).sum := by decide
  have hdescent : baseEnd_6347333 < baseStart_6347333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347346 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_6347346 : Nat := 118140960795 + 6347346 * 2 ^ 59
def prefixEnd_6347346 : Nat := 4983230072969 + 3 ^ 40 * 6347346 * 2
def baseEnd_6347346 : Nat := 3259239378393228213284093

theorem tailTrace_6347346 : CollatzResearch.WordTrace tailWord_6347346 prefixEnd_6347346 3259239378393228213284093 := by
  unfold tailWord_6347346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57876681915664239309261473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154337818441771304824697261 57876681915664239309261473)
  ·
    refine ⟨43407511436748179481946105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57876681915664239309261473 43407511436748179481946105)
    ·
      refine ⟨32555633577561134611459579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43407511436748179481946105 32555633577561134611459579)
      ·
        refine ⟨48833450366341701917189369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32555633577561134611459579 48833450366341701917189369)
        ·
          refine ⟨36625087774756276437892027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48833450366341701917189369 36625087774756276437892027)
          ·
            refine ⟨54937631662134414656838041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36625087774756276437892027 54937631662134414656838041)
            ·
              refine ⟨41203223746600810992628531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54937631662134414656838041 41203223746600810992628531)
              ·
                refine ⟨61804835619901216488942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41203223746600810992628531 61804835619901216488942797)
                ·
                  refine ⟨23176813357462956183353549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61804835619901216488942797 23176813357462956183353549)
                  ·
                    refine ⟨8691305009048608568757581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23176813357462956183353549 8691305009048608568757581)
                    ·
                      refine ⟨3259239378393228213284093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691305009048608568757581 3259239378393228213284093)
                      ·
                        rfl

theorem cell23_6347346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_6347346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347346 prefixEnd_6347346 := by exact prefixLift 6347346
  have htrace : WordTrace (prefixWord ++ tailWord_6347346) baseStart_6347346 baseEnd_6347346 := by
    simpa [prefixWord, tailWord_6347346, baseEnd_6347346] using wordTrace_append hprefix tailTrace_6347346
  have hstable : (prefixWord ++ tailWord_6347346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347346).length < 2 ^ (prefixWord ++ tailWord_6347346).sum := by decide
  have hdescent : baseEnd_6347346 < baseStart_6347346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347358 : List Nat := [4, 4, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6347358 : Nat := 118140960795 + 6347358 * 2 ^ 59
def prefixEnd_6347358 : Nat := 4983230072969 + 3 ^ 40 * 6347358 * 2
def baseEnd_6347358 : Nat := 3259245540161082166334039

theorem tailTrace_6347358 : CollatzResearch.WordTrace tailWord_6347358 prefixEnd_6347358 3259245540161082166334039 := by
  unfold tailWord_6347358
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938395667326685410810341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154338110225742322190988485 28938395667326685410810341)
  ·
    refine ⟨5425949187623753514526939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28938395667326685410810341 5425949187623753514526939)
    ·
      refine ⟨8138923781435630271790409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425949187623753514526939 8138923781435630271790409)
      ·
        refine ⟨6104192836076722703842807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8138923781435630271790409 6104192836076722703842807)
        ·
          refine ⟨9156289254115084055764211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104192836076722703842807 9156289254115084055764211)
          ·
            refine ⟨13734433881172626083646317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156289254115084055764211 13734433881172626083646317)
            ·
              refine ⟨5150412705439734781367369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13734433881172626083646317 5150412705439734781367369)
              ·
                refine ⟨3862809529079801086025527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150412705439734781367369 3862809529079801086025527)
                ·
                  refine ⟨5794214293619701629038291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862809529079801086025527 5794214293619701629038291)
                  ·
                    refine ⟨8691321440429552443557437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794214293619701629038291 8691321440429552443557437)
                    ·
                      refine ⟨3259245540161082166334039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691321440429552443557437 3259245540161082166334039)
                      ·
                        rfl

theorem cell23_6347358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6347358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347358 prefixEnd_6347358 := by exact prefixLift 6347358
  have htrace : WordTrace (prefixWord ++ tailWord_6347358) baseStart_6347358 baseEnd_6347358 := by
    simpa [prefixWord, tailWord_6347358, baseEnd_6347358] using wordTrace_append hprefix tailTrace_6347358
  have hstable : (prefixWord ++ tailWord_6347358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347358).length < 2 ^ (prefixWord ++ tailWord_6347358).sum := by decide
  have hdescent : baseEnd_6347358 < baseStart_6347358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347363 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 3]
def baseStart_6347363 : Nat := 118140960795 + 6347363 * 2 ^ 59
def prefixEnd_6347363 : Nat := 4983230072969 + 3 ^ 40 * 6347363 * 2
def baseEnd_6347363 : Nat := 3259248107564354646771515

theorem tailTrace_6347363 : CollatzResearch.WordTrace tailWord_6347363 prefixEnd_6347363 3259248107564354646771515 := by
  unfold tailWord_6347363
  simp only [CollatzResearch.WordTrace]
  refine ⟨231507347703595369140414743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154338231802396912760276495 231507347703595369140414743)
  ·
    refine ⟨347261021555393053710622115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231507347703595369140414743 347261021555393053710622115)
    ·
      refine ⟨520891532333089580565933173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347261021555393053710622115 520891532333089580565933173)
      ·
        refine ⟨48833581156227148178056235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 520891532333089580565933173 48833581156227148178056235)
        ·
          refine ⟨73250371734340722267084353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48833581156227148178056235 73250371734340722267084353)
          ·
            refine ⟨54937778800755541700313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73250371734340722267084353 54937778800755541700313265)
            ·
              refine ⟨41203334100566656275234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54937778800755541700313265 41203334100566656275234949)
              ·
                refine ⟨7725625143856248051606553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41203334100566656275234949 7725625143856248051606553)
                ·
                  refine ⟨5794218857892186038704915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725625143856248051606553 5794218857892186038704915)
                  ·
                    refine ⟨8691328286838279058057373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794218857892186038704915 8691328286838279058057373)
                    ·
                      refine ⟨3259248107564354646771515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691328286838279058057373 3259248107564354646771515)
                      ·
                        rfl

theorem cell23_6347363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_6347363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347363 prefixEnd_6347363 := by exact prefixLift 6347363
  have htrace : WordTrace (prefixWord ++ tailWord_6347363) baseStart_6347363 baseEnd_6347363 := by
    simpa [prefixWord, tailWord_6347363, baseEnd_6347363] using wordTrace_append hprefix tailTrace_6347363
  have hstable : (prefixWord ++ tailWord_6347363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347363).length < 2 ^ (prefixWord ++ tailWord_6347363).sum := by decide
  have hdescent : baseEnd_6347363 < baseStart_6347363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347369 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_6347369 : Nat := 118140960795 + 6347369 * 2 ^ 59
def prefixEnd_6347369 : Nat := 4983230072969 + 3 ^ 40 * 6347369 * 2
def baseEnd_6347369 : Nat := 3259251188448281623296487

theorem tailTrace_6347369 : CollatzResearch.WordTrace tailWord_6347369 prefixEnd_6347369 3259251188448281623296487 := by
  unfold tailWord_6347369
  simp only [CollatzResearch.WordTrace]
  refine ⟨231507566541573632165133161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154338377694382421443422107 231507566541573632165133161)
  ·
    refine ⟨173630674906180224123849871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231507566541573632165133161 173630674906180224123849871)
    ·
      refine ⟨260446012359270336185774807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173630674906180224123849871 260446012359270336185774807)
      ·
        refine ⟨390669018538905504278662211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260446012359270336185774807 390669018538905504278662211)
        ·
          refine ⟨586003527808358256417993317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390669018538905504278662211 586003527808358256417993317)
          ·
            refine ⟨109875661464067173078373747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586003527808358256417993317 109875661464067173078373747)
            ·
              refine ⟨164813492196100759617560621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109875661464067173078373747 164813492196100759617560621)
              ·
                refine ⟨61805059573537784856585233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164813492196100759617560621 61805059573537784856585233)
                ·
                  refine ⟨46353794680153338642438925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61805059573537784856585233 46353794680153338642438925)
                  ·
                    refine ⟨17382673005057501990914597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46353794680153338642438925 17382673005057501990914597)
                    ·
                      refine ⟨3259251188448281623296487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17382673005057501990914597 3259251188448281623296487)
                      ·
                        rfl

theorem cell23_6347369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_6347369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347369 prefixEnd_6347369 := by exact prefixLift 6347369
  have htrace : WordTrace (prefixWord ++ tailWord_6347369) baseStart_6347369 baseEnd_6347369 := by
    simpa [prefixWord, tailWord_6347369, baseEnd_6347369] using wordTrace_append hprefix tailTrace_6347369
  have hstable : (prefixWord ++ tailWord_6347369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347369).length < 2 ^ (prefixWord ++ tailWord_6347369).sum := by decide
  have hdescent : baseEnd_6347369 < baseStart_6347369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347403 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 4, 2, 2]
def baseStart_6347403 : Nat := 118140960795 + 6347403 * 2 ^ 59
def prefixEnd_6347403 : Nat := 4983230072969 + 3 ^ 40 * 6347403 * 2
def baseEnd_6347403 : Nat := 3259268646790534490271331

theorem tailTrace_6347403 : CollatzResearch.WordTrace tailWord_6347403 prefixEnd_6347403 3259268646790534490271331 := by
  unfold tailWord_6347403
  simp only [CollatzResearch.WordTrace]
  refine ⟨231508806623450455971870863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154339204415633637314580575 231508806623450455971870863)
  ·
    refine ⟨347263209935175683957806295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231508806623450455971870863 347263209935175683957806295)
    ·
      refine ⟨520894814902763525936709443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347263209935175683957806295 520894814902763525936709443)
      ·
        refine ⟨781342222354145288905064165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520894814902763525936709443 781342222354145288905064165)
        ·
          refine ⟨146501666691402241669699531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 781342222354145288905064165 146501666691402241669699531)
          ·
            refine ⟨219752500037103362504549297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146501666691402241669699531 219752500037103362504549297)
            ·
              refine ⟨164814375027827521878411973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219752500037103362504549297 164814375027827521878411973)
              ·
                refine ⟨30902695317717660352202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164814375027827521878411973 30902695317717660352202245)
                ·
                  refine ⟨5794255372072061316037921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30902695317717660352202245 5794255372072061316037921)
                  ·
                    refine ⟨4345691529054045987028441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794255372072061316037921 4345691529054045987028441)
                    ·
                      refine ⟨3259268646790534490271331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345691529054045987028441 3259268646790534490271331)
                      ·
                        rfl

theorem cell23_6347403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 2, 2].length) (baseStart_6347403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347403 prefixEnd_6347403 := by exact prefixLift 6347403
  have htrace : WordTrace (prefixWord ++ tailWord_6347403) baseStart_6347403 baseEnd_6347403 := by
    simpa [prefixWord, tailWord_6347403, baseEnd_6347403] using wordTrace_append hprefix tailTrace_6347403
  have hstable : (prefixWord ++ tailWord_6347403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347403).length < 2 ^ (prefixWord ++ tailWord_6347403).sum := by decide
  have hdescent : baseEnd_6347403 < baseStart_6347403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347406 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6347406 : Nat := 118140960795 + 6347406 * 2 ^ 59
def prefixEnd_6347406 : Nat := 4983230072969 + 3 ^ 40 * 6347406 * 2
def baseEnd_6347406 : Nat := 3259270187232497978533817

theorem tailTrace_6347406 : CollatzResearch.WordTrace tailWord_6347406 prefixEnd_6347406 3259270187232497978533817 := by
  unfold tailWord_6347406
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938614505304948435528759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154339277361626391656153381 28938614505304948435528759)
  ·
    refine ⟨43407921757957422653293139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28938614505304948435528759 43407921757957422653293139)
    ·
      refine ⟨65111882636936133979939709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43407921757957422653293139 65111882636936133979939709)
      ·
        refine ⟨24416955988851050242477391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65111882636936133979939709 24416955988851050242477391)
        ·
          refine ⟨36625433983276575363716087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416955988851050242477391 36625433983276575363716087)
          ·
            refine ⟨54938150974914863045574131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36625433983276575363716087 54938150974914863045574131)
            ·
              refine ⟨82407226462372294568361197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54938150974914863045574131 82407226462372294568361197)
              ·
                refine ⟨30902709923389610463135449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82407226462372294568361197 30902709923389610463135449)
                ·
                  refine ⟨23177032442542207847351587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30902709923389610463135449 23177032442542207847351587)
                  ·
                    refine ⟨34765548663813311771027381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23177032442542207847351587 34765548663813311771027381)
                    ·
                      refine ⟨3259270187232497978533817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34765548663813311771027381 3259270187232497978533817)
                      ·
                        rfl

theorem cell23_6347406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6347406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347406 prefixEnd_6347406 := by exact prefixLift 6347406
  have htrace : WordTrace (prefixWord ++ tailWord_6347406) baseStart_6347406 baseEnd_6347406 := by
    simpa [prefixWord, tailWord_6347406, baseEnd_6347406] using wordTrace_append hprefix tailTrace_6347406
  have hstable : (prefixWord ++ tailWord_6347406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347406).length < 2 ^ (prefixWord ++ tailWord_6347406).sum := by decide
  have hdescent : baseEnd_6347406 < baseStart_6347406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347416 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6347416 : Nat := 118140960795 + 6347416 * 2 ^ 59
def prefixEnd_6347416 : Nat := 4983230072969 + 3 ^ 40 * 6347416 * 2
def baseEnd_6347416 : Nat := 3259275322039042939408771

theorem tailTrace_6347416 : CollatzResearch.WordTrace tailWord_6347416 prefixEnd_6347416 3259275322039042939408771 := by
  unfold tailWord_6347416
  simp only [CollatzResearch.WordTrace]
  refine ⟨115754640386201679596047051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154339520514935572794729401 115754640386201679596047051)
  ·
    refine ⟨173631960579302519394070577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115754640386201679596047051 173631960579302519394070577)
    ·
      refine ⟨130223970434476889545552933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173631960579302519394070577 130223970434476889545552933)
      ·
        refine ⟨24416994456464416789791175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130223970434476889545552933 24416994456464416789791175)
        ·
          refine ⟨36625491684696625184686763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416994456464416789791175 36625491684696625184686763)
          ·
            refine ⟨54938237527044937777030145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36625491684696625184686763 54938237527044937777030145)
            ·
              refine ⟨41203678145283703332772609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54938237527044937777030145 41203678145283703332772609)
              ·
                refine ⟨30902758608962777499579457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41203678145283703332772609 30902758608962777499579457)
                ·
                  refine ⟨23177068956722083124684593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30902758608962777499579457 23177068956722083124684593)
                  ·
                    refine ⟨17382801717541562343513445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23177068956722083124684593 17382801717541562343513445)
                    ·
                      refine ⟨3259275322039042939408771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17382801717541562343513445 3259275322039042939408771)
                      ·
                        rfl

theorem cell23_6347416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6347416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347416 prefixEnd_6347416 := by exact prefixLift 6347416
  have htrace : WordTrace (prefixWord ++ tailWord_6347416) baseStart_6347416 baseEnd_6347416 := by
    simpa [prefixWord, tailWord_6347416, baseEnd_6347416] using wordTrace_append hprefix tailTrace_6347416
  have hstable : (prefixWord ++ tailWord_6347416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347416).length < 2 ^ (prefixWord ++ tailWord_6347416).sum := by decide
  have hdescent : baseEnd_6347416 < baseStart_6347416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347429 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_6347429 : Nat := 118140960795 + 6347429 * 2 ^ 59
def prefixEnd_6347429 : Nat := 4983230072969 + 3 ^ 40 * 6347429 * 2
def baseEnd_6347429 : Nat := 3259281997287551388546211

theorem tailTrace_6347429 : CollatzResearch.WordTrace tailWord_6347429 prefixEnd_6347429 3259281997287551388546211 := by
  unfold tailWord_6347429
  simp only [CollatzResearch.WordTrace]
  refine ⟨231509754921356262412317341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154339836614237508274878227 231509754921356262412317341)
  ·
    refine ⟨86816158095508598404619003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231509754921356262412317341 86816158095508598404619003)
    ·
      refine ⟨130224237143262897606928505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86816158095508598404619003 130224237143262897606928505)
      ·
        refine ⟨97668177857447173205196379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130224237143262897606928505 97668177857447173205196379)
        ·
          refine ⟨146502266786170759807794569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97668177857447173205196379 146502266786170759807794569)
          ·
            refine ⟨109876700089628069855845927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146502266786170759807794569 109876700089628069855845927)
            ·
              refine ⟨164815050134442104783768891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109876700089628069855845927 164815050134442104783768891)
              ·
                refine ⟨247222575201663157175653337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164815050134442104783768891 247222575201663157175653337)
                ·
                  refine ⟨185416931401247367881740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247222575201663157175653337 185416931401247367881740003)
                  ·
                    refine ⟨278125397101871051822610005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185416931401247367881740003 278125397101871051822610005)
                    ·
                      refine ⟨3259281997287551388546211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278125397101871051822610005 3259281997287551388546211)
                      ·
                        rfl

theorem cell23_6347429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_6347429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347429 prefixEnd_6347429 := by exact prefixLift 6347429
  have htrace : WordTrace (prefixWord ++ tailWord_6347429) baseStart_6347429 baseEnd_6347429 := by
    simpa [prefixWord, tailWord_6347429, baseEnd_6347429] using wordTrace_append hprefix tailTrace_6347429
  have hstable : (prefixWord ++ tailWord_6347429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347429).length < 2 ^ (prefixWord ++ tailWord_6347429).sum := by decide
  have hdescent : baseEnd_6347429 < baseStart_6347429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347437 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_6347437 : Nat := 118140960795 + 6347437 * 2 ^ 59
def prefixEnd_6347437 : Nat := 4983230072969 + 3 ^ 40 * 6347437 * 2
def baseEnd_6347437 : Nat := 3259286105132787357246175

theorem tailTrace_6347437 : CollatzResearch.WordTrace tailWord_6347437 prefixEnd_6347437 3259286105132787357246175 := by
  unfold tailWord_6347437
  simp only [CollatzResearch.WordTrace]
  refine ⟨231510046705327279778608565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154340031136884853185739043 231510046705327279778608565)
  ·
    refine ⟨21704066878624432479244553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231510046705327279778608565 21704066878624432479244553)
    ·
      refine ⟨16278050158968324359433415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21704066878624432479244553 16278050158968324359433415)
      ·
        refine ⟨24417075238452486539150123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278050158968324359433415 24417075238452486539150123)
        ·
          refine ⟨36625612857678729808725185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417075238452486539150123 36625612857678729808725185)
          ·
            refine ⟨27469209643259047356543889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36625612857678729808725185 27469209643259047356543889)
            ·
              refine ⟨20601907232444285517407917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27469209643259047356543889 20601907232444285517407917)
              ·
                refine ⟨7725715212166607069027969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20601907232444285517407917 7725715212166607069027969)
                ·
                  refine ⟨5794286409124955301770977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725715212166607069027969 5794286409124955301770977)
                  ·
                    refine ⟨4345714806843716476328233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794286409124955301770977 4345714806843716476328233)
                    ·
                      refine ⟨3259286105132787357246175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345714806843716476328233 3259286105132787357246175)
                      ·
                        rfl

theorem cell23_6347437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_6347437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347437 prefixEnd_6347437 := by exact prefixLift 6347437
  have htrace : WordTrace (prefixWord ++ tailWord_6347437) baseStart_6347437 baseEnd_6347437 := by
    simpa [prefixWord, tailWord_6347437, baseEnd_6347437] using wordTrace_append hprefix tailTrace_6347437
  have hstable : (prefixWord ++ tailWord_6347437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347437).length < 2 ^ (prefixWord ++ tailWord_6347437).sum := by decide
  have hdescent : baseEnd_6347437 < baseStart_6347437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347456 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_6347456 : Nat := 118140960795 + 6347456 * 2 ^ 59
def prefixEnd_6347456 : Nat := 4983230072969 + 3 ^ 40 * 6347456 * 2
def baseEnd_6347456 : Nat := 1086431953755074260969529

theorem tailTrace_6347456 : CollatzResearch.WordTrace tailWord_6347456 prefixEnd_6347456 1086431953755074260969529 := by
  unfold tailWord_6347456
  simp only [CollatzResearch.WordTrace]
  refine ⟨115755369846129223011775111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154340493128172297349033481 115755369846129223011775111)
  ·
    refine ⟨173633054769193834517662667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115755369846129223011775111 173633054769193834517662667)
    ·
      refine ⟨260449582153790751776494001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173633054769193834517662667 260449582153790751776494001)
      ·
        refine ⟨195337186615343063832370501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260449582153790751776494001 195337186615343063832370501)
        ·
          refine ⟨36625722490376824468569469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195337186615343063832370501 36625722490376824468569469)
          ·
            refine ⟨13734645933891309175713551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36625722490376824468569469 13734645933891309175713551)
            ·
              refine ⟨20601968900836963763570327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13734645933891309175713551 20601968900836963763570327)
              ·
                refine ⟨30902953351255445645355491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20601968900836963763570327 30902953351255445645355491)
                ·
                  refine ⟨46354430026883168468033237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30902953351255445645355491 46354430026883168468033237)
                  ·
                    refine ⟨1086431953755074260969529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46354430026883168468033237 1086431953755074260969529)
                    ·
                      rfl

theorem cell23_6347456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_6347456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347456 prefixEnd_6347456 := by exact prefixLift 6347456
  have htrace : WordTrace (prefixWord ++ tailWord_6347456) baseStart_6347456 baseEnd_6347456 := by
    simpa [prefixWord, tailWord_6347456, baseEnd_6347456] using wordTrace_append hprefix tailTrace_6347456
  have hstable : (prefixWord ++ tailWord_6347456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347456).length < 2 ^ (prefixWord ++ tailWord_6347456).sum := by decide
  have hdescent : baseEnd_6347456 < baseStart_6347456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347460 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 5]
def baseStart_6347460 : Nat := 118140960795 + 6347460 * 2 ^ 59
def prefixEnd_6347460 : Nat := 4983230072969 + 3 ^ 40 * 6347460 * 2
def baseEnd_6347460 : Nat := 362144212798648974139841

theorem tailTrace_6347460 : CollatzResearch.WordTrace tailWord_6347460 prefixEnd_6347460 362144212798648974139841 := by
  unfold tailWord_6347460
  simp only [CollatzResearch.WordTrace]
  refine ⟨115755442792121977353347917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154340590389495969804463889 115755442792121977353347917)
  ·
    refine ⟨43408291047045741507505469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115755442792121977353347917 43408291047045741507505469)
    ·
      refine ⟨16278109142642153065314551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43408291047045741507505469 16278109142642153065314551)
      ·
        refine ⟨24417163713963229597971827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278109142642153065314551 24417163713963229597971827)
        ·
          refine ⟨36625745570944844396957741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417163713963229597971827 36625745570944844396957741)
          ·
            refine ⟨13734654589104316648859153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36625745570944844396957741 13734654589104316648859153)
            ·
              refine ⟨10300990941828237486644365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13734654589104316648859153 10300990941828237486644365)
              ·
                refine ⟨3862871603185589057491637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10300990941828237486644365 3862871603185589057491637)
                ·
                  refine ⟨362144212798648974139841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3862871603185589057491637 362144212798648974139841)
                  ·
                    rfl

theorem cell23_6347460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_6347460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347460 prefixEnd_6347460 := by exact prefixLift 6347460
  have htrace : WordTrace (prefixWord ++ tailWord_6347460) baseStart_6347460 baseEnd_6347460 := by
    simpa [prefixWord, tailWord_6347460, baseEnd_6347460] using wordTrace_append hprefix tailTrace_6347460
  have hstable : (prefixWord ++ tailWord_6347460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347460).length < 2 ^ (prefixWord ++ tailWord_6347460).sum := by decide
  have hdescent : baseEnd_6347460 < baseStart_6347460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347503 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 3, 4]
def baseStart_6347503 : Nat := 118140960795 + 6347503 * 2 ^ 59
def prefixEnd_6347503 : Nat := 4983230072969 + 3 ^ 40 * 6347503 * 2
def baseEnd_6347503 : Nat := 1086439998285328033006957

theorem tailTrace_6347503 : CollatzResearch.WordTrace tailWord_6347503 prefixEnd_6347503 1086439998285328033006957 := by
  unfold tailWord_6347503
  simp only [CollatzResearch.WordTrace]
  refine ⟨231512453923088173050511163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154341635948725448700340775 231512453923088173050511163)
  ·
    refine ⟨347268680884632259575766745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231512453923088173050511163 347268680884632259575766745)
    ·
      refine ⟨260451510663474194681825059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347268680884632259575766745 260451510663474194681825059)
      ·
        refine ⟨390677265995211292022737589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260451510663474194681825059 390677265995211292022737589)
        ·
          refine ⟨36625993687051058627131649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390677265995211292022737589 36625993687051058627131649)
          ·
            refine ⟨27469495265288293970348737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36625993687051058627131649 27469495265288293970348737)
            ·
              refine ⟨20602121448966220477761553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27469495265288293970348737 20602121448966220477761553)
              ·
                refine ⟨15451591086724665358321165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20602121448966220477761553 15451591086724665358321165)
                ·
                  refine ⟨5794346657521749509370437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15451591086724665358321165 5794346657521749509370437)
                  ·
                    refine ⟨1086439998285328033006957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794346657521749509370437 1086439998285328033006957)
                    ·
                      rfl

theorem cell23_6347503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_6347503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347503 prefixEnd_6347503 := by exact prefixLift 6347503
  have htrace : WordTrace (prefixWord ++ tailWord_6347503) baseStart_6347503 baseEnd_6347503 := by
    simpa [prefixWord, tailWord_6347503, baseEnd_6347503] using wordTrace_append hprefix tailTrace_6347503
  have hstable : (prefixWord ++ tailWord_6347503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347503).length < 2 ^ (prefixWord ++ tailWord_6347503).sum := by decide
  have hdescent : baseEnd_6347503 < baseStart_6347503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347516 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 8]
def baseStart_6347516 : Nat := 118140960795 + 6347516 * 2 ^ 59
def prefixEnd_6347516 : Nat := 4983230072969 + 3 ^ 40 * 6347516 * 2
def baseEnd_6347516 : Nat := 362147407789388060906479

theorem tailTrace_6347516 : CollatzResearch.WordTrace tailWord_6347516 prefixEnd_6347516 362147407789388060906479 := by
  unfold tailWord_6347516
  simp only [CollatzResearch.WordTrace]
  refine ⟨115756464036020538135367201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154341952048027384180489601 115756464036020538135367201)
  ·
    refine ⟨86817348027015403601525401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115756464036020538135367201 86817348027015403601525401)
    ·
      refine ⟨65113011020261552701144051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86817348027015403601525401 65113011020261552701144051)
      ·
        refine ⟨97669516530392329051716077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65113011020261552701144051 97669516530392329051716077)
        ·
          refine ⟨36626068698897123394393529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97669516530392329051716077 36626068698897123394393529)
          ·
            refine ⟨27469551524172842545795147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36626068698897123394393529 27469551524172842545795147)
            ·
              refine ⟨41204327286259263818692721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27469551524172842545795147 41204327286259263818692721)
              ·
                refine ⟨30903245464694447864019541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41204327286259263818692721 30903245464694447864019541)
                ·
                  refine ⟨362147407789388060906479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30903245464694447864019541 362147407789388060906479)
                  ·
                    rfl

theorem cell23_6347516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_6347516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347516 prefixEnd_6347516 := by exact prefixLift 6347516
  have htrace : WordTrace (prefixWord ++ tailWord_6347516) baseStart_6347516 baseEnd_6347516 := by
    simpa [prefixWord, tailWord_6347516, baseEnd_6347516] using wordTrace_append hprefix tailTrace_6347516
  have hstable : (prefixWord ++ tailWord_6347516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347516).length < 2 ^ (prefixWord ++ tailWord_6347516).sum := by decide
  have hdescent : baseEnd_6347516 < baseStart_6347516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347560 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6347560 : Nat := 118140960795 + 6347560 * 2 ^ 59
def prefixEnd_6347560 : Nat := 4983230072969 + 3 ^ 40 * 6347560 * 2
def baseEnd_6347560 : Nat := 3259349263253290376008109

theorem tailTrace_6347560 : CollatzResearch.WordTrace tailWord_6347560 prefixEnd_6347560 3259349263253290376008109 := by
  unfold tailWord_6347560
  simp only [CollatzResearch.WordTrace]
  refine ⟨115757266441940835892668067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154343021922587781190224089 115757266441940835892668067)
  ·
    refine ⟨173635899662911253839002101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115757266441940835892668067 173635899662911253839002101)
    ·
      refine ⟨16278365593397930047406447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173635899662911253839002101 16278365593397930047406447)
      ·
        refine ⟨24417548390096895071109671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278365593397930047406447 24417548390096895071109671)
        ·
          refine ⟨36626322585145342606664507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417548390096895071109671 36626322585145342606664507)
          ·
            refine ⟨54939483877718013909996761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36626322585145342606664507 54939483877718013909996761)
            ·
              refine ⟨41204612908288510432497571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54939483877718013909996761 41204612908288510432497571)
              ·
                refine ⟨61806919362432765648746357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41204612908288510432497571 61806919362432765648746357)
                ·
                  refine ⟨5794398690228071779569971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61806919362432765648746357 5794398690228071779569971)
                  ·
                    refine ⟨8691598035342107669354957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794398690228071779569971 8691598035342107669354957)
                    ·
                      refine ⟨3259349263253290376008109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691598035342107669354957 3259349263253290376008109)
                      ·
                        rfl

theorem cell23_6347560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6347560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347560 prefixEnd_6347560 := by exact prefixLift 6347560
  have htrace : WordTrace (prefixWord ++ tailWord_6347560) baseStart_6347560 baseEnd_6347560 := by
    simpa [prefixWord, tailWord_6347560, baseEnd_6347560] using wordTrace_append hprefix tailTrace_6347560
  have hstable : (prefixWord ++ tailWord_6347560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347560).length < 2 ^ (prefixWord ++ tailWord_6347560).sum := by decide
  have hdescent : baseEnd_6347560 < baseStart_6347560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347588 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6347588 : Nat := 118140960795 + 6347588 * 2 ^ 59
def prefixEnd_6347588 : Nat := 4983230072969 + 3 ^ 40 * 6347588 * 2
def baseEnd_6347588 : Nat := 1086454546903872088819327

theorem tailTrace_6347588 : CollatzResearch.WordTrace tailWord_6347588 prefixEnd_6347588 1086454546903872088819327 := by
  unfold tailWord_6347588
  simp only [CollatzResearch.WordTrace]
  refine ⟨115757777063890116283677709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154343702751853488378236945 115757777063890116283677709)
  ·
    refine ⟨43409166398958793606379141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115757777063890116283677709 43409166398958793606379141)
    ·
      refine ⟨8139218699804773801196089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43409166398958793606379141 8139218699804773801196089)
      ·
        refine ⟨6104414024853580350897067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139218699804773801196089 6104414024853580350897067)
        ·
          refine ⟨9156621037280370526345601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104414024853580350897067 9156621037280370526345601)
          ·
            refine ⟨6867465777960277894759201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156621037280370526345601 6867465777960277894759201)
            ·
              refine ⟨5150599333470208421069401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6867465777960277894759201 5150599333470208421069401)
              ·
                refine ⟨3862949500102656315802051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150599333470208421069401 3862949500102656315802051)
                ·
                  refine ⟨5794424250153984473703077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862949500102656315802051 5794424250153984473703077)
                  ·
                    refine ⟨1086454546903872088819327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794424250153984473703077 1086454546903872088819327)
                    ·
                      rfl

theorem cell23_6347588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6347588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347588 prefixEnd_6347588 := by exact prefixLift 6347588
  have htrace : WordTrace (prefixWord ++ tailWord_6347588) baseStart_6347588 baseEnd_6347588 := by
    simpa [prefixWord, tailWord_6347588, baseEnd_6347588] using wordTrace_append hprefix tailTrace_6347588
  have hstable : (prefixWord ++ tailWord_6347588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347588).length < 2 ^ (prefixWord ++ tailWord_6347588).sum := by decide
  have hdescent : baseEnd_6347588 < baseStart_6347588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347610 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_6347610 : Nat := 118140960795 + 6347610 * 2 ^ 59
def prefixEnd_6347610 : Nat := 4983230072969 + 3 ^ 40 * 6347610 * 2
def baseEnd_6347610 : Nat := 1086458312428671726794293

theorem tailTrace_6347610 : CollatzResearch.WordTrace tailWord_6347610 prefixEnd_6347610 1086458312428671726794293 := by
  unfold tailWord_6347610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57879089133425132581164071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154344237689133686883104189 57879089133425132581164071)
  ·
    refine ⟨86818633700137698871746107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57879089133425132581164071 86818633700137698871746107)
    ·
      refine ⟨130227950550206548307619161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86818633700137698871746107 130227950550206548307619161)
      ·
        refine ⟨97670962912654911230714371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130227950550206548307619161 97670962912654911230714371)
        ·
          refine ⟨146506444368982366846071557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97670962912654911230714371 146506444368982366846071557)
          ·
            refine ⟨27469958319184193783638417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146506444368982366846071557 27469958319184193783638417)
            ·
              refine ⟨20602468739388145337728813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27469958319184193783638417 20602468739388145337728813)
              ·
                refine ⟨7725925777270554501648305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20602468739388145337728813 7725925777270554501648305)
                ·
                  refine ⟨5794444332952915876236229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725925777270554501648305 5794444332952915876236229)
                  ·
                    refine ⟨1086458312428671726794293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5794444332952915876236229 1086458312428671726794293)
                    ·
                      rfl

theorem cell23_6347610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_6347610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347610 prefixEnd_6347610 := by exact prefixLift 6347610
  have htrace : WordTrace (prefixWord ++ tailWord_6347610) baseStart_6347610 baseEnd_6347610 := by
    simpa [prefixWord, tailWord_6347610, baseEnd_6347610] using wordTrace_append hprefix tailTrace_6347610
  have hstable : (prefixWord ++ tailWord_6347610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347610).length < 2 ^ (prefixWord ++ tailWord_6347610).sum := by decide
  have hdescent : baseEnd_6347610 < baseStart_6347610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347620 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_6347620 : Nat := 118140960795 + 6347620 * 2 ^ 59
def prefixEnd_6347620 : Nat := 4983230072969 + 3 ^ 40 * 6347620 * 2
def baseEnd_6347620 : Nat := 3259380072092560141257833

theorem tailTrace_6347620 : CollatzResearch.WordTrace tailWord_6347620 prefixEnd_6347620 3259380072092560141257833 := by
  unfold tailWord_6347620
  simp only [CollatzResearch.WordTrace]
  refine ⟨115758360631832151016260157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154344480842442868021680209 115758360631832151016260157)
  ·
    refine ⟨43409385236937056631097559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115758360631832151016260157 43409385236937056631097559)
    ·
      refine ⟨65114077855405584946646339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43409385236937056631097559 65114077855405584946646339)
      ·
        refine ⟨97671116783108377419969509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65114077855405584946646339 97671116783108377419969509)
        ·
          refine ⟨18313334396832820766244283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97671116783108377419969509 18313334396832820766244283)
          ·
            refine ⟨27470001595249231149366425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18313334396832820766244283 27470001595249231149366425)
            ·
              refine ⟨20602501196436923362024819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27470001595249231149366425 20602501196436923362024819)
              ·
                refine ⟨30903751794655385043037229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20602501196436923362024819 30903751794655385043037229)
                ·
                  refine ⟨11588906922995769391138961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30903751794655385043037229 11588906922995769391138961)
                  ·
                    refine ⟨8691680192246827043354221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588906922995769391138961 8691680192246827043354221)
                    ·
                      refine ⟨3259380072092560141257833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691680192246827043354221 3259380072092560141257833)
                      ·
                        rfl

theorem cell23_6347620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_6347620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347620 prefixEnd_6347620 := by exact prefixLift 6347620
  have htrace : WordTrace (prefixWord ++ tailWord_6347620) baseStart_6347620 baseEnd_6347620 := by
    simpa [prefixWord, tailWord_6347620, baseEnd_6347620] using wordTrace_append hprefix tailTrace_6347620
  have hstable : (prefixWord ++ tailWord_6347620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347620).length < 2 ^ (prefixWord ++ tailWord_6347620).sum := by decide
  have hdescent : baseEnd_6347620 < baseStart_6347620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347634 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6347634 : Nat := 118140960795 + 6347634 * 2 ^ 59
def prefixEnd_6347634 : Nat := 4983230072969 + 3 ^ 40 * 6347634 * 2
def baseEnd_6347634 : Nat := 3259387260821723086482769

theorem tailTrace_6347634 : CollatzResearch.WordTrace tailWord_6347634 prefixEnd_6347634 3259387260821723086482769 := by
  unfold tailWord_6347634
  simp only [CollatzResearch.WordTrace]
  refine ⟨57879307971403395605882489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154344821257075721615686637 57879307971403395605882489)
  ·
    refine ⟨43409480978552546704411867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57879307971403395605882489 43409480978552546704411867)
    ·
      refine ⟨65114221467828820056617801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43409480978552546704411867 65114221467828820056617801)
      ·
        refine ⟨48835666100871615042463351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65114221467828820056617801 48835666100871615042463351)
        ·
          refine ⟨73253499151307422563695027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48835666100871615042463351 73253499151307422563695027)
          ·
            refine ⟨109880248726961133845542541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73253499151307422563695027 109880248726961133845542541)
            ·
              refine ⟨41205093272610425192078453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109880248726961133845542541 41205093272610425192078453)
              ·
                refine ⟨3862977494307227361757355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41205093272610425192078453 3862977494307227361757355)
                ·
                  refine ⟨5794466241460841042636033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862977494307227361757355 5794466241460841042636033)
                  ·
                    refine ⟨4345849681095630781977025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794466241460841042636033 4345849681095630781977025)
                    ·
                      refine ⟨3259387260821723086482769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345849681095630781977025 3259387260821723086482769)
                      ·
                        rfl

theorem cell23_6347634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6347634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347634 prefixEnd_6347634 := by exact prefixLift 6347634
  have htrace : WordTrace (prefixWord ++ tailWord_6347634) baseStart_6347634 baseEnd_6347634 := by
    simpa [prefixWord, tailWord_6347634, baseEnd_6347634] using wordTrace_append hprefix tailTrace_6347634
  have hstable : (prefixWord ++ tailWord_6347634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347634).length < 2 ^ (prefixWord ++ tailWord_6347634).sum := by decide
  have hdescent : baseEnd_6347634 < baseStart_6347634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347637 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6347637 : Nat := 118140960795 + 6347637 * 2 ^ 59
def prefixEnd_6347637 : Nat := 4983230072969 + 3 ^ 40 * 6347637 * 2
def baseEnd_6347637 : Nat := 3259388801263686574745255

theorem tailTrace_6347637 : CollatzResearch.WordTrace tailWord_6347637 prefixEnd_6347637 3259388801263686574745255 := by
  unfold tailWord_6347637
  simp only [CollatzResearch.WordTrace]
  refine ⟨231517341304602713935889165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154344894203068475957259443 231517341304602713935889165)
  ·
    refine ⟨86819002989226017725958437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231517341304602713935889165 86819002989226017725958437)
    ·
      refine ⟨16278563060479878323617207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86819002989226017725958437 16278563060479878323617207)
      ·
        refine ⟨24417844590719817485425811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278563060479878323617207 24417844590719817485425811)
        ·
          refine ⟨36626766886079726228138717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417844590719817485425811 36626766886079726228138717)
          ·
            refine ⟨13735037582279897335552019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36626766886079726228138717 13735037582279897335552019)
            ·
              refine ⟨20602556373419846003328029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735037582279897335552019 20602556373419846003328029)
              ·
                refine ⟨7725958640032442251248011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20602556373419846003328029 7725958640032442251248011)
                ·
                  refine ⟨11588937960048663376872017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725958640032442251248011 11588937960048663376872017)
                  ·
                    refine ⟨8691703470036497532654013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588937960048663376872017 8691703470036497532654013)
                    ·
                      refine ⟨3259388801263686574745255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691703470036497532654013 3259388801263686574745255)
                      ·
                        rfl

theorem cell23_6347637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6347637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347637 prefixEnd_6347637 := by exact prefixLift 6347637
  have htrace : WordTrace (prefixWord ++ tailWord_6347637) baseStart_6347637 baseEnd_6347637 := by
    simpa [prefixWord, tailWord_6347637, baseEnd_6347637] using wordTrace_append hprefix tailTrace_6347637
  have hstable : (prefixWord ++ tailWord_6347637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347637).length < 2 ^ (prefixWord ++ tailWord_6347637).sum := by decide
  have hdescent : baseEnd_6347637 < baseStart_6347637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347660 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6347660 : Nat := 118140960795 + 6347660 * 2 ^ 59
def prefixEnd_6347660 : Nat := 4983230072969 + 3 ^ 40 * 6347660 * 2
def baseEnd_6347660 : Nat := 3259400611318739984757649

theorem tailTrace_6347660 : CollatzResearch.WordTrace tailWord_6347660 prefixEnd_6347660 3259400611318739984757649 := by
  unfold tailWord_6347660
  simp only [CollatzResearch.WordTrace]
  refine ⟨115759090091759694431988217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154345453455679592575984289 115759090091759694431988217)
  ·
    refine ⟨86819317568819770823991163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115759090091759694431988217 86819317568819770823991163)
    ·
      refine ⟨130228976353229656235986745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86819317568819770823991163 130228976353229656235986745)
      ·
        refine ⟨97671732264922242176990059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130228976353229656235986745 97671732264922242176990059)
        ·
          refine ⟨146507598397383363265485089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97671732264922242176990059 146507598397383363265485089)
          ·
            refine ⟨109880698798037522449113817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146507598397383363265485089 109880698798037522449113817)
            ·
              refine ⟨82410524098528141836835363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109880698798037522449113817 82410524098528141836835363)
              ·
                refine ⟨123615786147792212755253045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82410524098528141836835363 123615786147792212755253045)
                ·
                  refine ⟨11588979951355519945804973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123615786147792212755253045 11588979951355519945804973)
                  ·
                    refine ⟨4345867481758319979676865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11588979951355519945804973 4345867481758319979676865)
                    ·
                      refine ⟨3259400611318739984757649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345867481758319979676865 3259400611318739984757649)
                      ·
                        rfl

theorem cell23_6347660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6347660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347660 prefixEnd_6347660 := by exact prefixLift 6347660
  have htrace : WordTrace (prefixWord ++ tailWord_6347660) baseStart_6347660 baseEnd_6347660 := by
    simpa [prefixWord, tailWord_6347660, baseEnd_6347660] using wordTrace_append hprefix tailTrace_6347660
  have hstable : (prefixWord ++ tailWord_6347660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347660).length < 2 ^ (prefixWord ++ tailWord_6347660).sum := by decide
  have hdescent : baseEnd_6347660 < baseStart_6347660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347702 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6347702 : Nat := 118140960795 + 6347702 * 2 ^ 59
def prefixEnd_6347702 : Nat := 4983230072969 + 3 ^ 40 * 6347702 * 2
def baseEnd_6347702 : Nat := 3259422177506228820432457

theorem tailTrace_6347702 : CollatzResearch.WordTrace tailWord_6347702 prefixEnd_6347702 3259422177506228820432457 := by
  unfold tailWord_6347702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469982003085451877312835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154346474699578153358003573 14469982003085451877312835)
  ·
    refine ⟨21704973004628177815969253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14469982003085451877312835 21704973004628177815969253)
    ·
      refine ⟨4069682438367783340494235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21704973004628177815969253 4069682438367783340494235)
      ·
        refine ⟨6104523657551675010741353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069682438367783340494235 6104523657551675010741353)
        ·
          refine ⟨4578392743163756258056015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104523657551675010741353 4578392743163756258056015)
          ·
            refine ⟨6867589114745634387084023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578392743163756258056015 6867589114745634387084023)
            ·
              refine ⟨10301383672118451580626035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867589114745634387084023 10301383672118451580626035)
              ·
                refine ⟨15452075508177677370939053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10301383672118451580626035 15452075508177677370939053)
                ·
                  refine ⟨5794528315566629014102145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15452075508177677370939053 5794528315566629014102145)
                  ·
                    refine ⟨4345896236674971760576609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794528315566629014102145 4345896236674971760576609)
                    ·
                      refine ⟨3259422177506228820432457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345896236674971760576609 3259422177506228820432457)
                      ·
                        rfl

theorem cell23_6347702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6347702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347702 prefixEnd_6347702 := by exact prefixLift 6347702
  have htrace : WordTrace (prefixWord ++ tailWord_6347702) baseStart_6347702 baseEnd_6347702 := by
    simpa [prefixWord, tailWord_6347702, baseEnd_6347702] using wordTrace_append hprefix tailTrace_6347702
  have hstable : (prefixWord ++ tailWord_6347702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347702).length < 2 ^ (prefixWord ++ tailWord_6347702).sum := by decide
  have hdescent : baseEnd_6347702 < baseStart_6347702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347703 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_6347703 : Nat := 118140960795 + 6347703 * 2 ^ 59
def prefixEnd_6347703 : Nat := 4983230072969 + 3 ^ 40 * 6347703 * 2
def baseEnd_6347703 : Nat := 3259422690986883316519951

theorem tailTrace_6347703 : CollatzResearch.WordTrace tailWord_6347703 prefixEnd_6347703 3259422690986883316519951 := by
  unfold tailWord_6347703
  simp only [CollatzResearch.WordTrace]
  refine ⟨231519748522363607207791763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154346499014909071471861175 231519748522363607207791763)
  ·
    refine ⟨347279622783545410811687645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231519748522363607207791763 347279622783545410811687645)
    ·
      refine ⟨130229858543829529054382867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347279622783545410811687645 130229858543829529054382867)
      ·
        refine ⟨195344787815744293581574301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130229858543829529054382867 195344787815744293581574301)
        ·
          refine ⟨73254295430904110093090363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195344787815744293581574301 73254295430904110093090363)
          ·
            refine ⟨109881443146356165139635545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73254295430904110093090363 109881443146356165139635545)
            ·
              refine ⟨82411082359767123854726659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109881443146356165139635545 82411082359767123854726659)
              ·
                refine ⟨123616623539650685782089989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82411082359767123854726659 123616623539650685782089989)
                ·
                  refine ⟨23178116913684503584141873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123616623539650685782089989 23178116913684503584141873)
                  ·
                    refine ⟨17383587685263377688106405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23178116913684503584141873 17383587685263377688106405)
                    ·
                      refine ⟨3259422690986883316519951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17383587685263377688106405 3259422690986883316519951)
                      ·
                        rfl

theorem cell23_6347703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_6347703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347703 prefixEnd_6347703 := by exact prefixLift 6347703
  have htrace : WordTrace (prefixWord ++ tailWord_6347703) baseStart_6347703 baseEnd_6347703 := by
    simpa [prefixWord, tailWord_6347703, baseEnd_6347703] using wordTrace_append hprefix tailTrace_6347703
  have hstable : (prefixWord ++ tailWord_6347703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347703).length < 2 ^ (prefixWord ++ tailWord_6347703).sum := by decide
  have hdescent : baseEnd_6347703 < baseStart_6347703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347710 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_6347710 : Nat := 118140960795 + 6347710 * 2 ^ 59
def prefixEnd_6347710 : Nat := 4983230072969 + 3 ^ 40 * 6347710 * 2
def baseEnd_6347710 : Nat := 3259426285351464789132419

theorem tailTrace_6347710 : CollatzResearch.WordTrace tailWord_6347710 prefixEnd_6347710 3259426285351464789132419 := by
  unfold tailWord_6347710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940000479167280925412073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154346669222225498268864389 28940000479167280925412073)
  ·
    refine ⟨21705000359375460694059055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28940000479167280925412073 21705000359375460694059055)
    ·
      refine ⟨32557500539063191041088583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705000359375460694059055 32557500539063191041088583)
      ·
        refine ⟨48836250808594786561632875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32557500539063191041088583 48836250808594786561632875)
        ·
          refine ⟨73254376212892179842449313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48836250808594786561632875 73254376212892179842449313)
          ·
            refine ⟨54940782159669134881836985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73254376212892179842449313 54940782159669134881836985)
            ·
              refine ⟨41205586619751851161377739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54940782159669134881836985 41205586619751851161377739)
              ·
                refine ⟨61808379929627776742066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41205586619751851161377739 61808379929627776742066609)
                ·
                  refine ⟨46356284947220832556549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61808379929627776742066609 46356284947220832556549957)
                  ·
                    refine ⟨8691803427603906104353117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46356284947220832556549957 8691803427603906104353117)
                    ·
                      refine ⟨3259426285351464789132419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691803427603906104353117 3259426285351464789132419)
                      ·
                        rfl

theorem cell23_6347710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_6347710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347710 prefixEnd_6347710 := by exact prefixLift 6347710
  have htrace : WordTrace (prefixWord ++ tailWord_6347710) baseStart_6347710 baseEnd_6347710 := by
    simpa [prefixWord, tailWord_6347710, baseEnd_6347710] using wordTrace_append hprefix tailTrace_6347710
  have hstable : (prefixWord ++ tailWord_6347710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347710).length < 2 ^ (prefixWord ++ tailWord_6347710).sum := by decide
  have hdescent : baseEnd_6347710 < baseStart_6347710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347724 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6347724 : Nat := 118140960795 + 6347724 * 2 ^ 59
def prefixEnd_6347724 : Nat := 4983230072969 + 3 ^ 40 * 6347724 * 2
def baseEnd_6347724 : Nat := 3259433474080627734357355

theorem tailTrace_6347724 : CollatzResearch.WordTrace tailWord_6347724 prefixEnd_6347724 3259433474080627734357355 := by
  unfold tailWord_6347724
  simp only [CollatzResearch.WordTrace]
  refine ⟨115760257227643763897153113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154347009636858351862870817 115760257227643763897153113)
  ·
    refine ⟨86820192920732822922864835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115760257227643763897153113 86820192920732822922864835)
    ·
      refine ⟨130230289381099234384297253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86820192920732822922864835 130230289381099234384297253)
      ·
        refine ⟨24418179258956106447055735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130230289381099234384297253 24418179258956106447055735)
        ·
          refine ⟨36627268888434159670583603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24418179258956106447055735 36627268888434159670583603)
          ·
            refine ⟨54940903332651239505875405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36627268888434159670583603 54940903332651239505875405)
            ·
              refine ⟨20602838749744214814703277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54940903332651239505875405 20602838749744214814703277)
              ·
                refine ⟨7726064531154080555513729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20602838749744214814703277 7726064531154080555513729)
                ·
                  refine ⟨5794548398365560416635297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726064531154080555513729 5794548398365560416635297)
                  ·
                    refine ⟨4345911298774170312476473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794548398365560416635297 4345911298774170312476473)
                    ·
                      refine ⟨3259433474080627734357355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4345911298774170312476473 3259433474080627734357355)
                      ·
                        rfl

theorem cell23_6347724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6347724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347724 prefixEnd_6347724 := by exact prefixLift 6347724
  have htrace : WordTrace (prefixWord ++ tailWord_6347724) baseStart_6347724 baseEnd_6347724 := by
    simpa [prefixWord, tailWord_6347724, baseEnd_6347724] using wordTrace_append hprefix tailTrace_6347724
  have hstable : (prefixWord ++ tailWord_6347724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347724).length < 2 ^ (prefixWord ++ tailWord_6347724).sum := by decide
  have hdescent : baseEnd_6347724 < baseStart_6347724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347763 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_6347763 : Nat := 118140960795 + 6347763 * 2 ^ 59
def prefixEnd_6347763 : Nat := 4983230072969 + 3 ^ 40 * 6347763 * 2
def baseEnd_6347763 : Nat := 3259453499826153081769675

theorem tailTrace_6347763 : CollatzResearch.WordTrace tailWord_6347763 prefixEnd_6347763 3259453499826153081769675 := by
  unfold tailWord_6347763
  simp only [CollatzResearch.WordTrace]
  refine ⟨231521936902146237454975943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154347957934764158303317295 231521936902146237454975943)
  ·
    refine ⟨347282905353219356182463915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231521936902146237454975943 347282905353219356182463915)
    ·
      refine ⟨520924358029829034273695873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347282905353219356182463915 520924358029829034273695873)
      ·
        refine ⟨390693268522371775705271905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520924358029829034273695873 390693268522371775705271905)
        ·
          refine ⟨293019951391778831778953929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390693268522371775705271905 293019951391778831778953929)
          ·
            refine ⟨219764963543834123834215447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293019951391778831778953929 219764963543834123834215447)
            ·
              refine ⟨329647445315751185751323171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219764963543834123834215447 329647445315751185751323171)
              ·
                refine ⟨494471167973626778626984757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329647445315751185751323171 494471167973626778626984757)
                ·
                  refine ⟨46356671997527510496279821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 494471167973626778626984757 46356671997527510496279821)
                  ·
                    refine ⟨17383751999072816436104933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46356671997527510496279821 17383751999072816436104933)
                    ·
                      refine ⟨3259453499826153081769675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17383751999072816436104933 3259453499826153081769675)
                      ·
                        rfl

theorem cell23_6347763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_6347763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347763 prefixEnd_6347763 := by exact prefixLift 6347763
  have htrace : WordTrace (prefixWord ++ tailWord_6347763) baseStart_6347763 baseEnd_6347763 := by
    simpa [prefixWord, tailWord_6347763, baseEnd_6347763] using wordTrace_append hprefix tailTrace_6347763
  have hstable : (prefixWord ++ tailWord_6347763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347763).length < 2 ^ (prefixWord ++ tailWord_6347763).sum := by decide
  have hdescent : baseEnd_6347763 < baseStart_6347763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347773 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_6347773 : Nat := 118140960795 + 6347773 * 2 ^ 59
def prefixEnd_6347773 : Nat := 4983230072969 + 3 ^ 40 * 6347773 * 2
def baseEnd_6347773 : Nat := 1086486211544232680881543

theorem tailTrace_6347773 : CollatzResearch.WordTrace tailWord_6347773 prefixEnd_6347773 1086486211544232680881543 := by
  unfold tailWord_6347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨231522301632110009162839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154348201088073339441893315 231522301632110009162839973)
  ·
    refine ⟨43410431556020626718032495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231522301632110009162839973 43410431556020626718032495)
    ·
      refine ⟨65115647334030940077048743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43410431556020626718032495 65115647334030940077048743)
      ·
        refine ⟨97673471001046410115573115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65115647334030940077048743 97673471001046410115573115)
        ·
          refine ⟨146510206501569615173359673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97673471001046410115573115 146510206501569615173359673)
          ·
            refine ⟨109882654876177211380019755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146510206501569615173359673 109882654876177211380019755)
            ·
              refine ⟨164823982314265817070029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109882654876177211380019755 164823982314265817070029633)
              ·
                refine ⟨123617986735699362802522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164823982314265817070029633 123617986735699362802522225)
                ·
                  refine ⟨92713490051774522101891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123617986735699362802522225 92713490051774522101891669)
                  ·
                    refine ⟨1086486211544232680881543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92713490051774522101891669 1086486211544232680881543)
                    ·
                      rfl

theorem cell23_6347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_6347773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347773 prefixEnd_6347773 := by exact prefixLift 6347773
  have htrace : WordTrace (prefixWord ++ tailWord_6347773) baseStart_6347773 baseEnd_6347773 := by
    simpa [prefixWord, tailWord_6347773, baseEnd_6347773] using wordTrace_append hprefix tailTrace_6347773
  have hstable : (prefixWord ++ tailWord_6347773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347773).length < 2 ^ (prefixWord ++ tailWord_6347773).sum := by decide
  have hdescent : baseEnd_6347773 < baseStart_6347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347774 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6347774 : Nat := 118140960795 + 6347774 * 2 ^ 59
def prefixEnd_6347774 : Nat := 4983230072969 + 3 ^ 40 * 6347774 * 2
def baseEnd_6347774 : Nat := 3259459148113352538732125

theorem tailTrace_6347774 : CollatzResearch.WordTrace tailWord_6347774 prefixEnd_6347774 3259459148113352538732125 := by
  unfold tailWord_6347774
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940292263138298291703297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154348225403404257555750917 28940292263138298291703297)
  ·
    refine ⟨21705219197353723718777473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28940292263138298291703297 21705219197353723718777473)
    ·
      refine ⟨16278914398015292789083105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21705219197353723718777473 16278914398015292789083105)
      ·
        refine ⟨12209185798511469591812329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16278914398015292789083105 12209185798511469591812329)
        ·
          refine ⟨9156889348883602193859247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209185798511469591812329 9156889348883602193859247)
          ·
            refine ⟨13735334023325403290788871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156889348883602193859247 13735334023325403290788871)
            ·
              refine ⟨20603001034988104936183307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735334023325403290788871 20603001034988104936183307)
              ·
                refine ⟨30904501552482157404274961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20603001034988104936183307 30904501552482157404274961)
                ·
                  refine ⟨23178376164361618053206221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30904501552482157404274961 23178376164361618053206221)
                  ·
                    refine ⟨8691891061635606769952333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23178376164361618053206221 8691891061635606769952333)
                    ·
                      refine ⟨3259459148113352538732125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8691891061635606769952333 3259459148113352538732125)
                      ·
                        rfl

theorem cell23_6347774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6347774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347774 prefixEnd_6347774 := by exact prefixLift 6347774
  have htrace : WordTrace (prefixWord ++ tailWord_6347774) baseStart_6347774 baseEnd_6347774 := by
    simpa [prefixWord, tailWord_6347774, baseEnd_6347774] using wordTrace_append hprefix tailTrace_6347774
  have hstable : (prefixWord ++ tailWord_6347774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347774).length < 2 ^ (prefixWord ++ tailWord_6347774).sum := by decide
  have hdescent : baseEnd_6347774 < baseStart_6347774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347793 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6347793 : Nat := 118140960795 + 6347793 * 2 ^ 59
def prefixEnd_6347793 : Nat := 4983230072969 + 3 ^ 40 * 6347793 * 2
def baseEnd_6347793 : Nat := 3259468904245787964394537

theorem tailTrace_6347793 : CollatzResearch.WordTrace tailWord_6347793 prefixEnd_6347793 3259468904245787964394537 := by
  unfold tailWord_6347793
  simp only [CollatzResearch.WordTrace]
  refine ⟨231523031092037552578568033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154348687394691701719045355 231523031092037552578568033)
  ·
    refine ⟨173642273319028164433926025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231523031092037552578568033 173642273319028164433926025)
    ·
      refine ⟨130231704989271123325444519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173642273319028164433926025 130231704989271123325444519)
      ·
        refine ⟨195347557483906684988166779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130231704989271123325444519 195347557483906684988166779)
        ·
          refine ⟨293021336225860027482250169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195347557483906684988166779 293021336225860027482250169)
          ·
            refine ⟨219766002169395020611687627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293021336225860027482250169 219766002169395020611687627)
            ·
              refine ⟨329649003254092530917531441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219766002169395020611687627 329649003254092530917531441)
              ·
                refine ⟨247236752440569398188148581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329649003254092530917531441 247236752440569398188148581)
                ·
                  refine ⟨46356891082606762160277859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247236752440569398188148581 46356891082606762160277859)
                  ·
                    refine ⟨69535336623910143240416789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46356891082606762160277859 69535336623910143240416789)
                    ·
                      refine ⟨3259468904245787964394537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69535336623910143240416789 3259468904245787964394537)
                      ·
                        rfl

theorem cell23_6347793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6347793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347793 prefixEnd_6347793 := by exact prefixLift 6347793
  have htrace : WordTrace (prefixWord ++ tailWord_6347793) baseStart_6347793 baseEnd_6347793 := by
    simpa [prefixWord, tailWord_6347793, baseEnd_6347793] using wordTrace_append hprefix tailTrace_6347793
  have hstable : (prefixWord ++ tailWord_6347793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347793).length < 2 ^ (prefixWord ++ tailWord_6347793).sum := by decide
  have hdescent : baseEnd_6347793 < baseStart_6347793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347797 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_6347797 : Nat := 118140960795 + 6347797 * 2 ^ 59
def prefixEnd_6347797 : Nat := 4983230072969 + 3 ^ 40 * 6347797 * 2
def baseEnd_6347797 : Nat := 3259470958168405948744519

theorem tailTrace_6347797 : CollatzResearch.WordTrace tailWord_6347797 prefixEnd_6347797 3259470958168405948744519 := by
  unfold tailWord_6347797
  simp only [CollatzResearch.WordTrace]
  refine ⟨231523176984023061261713645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154348784656015374174475763 231523176984023061261713645)
  ·
    refine ⟨86821191369008647973142617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231523176984023061261713645 86821191369008647973142617)
    ·
      refine ⟨65115893526756485979856963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86821191369008647973142617 65115893526756485979856963)
      ·
        refine ⟨97673840290134728969785445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65115893526756485979856963 97673840290134728969785445)
        ·
          refine ⟨18313845054400261681834771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97673840290134728969785445 18313845054400261681834771)
          ·
            refine ⟨27470767581600392522752157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18313845054400261681834771 27470767581600392522752157)
            ·
              refine ⟨10301537843100147196032059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27470767581600392522752157 10301537843100147196032059)
              ·
                refine ⟨15452306764650220794048089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10301537843100147196032059 15452306764650220794048089)
                ·
                  refine ⟨11589230073487665595536067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15452306764650220794048089 11589230073487665595536067)
                  ·
                    refine ⟨17383845110231498393304101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11589230073487665595536067 17383845110231498393304101)
                    ·
                      refine ⟨3259470958168405948744519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17383845110231498393304101 3259470958168405948744519)
                      ·
                        rfl

theorem cell23_6347797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_6347797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347797 prefixEnd_6347797 := by exact prefixLift 6347797
  have htrace : WordTrace (prefixWord ++ tailWord_6347797) baseStart_6347797 baseEnd_6347797 := by
    simpa [prefixWord, tailWord_6347797, baseEnd_6347797] using wordTrace_append hprefix tailTrace_6347797
  have hstable : (prefixWord ++ tailWord_6347797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347797).length < 2 ^ (prefixWord ++ tailWord_6347797).sum := by decide
  have hdescent : baseEnd_6347797 < baseStart_6347797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347810 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_6347810 : Nat := 118140960795 + 6347810 * 2 ^ 59
def prefixEnd_6347810 : Nat := 4983230072969 + 3 ^ 40 * 6347810 * 2
def baseEnd_6347810 : Nat := 3259477633416914397881959

theorem tailTrace_6347810 : CollatzResearch.WordTrace tailWord_6347810 prefixEnd_6347810 3259477633416914397881959 := by
  unfold tailWord_6347810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57880912783243991120484221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154349100755317309654624589 57880912783243991120484221)
  ·
    refine ⟨21705342293716496670181583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57880912783243991120484221 21705342293716496670181583)
    ·
      refine ⟨32558013440574745005272375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705342293716496670181583 32558013440574745005272375)
      ·
        refine ⟨48837020160862117507908563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32558013440574745005272375 48837020160862117507908563)
        ·
          refine ⟨73255530241293176261862845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48837020160862117507908563 73255530241293176261862845)
          ·
            refine ⟨27470823840484941098198567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73255530241293176261862845 27470823840484941098198567)
            ·
              refine ⟨41206235760727411647297851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27470823840484941098198567 41206235760727411647297851)
              ·
                refine ⟨61809353641091117470946777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41206235760727411647297851 61809353641091117470946777)
                ·
                  refine ⟨46357015230818338103210083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61809353641091117470946777 46357015230818338103210083)
                  ·
                    refine ⟨69535522846227507154815125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46357015230818338103210083 69535522846227507154815125)
                    ·
                      refine ⟨3259477633416914397881959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69535522846227507154815125 3259477633416914397881959)
                      ·
                        rfl

theorem cell23_6347810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_6347810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347810 prefixEnd_6347810 := by exact prefixLift 6347810
  have htrace : WordTrace (prefixWord ++ tailWord_6347810) baseStart_6347810 baseEnd_6347810 := by
    simpa [prefixWord, tailWord_6347810, baseEnd_6347810] using wordTrace_append hprefix tailTrace_6347810
  have hstable : (prefixWord ++ tailWord_6347810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347810).length < 2 ^ (prefixWord ++ tailWord_6347810).sum := by decide
  have hdescent : baseEnd_6347810 < baseStart_6347810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347850 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_6347850 : Nat := 118140960795 + 6347850 * 2 ^ 59
def prefixEnd_6347850 : Nat := 4983230072969 + 3 ^ 40 * 6347850 * 2
def baseEnd_6347850 : Nat := 1086499390881031413793925

theorem tailTrace_6347850 : CollatzResearch.WordTrace tailWord_6347850 prefixEnd_6347850 1086499390881031413793925 := by
  unfold tailWord_6347850
  simp only [CollatzResearch.WordTrace]
  refine ⟨57881277513207762828348251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154350073368554034208928669 57881277513207762828348251)
  ·
    refine ⟨86821916269811644242522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57881277513207762828348251 86821916269811644242522377)
    ·
      refine ⟨65116437202358733181891783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86821916269811644242522377 65116437202358733181891783)
      ·
        refine ⟨97674655803538099772837675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65116437202358733181891783 97674655803538099772837675)
        ·
          refine ⟨146511983705307149659256513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97674655803538099772837675 146511983705307149659256513)
          ·
            refine ⟨109883987778980362244442385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146511983705307149659256513 109883987778980362244442385)
            ·
              refine ⟨82412990834235271683331789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109883987778980362244442385 82412990834235271683331789)
              ·
                refine ⟨30904871562838226881249421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82412990834235271683331789 30904871562838226881249421)
                ·
                  refine ⟨11589326836064335080468533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30904871562838226881249421 11589326836064335080468533)
                  ·
                    refine ⟨1086499390881031413793925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11589326836064335080468533 1086499390881031413793925)
                    ·
                      rfl

theorem cell23_6347850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_6347850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347850 prefixEnd_6347850 := by exact prefixLift 6347850
  have htrace : WordTrace (prefixWord ++ tailWord_6347850) baseStart_6347850 baseEnd_6347850 := by
    simpa [prefixWord, tailWord_6347850, baseEnd_6347850] using wordTrace_append hprefix tailTrace_6347850
  have hstable : (prefixWord ++ tailWord_6347850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347850).length < 2 ^ (prefixWord ++ tailWord_6347850).sum := by decide
  have hdescent : baseEnd_6347850 < baseStart_6347850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347857 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_6347857 : Nat := 118140960795 + 6347857 * 2 ^ 59
def prefixEnd_6347857 : Nat := 4983230072969 + 3 ^ 40 * 6347857 * 2
def baseEnd_6347857 : Nat := 3259501767007675713994243

theorem tailTrace_6347857 : CollatzResearch.WordTrace tailWord_6347857 prefixEnd_6347857 3259501767007675713994243 := by
  unfold tailWord_6347857
  simp only [CollatzResearch.WordTrace]
  refine ⟨231525365363805691508897825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154350243575870461005931883 231525365363805691508897825)
  ·
    refine ⟨173644024022854268631673369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231525365363805691508897825 173644024022854268631673369)
    ·
      refine ⟨130233018017140701473755027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173644024022854268631673369 130233018017140701473755027)
      ·
        refine ⟨195349527025711052210632541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130233018017140701473755027 195349527025711052210632541)
        ·
          refine ⟨73256072634641644578987203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195349527025711052210632541 73256072634641644578987203)
          ·
            refine ⟨109884108951962466868480805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73256072634641644578987203 109884108951962466868480805)
            ·
              refine ⟨20603270428492962537840151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109884108951962466868480805 20603270428492962537840151)
              ·
                refine ⟨30904905642739443806760227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20603270428492962537840151 30904905642739443806760227)
                ·
                  refine ⟨46357358464109165710140341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30904905642739443806760227 46357358464109165710140341)
                  ·
                    refine ⟨4346002356010234285325657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46357358464109165710140341 4346002356010234285325657)
                    ·
                      refine ⟨3259501767007675713994243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346002356010234285325657 3259501767007675713994243)
                      ·
                        rfl

theorem cell23_6347857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_6347857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347857 prefixEnd_6347857 := by exact prefixLift 6347857
  have htrace : WordTrace (prefixWord ++ tailWord_6347857) baseStart_6347857 baseEnd_6347857 := by
    simpa [prefixWord, tailWord_6347857, baseEnd_6347857] using wordTrace_append hprefix tailTrace_6347857
  have hstable : (prefixWord ++ tailWord_6347857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347857).length < 2 ^ (prefixWord ++ tailWord_6347857).sum := by decide
  have hdescent : baseEnd_6347857 < baseStart_6347857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347900 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6347900 : Nat := 118140960795 + 6347900 * 2 ^ 59
def prefixEnd_6347900 : Nat := 4983230072969 + 3 ^ 40 * 6347900 * 2
def baseEnd_6347900 : Nat := 3259523846675819045756545

theorem tailTrace_6347900 : CollatzResearch.WordTrace tailWord_6347900 prefixEnd_6347900 3259523846675819045756545 := by
  unfold tailWord_6347900
  simp only [CollatzResearch.WordTrace]
  refine ⟨115763466851324954926356577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154351289135099939901808769 115763466851324954926356577)
  ·
    refine ⟨86822600138493716194767433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115763466851324954926356577 86822600138493716194767433)
    ·
      refine ⟨65116950103870287146075575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86822600138493716194767433 65116950103870287146075575)
      ·
        refine ⟨97675425155805430719113363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65116950103870287146075575 97675425155805430719113363)
        ·
          refine ⟨146513137733708146078670045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97675425155805430719113363 146513137733708146078670045)
          ·
            refine ⟨54942426650140554779501267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146513137733708146078670045 54942426650140554779501267)
            ·
              refine ⟨82413639975210832169251901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54942426650140554779501267 82413639975210832169251901)
              ·
                refine ⟨30905114990704062063469463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82413639975210832169251901 30905114990704062063469463)
                ·
                  refine ⟨46357672486056093095204195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30905114990704062063469463 46357672486056093095204195)
                  ·
                    refine ⟨69536508729084139642806293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46357672486056093095204195 69536508729084139642806293)
                    ·
                      refine ⟨3259523846675819045756545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69536508729084139642806293 3259523846675819045756545)
                      ·
                        rfl

theorem cell23_6347900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6347900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347900 prefixEnd_6347900 := by exact prefixLift 6347900
  have htrace : WordTrace (prefixWord ++ tailWord_6347900) baseStart_6347900 baseEnd_6347900 := by
    simpa [prefixWord, tailWord_6347900, baseEnd_6347900] using wordTrace_append hprefix tailTrace_6347900
  have hstable : (prefixWord ++ tailWord_6347900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347900).length < 2 ^ (prefixWord ++ tailWord_6347900).sum := by decide
  have hdescent : baseEnd_6347900 < baseStart_6347900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347904 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2]
def baseStart_6347904 : Nat := 118140960795 + 6347904 * 2 ^ 59
def prefixEnd_6347904 : Nat := 4983230072969 + 3 ^ 40 * 6347904 * 2
def baseEnd_6347904 : Nat := 3259525900598437030106527

theorem tailTrace_6347904 : CollatzResearch.WordTrace tailWord_6347904 prefixEnd_6347904 3259525900598437030106527 := by
  unfold tailWord_6347904
  simp only [CollatzResearch.WordTrace]
  refine ⟨115763539797317709267929383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154351386396423612357239177 115763539797317709267929383)
  ·
    refine ⟨173645309695976563901894075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115763539797317709267929383 173645309695976563901894075)
    ·
      refine ⟨260467964543964845852841113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173645309695976563901894075 260467964543964845852841113)
      ·
        refine ⟨195350973407973634389630835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260467964543964845852841113 195350973407973634389630835)
        ·
          refine ⟨293026460111960451584446253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195350973407973634389630835 293026460111960451584446253)
          ·
            refine ⟨109884922541985169344167345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293026460111960451584446253 109884922541985169344167345)
            ·
              refine ⟨82413691906488877008125509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109884922541985169344167345 82413691906488877008125509)
              ·
                refine ⟨15452567232466664439023533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82413691906488877008125509 15452567232466664439023533)
                ·
                  refine ⟨5794712712174999164633825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15452567232466664439023533 5794712712174999164633825)
                  ·
                    refine ⟨4346034534131249373475369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794712712174999164633825 4346034534131249373475369)
                    ·
                      refine ⟨3259525900598437030106527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346034534131249373475369 3259525900598437030106527)
                      ·
                        rfl

theorem cell23_6347904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_6347904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347904 prefixEnd_6347904 := by exact prefixLift 6347904
  have htrace : WordTrace (prefixWord ++ tailWord_6347904) baseStart_6347904 baseEnd_6347904 := by
    simpa [prefixWord, tailWord_6347904, baseEnd_6347904] using wordTrace_append hprefix tailTrace_6347904
  have hstable : (prefixWord ++ tailWord_6347904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347904).length < 2 ^ (prefixWord ++ tailWord_6347904).sum := by decide
  have hdescent : baseEnd_6347904 < baseStart_6347904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347907 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3]
def baseStart_6347907 : Nat := 118140960795 + 6347907 * 2 ^ 59
def prefixEnd_6347907 : Nat := 4983230072969 + 3 ^ 40 * 6347907 * 2
def baseEnd_6347907 : Nat := 3259527441040400518369013

theorem tailTrace_6347907 : CollatzResearch.WordTrace tailWord_6347907 prefixEnd_6347907 3259527441040400518369013 := by
  unfold tailWord_6347907
  simp only [CollatzResearch.WordTrace]
  refine ⟨231527189013624550048217975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154351459342416366698811983 231527189013624550048217975)
  ·
    refine ⟨347290783520436825072326963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231527189013624550048217975 347290783520436825072326963)
    ·
      refine ⟨520936175280655237608490445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347290783520436825072326963 520936175280655237608490445)
      ·
        refine ⟨195351065730245714103183917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520936175280655237608490445 195351065730245714103183917)
        ·
          refine ⟨73256649648842142788693969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195351065730245714103183917 73256649648842142788693969)
          ·
            refine ⟨54942487236631607091520477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73256649648842142788693969 54942487236631607091520477)
            ·
              refine ⟨20603432713736852659320179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54942487236631607091520477 20603432713736852659320179)
              ·
                refine ⟨30905149070605278988980269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20603432713736852659320179 30905149070605278988980269)
                ·
                  refine ⟨11589430901476979620867601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30905149070605278988980269 11589430901476979620867601)
                  ·
                    refine ⟨8692073176107734715650701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11589430901476979620867601 8692073176107734715650701)
                    ·
                      refine ⟨3259527441040400518369013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692073176107734715650701 3259527441040400518369013)
                      ·
                        rfl

theorem cell23_6347907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_6347907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347907 prefixEnd_6347907 := by exact prefixLift 6347907
  have htrace : WordTrace (prefixWord ++ tailWord_6347907) baseStart_6347907 baseEnd_6347907 := by
    simpa [prefixWord, tailWord_6347907, baseEnd_6347907] using wordTrace_append hprefix tailTrace_6347907
  have hstable : (prefixWord ++ tailWord_6347907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347907).length < 2 ^ (prefixWord ++ tailWord_6347907).sum := by decide
  have hdescent : baseEnd_6347907 < baseStart_6347907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347937 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6347937 : Nat := 118140960795 + 6347937 * 2 ^ 59
def prefixEnd_6347937 : Nat := 4983230072969 + 3 ^ 40 * 6347937 * 2
def baseEnd_6347937 : Nat := 3259542845460035400993875

theorem tailTrace_6347937 : CollatzResearch.WordTrace tailWord_6347937 prefixEnd_6347937 3259542845460035400993875 := by
  unfold tailWord_6347937
  simp only [CollatzResearch.WordTrace]
  refine ⟨231528283203515865171810065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154352188802343910114540043 231528283203515865171810065)
  ·
    refine ⟨173646212402636898878857549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231528283203515865171810065 173646212402636898878857549)
    ·
      refine ⟨65117329650988837079571581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173646212402636898878857549 65117329650988837079571581)
      ·
        refine ⟨24418998619120813904839343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65117329650988837079571581 24418998619120813904839343)
        ·
          refine ⟨36628497928681220857259015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24418998619120813904839343 36628497928681220857259015)
          ·
            refine ⟨54942746893021831285888523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36628497928681220857259015 54942746893021831285888523)
            ·
              refine ⟨82414120339532746928832785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54942746893021831285888523 82414120339532746928832785)
              ·
                refine ⟨61810590254649560196624589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82414120339532746928832785 61810590254649560196624589)
                ·
                  refine ⟨23178971345493585073734221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61810590254649560196624589 23178971345493585073734221)
                  ·
                    refine ⟨8692114254560094402650333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23178971345493585073734221 8692114254560094402650333)
                    ·
                      refine ⟨3259542845460035400993875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692114254560094402650333 3259542845460035400993875)
                      ·
                        rfl

theorem cell23_6347937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6347937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347937 prefixEnd_6347937 := by exact prefixLift 6347937
  have htrace : WordTrace (prefixWord ++ tailWord_6347937) baseStart_6347937 baseEnd_6347937 := by
    simpa [prefixWord, tailWord_6347937, baseEnd_6347937] using wordTrace_append hprefix tailTrace_6347937
  have hstable : (prefixWord ++ tailWord_6347937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347937).length < 2 ^ (prefixWord ++ tailWord_6347937).sum := by decide
  have hdescent : baseEnd_6347937 < baseStart_6347937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347954 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_6347954 : Nat := 118140960795 + 6347954 * 2 ^ 59
def prefixEnd_6347954 : Nat := 4983230072969 + 3 ^ 40 * 6347954 * 2
def baseEnd_6347954 : Nat := 3259551574631161834481297

theorem tailTrace_6347954 : CollatzResearch.WordTrace tailWord_6347954 prefixEnd_6347954 3259551574631161834481297 := by
  unfold tailWord_6347954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57882225811113569268794729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154352602162969518050119277 57882225811113569268794729)
  ·
    refine ⟨43411669358335176951596047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57882225811113569268794729 43411669358335176951596047)
    ·
      refine ⟨65117504037502765427394071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43411669358335176951596047 65117504037502765427394071)
      ·
        refine ⟨97676256056254148141091107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65117504037502765427394071 97676256056254148141091107)
        ·
          refine ⟨146514384084381222211636661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97676256056254148141091107 146514384084381222211636661)
          ·
            refine ⟨13735723507910739582340937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146514384084381222211636661 13735723507910739582340937)
            ·
              refine ⟨10301792630933054686755703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13735723507910739582340937 10301792630933054686755703)
              ·
                refine ⟨15452688946399582030133555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10301792630933054686755703 15452688946399582030133555)
                ·
                  refine ⟨23179033419599373045200333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15452688946399582030133555 23179033419599373045200333)
                  ·
                    refine ⟨8692137532349764891950125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23179033419599373045200333 8692137532349764891950125)
                    ·
                      refine ⟨3259551574631161834481297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692137532349764891950125 3259551574631161834481297)
                      ·
                        rfl

theorem cell23_6347954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_6347954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347954 prefixEnd_6347954 := by exact prefixLift 6347954
  have htrace : WordTrace (prefixWord ++ tailWord_6347954) baseStart_6347954 baseEnd_6347954 := by
    simpa [prefixWord, tailWord_6347954, baseEnd_6347954] using wordTrace_append hprefix tailTrace_6347954
  have hstable : (prefixWord ++ tailWord_6347954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347954).length < 2 ^ (prefixWord ++ tailWord_6347954).sum := by decide
  have hdescent : baseEnd_6347954 < baseStart_6347954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347977 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 8, 2]
def baseStart_6347977 : Nat := 118140960795 + 6347977 * 2 ^ 59
def prefixEnd_6347977 : Nat := 4983230072969 + 3 ^ 40 * 6347977 * 2
def baseEnd_6347977 : Nat := 3259563384686215244493691

theorem tailTrace_6347977 : CollatzResearch.WordTrace tailWord_6347977 prefixEnd_6347977 3259563384686215244493691 := by
  unfold tailWord_6347977
  simp only [CollatzResearch.WordTrace]
  refine ⟨231529742123370952003266185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154353161415580634668844123 231529742123370952003266185)
  ·
    refine ⟨173647306592528214002449639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231529742123370952003266185 173647306592528214002449639)
    ·
      refine ⟨260470959888792321003674459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173647306592528214002449639 260470959888792321003674459)
      ·
        refine ⟨390706439833188481505511689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260470959888792321003674459 390706439833188481505511689)
        ·
          refine ⟨293029829874891361129133767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390706439833188481505511689 293029829874891361129133767)
          ·
            refine ⟨439544744812337041693700651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293029829874891361129133767 439544744812337041693700651)
            ·
              refine ⟨659317117218505562540550977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439544744812337041693700651 659317117218505562540550977)
              ·
                refine ⟨494487837913879171905413233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659317117218505562540550977 494487837913879171905413233)
                ·
                  refine ⟨370865878435409378929059925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494487837913879171905413233 370865878435409378929059925)
                  ·
                    refine ⟨4346084512914953659324921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 370865878435409378929059925 4346084512914953659324921)
                    ·
                      refine ⟨3259563384686215244493691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346084512914953659324921 3259563384686215244493691)
                      ·
                        rfl

theorem cell23_6347977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8, 2].length) (baseStart_6347977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347977 prefixEnd_6347977 := by exact prefixLift 6347977
  have htrace : WordTrace (prefixWord ++ tailWord_6347977) baseStart_6347977 baseEnd_6347977 := by
    simpa [prefixWord, tailWord_6347977, baseEnd_6347977] using wordTrace_append hprefix tailTrace_6347977
  have hstable : (prefixWord ++ tailWord_6347977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347977).length < 2 ^ (prefixWord ++ tailWord_6347977).sum := by decide
  have hdescent : baseEnd_6347977 < baseStart_6347977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6347988 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6347988 : Nat := 118140960795 + 6347988 * 2 ^ 59
def prefixEnd_6347988 : Nat := 4983230072969 + 3 ^ 40 * 6347988 * 2
def baseEnd_6347988 : Nat := 3259569032973414701456141

theorem tailTrace_6347988 : CollatzResearch.WordTrace tailWord_6347988 prefixEnd_6347988 3259569032973414701456141 := by
  unfold tailWord_6347988
  simp only [CollatzResearch.WordTrace]
  refine ⟨115765071663165550440958309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154353428884220733921277745 115765071663165550440958309)
  ·
    refine ⟨21705950936843540707679683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115765071663165550440958309 21705950936843540707679683)
    ·
      refine ⟨32558926405265311061519525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705950936843540707679683 32558926405265311061519525)
      ·
        refine ⟨6104798700987245824034911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32558926405265311061519525 6104798700987245824034911)
        ·
          refine ⟨9157198051480868736052367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104798700987245824034911 9157198051480868736052367)
          ·
            refine ⟨13735797077221303104078551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157198051480868736052367 13735797077221303104078551)
            ·
              refine ⟨20603695615831954656117827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735797077221303104078551 20603695615831954656117827)
              ·
                refine ⟨30905543423747931984176741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20603695615831954656117827 30905543423747931984176741)
                ·
                  refine ⟨5794789391952737247033139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30905543423747931984176741 5794789391952737247033139)
                  ·
                    refine ⟨8692184087929105870549709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794789391952737247033139 8692184087929105870549709)
                    ·
                      refine ⟨3259569032973414701456141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692184087929105870549709 3259569032973414701456141)
                      ·
                        rfl

theorem cell23_6347988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6347988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6347988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6347988 prefixEnd_6347988 := by exact prefixLift 6347988
  have htrace : WordTrace (prefixWord ++ tailWord_6347988) baseStart_6347988 baseEnd_6347988 := by
    simpa [prefixWord, tailWord_6347988, baseEnd_6347988] using wordTrace_append hprefix tailTrace_6347988
  have hstable : (prefixWord ++ tailWord_6347988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6347988).length < 2 ^ (prefixWord ++ tailWord_6347988).sum := by decide
  have hdescent : baseEnd_6347988 < baseStart_6347988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6347988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348011 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 4, 2]
def baseStart_6348011 : Nat := 118140960795 + 6348011 * 2 ^ 59
def prefixEnd_6348011 : Nat := 4983230072969 + 3 ^ 40 * 6348011 * 2
def baseEnd_6348011 : Nat := 3259580843028468111468535

theorem tailTrace_6348011 : CollatzResearch.WordTrace tailWord_6348011 prefixEnd_6348011 3259580843028468111468535 := by
  unfold tailWord_6348011
  simp only [CollatzResearch.WordTrace]
  refine ⟨231530982205247775810003887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154353988136831850540002591 231530982205247775810003887)
  ·
    refine ⟨347296473307871663715005831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231530982205247775810003887 347296473307871663715005831)
    ·
      refine ⟨520944709961807495572508747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347296473307871663715005831 520944709961807495572508747)
      ·
        refine ⟨781417064942711243358763121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520944709961807495572508747 781417064942711243358763121)
        ·
          refine ⟨586062798707033432519072341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781417064942711243358763121 586062798707033432519072341)
          ·
            refine ⟨6867923422348048037332879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 586062798707033432519072341 6867923422348048037332879)
            ·
              refine ⟨10301885133522072055999319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867923422348048037332879 10301885133522072055999319)
              ·
                refine ⟨15452827700283108083998979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10301885133522072055999319 15452827700283108083998979)
                ·
                  refine ⟨23179241550424662125998469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15452827700283108083998979 23179241550424662125998469)
                  ·
                    refine ⟨4346107790704624148624713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23179241550424662125998469 4346107790704624148624713)
                    ·
                      refine ⟨3259580843028468111468535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346107790704624148624713 3259580843028468111468535)
                      ·
                        rfl

theorem cell23_6348011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 4, 2].length) (baseStart_6348011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348011 prefixEnd_6348011 := by exact prefixLift 6348011
  have htrace : WordTrace (prefixWord ++ tailWord_6348011) baseStart_6348011 baseEnd_6348011 := by
    simpa [prefixWord, tailWord_6348011, baseEnd_6348011] using wordTrace_append hprefix tailTrace_6348011
  have hstable : (prefixWord ++ tailWord_6348011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348011).length < 2 ^ (prefixWord ++ tailWord_6348011).sum := by decide
  have hdescent : baseEnd_6348011 < baseStart_6348011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348062 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6348062 : Nat := 118140960795 + 6348062 * 2 ^ 59
def prefixEnd_6348062 : Nat := 4983230072969 + 3 ^ 40 * 6348062 * 2
def baseEnd_6348062 : Nat := 3259607030541847411930801

theorem tailTrace_6348062 : CollatzResearch.WordTrace tailWord_6348062 prefixEnd_6348062 3259607030541847411930801 := by
  unfold tailWord_6348062
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941605291007876440013805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154355228218708674346740293 28941605291007876440013805)
  ·
    refine ⟨10853101984127953665005177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28941605291007876440013805 10853101984127953665005177)
    ·
      refine ⟨8139826488095965248753883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853101984127953665005177 8139826488095965248753883)
      ·
        refine ⟨12209739732143947873130825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139826488095965248753883 12209739732143947873130825)
        ·
          refine ⟨9157304799107960904848119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209739732143947873130825 9157304799107960904848119)
          ·
            refine ⟨13735957198661941357272179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157304799107960904848119 13735957198661941357272179)
            ·
              refine ⟨20603935797992912035908269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735957198661941357272179 20603935797992912035908269)
              ·
                refine ⟨7726475924247342013465601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20603935797992912035908269 7726475924247342013465601)
                ·
                  refine ⟨5794856943185506510099201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726475924247342013465601 5794856943185506510099201)
                  ·
                    refine ⟨4346142707389129882574401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794856943185506510099201 4346142707389129882574401)
                    ·
                      refine ⟨3259607030541847411930801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346142707389129882574401 3259607030541847411930801)
                      ·
                        rfl

theorem cell23_6348062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6348062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348062 prefixEnd_6348062 := by exact prefixLift 6348062
  have htrace : WordTrace (prefixWord ++ tailWord_6348062) baseStart_6348062 baseEnd_6348062 := by
    simpa [prefixWord, tailWord_6348062, baseEnd_6348062] using wordTrace_append hprefix tailTrace_6348062
  have hstable : (prefixWord ++ tailWord_6348062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348062).length < 2 ^ (prefixWord ++ tailWord_6348062).sum := by decide
  have hdescent : baseEnd_6348062 < baseStart_6348062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348154 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_6348154 : Nat := 118140960795 + 6348154 * 2 ^ 59
def prefixEnd_6348154 : Nat := 4983230072969 + 3 ^ 40 * 6348154 * 2
def baseEnd_6348154 : Nat := 1086551423587353683993459

theorem tailTrace_6348154 : CollatzResearch.WordTrace tailWord_6348154 prefixEnd_6348154 1086551423587353683993459 := by
  unfold tailWord_6348154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57884049460932427808114879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154357465229153140821639677 57884049460932427808114879)
  ·
    refine ⟨86826074191398641712172319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57884049460932427808114879 86826074191398641712172319)
    ·
      refine ⟨130239111287097962568258479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86826074191398641712172319 130239111287097962568258479)
      ·
        refine ⟨195358666930646943852387719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130239111287097962568258479 195358666930646943852387719)
        ·
          refine ⟨293038000395970415778581579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195358666930646943852387719 293038000395970415778581579)
          ·
            refine ⟨439557000593955623667872369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293038000395970415778581579 439557000593955623667872369)
            ·
              refine ⟨329667750445466717750904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439557000593955623667872369 329667750445466717750904277)
              ·
                refine ⟨7726587901065626197286819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329667750445466717750904277 7726587901065626197286819)
                ·
                  refine ⟨11589881851598439295930229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7726587901065626197286819 11589881851598439295930229)
                  ·
                    refine ⟨1086551423587353683993459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11589881851598439295930229 1086551423587353683993459)
                    ·
                      rfl

theorem cell23_6348154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_6348154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348154 prefixEnd_6348154 := by exact prefixLift 6348154
  have htrace : WordTrace (prefixWord ++ tailWord_6348154) baseStart_6348154 baseEnd_6348154 := by
    simpa [prefixWord, tailWord_6348154, baseEnd_6348154] using wordTrace_append hprefix tailTrace_6348154
  have hstable : (prefixWord ++ tailWord_6348154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348154).length < 2 ^ (prefixWord ++ tailWord_6348154).sum := by decide
  have hdescent : baseEnd_6348154 < baseStart_6348154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348158 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_6348158 : Nat := 118140960795 + 6348158 * 2 ^ 59
def prefixEnd_6348158 : Nat := 4983230072969 + 3 ^ 40 * 6348158 * 2
def baseEnd_6348158 : Nat := 362184036076075448481151

theorem tailTrace_6348158 : CollatzResearch.WordTrace tailWord_6348158 prefixEnd_6348158 362184036076075448481151 := by
  unfold tailWord_6348158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942042966964402489450641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154357562490476813277070085 28942042966964402489450641)
  ·
    refine ⟨21706532225223301867087981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28942042966964402489450641 21706532225223301867087981)
    ·
      refine ⟨8139949584458738200157993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21706532225223301867087981 8139949584458738200157993)
      ·
        refine ⟨6104962188344053650118495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139949584458738200157993 6104962188344053650118495)
        ·
          refine ⟨9157443282516080475177743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104962188344053650118495 9157443282516080475177743)
          ·
            refine ⟨13736164923774120712766615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157443282516080475177743 13736164923774120712766615)
            ·
              refine ⟨20604247385661181069149923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736164923774120712766615 20604247385661181069149923)
              ·
                refine ⟨30906371078491771603724885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20604247385661181069149923 30906371078491771603724885)
                ·
                  refine ⟨362184036076075448481151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30906371078491771603724885 362184036076075448481151)
                  ·
                    rfl

theorem cell23_6348158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_6348158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348158 prefixEnd_6348158 := by exact prefixLift 6348158
  have htrace : WordTrace (prefixWord ++ tailWord_6348158) baseStart_6348158 baseEnd_6348158 := by
    simpa [prefixWord, tailWord_6348158, baseEnd_6348158] using wordTrace_append hprefix tailTrace_6348158
  have hstable : (prefixWord ++ tailWord_6348158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348158).length < 2 ^ (prefixWord ++ tailWord_6348158).sum := by decide
  have hdescent : baseEnd_6348158 < baseStart_6348158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348168 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_6348168 : Nat := 118140960795 + 6348168 * 2 ^ 59
def prefixEnd_6348168 : Nat := 4983230072969 + 3 ^ 40 * 6348168 * 2
def baseEnd_6348168 : Nat := 3259661459491223997205313

theorem tailTrace_6348168 : CollatzResearch.WordTrace tailWord_6348168 prefixEnd_6348168 3259661459491223997205313 := by
  unfold tailWord_6348168
  simp only [CollatzResearch.WordTrace]
  refine ⟨115768354232839495811734579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154357805643785994415646105 115768354232839495811734579)
  ·
    refine ⟨173652531349259243717601869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115768354232839495811734579 173652531349259243717601869)
    ·
      refine ⟨65119699255972216394100701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173652531349259243717601869 65119699255972216394100701)
      ·
        refine ⟨24419887220989581147787763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65119699255972216394100701 24419887220989581147787763)
        ·
          refine ⟨36629830831484371721681645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24419887220989581147787763 36629830831484371721681645)
          ·
            refine ⟨13736186561806639395630617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36629830831484371721681645 13736186561806639395630617)
            ·
              refine ⟨10302139921354979546722963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13736186561806639395630617 10302139921354979546722963)
              ·
                refine ⟨15453209882032469320084445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10302139921354979546722963 15453209882032469320084445)
                ·
                  refine ⟨5794953705762175995031667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15453209882032469320084445 5794953705762175995031667)
                  ·
                    refine ⟨8692430558643263992547501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794953705762175995031667 8692430558643263992547501)
                    ·
                      refine ⟨3259661459491223997205313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692430558643263992547501 3259661459491223997205313)
                      ·
                        rfl

theorem cell23_6348168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_6348168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348168 prefixEnd_6348168 := by exact prefixLift 6348168
  have htrace : WordTrace (prefixWord ++ tailWord_6348168) baseStart_6348168 baseEnd_6348168 := by
    simpa [prefixWord, tailWord_6348168, baseEnd_6348168] using wordTrace_append hprefix tailTrace_6348168
  have hstable : (prefixWord ++ tailWord_6348168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348168).length < 2 ^ (prefixWord ++ tailWord_6348168).sum := by decide
  have hdescent : baseEnd_6348168 < baseStart_6348168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348187 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_6348187 : Nat := 118140960795 + 6348187 * 2 ^ 59
def prefixEnd_6348187 : Nat := 4983230072969 + 3 ^ 40 * 6348187 * 2
def baseEnd_6348187 : Nat := 3259671215623659422867725

theorem tailTrace_6348187 : CollatzResearch.WordTrace tailWord_6348187 prefixEnd_6348187 3259671215623659422867725 := by
  unfold tailWord_6348187
  simp only [CollatzResearch.WordTrace]
  refine ⟨231537401452610157868410815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154358267635073438578940543 231537401452610157868410815)
  ·
    refine ⟨347306102178915236802616223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231537401452610157868410815 347306102178915236802616223)
    ·
      refine ⟨520959153268372855203924335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347306102178915236802616223 520959153268372855203924335)
      ·
        refine ⟨781438729902559282805886503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520959153268372855203924335 781438729902559282805886503)
        ·
          refine ⟨1172158094853838924208829755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781438729902559282805886503 1172158094853838924208829755)
          ·
            refine ⟨1758237142280758386313244633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172158094853838924208829755 1758237142280758386313244633)
            ·
              refine ⟨1318677856710568789734933475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758237142280758386313244633 1318677856710568789734933475)
              ·
                refine ⟨1978016785065853184602400213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318677856710568789734933475 1978016785065853184602400213)
                ·
                  refine ⟨46359768399980934014118755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1978016785065853184602400213 46359768399980934014118755)
                  ·
                    refine ⟨69539652599971401021178133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46359768399980934014118755 69539652599971401021178133)
                    ·
                      refine ⟨3259671215623659422867725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69539652599971401021178133 3259671215623659422867725)
                      ·
                        rfl

theorem cell23_6348187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_6348187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348187 prefixEnd_6348187 := by exact prefixLift 6348187
  have htrace : WordTrace (prefixWord ++ tailWord_6348187) baseStart_6348187 baseEnd_6348187 := by
    simpa [prefixWord, tailWord_6348187, baseEnd_6348187] using wordTrace_append hprefix tailTrace_6348187
  have hstable : (prefixWord ++ tailWord_6348187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348187).length < 2 ^ (prefixWord ++ tailWord_6348187).sum := by decide
  have hdescent : baseEnd_6348187 < baseStart_6348187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348191 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6348191 : Nat := 118140960795 + 6348191 * 2 ^ 59
def prefixEnd_6348191 : Nat := 4983230072969 + 3 ^ 40 * 6348191 * 2
def baseEnd_6348191 : Nat := 3259673269546277407217707

theorem tailTrace_6348191 : CollatzResearch.WordTrace tailWord_6348191 prefixEnd_6348191 3259673269546277407217707 := by
  unfold tailWord_6348191
  simp only [CollatzResearch.WordTrace]
  refine ⟨231537547344595666551556427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154358364896397111034370951 231537547344595666551556427)
  ·
    refine ⟨347306321016893499827334641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231537547344595666551556427 347306321016893499827334641)
    ·
      refine ⟨260479740762670124870500981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347306321016893499827334641 260479740762670124870500981)
      ·
        refine ⟨24419975696500324206609467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260479740762670124870500981 24419975696500324206609467)
        ·
          refine ⟨36629963544750486309914201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24419975696500324206609467 36629963544750486309914201)
          ·
            refine ⟨27472472658562864732435651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36629963544750486309914201 27472472658562864732435651)
            ·
              refine ⟨41208708987844297098653477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27472472658562864732435651 41208708987844297098653477)
              ·
                refine ⟨7726632935220805705997527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41208708987844297098653477 7726632935220805705997527)
                ·
                  refine ⟨11589949402831208558996291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7726632935220805705997527 11589949402831208558996291)
                  ·
                    refine ⟨17384924104246812838494437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11589949402831208558996291 17384924104246812838494437)
                    ·
                      refine ⟨3259673269546277407217707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17384924104246812838494437 3259673269546277407217707)
                      ·
                        rfl

theorem cell23_6348191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6348191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348191 prefixEnd_6348191 := by exact prefixLift 6348191
  have htrace : WordTrace (prefixWord ++ tailWord_6348191) baseStart_6348191 baseEnd_6348191 := by
    simpa [prefixWord, tailWord_6348191, baseEnd_6348191] using wordTrace_append hprefix tailTrace_6348191
  have hstable : (prefixWord ++ tailWord_6348191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348191).length < 2 ^ (prefixWord ++ tailWord_6348191).sum := by decide
  have hdescent : baseEnd_6348191 < baseStart_6348191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348204 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_6348204 : Nat := 118140960795 + 6348204 * 2 ^ 59
def prefixEnd_6348204 : Nat := 4983230072969 + 3 ^ 40 * 6348204 * 2
def baseEnd_6348204 : Nat := 3259679944794785856355147

theorem tailTrace_6348204 : CollatzResearch.WordTrace tailWord_6348204 prefixEnd_6348204 3259679944794785856355147 := by
  unfold tailWord_6348204
  simp only [CollatzResearch.WordTrace]
  refine ⟨115769010746774284885889833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154358680995699046514519777 115769010746774284885889833)
  ·
    refine ⟨86826758060080713664417375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115769010746774284885889833 86826758060080713664417375)
    ·
      refine ⟨130240137090121070496626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86826758060080713664417375 130240137090121070496626063)
      ·
        refine ⟨195360205635181605744939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130240137090121070496626063 195360205635181605744939095)
        ·
          refine ⟨293040308452772408617408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195360205635181605744939095 293040308452772408617408643)
          ·
            refine ⟨439560462679158612926112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293040308452772408617408643 439560462679158612926112965)
            ·
              refine ⟨82417586752342239923646181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439560462679158612926112965 82417586752342239923646181)
              ·
                refine ⟨15453297516064169985683659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82417586752342239923646181 15453297516064169985683659)
                ·
                  refine ⟨23179946274096254978525489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15453297516064169985683659 23179946274096254978525489)
                  ·
                    refine ⟨17384959705572191233894117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23179946274096254978525489 17384959705572191233894117)
                    ·
                      refine ⟨3259679944794785856355147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17384959705572191233894117 3259679944794785856355147)
                      ·
                        rfl

theorem cell23_6348204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_6348204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348204 prefixEnd_6348204 := by exact prefixLift 6348204
  have htrace : WordTrace (prefixWord ++ tailWord_6348204) baseStart_6348204 baseEnd_6348204 := by
    simpa [prefixWord, tailWord_6348204, baseEnd_6348204] using wordTrace_append hprefix tailTrace_6348204
  have hstable : (prefixWord ++ tailWord_6348204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348204).length < 2 ^ (prefixWord ++ tailWord_6348204).sum := by decide
  have hdescent : baseEnd_6348204 < baseStart_6348204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348226 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6348226 : Nat := 118140960795 + 6348226 * 2 ^ 59
def prefixEnd_6348226 : Nat := 4983230072969 + 3 ^ 40 * 6348226 * 2
def baseEnd_6348226 : Nat := 362187915707687196697783

theorem tailTrace_6348226 : CollatzResearch.WordTrace tailWord_6348226 prefixEnd_6348226 362187915707687196697783 := by
  unfold tailWord_6348226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57884705974867216882270133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154359215932979245019387021 57884705974867216882270133)
  ·
    refine ⟨5426691185143801582712825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57884705974867216882270133 5426691185143801582712825)
    ·
      refine ⟨4070018388857851187034619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426691185143801582712825 4070018388857851187034619)
      ·
        refine ⟨6105027583286776780551929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070018388857851187034619 6105027583286776780551929)
        ·
          refine ⟨4578770687465082585413947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6105027583286776780551929 4578770687465082585413947)
          ·
            refine ⟨6868156031197623878120921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578770687465082585413947 6868156031197623878120921)
            ·
              refine ⟨5151117023398217908590691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868156031197623878120921 5151117023398217908590691)
              ·
                refine ⟨7726675535097326862886037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151117023398217908590691 7726675535097326862886037)
                ·
                  refine ⟨362187915707687196697783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7726675535097326862886037 362187915707687196697783)
                  ·
                    rfl

theorem cell23_6348226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6348226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348226 prefixEnd_6348226 := by exact prefixLift 6348226
  have htrace : WordTrace (prefixWord ++ tailWord_6348226) baseStart_6348226 baseEnd_6348226 := by
    simpa [prefixWord, tailWord_6348226, baseEnd_6348226] using wordTrace_append hprefix tailTrace_6348226
  have hstable : (prefixWord ++ tailWord_6348226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348226).length < 2 ^ (prefixWord ++ tailWord_6348226).sum := by decide
  have hdescent : baseEnd_6348226 < baseStart_6348226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 4, 2]
def baseStart_6348281 : Nat := 118140960795 + 6348281 * 2 ^ 59
def prefixEnd_6348281 : Nat := 4983230072969 + 3 ^ 40 * 6348281 * 2
def baseEnd_6348281 : Nat := 3259719482805182055092293

theorem tailTrace_6348281 : CollatzResearch.WordTrace tailWord_6348281 prefixEnd_6348281 3259719482805182055092293 := by
  unfold tailWord_6348281
  simp only [CollatzResearch.WordTrace]
  refine ⟨231540829914269611922332697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154360553276179741281555131 231540829914269611922332697)
  ·
    refine ⟨173655622435702208941749523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231540829914269611922332697 173655622435702208941749523)
    ·
      refine ⟨260483433653553313412624285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173655622435702208941749523 260483433653553313412624285)
      ·
        refine ⟨97681287620082492529734107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260483433653553313412624285 97681287620082492529734107)
        ·
          refine ⟨146521931430123738794601161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97681287620082492529734107 146521931430123738794601161)
          ·
            refine ⟨109891448572592804095950871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146521931430123738794601161 109891448572592804095950871)
            ·
              refine ⟨164837172858889206143926307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109891448572592804095950871 164837172858889206143926307)
              ·
                refine ⟨247255759288333809215889461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164837172858889206143926307 247255759288333809215889461)
                ·
                  refine ⟨23180227433281294613989637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247255759288333809215889461 23180227433281294613989637)
                  ·
                    refine ⟨4346292643740242740123057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23180227433281294613989637 4346292643740242740123057)
                    ·
                      refine ⟨3259719482805182055092293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346292643740242740123057 3259719482805182055092293)
                      ·
                        rfl

theorem cell23_6348281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_6348281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348281 prefixEnd_6348281 := by exact prefixLift 6348281
  have htrace : WordTrace (prefixWord ++ tailWord_6348281) baseStart_6348281 baseEnd_6348281 := by
    simpa [prefixWord, tailWord_6348281, baseEnd_6348281] using wordTrace_append hprefix tailTrace_6348281
  have hstable : (prefixWord ++ tailWord_6348281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348281).length < 2 ^ (prefixWord ++ tailWord_6348281).sum := by decide
  have hdescent : baseEnd_6348281 < baseStart_6348281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348284 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6348284 : Nat := 118140960795 + 6348284 * 2 ^ 59
def prefixEnd_6348284 : Nat := 4983230072969 + 3 ^ 40 * 6348284 * 2
def baseEnd_6348284 : Nat := 3259721023247145543354779

theorem tailTrace_6348284 : CollatzResearch.WordTrace tailWord_6348284 prefixEnd_6348284 3259721023247145543354779 := by
  unfold tailWord_6348284
  simp only [CollatzResearch.WordTrace]
  refine ⟨115770469666629371717345953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154360626222172495623127937 115770469666629371717345953)
  ·
    refine ⟨86827852249972028788009465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115770469666629371717345953 86827852249972028788009465)
    ·
      refine ⟨65120889187479021591007099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86827852249972028788009465 65120889187479021591007099)
      ·
        refine ⟨97681333781218532386510649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65120889187479021591007099 97681333781218532386510649)
        ·
          refine ⟨73261000335913899289882987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97681333781218532386510649 73261000335913899289882987)
          ·
            refine ⟨109891500503870848934824481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73261000335913899289882987 109891500503870848934824481)
            ·
              refine ⟨82418625377903136701118361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109891500503870848934824481 82418625377903136701118361)
              ·
                refine ⟨61813969033427352525838771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82418625377903136701118361 61813969033427352525838771)
                ·
                  refine ⟨92720953550141028788758157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61813969033427352525838771 92720953550141028788758157)
                  ·
                    refine ⟨34770357581302885795784309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92720953550141028788758157 34770357581302885795784309)
                    ·
                      refine ⟨3259721023247145543354779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34770357581302885795784309 3259721023247145543354779)
                      ·
                        rfl

theorem cell23_6348284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6348284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348284 prefixEnd_6348284 := by exact prefixLift 6348284
  have htrace : WordTrace (prefixWord ++ tailWord_6348284) baseStart_6348284 baseEnd_6348284 := by
    simpa [prefixWord, tailWord_6348284, baseEnd_6348284] using wordTrace_append hprefix tailTrace_6348284
  have hstable : (prefixWord ++ tailWord_6348284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348284).length < 2 ^ (prefixWord ++ tailWord_6348284).sum := by decide
  have hdescent : baseEnd_6348284 < baseStart_6348284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348298 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_6348298 : Nat := 118140960795 + 6348298 * 2 ^ 59
def prefixEnd_6348298 : Nat := 4983230072969 + 3 ^ 40 * 6348298 * 2
def baseEnd_6348298 : Nat := 3259728211976308488579715

theorem tailTrace_6348298 : CollatzResearch.WordTrace tailWord_6348298 prefixEnd_6348298 3259728211976308488579715 := by
  unfold tailWord_6348298
  simp only [CollatzResearch.WordTrace]
  refine ⟨57885362488802005956425387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154360966636805349217134365 57885362488802005956425387)
  ·
    refine ⟨86828043733203008934638081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57885362488802005956425387 86828043733203008934638081)
    ·
      refine ⟨65121032799902256700978561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86828043733203008934638081 65121032799902256700978561)
      ·
        refine ⟨48840774599926692525733921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65121032799902256700978561 48840774599926692525733921)
        ·
          refine ⟨36630580949945019394300441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48840774599926692525733921 36630580949945019394300441)
          ·
            refine ⟨27472935712458764545725331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36630580949945019394300441 27472935712458764545725331)
            ·
              refine ⟨41209403568688146818587997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27472935712458764545725331 41209403568688146818587997)
              ·
                refine ⟨15453526338258055056970499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41209403568688146818587997 15453526338258055056970499)
                ·
                  refine ⟨23180289507387082585455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15453526338258055056970499 23180289507387082585455749)
                  ·
                    refine ⟨4346304282635077984772953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23180289507387082585455749 4346304282635077984772953)
                    ·
                      refine ⟨3259728211976308488579715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346304282635077984772953 3259728211976308488579715)
                      ·
                        rfl

theorem cell23_6348298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_6348298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348298 prefixEnd_6348298 := by exact prefixLift 6348298
  have htrace : WordTrace (prefixWord ++ tailWord_6348298) baseStart_6348298 baseEnd_6348298 := by
    simpa [prefixWord, tailWord_6348298, baseEnd_6348298] using wordTrace_append hprefix tailTrace_6348298
  have hstable : (prefixWord ++ tailWord_6348298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348298).length < 2 ^ (prefixWord ++ tailWord_6348298).sum := by decide
  have hdescent : baseEnd_6348298 < baseStart_6348298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348314 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_6348314 : Nat := 118140960795 + 6348314 * 2 ^ 59
def prefixEnd_6348314 : Nat := 4983230072969 + 3 ^ 40 * 6348314 * 2
def baseEnd_6348314 : Nat := 3259736427666780425979641

theorem tailTrace_6348314 : CollatzResearch.WordTrace tailWord_6348314 prefixEnd_6348314 3259736427666780425979641 := by
  unfold tailWord_6348314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57885508380787514639570999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154361355682100039038855997 57885508380787514639570999)
  ·
    refine ⟨86828262571181271959356499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57885508380787514639570999 86828262571181271959356499)
    ·
      refine ⟨130242393856771907939034749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86828262571181271959356499 130242393856771907939034749)
      ·
        refine ⟨48840897696289465477138031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130242393856771907939034749 48840897696289465477138031)
        ·
          refine ⟨73261346544434198215707047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48840897696289465477138031 73261346544434198215707047)
          ·
            refine ⟨109892019816651297323560571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73261346544434198215707047 109892019816651297323560571)
            ·
              refine ⟨164838029724976945985340857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109892019816651297323560571 164838029724976945985340857)
              ·
                refine ⟨123628522293732709489005643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164838029724976945985340857 123628522293732709489005643)
                ·
                  refine ⟨185442783440599064233508465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123628522293732709489005643 185442783440599064233508465)
                  ·
                    refine ⟨139082087580449298175131349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185442783440599064233508465 139082087580449298175131349)
                    ·
                      refine ⟨3259736427666780425979641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139082087580449298175131349 3259736427666780425979641)
                      ·
                        rfl

theorem cell23_6348314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_6348314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348314 prefixEnd_6348314 := by exact prefixLift 6348314
  have htrace : WordTrace (prefixWord ++ tailWord_6348314) baseStart_6348314 baseEnd_6348314 := by
    simpa [prefixWord, tailWord_6348314, baseEnd_6348314] using wordTrace_append hprefix tailTrace_6348314
  have hstable : (prefixWord ++ tailWord_6348314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348314).length < 2 ^ (prefixWord ++ tailWord_6348314).sum := by decide
  have hdescent : baseEnd_6348314 < baseStart_6348314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348349 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6348349 : Nat := 118140960795 + 6348349 * 2 ^ 59
def prefixEnd_6348349 : Nat := 4983230072969 + 3 ^ 40 * 6348349 * 2
def baseEnd_6348349 : Nat := 3259754399489687789041981

theorem tailTrace_6348349 : CollatzResearch.WordTrace tailWord_6348349 prefixEnd_6348349 3259754399489687789041981 := by
  unfold tailWord_6348349
  simp only [CollatzResearch.WordTrace]
  refine ⟨231543310078023259535808101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154362206718682173023872067 231543310078023259535808101)
  ·
    refine ⟨43414370639629361162964019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231543310078023259535808101 43414370639629361162964019)
    ·
      refine ⟨65121555959444041744446029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43414370639629361162964019 65121555959444041744446029)
      ·
        refine ⟨24420583484791515654167261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65121555959444041744446029 24420583484791515654167261)
        ·
          refine ⟨9157718806796818370312723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24420583484791515654167261 9157718806796818370312723)
          ·
            refine ⟨13736578210195227555469085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157718806796818370312723 13736578210195227555469085)
            ·
              refine ⟨5151216828823210333300907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13736578210195227555469085 5151216828823210333300907)
              ·
                refine ⟨7726825243234815499951361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151216828823210333300907 7726825243234815499951361)
                ·
                  refine ⟨5795118932426111624963521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726825243234815499951361 5795118932426111624963521)
                  ·
                    refine ⟨4346339199319583718722641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795118932426111624963521 4346339199319583718722641)
                    ·
                      refine ⟨3259754399489687789041981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346339199319583718722641 3259754399489687789041981)
                      ·
                        rfl

theorem cell23_6348349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6348349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348349 prefixEnd_6348349 := by exact prefixLift 6348349
  have htrace : WordTrace (prefixWord ++ tailWord_6348349) baseStart_6348349 baseEnd_6348349 := by
    simpa [prefixWord, tailWord_6348349, baseEnd_6348349] using wordTrace_append hprefix tailTrace_6348349
  have hstable : (prefixWord ++ tailWord_6348349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348349).length < 2 ^ (prefixWord ++ tailWord_6348349).sum := by decide
  have hdescent : baseEnd_6348349 < baseStart_6348349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348388 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_6348388 : Nat := 118140960795 + 6348388 * 2 ^ 59
def prefixEnd_6348388 : Nat := 4983230072969 + 3 ^ 40 * 6348388 * 2
def baseEnd_6348388 : Nat := 3259774425235213136454301

theorem tailTrace_6348388 : CollatzResearch.WordTrace tailWord_6348388 prefixEnd_6348388 3259774425235213136454301 := by
  unfold tailWord_6348388
  simp only [CollatzResearch.WordTrace]
  refine ⟨115772366262440984598238909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154363155016587979464318545 115772366262440984598238909)
  ·
    refine ⟨43414637348415369224339591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115772366262440984598238909 43414637348415369224339591)
    ·
      refine ⟨65121956022623053836509387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43414637348415369224339591 65121956022623053836509387)
      ·
        refine ⟨97682934033934580754764081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65121956022623053836509387 97682934033934580754764081)
        ·
          refine ⟨73262200525450935566073061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97682934033934580754764081 73262200525450935566073061)
          ·
            refine ⟨13736662598522050418638699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73262200525450935566073061 13736662598522050418638699)
            ·
              refine ⟨20604993897783075627958049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736662598522050418638699 20604993897783075627958049)
              ·
                refine ⟨15453745423337306720968537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20604993897783075627958049 15453745423337306720968537)
                ·
                  refine ⟨11590309067502980040726403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15453745423337306720968537 11590309067502980040726403)
                  ·
                    refine ⟨17385463601254470061089605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11590309067502980040726403 17385463601254470061089605)
                    ·
                      refine ⟨3259774425235213136454301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17385463601254470061089605 3259774425235213136454301)
                      ·
                        rfl

theorem cell23_6348388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_6348388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348388 prefixEnd_6348388 := by exact prefixLift 6348388
  have htrace : WordTrace (prefixWord ++ tailWord_6348388) baseStart_6348388 baseEnd_6348388 := by
    simpa [prefixWord, tailWord_6348388, baseEnd_6348388] using wordTrace_append hprefix tailTrace_6348388
  have hstable : (prefixWord ++ tailWord_6348388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348388).length < 2 ^ (prefixWord ++ tailWord_6348388).sum := by decide
  have hdescent : baseEnd_6348388 < baseStart_6348388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348411 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 6]
def baseStart_6348411 : Nat := 118140960795 + 6348411 * 2 ^ 59
def prefixEnd_6348411 : Nat := 4983230072969 + 3 ^ 40 * 6348411 * 2
def baseEnd_6348411 : Nat := 362198470587807394051855

theorem tailTrace_6348411 : CollatzResearch.WordTrace tailWord_6348411 prefixEnd_6348411 362198470587807394051855 := by
  unfold tailWord_6348411
  simp only [CollatzResearch.WordTrace]
  refine ⟨231545571403798644124565087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154363714269199096083043391 231545571403798644124565087)
  ·
    refine ⟨347318357105697966186847631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231545571403798644124565087 347318357105697966186847631)
    ·
      refine ⟨520977535658546949280271447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347318357105697966186847631 520977535658546949280271447)
      ·
        refine ⟨781466303487820423920407171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520977535658546949280271447 781466303487820423920407171)
        ·
          refine ⟨1172199455231730635880610757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781466303487820423920407171 1172199455231730635880610757)
          ·
            refine ⟨219787397855949494227614517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1172199455231730635880610757 219787397855949494227614517)
            ·
              refine ⟨20605068548995265083838861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219787397855949494227614517 20605068548995265083838861)
              ·
                refine ⟨7726900705873224406439573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20605068548995265083838861 7726900705873224406439573)
                ·
                  refine ⟨362198470587807394051855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7726900705873224406439573 362198470587807394051855)
                  ·
                    rfl

theorem cell23_6348411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 6].length) (baseStart_6348411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348411 prefixEnd_6348411 := by exact prefixLift 6348411
  have htrace : WordTrace (prefixWord ++ tailWord_6348411) baseStart_6348411 baseEnd_6348411 := by
    simpa [prefixWord, tailWord_6348411, baseEnd_6348411] using wordTrace_append hprefix tailTrace_6348411
  have hstable : (prefixWord ++ tailWord_6348411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348411).length < 2 ^ (prefixWord ++ tailWord_6348411).sum := by decide
  have hdescent : baseEnd_6348411 < baseStart_6348411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348449 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 1, 4]
def baseStart_6348449 : Nat := 118140960795 + 6348449 * 2 ^ 59
def prefixEnd_6348449 : Nat := 4983230072969 + 3 ^ 40 * 6348449 * 2
def baseEnd_6348449 : Nat := 1086601915851712465930507

theorem tailTrace_6348449 : CollatzResearch.WordTrace tailWord_6348449 prefixEnd_6348449 1086601915851712465930507 := by
  unfold tailWord_6348449
  simp only [CollatzResearch.WordTrace]
  refine ⟨231546957377660976614448401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154364638251773984409632267 231546957377660976614448401)
  ·
    refine ⟨173660218033245732460836301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231546957377660976614448401 173660218033245732460836301)
    ·
      refine ⟨65122581762467149672813613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173660218033245732460836301 65122581762467149672813613)
      ·
        refine ⟨24420968160925181127305105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65122581762467149672813613 24420968160925181127305105)
        ·
          refine ⟨18315726120693885845478829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24420968160925181127305105 18315726120693885845478829)
          ·
            refine ⟨6868397295260207192054561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18315726120693885845478829 6868397295260207192054561)
            ·
              refine ⟨5151297971445155394040921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868397295260207192054561 5151297971445155394040921)
              ·
                refine ⟨3863473478583866545530691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151297971445155394040921 3863473478583866545530691)
                ·
                  refine ⟨5795210217875799818296037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863473478583866545530691 5795210217875799818296037)
                  ·
                    refine ⟨1086601915851712465930507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5795210217875799818296037 1086601915851712465930507)
                    ·
                      rfl

theorem cell23_6348449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_6348449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348449 prefixEnd_6348449 := by exact prefixLift 6348449
  have htrace : WordTrace (prefixWord ++ tailWord_6348449) baseStart_6348449 baseEnd_6348449 := by
    simpa [prefixWord, tailWord_6348449, baseEnd_6348449] using wordTrace_append hprefix tailTrace_6348449
  have hstable : (prefixWord ++ tailWord_6348449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348449).length < 2 ^ (prefixWord ++ tailWord_6348449).sum := by decide
  have hdescent : baseEnd_6348449 < baseStart_6348449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348488 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_6348488 : Nat := 118140960795 + 6348488 * 2 ^ 59
def prefixEnd_6348488 : Nat := 4983230072969 + 3 ^ 40 * 6348488 * 2
def baseEnd_6348488 : Nat := 1086608591100220915067947

theorem tailTrace_6348488 : CollatzResearch.WordTrace tailWord_6348488 prefixEnd_6348488 1086608591100220915067947 := by
  unfold tailWord_6348488
  simp only [CollatzResearch.WordTrace]
  refine ⟨115774189912259843137559059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154365586549679790850078745 115774189912259843137559059)
  ·
    refine ⟨173661284868389764706338589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115774189912259843137559059 173661284868389764706338589)
    ·
      refine ⟨65122981825646161764876971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173661284868389764706338589 65122981825646161764876971)
      ·
        refine ⟨97684472738469242647315457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65122981825646161764876971 97684472738469242647315457)
        ·
          refine ⟨73263354553851931985486593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97684472738469242647315457 73263354553851931985486593)
          ·
            refine ⟨54947515915388948989114945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73263354553851931985486593 54947515915388948989114945)
            ·
              refine ⟨41210636936541711741836209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54947515915388948989114945 41210636936541711741836209)
              ·
                refine ⟨30907977702406283806377157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41210636936541711741836209 30907977702406283806377157)
                ·
                  refine ⟨5795245819201178213695717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30907977702406283806377157 5795245819201178213695717)
                  ·
                    refine ⟨1086608591100220915067947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5795245819201178213695717 1086608591100220915067947)
                    ·
                      rfl

theorem cell23_6348488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_6348488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348488 prefixEnd_6348488 := by exact prefixLift 6348488
  have htrace : WordTrace (prefixWord ++ tailWord_6348488) baseStart_6348488 baseEnd_6348488 := by
    simpa [prefixWord, tailWord_6348488, baseEnd_6348488] using wordTrace_append hprefix tailTrace_6348488
  have hstable : (prefixWord ++ tailWord_6348488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348488).length < 2 ^ (prefixWord ++ tailWord_6348488).sum := by decide
  have hdescent : baseEnd_6348488 < baseStart_6348488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348505 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 2, 4]
def baseStart_6348505 : Nat := 118140960795 + 6348505 * 2 ^ 59
def prefixEnd_6348505 : Nat := 4983230072969 + 3 ^ 40 * 6348505 * 2
def baseEnd_6348505 : Nat := 1086611500823929726230421

theorem tailTrace_6348505 : CollatzResearch.WordTrace tailWord_6348505 prefixEnd_6348505 1086611500823929726230421 := by
  unfold tailWord_6348505
  simp only [CollatzResearch.WordTrace]
  refine ⟨231548999865458098178486969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154365999910305398785657979 231548999865458098178486969)
  ·
    refine ⟨173661749899093573633865227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231548999865458098178486969 173661749899093573633865227)
    ·
      refine ⟨260492624848640360450797841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173661749899093573633865227 260492624848640360450797841)
      ·
        refine ⟨195369468636480270338098381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260492624848640360450797841 195369468636480270338098381)
        ·
          refine ⟨73263550738680101376786893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195369468636480270338098381 73263550738680101376786893)
          ·
            refine ⟨27473831527005038016295085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73263550738680101376786893 27473831527005038016295085)
            ·
              refine ⟨10302686822626889256110657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27473831527005038016295085 10302686822626889256110657)
              ·
                refine ⟨7727015116970166942082993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10302686822626889256110657 7727015116970166942082993)
                ·
                  refine ⟨5795261337727625206562245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727015116970166942082993 5795261337727625206562245)
                  ·
                    refine ⟨1086611500823929726230421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5795261337727625206562245 1086611500823929726230421)
                    ·
                      rfl

theorem cell23_6348505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_6348505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348505 prefixEnd_6348505 := by exact prefixLift 6348505
  have htrace : WordTrace (prefixWord ++ tailWord_6348505) baseStart_6348505 baseEnd_6348505 := by
    simpa [prefixWord, tailWord_6348505, baseEnd_6348505] using wordTrace_append hprefix tailTrace_6348505
  have hstable : (prefixWord ++ tailWord_6348505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348505).length < 2 ^ (prefixWord ++ tailWord_6348505).sum := by decide
  have hdescent : baseEnd_6348505 < baseStart_6348505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348515 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6348515 : Nat := 118140960795 + 6348515 * 2 ^ 59
def prefixEnd_6348515 : Nat := 4983230072969 + 3 ^ 40 * 6348515 * 2
def baseEnd_6348515 : Nat := 3259839637278334139566217

theorem tailTrace_6348515 : CollatzResearch.WordTrace tailWord_6348515 prefixEnd_6348515 3259839637278334139566217 := by
  unfold tailWord_6348515
  simp only [CollatzResearch.WordTrace]
  refine ⟨231549364595421869886350999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154366243063614579924233999 231549364595421869886350999)
  ·
    refine ⟨347324046893132804829526499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231549364595421869886350999 347324046893132804829526499)
    ·
      refine ⟨520986070339699207244289749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347324046893132804829526499 520986070339699207244289749)
      ·
        refine ⟨12210611023586700169788041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 520986070339699207244289749 12210611023586700169788041)
        ·
          refine ⟨9157958267690025127341031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12210611023586700169788041 9157958267690025127341031)
          ·
            refine ⟨13736937401535037691011547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157958267690025127341031 13736937401535037691011547)
            ·
              refine ⟨20605406102302556536517321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736937401535037691011547 20605406102302556536517321)
              ·
                refine ⟨15454054576726917402387991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20605406102302556536517321 15454054576726917402387991)
                ·
                  refine ⟨23181081865090376103581987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454054576726917402387991 23181081865090376103581987)
                  ·
                    refine ⟨34771622797635564155372981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23181081865090376103581987 34771622797635564155372981)
                    ·
                      refine ⟨3259839637278334139566217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34771622797635564155372981 3259839637278334139566217)
                      ·
                        rfl

theorem cell23_6348515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6348515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348515 prefixEnd_6348515 := by exact prefixLift 6348515
  have htrace : WordTrace (prefixWord ++ tailWord_6348515) baseStart_6348515 baseEnd_6348515 := by
    simpa [prefixWord, tailWord_6348515, baseEnd_6348515] using wordTrace_append hprefix tailTrace_6348515
  have hstable : (prefixWord ++ tailWord_6348515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348515).length < 2 ^ (prefixWord ++ tailWord_6348515).sum := by decide
  have hdescent : baseEnd_6348515 < baseStart_6348515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348525 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6348525 : Nat := 118140960795 + 6348525 * 2 ^ 59
def prefixEnd_6348525 : Nat := 4983230072969 + 3 ^ 40 * 6348525 * 2
def baseEnd_6348525 : Nat := 3259844772084879100441171

theorem tailTrace_6348525 : CollatzResearch.WordTrace tailWord_6348525 prefixEnd_6348525 3259844772084879100441171 := by
  unfold tailWord_6348525
  simp only [CollatzResearch.WordTrace]
  refine ⟨231549729325385641594215029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154366486216923761062810019 231549729325385641594215029)
  ·
    refine ⟨21707787124254903899457659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231549729325385641594215029 21707787124254903899457659)
    ·
      refine ⟨32561680686382355849186489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21707787124254903899457659 32561680686382355849186489)
      ·
        refine ⟨24421260514786766886889867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32561680686382355849186489 24421260514786766886889867)
        ·
          refine ⟨36631890772180150330334801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24421260514786766886889867 36631890772180150330334801)
          ·
            refine ⟨27473918079135112747751101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36631890772180150330334801 27473918079135112747751101)
            ·
              refine ⟨10302719279675667280406663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27473918079135112747751101 10302719279675667280406663)
              ·
                refine ⟨15454078919513500920609995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10302719279675667280406663 15454078919513500920609995)
                ·
                  refine ⟨23181118379270251380914993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454078919513500920609995 23181118379270251380914993)
                  ·
                    refine ⟨17385838784452688535686245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23181118379270251380914993 17385838784452688535686245)
                    ·
                      refine ⟨3259844772084879100441171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17385838784452688535686245 3259844772084879100441171)
                      ·
                        rfl

theorem cell23_6348525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6348525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348525 prefixEnd_6348525 := by exact prefixLift 6348525
  have htrace : WordTrace (prefixWord ++ tailWord_6348525) baseStart_6348525 baseEnd_6348525 := by
    simpa [prefixWord, tailWord_6348525, baseEnd_6348525] using wordTrace_append hprefix tailTrace_6348525
  have hstable : (prefixWord ++ tailWord_6348525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348525).length < 2 ^ (prefixWord ++ tailWord_6348525).sum := by decide
  have hdescent : baseEnd_6348525 < baseStart_6348525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348528 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_6348528 : Nat := 118140960795 + 6348528 * 2 ^ 59
def prefixEnd_6348528 : Nat := 4983230072969 + 3 ^ 40 * 6348528 * 2
def baseEnd_6348528 : Nat := 3259846312526842588703657

theorem tailTrace_6348528 : CollatzResearch.WordTrace tailWord_6348528 prefixEnd_6348528 3259846312526842588703657 := by
  unfold tailWord_6348528
  simp only [CollatzResearch.WordTrace]
  refine ⟨115774919372187386553287119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154366559162916515404382825 115774919372187386553287119)
  ·
    refine ⟨173662379058281079829930679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115774919372187386553287119 173662379058281079829930679)
    ·
      refine ⟨260493568587421619744896019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173662379058281079829930679 260493568587421619744896019)
      ·
        refine ⟨390740352881132429617344029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260493568587421619744896019 390740352881132429617344029)
        ·
          refine ⟨146527632330424661106504011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390740352881132429617344029 146527632330424661106504011)
          ·
            refine ⟨219791448495636991659756017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146527632330424661106504011 219791448495636991659756017)
            ·
              refine ⟨164843586371727743744817013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219791448495636991659756017 164843586371727743744817013)
              ·
                refine ⟨15454086222349475976076595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164843586371727743744817013 15454086222349475976076595)
                ·
                  refine ⟨23181129333524213964114893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454086222349475976076595 23181129333524213964114893)
                  ·
                    refine ⟨8692923500071580236543085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23181129333524213964114893 8692923500071580236543085)
                    ·
                      refine ⟨3259846312526842588703657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692923500071580236543085 3259846312526842588703657)
                      ·
                        rfl

theorem cell23_6348528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_6348528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348528 prefixEnd_6348528 := by exact prefixLift 6348528
  have htrace : WordTrace (prefixWord ++ tailWord_6348528) baseStart_6348528 baseEnd_6348528 := by
    simpa [prefixWord, tailWord_6348528, baseEnd_6348528] using wordTrace_append hprefix tailTrace_6348528
  have hstable : (prefixWord ++ tailWord_6348528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348528).length < 2 ^ (prefixWord ++ tailWord_6348528).sum := by decide
  have hdescent : baseEnd_6348528 < baseStart_6348528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348531 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 7]
def baseStart_6348531 : Nat := 118140960795 + 6348531 * 2 ^ 59
def prefixEnd_6348531 : Nat := 4983230072969 + 3 ^ 40 * 6348531 * 2
def baseEnd_6348531 : Nat := 1086615950989602025655381

theorem tailTrace_6348531 : CollatzResearch.WordTrace tailWord_6348531 prefixEnd_6348531 1086615950989602025655381 := by
  unfold tailWord_6348531
  simp only [CollatzResearch.WordTrace]
  refine ⟨231549948163363904618933447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154366632108909269745955631 231549948163363904618933447)
  ·
    refine ⟨347324922245045856928400171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231549948163363904618933447 347324922245045856928400171)
    ·
      refine ⟨520987383367568785392600257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347324922245045856928400171 520987383367568785392600257)
      ·
        refine ⟨390740537525676589044450193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520987383367568785392600257 390740537525676589044450193)
        ·
          refine ⟨293055403144257441783337645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390740537525676589044450193 293055403144257441783337645)
          ·
            refine ⟨109895776179096540668751617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293055403144257441783337645 109895776179096540668751617)
            ·
              refine ⟨82421832134322405501563713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109895776179096540668751617 82421832134322405501563713)
              ·
                refine ⟨61816374100741804126172785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82421832134322405501563713 61816374100741804126172785)
                ·
                  refine ⟨46362280575556353094629589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61816374100741804126172785 46362280575556353094629589)
                  ·
                    refine ⟨1086615950989602025655381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46362280575556353094629589 1086615950989602025655381)
                    ·
                      rfl

theorem cell23_6348531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_6348531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348531 prefixEnd_6348531 := by exact prefixLift 6348531
  have htrace : WordTrace (prefixWord ++ tailWord_6348531) baseStart_6348531 baseEnd_6348531 := by
    simpa [prefixWord, tailWord_6348531, baseEnd_6348531] using wordTrace_append hprefix tailTrace_6348531
  have hstable : (prefixWord ++ tailWord_6348531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348531).length < 2 ^ (prefixWord ++ tailWord_6348531).sum := by decide
  have hdescent : baseEnd_6348531 < baseStart_6348531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348545 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_6348545 : Nat := 118140960795 + 6348545 * 2 ^ 59
def prefixEnd_6348545 : Nat := 4983230072969 + 3 ^ 40 * 6348545 * 2
def baseEnd_6348545 : Nat := 3259855041697969022191079

theorem tailTrace_6348545 : CollatzResearch.WordTrace tailWord_6348545 prefixEnd_6348545 3259855041697969022191079 := by
  unfold tailWord_6348545
  simp only [CollatzResearch.WordTrace]
  refine ⟨231550458785313185009943089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154366972523542123339962059 231550458785313185009943089)
  ·
    refine ⟨173662844088984888757457317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231550458785313185009943089 173662844088984888757457317)
    ·
      refine ⟨32561783266684666642023247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173662844088984888757457317 32561783266684666642023247)
      ·
        refine ⟨48842674900026999963034871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32561783266684666642023247 48842674900026999963034871)
        ·
          refine ⟨73264012350040499944552307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48842674900026999963034871 73264012350040499944552307)
          ·
            refine ⟨109896018525060749916828461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73264012350040499944552307 109896018525060749916828461)
            ·
              refine ⟨41211006946897781218810673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109896018525060749916828461 41211006946897781218810673)
              ·
                refine ⟨30908255210173335914108005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41211006946897781218810673 30908255210173335914108005)
                ·
                  refine ⟨5795297851907500483895251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30908255210173335914108005 5795297851907500483895251)
                  ·
                    refine ⟨8692946777861250725842877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795297851907500483895251 8692946777861250725842877)
                    ·
                      refine ⟨3259855041697969022191079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692946777861250725842877 3259855041697969022191079)
                      ·
                        rfl

theorem cell23_6348545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_6348545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348545 prefixEnd_6348545 := by exact prefixLift 6348545
  have htrace : WordTrace (prefixWord ++ tailWord_6348545) baseStart_6348545 baseEnd_6348545 := by
    simpa [prefixWord, tailWord_6348545, baseEnd_6348545] using wordTrace_append hprefix tailTrace_6348545
  have hstable : (prefixWord ++ tailWord_6348545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348545).length < 2 ^ (prefixWord ++ tailWord_6348545).sum := by decide
  have hdescent : baseEnd_6348545 < baseStart_6348545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348550 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6348550 : Nat := 118140960795 + 6348550 * 2 ^ 59
def prefixEnd_6348550 : Nat := 4983230072969 + 3 ^ 40 * 6348550 * 2
def baseEnd_6348550 : Nat := 3259857609101241502628557

theorem tailTrace_6348550 : CollatzResearch.WordTrace tailWord_6348550 prefixEnd_6348550 3259857609101241502628557 := by
  unfold tailWord_6348550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235957535946720964496097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154367094100196713909250069 7235957535946720964496097)
  ·
    refine ⟨5426968151960040723372073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7235957535946720964496097 5426968151960040723372073)
    ·
      refine ⟨4070226113970030542529055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426968151960040723372073 4070226113970030542529055)
      ·
        refine ⟨6105339170955045813793583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070226113970030542529055 6105339170955045813793583)
        ·
          refine ⟨9158008756432568720690375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105339170955045813793583 9158008756432568720690375)
          ·
            refine ⟨13737013134648853081035563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158008756432568720690375 13737013134648853081035563)
            ·
              refine ⟨20605519701973279621553345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737013134648853081035563 20605519701973279621553345)
              ·
                refine ⟨15454139776479959716165009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20605519701973279621553345 15454139776479959716165009)
                ·
                  refine ⟨11590604832359969787123757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15454139776479959716165009 11590604832359969787123757)
                  ·
                    refine ⟨4346476812134988670171409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11590604832359969787123757 4346476812134988670171409)
                    ·
                      refine ⟨3259857609101241502628557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346476812134988670171409 3259857609101241502628557)
                      ·
                        rfl

theorem cell23_6348550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6348550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348550 prefixEnd_6348550 := by exact prefixLift 6348550
  have htrace : WordTrace (prefixWord ++ tailWord_6348550) baseStart_6348550 baseEnd_6348550 := by
    simpa [prefixWord, tailWord_6348550, baseEnd_6348550] using wordTrace_append hprefix tailTrace_6348550
  have hstable : (prefixWord ++ tailWord_6348550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348550).length < 2 ^ (prefixWord ++ tailWord_6348550).sum := by decide
  have hdescent : baseEnd_6348550 < baseStart_6348550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348557 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6348557 : Nat := 118140960795 + 6348557 * 2 ^ 59
def prefixEnd_6348557 : Nat := 4983230072969 + 3 ^ 40 * 6348557 * 2
def baseEnd_6348557 : Nat := 3259861203465822975241025

theorem tailTrace_6348557 : CollatzResearch.WordTrace tailWord_6348557 prefixEnd_6348557 3259861203465822975241025 := by
  unfold tailWord_6348557
  simp only [CollatzResearch.WordTrace]
  refine ⟨231550896461269711059379925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154367264307513140706253283 231550896461269711059379925)
  ·
    refine ⟨5426974135811008852954217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 231550896461269711059379925 5426974135811008852954217)
    ·
      refine ⟨4070230601858256639715663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426974135811008852954217 4070230601858256639715663)
      ·
        refine ⟨6105345902787384959573495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070230601858256639715663 6105345902787384959573495)
        ·
          refine ⟨9158018854181077439360243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105345902787384959573495 9158018854181077439360243)
          ·
            refine ⟨13737028281271616159040365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158018854181077439360243 13737028281271616159040365)
            ·
              refine ⟨5151385605476856059640137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13737028281271616159040365 5151385605476856059640137)
              ·
                refine ⟨3863539204107642044730103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151385605476856059640137 3863539204107642044730103)
                ·
                  refine ⟨5795308806161463067095155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863539204107642044730103 5795308806161463067095155)
                  ·
                    refine ⟨8692963209242194600642733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795308806161463067095155 8692963209242194600642733)
                    ·
                      refine ⟨3259861203465822975241025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8692963209242194600642733 3259861203465822975241025)
                      ·
                        rfl

theorem cell23_6348557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6348557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348557 prefixEnd_6348557 := by exact prefixLift 6348557
  have htrace : WordTrace (prefixWord ++ tailWord_6348557) baseStart_6348557 baseEnd_6348557 := by
    simpa [prefixWord, tailWord_6348557, baseEnd_6348557] using wordTrace_append hprefix tailTrace_6348557
  have hstable : (prefixWord ++ tailWord_6348557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348557).length < 2 ^ (prefixWord ++ tailWord_6348557).sum := by decide
  have hdescent : baseEnd_6348557 < baseStart_6348557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348578 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6348578 : Nat := 118140960795 + 6348578 * 2 ^ 59
def prefixEnd_6348578 : Nat := 4983230072969 + 3 ^ 40 * 6348578 * 2
def baseEnd_6348578 : Nat := 1086623995519855797692809

theorem tailTrace_6348578 : CollatzResearch.WordTrace tailWord_6348578 prefixEnd_6348578 1086623995519855797692809 := by
  unfold tailWord_6348578
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887915598548407911473597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154367774929462421097262925 57887915598548407911473597)
  ·
    refine ⟨21707968349455652966802599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57887915598548407911473597 21707968349455652966802599)
    ·
      refine ⟨32561952524183479450203899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21707968349455652966802599 32561952524183479450203899)
      ·
        refine ⟨48842928786275219175305849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32561952524183479450203899 48842928786275219175305849)
        ·
          refine ⟨36632196589706414381479387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48842928786275219175305849 36632196589706414381479387)
          ·
            refine ⟨54948294884559621572219081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36632196589706414381479387 54948294884559621572219081)
            ·
              refine ⟨41211221163419716179164311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54948294884559621572219081 41211221163419716179164311)
              ·
                refine ⟨61816831745129574268746467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41211221163419716179164311 61816831745129574268746467)
                ·
                  refine ⟨92725247617694361403119701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61816831745129574268746467 92725247617694361403119701)
                  ·
                    refine ⟨1086623995519855797692809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92725247617694361403119701 1086623995519855797692809)
                    ·
                      rfl

theorem cell23_6348578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6348578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348578 prefixEnd_6348578 := by exact prefixLift 6348578
  have htrace : WordTrace (prefixWord ++ tailWord_6348578) baseStart_6348578 baseEnd_6348578 := by
    simpa [prefixWord, tailWord_6348578, baseEnd_6348578] using wordTrace_append hprefix tailTrace_6348578
  have hstable : (prefixWord ++ tailWord_6348578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348578).length < 2 ^ (prefixWord ++ tailWord_6348578).sum := by decide
  have hdescent : baseEnd_6348578 < baseStart_6348578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348588 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_6348588 : Nat := 118140960795 + 6348588 * 2 ^ 59
def prefixEnd_6348588 : Nat := 4983230072969 + 3 ^ 40 * 6348588 * 2
def baseEnd_6348588 : Nat := 3259877121366112353953381

theorem tailTrace_6348588 : CollatzResearch.WordTrace tailWord_6348588 prefixEnd_6348588 3259877121366112353953381 := by
  unfold tailWord_6348588
  simp only [CollatzResearch.WordTrace]
  refine ⟨115776013562078701676879209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154368018082771602235838945 115776013562078701676879209)
  ·
    refine ⟨86832010171559026257659407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115776013562078701676879209 86832010171559026257659407)
    ·
      refine ⟨130248015257338539386489111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86832010171559026257659407 130248015257338539386489111)
      ·
        refine ⟨195372022886007809079733667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130248015257338539386489111 195372022886007809079733667)
        ·
          refine ⟨293058034329011713619600501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195372022886007809079733667 293058034329011713619600501)
          ·
            refine ⟨27474190718344848151837547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293058034329011713619600501 27474190718344848151837547)
            ·
              refine ⟨41211286077517272227756321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27474190718344848151837547 41211286077517272227756321)
              ·
                refine ⟨30908464558137954170817241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41211286077517272227756321 30908464558137954170817241)
                ·
                  refine ⟨23181348418603465628112931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30908464558137954170817241 23181348418603465628112931)
                  ·
                    refine ⟨34772022627905198442169397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23181348418603465628112931 34772022627905198442169397)
                    ·
                      refine ⟨3259877121366112353953381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34772022627905198442169397 3259877121366112353953381)
                      ·
                        rfl

theorem cell23_6348588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_6348588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348588 prefixEnd_6348588 := by exact prefixLift 6348588
  have htrace : WordTrace (prefixWord ++ tailWord_6348588) baseStart_6348588 baseEnd_6348588 := by
    simpa [prefixWord, tailWord_6348588, baseEnd_6348588] using wordTrace_append hprefix tailTrace_6348588
  have hstable : (prefixWord ++ tailWord_6348588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348588).length < 2 ^ (prefixWord ++ tailWord_6348588).sum := by decide
  have hdescent : baseEnd_6348588 < baseStart_6348588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348602 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_6348602 : Nat := 118140960795 + 6348602 * 2 ^ 59
def prefixEnd_6348602 : Nat := 4983230072969 + 3 ^ 40 * 6348602 * 2
def baseEnd_6348602 : Nat := 3259884310095275299178317

theorem tailTrace_6348602 : CollatzResearch.WordTrace tailWord_6348602 prefixEnd_6348602 3259884310095275299178317 := by
  unfold tailWord_6348602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57888134436526670936192015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154368358497404455829845373 57888134436526670936192015)
  ·
    refine ⟨86832201654790006404288023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57888134436526670936192015 86832201654790006404288023)
    ·
      refine ⟨130248302482185009606432035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86832201654790006404288023 130248302482185009606432035)
      ·
        refine ⟨195372453723277514409648053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130248302482185009606432035 195372453723277514409648053)
        ·
          refine ⟨18316167536557266975904505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195372453723277514409648053 18316167536557266975904505)
          ·
            refine ⟨13737125652417950231928379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18316167536557266975904505 13737125652417950231928379)
            ·
              refine ⟨20605688478626925347892569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737125652417950231928379 20605688478626925347892569)
              ·
                refine ⟨15454266358970194010919427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20605688478626925347892569 15454266358970194010919427)
                ·
                  refine ⟨23181399538455291016379141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454266358970194010919427 23181399538455291016379141)
                  ·
                    refine ⟨4346512413460367065571089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23181399538455291016379141 4346512413460367065571089)
                    ·
                      refine ⟨3259884310095275299178317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346512413460367065571089 3259884310095275299178317)
                      ·
                        rfl

theorem cell23_6348602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_6348602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348602 prefixEnd_6348602 := by exact prefixLift 6348602
  have htrace : WordTrace (prefixWord ++ tailWord_6348602) baseStart_6348602 baseEnd_6348602 := by
    simpa [prefixWord, tailWord_6348602, baseEnd_6348602] using wordTrace_append hprefix tailTrace_6348602
  have hstable : (prefixWord ++ tailWord_6348602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348602).length < 2 ^ (prefixWord ++ tailWord_6348602).sum := by decide
  have hdescent : baseEnd_6348602 < baseStart_6348602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348605 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6348605 : Nat := 118140960795 + 6348605 * 2 ^ 59
def prefixEnd_6348605 : Nat := 4983230072969 + 3 ^ 40 * 6348605 * 2
def baseEnd_6348605 : Nat := 3259885850537238787440803

theorem tailTrace_6348605 : CollatzResearch.WordTrace tailWord_6348605 prefixEnd_6348605 3259885850537238787440803 := by
  unfold tailWord_6348605
  simp only [CollatzResearch.WordTrace]
  refine ⟨231552647165095815257127269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154368431443397210171418179 231552647165095815257127269)
  ·
    refine ⟨43416121343455465360711363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231552647165095815257127269 43416121343455465360711363)
    ·
      refine ⟨65124182015183198041067045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43416121343455465360711363 65124182015183198041067045)
      ·
        refine ⟨12210784127846849632700071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65124182015183198041067045 12210784127846849632700071)
        ·
          refine ⟨18316176191770274449050107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12210784127846849632700071 18316176191770274449050107)
          ·
            refine ⟨27474264287655411673575161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18316176191770274449050107 27474264287655411673575161)
            ·
              refine ⟨20605698215741558755181371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27474264287655411673575161 20605698215741558755181371)
              ·
                refine ⟨30908547323612338132772057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20605698215741558755181371 30908547323612338132772057)
                ·
                  refine ⟨23181410492709253599579043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30908547323612338132772057 23181410492709253599579043)
                  ·
                    refine ⟨34772115739063880399368565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23181410492709253599579043 34772115739063880399368565)
                    ·
                      refine ⟨3259885850537238787440803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34772115739063880399368565 3259885850537238787440803)
                      ·
                        rfl

theorem cell23_6348605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6348605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348605 prefixEnd_6348605 := by exact prefixLift 6348605
  have htrace : WordTrace (prefixWord ++ tailWord_6348605) baseStart_6348605 baseEnd_6348605 := by
    simpa [prefixWord, tailWord_6348605, baseEnd_6348605] using wordTrace_append hprefix tailTrace_6348605
  have hstable : (prefixWord ++ tailWord_6348605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348605).length < 2 ^ (prefixWord ++ tailWord_6348605).sum := by decide
  have hdescent : baseEnd_6348605 < baseStart_6348605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348606 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_6348606 : Nat := 118140960795 + 6348606 * 2 ^ 59
def prefixEnd_6348606 : Nat := 4983230072969 + 3 ^ 40 * 6348606 * 2
def baseEnd_6348606 : Nat := 3259886364017893283528299

theorem tailTrace_6348606 : CollatzResearch.WordTrace tailWord_6348606 prefixEnd_6348606 3259886364017893283528299 := by
  unfold tailWord_6348606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28944085454761524053489209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154368455758728128285275781 28944085454761524053489209)
  ·
    refine ⟨21708064091071143040116907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28944085454761524053489209 21708064091071143040116907)
    ·
      refine ⟨32562096136606714560175361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21708064091071143040116907 32562096136606714560175361)
      ·
        refine ⟨24421572102455035920131521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32562096136606714560175361 24421572102455035920131521)
        ·
          refine ⟨18316179076841276940098641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24421572102455035920131521 18316179076841276940098641)
          ·
            refine ⟨13737134307630957705073981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18316179076841276940098641 13737134307630957705073981)
            ·
              refine ⟨5151425365361609139402743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13737134307630957705073981 5151425365361609139402743)
              ·
                refine ⟨7727138048042413709104115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151425365361609139402743 7727138048042413709104115)
                ·
                  refine ⟨11590707072063620563656173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7727138048042413709104115 11590707072063620563656173)
                  ·
                    refine ⟨4346515152023857711371065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11590707072063620563656173 4346515152023857711371065)
                    ·
                      refine ⟨3259886364017893283528299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346515152023857711371065 3259886364017893283528299)
                      ·
                        rfl

theorem cell23_6348606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_6348606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348606 prefixEnd_6348606 := by exact prefixLift 6348606
  have htrace : WordTrace (prefixWord ++ tailWord_6348606) baseStart_6348606 baseEnd_6348606 := by
    simpa [prefixWord, tailWord_6348606, baseEnd_6348606] using wordTrace_append hprefix tailTrace_6348606
  have hstable : (prefixWord ++ tailWord_6348606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348606).length < 2 ^ (prefixWord ++ tailWord_6348606).sum := by decide
  have hdescent : baseEnd_6348606 < baseStart_6348606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348645 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 5, 2]
def baseStart_6348645 : Nat := 118140960795 + 6348645 * 2 ^ 59
def prefixEnd_6348645 : Nat := 4983230072969 + 3 ^ 40 * 6348645 * 2
def baseEnd_6348645 : Nat := 3259906389763418630940619

theorem tailTrace_6348645 : CollatzResearch.WordTrace tailWord_6348645 prefixEnd_6348645 3259906389763418630940619 := by
  unfold tailWord_6348645
  simp only [CollatzResearch.WordTrace]
  refine ⟨231554106084950902088583389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154369404056633934725722259 231554106084950902088583389)
  ·
    refine ⟨86832789781856588283218771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231554106084950902088583389 86832789781856588283218771)
    ·
      refine ⟨130249184672784882424828157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86832789781856588283218771 130249184672784882424828157)
      ·
        refine ⟨48843444252294330909310559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130249184672784882424828157 48843444252294330909310559)
        ·
          refine ⟨73265166378441496363965839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48843444252294330909310559 73265166378441496363965839)
          ·
            refine ⟨109897749567662244545948759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73265166378441496363965839 109897749567662244545948759)
            ·
              refine ⟨164846624351493366818923139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109897749567662244545948759 164846624351493366818923139)
              ·
                refine ⟨247269936527240050228384709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164846624351493366818923139 247269936527240050228384709)
                ·
                  refine ⟨46363113098857509417822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247269936527240050228384709 46363113098857509417822133)
                  ·
                    refine ⟨4346541853017891507920825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46363113098857509417822133 4346541853017891507920825)
                    ·
                      refine ⟨3259906389763418630940619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346541853017891507920825 3259906389763418630940619)
                      ·
                        rfl

theorem cell23_6348645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_6348645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348645 prefixEnd_6348645 := by exact prefixLift 6348645
  have htrace : WordTrace (prefixWord ++ tailWord_6348645) baseStart_6348645 baseEnd_6348645 := by
    simpa [prefixWord, tailWord_6348645, baseEnd_6348645] using wordTrace_append hprefix tailTrace_6348645
  have hstable : (prefixWord ++ tailWord_6348645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348645).length < 2 ^ (prefixWord ++ tailWord_6348645).sum := by decide
  have hdescent : baseEnd_6348645 < baseStart_6348645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348688 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_6348688 : Nat := 118140960795 + 6348688 * 2 ^ 59
def prefixEnd_6348688 : Nat := 4983230072969 + 3 ^ 40 * 6348688 * 2
def baseEnd_6348688 : Nat := 3259928469431561962702921

theorem tailTrace_6348688 : CollatzResearch.WordTrace tailWord_6348688 prefixEnd_6348688 3259928469431561962702921 := by
  unfold tailWord_6348688
  simp only [CollatzResearch.WordTrace]
  refine ⟨115777837211897560216199359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154370449615863413621599145 115777837211897560216199359)
  ·
    refine ⟨173666755817846340324299039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115777837211897560216199359 173666755817846340324299039)
    ·
      refine ⟨260500133726769510486448559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173666755817846340324299039 260500133726769510486448559)
      ·
        refine ⟨390750200590154265729672839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260500133726769510486448559 390750200590154265729672839)
        ·
          refine ⟨586125300885231398594509259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390750200590154265729672839 586125300885231398594509259)
          ·
            refine ⟨879187951327847097891763889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586125300885231398594509259 879187951327847097891763889)
            ·
              refine ⟨659390963495885323418822917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879187951327847097891763889 659390963495885323418822917)
              ·
                refine ⟨123635805655478498141029297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659390963495885323418822917 123635805655478498141029297)
                ·
                  refine ⟨92726854241608873605771973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123635805655478498141029297 92726854241608873605771973)
                  ·
                    refine ⟨17386285170301663801082245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92726854241608873605771973 17386285170301663801082245)
                    ·
                      refine ⟨3259928469431561962702921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17386285170301663801082245 3259928469431561962702921)
                      ·
                        rfl

theorem cell23_6348688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_6348688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348688 prefixEnd_6348688 := by exact prefixLift 6348688
  have htrace : WordTrace (prefixWord ++ tailWord_6348688) baseStart_6348688 baseEnd_6348688 := by
    simpa [prefixWord, tailWord_6348688, baseEnd_6348688] using wordTrace_append hprefix tailTrace_6348688
  have hstable : (prefixWord ++ tailWord_6348688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348688).length < 2 ^ (prefixWord ++ tailWord_6348688).sum := by decide
  have hdescent : baseEnd_6348688 < baseStart_6348688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348695 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3]
def baseStart_6348695 : Nat := 118140960795 + 6348695 * 2 ^ 59
def prefixEnd_6348695 : Nat := 4983230072969 + 3 ^ 40 * 6348695 * 2
def baseEnd_6348695 : Nat := 3259932063796143435315389

theorem tailTrace_6348695 : CollatzResearch.WordTrace tailWord_6348695 prefixEnd_6348695 3259932063796143435315389 := by
  unfold tailWord_6348695
  simp only [CollatzResearch.WordTrace]
  refine ⟨231555929734769760627903539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154370619823179840418602359 231555929734769760627903539)
  ·
    refine ⟨347333894602154640941855309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231555929734769760627903539 347333894602154640941855309)
    ·
      refine ⟨130250210475807990353195741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347333894602154640941855309 130250210475807990353195741)
      ·
        refine ⟨48843828928427996382448403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130250210475807990353195741 48843828928427996382448403)
        ·
          refine ⟨73265743392641994573672605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48843828928427996382448403 73265743392641994573672605)
          ·
            refine ⟨27474653772240747965127227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73265743392641994573672605 27474653772240747965127227)
            ·
              refine ⟨41211980658361121947690841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27474653772240747965127227 41211980658361121947690841)
              ·
                refine ⟨30908985493770841460768131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41211980658361121947690841 30908985493770841460768131)
                ·
                  refine ⟨46363478240656262191152197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30908985493770841460768131 46363478240656262191152197)
                  ·
                    refine ⟨8693152170123049160841037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46363478240656262191152197 8693152170123049160841037)
                    ·
                      refine ⟨3259932063796143435315389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693152170123049160841037 3259932063796143435315389)
                      ·
                        rfl

theorem cell23_6348695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_6348695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348695 prefixEnd_6348695 := by exact prefixLift 6348695
  have htrace : WordTrace (prefixWord ++ tailWord_6348695) baseStart_6348695 baseEnd_6348695 := by
    simpa [prefixWord, tailWord_6348695, baseEnd_6348695] using wordTrace_append hprefix tailTrace_6348695
  have hstable : (prefixWord ++ tailWord_6348695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348695).length < 2 ^ (prefixWord ++ tailWord_6348695).sum := by decide
  have hdescent : baseEnd_6348695 < baseStart_6348695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348762 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_6348762 : Nat := 118140960795 + 6348762 * 2 ^ 59
def prefixEnd_6348762 : Nat := 4983230072969 + 3 ^ 40 * 6348762 * 2
def baseEnd_6348762 : Nat := 1086655488999998224392527

theorem tailTrace_6348762 : CollatzResearch.WordTrace tailWord_6348762 prefixEnd_6348762 1086655488999998224392527 := by
  unfold tailWord_6348762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57889593356381757767648135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154372248950351354047061693 57889593356381757767648135)
  ·
    refine ⟨86834390034572636651472203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57889593356381757767648135 86834390034572636651472203)
    ·
      refine ⟨130251585051858954977208305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86834390034572636651472203 130251585051858954977208305)
      ·
        refine ⟨97688688788894216232906229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130251585051858954977208305 97688688788894216232906229)
        ·
          refine ⟨9158314573958832771834959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97688688788894216232906229 9158314573958832771834959)
          ·
            refine ⟨13737471860938249157752439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158314573958832771834959 13737471860938249157752439)
            ·
              refine ⟨20606207791407373736628659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737471860938249157752439 20606207791407373736628659)
              ·
                refine ⟨30909311687111060604942989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20606207791407373736628659 30909311687111060604942989)
                ·
                  refine ⟨11590991882666647726853621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30909311687111060604942989 11590991882666647726853621)
                  ·
                    refine ⟨1086655488999998224392527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11590991882666647726853621 1086655488999998224392527)
                    ·
                      rfl

theorem cell23_6348762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_6348762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348762 prefixEnd_6348762 := by exact prefixLift 6348762
  have htrace : WordTrace (prefixWord ++ tailWord_6348762) baseStart_6348762 baseEnd_6348762 := by
    simpa [prefixWord, tailWord_6348762, baseEnd_6348762] using wordTrace_append hprefix tailTrace_6348762
  have hstable : (prefixWord ++ tailWord_6348762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348762).length < 2 ^ (prefixWord ++ tailWord_6348762).sum := by decide
  have hdescent : baseEnd_6348762 < baseStart_6348762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348792 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_6348792 : Nat := 118140960795 + 6348792 * 2 ^ 59
def prefixEnd_6348792 : Nat := 4983230072969 + 3 ^ 40 * 6348792 * 2
def baseEnd_6348792 : Nat := 1086660623806543185267481

theorem tailTrace_6348792 : CollatzResearch.WordTrace tailWord_6348792 prefixEnd_6348792 1086660623806543185267481 := by
  unfold tailWord_6348792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115779733807709173097092315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154372978410278897462789753 115779733807709173097092315)
  ·
    refine ⟨173669600711563759645638473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115779733807709173097092315 173669600711563759645638473)
    ·
      refine ⟨130252200533672819734228855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173669600711563759645638473 130252200533672819734228855)
      ·
        refine ⟨195378300800509229601343283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130252200533672819734228855 195378300800509229601343283)
        ·
          refine ⟨293067451200763844402014925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195378300800509229601343283 293067451200763844402014925)
          ·
            refine ⟨109900294200286441650755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293067451200763844402014925 109900294200286441650755597)
            ·
              refine ⟨41212610325107415619033349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109900294200286441650755597 41212610325107415619033349)
              ·
                refine ⟨7727364435957640428568753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41212610325107415619033349 7727364435957640428568753)
                ·
                  refine ⟨5795523326968230321426565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727364435957640428568753 5795523326968230321426565)
                  ·
                    refine ⟨1086660623806543185267481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5795523326968230321426565 1086660623806543185267481)
                    ·
                      rfl

theorem cell23_6348792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_6348792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348792 prefixEnd_6348792 := by exact prefixLift 6348792
  have htrace : WordTrace (prefixWord ++ tailWord_6348792) baseStart_6348792 baseEnd_6348792 := by
    simpa [prefixWord, tailWord_6348792, baseEnd_6348792] using wordTrace_append hprefix tailTrace_6348792
  have hstable : (prefixWord ++ tailWord_6348792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348792).length < 2 ^ (prefixWord ++ tailWord_6348792).sum := by decide
  have hdescent : baseEnd_6348792 < baseStart_6348792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348793 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 1, 1, 3]
def baseStart_6348793 : Nat := 118140960795 + 6348793 * 2 ^ 59
def prefixEnd_6348793 : Nat := 4983230072969 + 3 ^ 40 * 6348793 * 2
def baseEnd_6348793 : Nat := 3259982384900284051889939

theorem tailTrace_6348793 : CollatzResearch.WordTrace tailWord_6348793 prefixEnd_6348793 3259982384900284051889939 := by
  unfold tailWord_6348793
  simp only [CollatzResearch.WordTrace]
  refine ⟨231559504088414723364971033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154373002725609815576647355 231559504088414723364971033)
  ·
    refine ⟨173669628066311042523728275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231559504088414723364971033 173669628066311042523728275)
    ·
      refine ⟨260504442099466563785592413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173669628066311042523728275 260504442099466563785592413)
      ·
        refine ⟨97689165787299961419597155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260504442099466563785592413 97689165787299961419597155)
        ·
          refine ⟨146533748680949942129395733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97689165787299961419597155 146533748680949942129395733)
          ·
            refine ⟨6868769469419528537315425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146533748680949942129395733 6868769469419528537315425)
            ·
              refine ⟨5151577102064646402986569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868769469419528537315425 5151577102064646402986569)
              ·
                refine ⟨3863682826548484802239927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151577102064646402986569 3863682826548484802239927)
                ·
                  refine ⟨5795524239822727203359891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863682826548484802239927 5795524239822727203359891)
                  ·
                    refine ⟨8693286359734090805039837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795524239822727203359891 8693286359734090805039837)
                    ·
                      refine ⟨3259982384900284051889939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693286359734090805039837 3259982384900284051889939)
                      ·
                        rfl

theorem cell23_6348793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_6348793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348793 prefixEnd_6348793 := by exact prefixLift 6348793
  have htrace : WordTrace (prefixWord ++ tailWord_6348793) baseStart_6348793 baseEnd_6348793 := by
    simpa [prefixWord, tailWord_6348793, baseEnd_6348793] using wordTrace_append hprefix tailTrace_6348793
  have hstable : (prefixWord ++ tailWord_6348793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348793).length < 2 ^ (prefixWord ++ tailWord_6348793).sum := by decide
  have hdescent : baseEnd_6348793 < baseStart_6348793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348805 : List Nat := [1, 3, 1, 1, 2, 4, 3, 8]
def baseStart_6348805 : Nat := 118140960795 + 6348805 * 2 ^ 59
def prefixEnd_6348805 : Nat := 4983230072969 + 3 ^ 40 * 6348805 * 2
def baseEnd_6348805 : Nat := 120740316543264370553329

theorem tailTrace_6348805 : CollatzResearch.WordTrace tailWord_6348805 prefixEnd_6348805 120740316543264370553329 := by
  unfold tailWord_6348805
  simp only [CollatzResearch.WordTrace]
  refine ⟨231559941764371249414407869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154373294509580832942938579 231559941764371249414407869)
  ·
    refine ⟨86834978161639218530402951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231559941764371249414407869 86834978161639218530402951)
    ·
      refine ⟨130252467242458827795604427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86834978161639218530402951 130252467242458827795604427)
      ·
        refine ⟨195378700863688241693406641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130252467242458827795604427 195378700863688241693406641)
        ·
          refine ⟨146534025647766181270054981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195378700863688241693406641 146534025647766181270054981)
          ·
            refine ⟨27475129808956158988135309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146534025647766181270054981 27475129808956158988135309)
            ·
              refine ⟨10303173678358559620550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27475129808956158988135309 10303173678358559620550741)
              ·
                refine ⟨120740316543264370553329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10303173678358559620550741 120740316543264370553329)
                ·
                  rfl

theorem cell23_6348805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 8].length) (baseStart_6348805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348805 prefixEnd_6348805 := by exact prefixLift 6348805
  have htrace : WordTrace (prefixWord ++ tailWord_6348805) baseStart_6348805 baseEnd_6348805 := by
    simpa [prefixWord, tailWord_6348805, baseEnd_6348805] using wordTrace_append hprefix tailTrace_6348805
  have hstable : (prefixWord ++ tailWord_6348805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348805).length < 2 ^ (prefixWord ++ tailWord_6348805).sum := by decide
  have hdescent : baseEnd_6348805 < baseStart_6348805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348812 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6348812 : Nat := 118140960795 + 6348812 * 2 ^ 59
def prefixEnd_6348812 : Nat := 4983230072969 + 3 ^ 40 * 6348812 * 2
def baseEnd_6348812 : Nat := 3259992141032719477552351

theorem tailTrace_6348812 : CollatzResearch.WordTrace tailWord_6348812 prefixEnd_6348812 3259992141032719477552351 := by
  unfold tailWord_6348812
  simp only [CollatzResearch.WordTrace]
  refine ⟨115780098537672944804956345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154373464716897259739941793 115780098537672944804956345)
  ·
    refine ⟨86835073903254708603717259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115780098537672944804956345 86835073903254708603717259)
    ·
      refine ⟨130252610854882062905575889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86835073903254708603717259 130252610854882062905575889)
      ·
        refine ⟨97689458141161547179181917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130252610854882062905575889 97689458141161547179181917)
        ·
          refine ⟨36633546802935580192193219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97689458141161547179181917 36633546802935580192193219)
          ·
            refine ⟨54950320204403370288289829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36633546802935580192193219 54950320204403370288289829)
            ·
              refine ⟨10303185038325631929054343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54950320204403370288289829 10303185038325631929054343)
              ·
                refine ⟨15454777557488447893581515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303185038325631929054343 15454777557488447893581515)
                ·
                  refine ⟨23182166336232671840372273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15454777557488447893581515 23182166336232671840372273)
                  ·
                    refine ⟨17386624752174503880279205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23182166336232671840372273 17386624752174503880279205)
                    ·
                      refine ⟨3259992141032719477552351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17386624752174503880279205 3259992141032719477552351)
                      ·
                        rfl

theorem cell23_6348812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6348812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348812 prefixEnd_6348812 := by exact prefixLift 6348812
  have htrace : WordTrace (prefixWord ++ tailWord_6348812) baseStart_6348812 baseEnd_6348812 := by
    simpa [prefixWord, tailWord_6348812, baseEnd_6348812] using wordTrace_append hprefix tailTrace_6348812
  have hstable : (prefixWord ++ tailWord_6348812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348812).length < 2 ^ (prefixWord ++ tailWord_6348812).sum := by decide
  have hdescent : baseEnd_6348812 < baseStart_6348812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348820 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6348820 : Nat := 118140960795 + 6348820 * 2 ^ 59
def prefixEnd_6348820 : Nat := 4983230072969 + 3 ^ 40 * 6348820 * 2
def baseEnd_6348820 : Nat := 3259996248877955446252315

theorem tailTrace_6348820 : CollatzResearch.WordTrace tailWord_6348820 prefixEnd_6348820 3259996248877955446252315 := by
  unfold tailWord_6348820
  simp only [CollatzResearch.WordTrace]
  refine ⟨115780244429658453488101957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154373659239544604650802609 115780244429658453488101957)
  ·
    refine ⟨21708795830560960029019117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115780244429658453488101957 21708795830560960029019117)
    ·
      refine ⟨8140798436460360010882169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21708795830560960029019117 8140798436460360010882169)
      ·
        refine ⟨6105598827345270008161627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140798436460360010882169 6105598827345270008161627)
        ·
          refine ⟨9158398241017905012242441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105598827345270008161627 9158398241017905012242441)
          ·
            refine ⟨6868798680763428759181831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158398241017905012242441 6868798680763428759181831)
            ·
              refine ⟨10303198021145143138772747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868798680763428759181831 10303198021145143138772747)
              ·
                refine ⟨15454797031717714708159121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303198021145143138772747 15454797031717714708159121)
                ·
                  refine ⟨11591097773788286031119341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15454797031717714708159121 11591097773788286031119341)
                  ·
                    refine ⟨4346661665170607261669753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11591097773788286031119341 4346661665170607261669753)
                    ·
                      refine ⟨3259996248877955446252315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346661665170607261669753 3259996248877955446252315)
                      ·
                        rfl

theorem cell23_6348820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6348820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348820 prefixEnd_6348820 := by exact prefixLift 6348820
  have htrace : WordTrace (prefixWord ++ tailWord_6348820) baseStart_6348820 baseEnd_6348820 := by
    simpa [prefixWord, tailWord_6348820, baseEnd_6348820] using wordTrace_append hprefix tailTrace_6348820
  have hstable : (prefixWord ++ tailWord_6348820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348820).length < 2 ^ (prefixWord ++ tailWord_6348820).sum := by decide
  have hdescent : baseEnd_6348820 < baseStart_6348820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348833 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6348833 : Nat := 118140960795 + 6348833 * 2 ^ 59
def prefixEnd_6348833 : Nat := 4983230072969 + 3 ^ 40 * 6348833 * 2
def baseEnd_6348833 : Nat := 3260002924126463895389755

theorem tailTrace_6348833 : CollatzResearch.WordTrace tailWord_6348833 prefixEnd_6348833 3260002924126463895389755 := by
  unfold tailWord_6348833
  simp only [CollatzResearch.WordTrace]
  refine ⟨231560963008269810196427153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154373975338846540130951435 231560963008269810196427153)
  ·
    refine ⟨173670722256202357647320365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231560963008269810196427153 173670722256202357647320365)
    ·
      refine ⟨65126520846075884117745137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173670722256202357647320365 65126520846075884117745137)
      ·
        refine ⟨48844890634556913088308853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65126520846075884117745137 48844890634556913088308853)
        ·
          refine ⟨4579208496989710602028955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48844890634556913088308853 4579208496989710602028955)
          ·
            refine ⟨6868812745484565903043433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579208496989710602028955 6868812745484565903043433)
            ·
              refine ⟨5151609559113424427282575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868812745484565903043433 5151609559113424427282575)
              ·
                refine ⟨7727414338670136640923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151609559113424427282575 7727414338670136640923863)
                ·
                  refine ⟨11591121508005204961385795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7727414338670136640923863 11591121508005204961385795)
                  ·
                    refine ⟨17386682262007807442078693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11591121508005204961385795 17386682262007807442078693)
                    ·
                      refine ⟨3260002924126463895389755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17386682262007807442078693 3260002924126463895389755)
                      ·
                        rfl

theorem cell23_6348833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6348833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348833 prefixEnd_6348833 := by exact prefixLift 6348833
  have htrace : WordTrace (prefixWord ++ tailWord_6348833) baseStart_6348833 baseEnd_6348833 := by
    simpa [prefixWord, tailWord_6348833, baseEnd_6348833] using wordTrace_append hprefix tailTrace_6348833
  have hstable : (prefixWord ++ tailWord_6348833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348833).length < 2 ^ (prefixWord ++ tailWord_6348833).sum := by decide
  have hdescent : baseEnd_6348833 < baseStart_6348833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348836 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6348836 : Nat := 118140960795 + 6348836 * 2 ^ 59
def prefixEnd_6348836 : Nat := 4983230072969 + 3 ^ 40 * 6348836 * 2
def baseEnd_6348836 : Nat := 3260004464568427383652241

theorem tailTrace_6348836 : CollatzResearch.WordTrace tailWord_6348836 prefixEnd_6348836 3260004464568427383652241 := by
  unfold tailWord_6348836
  simp only [CollatzResearch.WordTrace]
  refine ⟨115780536213629470854393181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154374048284839294472524241 115780536213629470854393181)
  ·
    refine ⟨43417701080111051570397443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115780536213629470854393181 43417701080111051570397443)
    ·
      refine ⟨65126551620166577355596165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43417701080111051570397443 65126551620166577355596165)
      ·
        refine ⟨12211228428781233254174281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65126551620166577355596165 12211228428781233254174281)
        ·
          refine ⟨9158421321585924940630711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211228428781233254174281 9158421321585924940630711)
          ·
            refine ⟨13737631982378887410946067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158421321585924940630711 13737631982378887410946067)
            ·
              refine ⟨20606447973568331116419101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737631982378887410946067 20606447973568331116419101)
              ·
                refine ⟨7727417990088124168657163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20606447973568331116419101 7727417990088124168657163)
                ·
                  refine ⟨11591126985132186252985745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7727417990088124168657163 11591126985132186252985745)
                  ·
                    refine ⟨8693345238849139689739309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11591126985132186252985745 8693345238849139689739309)
                    ·
                      refine ⟨3260004464568427383652241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693345238849139689739309 3260004464568427383652241)
                      ·
                        rfl

theorem cell23_6348836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6348836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348836 prefixEnd_6348836 := by exact prefixLift 6348836
  have htrace : WordTrace (prefixWord ++ tailWord_6348836) baseStart_6348836 baseEnd_6348836 := by
    simpa [prefixWord, tailWord_6348836, baseEnd_6348836] using wordTrace_append hprefix tailTrace_6348836
  have hstable : (prefixWord ++ tailWord_6348836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348836).length < 2 ^ (prefixWord ++ tailWord_6348836).sum := by decide
  have hdescent : baseEnd_6348836 < baseStart_6348836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348849 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_6348849 : Nat := 118140960795 + 6348849 * 2 ^ 59
def prefixEnd_6348849 : Nat := 4983230072969 + 3 ^ 40 * 6348849 * 2
def baseEnd_6348849 : Nat := 3260011139816935832789681

theorem tailTrace_6348849 : CollatzResearch.WordTrace tailWord_6348849 prefixEnd_6348849 3260011139816935832789681 := by
  unfold tailWord_6348849
  simp only [CollatzResearch.WordTrace]
  refine ⟨231561546576211844929009601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154374364384141229952673067 231561546576211844929009601)
  ·
    refine ⟨173671159932158883696757201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231561546576211844929009601 173671159932158883696757201)
    ·
      refine ⟨130253369949119162772567901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173671159932158883696757201 130253369949119162772567901)
      ·
        refine ⟨48845013730919686039712963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130253369949119162772567901 48845013730919686039712963)
        ·
          refine ⟨73267520596379529059569445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48845013730919686039712963 73267520596379529059569445)
          ·
            refine ⟨13737660111821161698669271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73267520596379529059569445 13737660111821161698669271)
            ·
              refine ⟨20606490167731742548003907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737660111821161698669271 20606490167731742548003907)
              ·
                refine ⟨30909735251597613822005861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20606490167731742548003907 30909735251597613822005861)
                ·
                  refine ⟨5795575359674552591626099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30909735251597613822005861 5795575359674552591626099)
                  ·
                    refine ⟨8693363039511828887439149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795575359674552591626099 8693363039511828887439149)
                    ·
                      refine ⟨3260011139816935832789681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693363039511828887439149 3260011139816935832789681)
                      ·
                        rfl

theorem cell23_6348849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_6348849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348849 prefixEnd_6348849 := by exact prefixLift 6348849
  have htrace : WordTrace (prefixWord ++ tailWord_6348849) baseStart_6348849 baseEnd_6348849 := by
    simpa [prefixWord, tailWord_6348849, baseEnd_6348849] using wordTrace_append hprefix tailTrace_6348849
  have hstable : (prefixWord ++ tailWord_6348849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348849).length < 2 ^ (prefixWord ++ tailWord_6348849).sum := by decide
  have hdescent : baseEnd_6348849 < baseStart_6348849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348855 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_6348855 : Nat := 118140960795 + 6348855 * 2 ^ 59
def prefixEnd_6348855 : Nat := 4983230072969 + 3 ^ 40 * 6348855 * 2
def baseEnd_6348855 : Nat := 3260014220700862809314653

theorem tailTrace_6348855 : CollatzResearch.WordTrace tailWord_6348855 prefixEnd_6348855 3260014220700862809314653 := by
  unfold tailWord_6348855
  simp only [CollatzResearch.WordTrace]
  refine ⟨231561765414190107953728019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154374510276126738635818679 231561765414190107953728019)
  ·
    refine ⟨347342648121285161930592029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231561765414190107953728019 347342648121285161930592029)
    ·
      refine ⟨130253493045481935723972011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347342648121285161930592029 130253493045481935723972011)
      ·
        refine ⟨195380239568222903585958017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130253493045481935723972011 195380239568222903585958017)
        ·
          refine ⟨146535179676167177689468513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195380239568222903585958017 146535179676167177689468513)
          ·
            refine ⟨109901384757125383267101385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146535179676167177689468513 109901384757125383267101385)
            ·
              refine ⟨82426038567844037450326039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109901384757125383267101385 82426038567844037450326039)
              ·
                refine ⟨123639057851766056175489059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82426038567844037450326039 123639057851766056175489059)
                ·
                  refine ⟨185458586777649084263233589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123639057851766056175489059 185458586777649084263233589)
                  ·
                    refine ⟨17386742510404601649678149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185458586777649084263233589 17386742510404601649678149)
                    ·
                      refine ⟨3260014220700862809314653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17386742510404601649678149 3260014220700862809314653)
                      ·
                        rfl

theorem cell23_6348855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_6348855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348855 prefixEnd_6348855 := by exact prefixLift 6348855
  have htrace : WordTrace (prefixWord ++ tailWord_6348855) baseStart_6348855 baseEnd_6348855 := by
    simpa [prefixWord, tailWord_6348855, baseEnd_6348855] using wordTrace_append hprefix tailTrace_6348855
  have hstable : (prefixWord ++ tailWord_6348855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348855).length < 2 ^ (prefixWord ++ tailWord_6348855).sum := by decide
  have hdescent : baseEnd_6348855 < baseStart_6348855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348875 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_6348875 : Nat := 118140960795 + 6348875 * 2 ^ 59
def prefixEnd_6348875 : Nat := 4983230072969 + 3 ^ 40 * 6348875 * 2
def baseEnd_6348875 : Nat := 3260024490313952731064561

theorem tailTrace_6348875 : CollatzResearch.WordTrace tailWord_6348875 prefixEnd_6348875 3260024490313952731064561 := by
  unfold tailWord_6348875
  simp only [CollatzResearch.WordTrace]
  refine ⟨231562494874117651369456079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154374996582745100912970719 231562494874117651369456079)
  ·
    refine ⟨347343742311176477054184119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231562494874117651369456079 347343742311176477054184119)
    ·
      refine ⟨521015613466764715581276179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347343742311176477054184119 521015613466764715581276179)
      ·
        refine ⟨781523420200147073371914269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521015613466764715581276179 781523420200147073371914269)
        ·
          refine ⟨293071282575055152514467851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 781523420200147073371914269 293071282575055152514467851)
          ·
            refine ⟨439606923862582728771701777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293071282575055152514467851 439606923862582728771701777)
            ·
              refine ⟨329705192896937046578776333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439606923862582728771701777 329705192896937046578776333)
              ·
                refine ⟨123639447336351392467041125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329705192896937046578776333 123639447336351392467041125)
                ·
                  refine ⟨23182396375565886087570211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123639447336351392467041125 23182396375565886087570211)
                  ·
                    refine ⟨34773594563348829131355317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23182396375565886087570211 34773594563348829131355317)
                    ·
                      refine ⟨3260024490313952731064561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34773594563348829131355317 3260024490313952731064561)
                      ·
                        rfl

theorem cell23_6348875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_6348875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348875 prefixEnd_6348875 := by exact prefixLift 6348875
  have htrace : WordTrace (prefixWord ++ tailWord_6348875) baseStart_6348875 baseEnd_6348875 := by
    simpa [prefixWord, tailWord_6348875, baseEnd_6348875] using wordTrace_append hprefix tailTrace_6348875
  have hstable : (prefixWord ++ tailWord_6348875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348875).length < 2 ^ (prefixWord ++ tailWord_6348875).sum := by decide
  have hdescent : baseEnd_6348875 < baseStart_6348875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348889 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 6, 2, 2]
def baseStart_6348889 : Nat := 118140960795 + 6348889 * 2 ^ 59
def prefixEnd_6348889 : Nat := 4983230072969 + 3 ^ 40 * 6348889 * 2
def baseEnd_6348889 : Nat := 3260031679043115676289497

theorem tailTrace_6348889 : CollatzResearch.WordTrace tailWord_6348889 prefixEnd_6348889 3260031679043115676289497 := by
  unfold tailWord_6348889
  simp only [CollatzResearch.WordTrace]
  refine ⟨231563005496066931760465721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154375336997377954506977147 231563005496066931760465721)
  ·
    refine ⟨173672254122050198820349291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231563005496066931760465721 173672254122050198820349291)
    ·
      refine ⟨260508381183075298230523937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173672254122050198820349291 260508381183075298230523937)
      ·
        refine ⟨195381285887306473672892953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260508381183075298230523937 195381285887306473672892953)
        ·
          refine ⟨146535964415479855254669715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195381285887306473672892953 146535964415479855254669715)
          ·
            refine ⟨219803946623219782882004573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146535964415479855254669715 219803946623219782882004573)
            ·
              refine ⟨82426479983707418580751715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219803946623219782882004573 82426479983707418580751715)
              ·
                refine ⟨123639719975561127871127573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82426479983707418580751715 123639719975561127871127573)
                ·
                  refine ⟨5795611873854427868959105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123639719975561127871127573 5795611873854427868959105)
                  ·
                    refine ⟨4346708905390820901719329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795611873854427868959105 4346708905390820901719329)
                    ·
                      refine ⟨3260031679043115676289497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346708905390820901719329 3260031679043115676289497)
                      ·
                        rfl

theorem cell23_6348889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_6348889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348889 prefixEnd_6348889 := by exact prefixLift 6348889
  have htrace : WordTrace (prefixWord ++ tailWord_6348889) baseStart_6348889 baseEnd_6348889 := by
    simpa [prefixWord, tailWord_6348889, baseEnd_6348889] using wordTrace_append hprefix tailTrace_6348889
  have hstable : (prefixWord ++ tailWord_6348889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348889).length < 2 ^ (prefixWord ++ tailWord_6348889).sum := by decide
  have hdescent : baseEnd_6348889 < baseStart_6348889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348892 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6348892 : Nat := 118140960795 + 6348892 * 2 ^ 59
def prefixEnd_6348892 : Nat := 4983230072969 + 3 ^ 40 * 6348892 * 2
def baseEnd_6348892 : Nat := 3260033219485079164551983

theorem tailTrace_6348892 : CollatzResearch.WordTrace tailWord_6348892 prefixEnd_6348892 3260033219485079164551983 := by
  unfold tailWord_6348892
  simp only [CollatzResearch.WordTrace]
  refine ⟨115781557457528031636412465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154375409943370708848549953 115781557457528031636412465)
  ·
    refine ⟨86836168093146023727309349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115781557457528031636412465 86836168093146023727309349)
    ·
      refine ⟨16281781517464879448870503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86836168093146023727309349 16281781517464879448870503)
      ·
        refine ⟨24422672276197319173305755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16281781517464879448870503 24422672276197319173305755)
        ·
          refine ⟨36634008414295978759958633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24422672276197319173305755 36634008414295978759958633)
          ·
            refine ⟨27475506310721984069968975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36634008414295978759958633 27475506310721984069968975)
            ·
              refine ⟨41213259466082976104953463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27475506310721984069968975 41213259466082976104953463)
              ·
                refine ⟨61819889199124464157430195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41213259466082976104953463 61819889199124464157430195)
                ·
                  refine ⟨92729833798686696236145293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61819889199124464157430195 92729833798686696236145293)
                  ·
                    refine ⟨34773687674507511088554485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92729833798686696236145293 34773687674507511088554485)
                    ·
                      refine ⟨3260033219485079164551983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34773687674507511088554485 3260033219485079164551983)
                      ·
                        rfl

theorem cell23_6348892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6348892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348892 prefixEnd_6348892 := by exact prefixLift 6348892
  have htrace : WordTrace (prefixWord ++ tailWord_6348892) baseStart_6348892 baseEnd_6348892 := by
    simpa [prefixWord, tailWord_6348892, baseEnd_6348892] using wordTrace_append hprefix tailTrace_6348892
  have hstable : (prefixWord ++ tailWord_6348892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348892).length < 2 ^ (prefixWord ++ tailWord_6348892).sum := by decide
  have hdescent : baseEnd_6348892 < baseStart_6348892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348893 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6348893 : Nat := 118140960795 + 6348893 * 2 ^ 59
def prefixEnd_6348893 : Nat := 4983230072969 + 3 ^ 40 * 6348893 * 2
def baseEnd_6348893 : Nat := 3260033732965733660639479

theorem tailTrace_6348893 : CollatzResearch.WordTrace tailWord_6348893 prefixEnd_6348893 3260033732965733660639479 := by
  unfold tailWord_6348893
  simp only [CollatzResearch.WordTrace]
  refine ⟨231563151388052440443611333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154375434258701626962407555 231563151388052440443611333)
  ·
    refine ⟨43418090885259832583177125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231563151388052440443611333 43418090885259832583177125)
    ·
      refine ⟨8140892040986218609345711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43418090885259832583177125 8140892040986218609345711)
      ·
        refine ⟨12211338061479327914018567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140892040986218609345711 12211338061479327914018567)
        ·
          refine ⟨18317007092218991871027851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211338061479327914018567 18317007092218991871027851)
          ·
            refine ⟨27475510638328487806541777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317007092218991871027851 27475510638328487806541777)
            ·
              refine ⟨20606632978746365854906333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27475510638328487806541777 20606632978746365854906333)
              ·
                refine ⟨7727487367029887195589875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20606632978746365854906333 7727487367029887195589875)
                ·
                  refine ⟨11591231050544830793384813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7727487367029887195589875 11591231050544830793384813)
                  ·
                    refine ⟨4346711643954311547519305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11591231050544830793384813 4346711643954311547519305)
                    ·
                      refine ⟨3260033732965733660639479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346711643954311547519305 3260033732965733660639479)
                      ·
                        rfl

theorem cell23_6348893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6348893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348893 prefixEnd_6348893 := by exact prefixLift 6348893
  have htrace : WordTrace (prefixWord ++ tailWord_6348893) baseStart_6348893 baseEnd_6348893 := by
    simpa [prefixWord, tailWord_6348893, baseEnd_6348893] using wordTrace_append hprefix tailTrace_6348893
  have hstable : (prefixWord ++ tailWord_6348893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348893).length < 2 ^ (prefixWord ++ tailWord_6348893).sum := by decide
  have hdescent : baseEnd_6348893 < baseStart_6348893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348905 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_6348905 : Nat := 118140960795 + 6348905 * 2 ^ 59
def prefixEnd_6348905 : Nat := 4983230072969 + 3 ^ 40 * 6348905 * 2
def baseEnd_6348905 : Nat := 3260039894733587613689423

theorem tailTrace_6348905 : CollatzResearch.WordTrace tailWord_6348905 prefixEnd_6348905 3260039894733587613689423 := by
  unfold tailWord_6348905
  simp only [CollatzResearch.WordTrace]
  refine ⟨231563589064008966493048169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154375726042672644328698779 231563589064008966493048169)
  ·
    refine ⟨173672691798006724869786127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231563589064008966493048169 173672691798006724869786127)
    ·
      refine ⟨260509037697010087304679191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173672691798006724869786127 260509037697010087304679191)
      ·
        refine ⟨390763556545515130957018787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260509037697010087304679191 390763556545515130957018787)
        ·
          refine ⟨586145334818272696435528181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390763556545515130957018787 586145334818272696435528181)
          ·
            refine ⟨54951125139213065290830767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 586145334818272696435528181 54951125139213065290830767)
            ·
              refine ⟨82426687708819597936246151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54951125139213065290830767 82426687708819597936246151)
              ·
                refine ⟨123640031563229396904369227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82426687708819597936246151 123640031563229396904369227)
                ·
                  refine ⟨185460047344844095356553841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123640031563229396904369227 185460047344844095356553841)
                  ·
                    refine ⟨139095035508633071517415381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185460047344844095356553841 139095035508633071517415381)
                    ·
                      refine ⟨3260039894733587613689423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139095035508633071517415381 3260039894733587613689423)
                      ·
                        rfl

theorem cell23_6348905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_6348905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348905 prefixEnd_6348905 := by exact prefixLift 6348905
  have htrace : WordTrace (prefixWord ++ tailWord_6348905) baseStart_6348905 baseEnd_6348905 := by
    simpa [prefixWord, tailWord_6348905, baseEnd_6348905] using wordTrace_append hprefix tailTrace_6348905
  have hstable : (prefixWord ++ tailWord_6348905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348905).length < 2 ^ (prefixWord ++ tailWord_6348905).sum := by decide
  have hdescent : baseEnd_6348905 < baseStart_6348905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348912 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 7]
def baseStart_6348912 : Nat := 118140960795 + 6348912 * 2 ^ 59
def prefixEnd_6348912 : Nat := 4983230072969 + 3 ^ 40 * 6348912 * 2
def baseEnd_6348912 : Nat := 362227054344241009589099

theorem tailTrace_6348912 : CollatzResearch.WordTrace tailWord_6348912 prefixEnd_6348912 362227054344241009589099 := by
  unfold tailWord_6348912
  simp only [CollatzResearch.WordTrace]
  refine ⟨115781922187491803344276495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154375896249989071125701993 115781922187491803344276495)
  ·
    refine ⟨173672883281237705016414743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115781922187491803344276495 173672883281237705016414743)
    ·
      refine ⟨260509324921856557524622115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173672883281237705016414743 260509324921856557524622115)
      ·
        refine ⟨390763987382784836286933173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260509324921856557524622115 390763987382784836286933173)
        ·
          refine ⟨36634123817136078401899985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390763987382784836286933173 36634123817136078401899985)
          ·
            refine ⟨27475592862852058801424989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36634123817136078401899985 27475592862852058801424989)
            ·
              refine ⟨10303347323569522050534371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27475592862852058801424989 10303347323569522050534371)
              ·
                refine ⟨15455020985354283075801557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303347323569522050534371 15455020985354283075801557)
                ·
                  refine ⟨362227054344241009589099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15455020985354283075801557 362227054344241009589099)
                  ·
                    rfl

theorem cell23_6348912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_6348912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348912 prefixEnd_6348912 := by exact prefixLift 6348912
  have htrace : WordTrace (prefixWord ++ tailWord_6348912) baseStart_6348912 baseEnd_6348912 := by
    simpa [prefixWord, tailWord_6348912, baseEnd_6348912] using wordTrace_append hprefix tailTrace_6348912
  have hstable : (prefixWord ++ tailWord_6348912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348912).length < 2 ^ (prefixWord ++ tailWord_6348912).sum := by decide
  have hdescent : baseEnd_6348912 < baseStart_6348912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 10]
def baseStart_6348955 : Nat := 118140960795 + 6348955 * 2 ^ 59
def prefixEnd_6348955 : Nat := 4983230072969 + 3 ^ 40 * 6348955 * 2
def baseEnd_6348955 : Nat := 1086688522922104139354731

theorem tailTrace_6348955 : CollatzResearch.WordTrace tailWord_6348955 prefixEnd_6348955 1086688522922104139354731 := by
  unfold tailWord_6348955
  simp only [CollatzResearch.WordTrace]
  refine ⟨231565412713827825032368319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154376941809218550021578879 231565412713827825032368319)
  ·
    refine ⟨347348119070741737548552479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231565412713827825032368319 347348119070741737548552479)
    ·
      refine ⟨521022178606112606322828719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347348119070741737548552479 521022178606112606322828719)
      ·
        refine ⟨781533267909168909484243079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521022178606112606322828719 781533267909168909484243079)
        ·
          refine ⟨1172299901863753364226364619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781533267909168909484243079 1172299901863753364226364619)
          ·
            refine ⟨1758449852795630046339546929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172299901863753364226364619 1758449852795630046339546929)
            ·
              refine ⟨1318837389596722534754660197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758449852795630046339546929 1318837389596722534754660197)
              ·
                refine ⟨247282010549385475266498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1318837389596722534754660197 247282010549385475266498787)
                ·
                  refine ⟨370923015824078212899748181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247282010549385475266498787 370923015824078212899748181)
                  ·
                    refine ⟨1086688522922104139354731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 370923015824078212899748181 1086688522922104139354731)
                    ·
                      rfl

theorem cell23_6348955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_6348955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348955 prefixEnd_6348955 := by exact prefixLift 6348955
  have htrace : WordTrace (prefixWord ++ tailWord_6348955) baseStart_6348955 baseEnd_6348955 := by
    simpa [prefixWord, tailWord_6348955, baseEnd_6348955] using wordTrace_append hprefix tailTrace_6348955
  have hstable : (prefixWord ++ tailWord_6348955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348955).length < 2 ^ (prefixWord ++ tailWord_6348955).sum := by decide
  have hdescent : baseEnd_6348955 < baseStart_6348955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348959 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 2, 5]
def baseStart_6348959 : Nat := 118140960795 + 6348959 * 2 ^ 59
def prefixEnd_6348959 : Nat := 4983230072969 + 3 ^ 40 * 6348959 * 2
def baseEnd_6348959 : Nat := 1086689207562976800804725

theorem tailTrace_6348959 : CollatzResearch.WordTrace tailWord_6348959 prefixEnd_6348959 1086689207562976800804725 := by
  unfold tailWord_6348959
  simp only [CollatzResearch.WordTrace]
  refine ⟨231565558605813333715513931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154377039070542222477009287 231565558605813333715513931)
  ·
    refine ⟨347348337908720000573270897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231565558605813333715513931 347348337908720000573270897)
    ·
      refine ⟨260511253431540000429953173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347348337908720000573270897 260511253431540000429953173)
      ·
        refine ⟨12211465004603437520154055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260511253431540000429953173 12211465004603437520154055)
        ·
          refine ⟨18317197506905156280231083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211465004603437520154055 18317197506905156280231083)
          ·
            refine ⟨27475796260357734420346625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317197506905156280231083 27475796260357734420346625)
            ·
              refine ⟨20606847195268300815259969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27475796260357734420346625 20606847195268300815259969)
              ·
                refine ⟨15455135396451225611444977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20606847195268300815259969 15455135396451225611444977)
                ·
                  refine ⟨11591351547338419208583733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15455135396451225611444977 11591351547338419208583733)
                  ·
                    refine ⟨1086689207562976800804725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11591351547338419208583733 1086689207562976800804725)
                    ·
                      rfl

theorem cell23_6348959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_6348959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348959 prefixEnd_6348959 := by exact prefixLift 6348959
  have htrace : WordTrace (prefixWord ++ tailWord_6348959) baseStart_6348959 baseEnd_6348959 := by
    simpa [prefixWord, tailWord_6348959, baseEnd_6348959] using wordTrace_append hprefix tailTrace_6348959
  have hstable : (prefixWord ++ tailWord_6348959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348959).length < 2 ^ (prefixWord ++ tailWord_6348959).sum := by decide
  have hdescent : baseEnd_6348959 < baseStart_6348959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348993 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6348993 : Nat := 118140960795 + 6348993 * 2 ^ 59
def prefixEnd_6348993 : Nat := 4983230072969 + 3 ^ 40 * 6348993 * 2
def baseEnd_6348993 : Nat := 1086695027010394423129673

theorem tailTrace_6348993 : CollatzResearch.WordTrace tailWord_6348993 prefixEnd_6348993 1086695027010394423129673 := by
  unfold tailWord_6348993
  simp only [CollatzResearch.WordTrace]
  refine ⟨231566798687690157522251633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154377865791793438348167755 231566798687690157522251633)
  ·
    refine ⟨173675099015767618141688725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231566798687690157522251633 173675099015767618141688725)
    ·
      refine ⟨8141020266364107100391659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173675099015767618141688725 8141020266364107100391659)
      ·
        refine ⟨12211530399546160650587489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141020266364107100391659 12211530399546160650587489)
        ·
          refine ⟨9158647799659620487940617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211530399546160650587489 9158647799659620487940617)
          ·
            refine ⟨6868985849744715365955463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158647799659620487940617 6868985849744715365955463)
            ·
              refine ⟨10303478774617073048933195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868985849744715365955463 10303478774617073048933195)
              ·
                refine ⟨15455218161925609573399793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303478774617073048933195 15455218161925609573399793)
                ·
                  refine ⟨11591413621444207180049845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15455218161925609573399793 11591413621444207180049845)
                  ·
                    refine ⟨1086695027010394423129673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11591413621444207180049845 1086695027010394423129673)
                    ·
                      rfl

theorem cell23_6348993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6348993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348993 prefixEnd_6348993 := by exact prefixLift 6348993
  have htrace : WordTrace (prefixWord ++ tailWord_6348993) baseStart_6348993 baseEnd_6348993 := by
    simpa [prefixWord, tailWord_6348993, baseEnd_6348993] using wordTrace_append hprefix tailTrace_6348993
  have hstable : (prefixWord ++ tailWord_6348993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348993).length < 2 ^ (prefixWord ++ tailWord_6348993).sum := by decide
  have hdescent : baseEnd_6348993 < baseStart_6348993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6348996 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_6348996 : Nat := 118140960795 + 6348996 * 2 ^ 59
def prefixEnd_6348996 : Nat := 4983230072969 + 3 ^ 40 * 6348996 * 2
def baseEnd_6348996 : Nat := 3260086621473146757651505

theorem tailTrace_6348996 : CollatzResearch.WordTrace tailWord_6348996 prefixEnd_6348996 3260086621473146757651505 := by
  unfold tailWord_6348996
  simp only [CollatzResearch.WordTrace]
  refine ⟨115783454053339644517305421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154377938737786192689740561 115783454053339644517305421)
  ·
    refine ⟨43418795270002366693989533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115783454053339644517305421 43418795270002366693989533)
    ·
      refine ⟨16282048226250887510246075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43418795270002366693989533 16282048226250887510246075)
      ·
        refine ⟨24423072339376331265369113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16282048226250887510246075 24423072339376331265369113)
        ·
          refine ⟨18317304254532248449026835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24423072339376331265369113 18317304254532248449026835)
          ·
            refine ⟨27475956381798372673540253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317304254532248449026835 27475956381798372673540253)
            ·
              refine ⟨10303483643174389752577595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27475956381798372673540253 10303483643174389752577595)
              ·
                refine ⟨15455225464761584628866393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303483643174389752577595 15455225464761584628866393)
                ·
                  refine ⟨11591419098571188471649795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15455225464761584628866393 11591419098571188471649795)
                  ·
                    refine ⟨17387128647856782707474693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11591419098571188471649795 17387128647856782707474693)
                    ·
                      refine ⟨3260086621473146757651505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17387128647856782707474693 3260086621473146757651505)
                      ·
                        rfl

theorem cell23_6348996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_6348996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6348996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6348996 prefixEnd_6348996 := by exact prefixLift 6348996
  have htrace : WordTrace (prefixWord ++ tailWord_6348996) baseStart_6348996 baseEnd_6348996 := by
    simpa [prefixWord, tailWord_6348996, baseEnd_6348996] using wordTrace_append hprefix tailTrace_6348996
  have hstable : (prefixWord ++ tailWord_6348996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6348996).length < 2 ^ (prefixWord ++ tailWord_6348996).sum := by decide
  have hdescent : baseEnd_6348996 < baseStart_6348996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6348996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349002 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_6349002 : Nat := 118140960795 + 6349002 * 2 ^ 59
def prefixEnd_6349002 : Nat := 4983230072969 + 3 ^ 40 * 6349002 * 2
def baseEnd_6349002 : Nat := 362232189150785970464053

theorem tailTrace_6349002 : CollatzResearch.WordTrace tailWord_6349002 prefixEnd_6349002 362232189150785970464053 := by
  unfold tailWord_6349002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57891781736164388014832315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154378084629771701372886173 57891781736164388014832315)
  ·
    refine ⟨86837672604246582022248473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57891781736164388014832315 86837672604246582022248473)
    ·
      refine ⟨65128254453184936516686355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86837672604246582022248473 65128254453184936516686355)
      ·
        refine ⟨97692381679777404775029533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65128254453184936516686355 97692381679777404775029533)
        ·
          refine ⟨36634643129916526790636075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97692381679777404775029533 36634643129916526790636075)
          ·
            refine ⟨54951964694874790185954113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36634643129916526790636075 54951964694874790185954113)
            ·
              refine ⟨41213973521156092639465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54951964694874790185954113 41213973521156092639465585)
              ·
                refine ⟨30910480140867069479599189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41213973521156092639465585 30910480140867069479599189)
                ·
                  refine ⟨362232189150785970464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30910480140867069479599189 362232189150785970464053)
                  ·
                    rfl

theorem cell23_6349002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_6349002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349002 prefixEnd_6349002 := by exact prefixLift 6349002
  have htrace : WordTrace (prefixWord ++ tailWord_6349002) baseStart_6349002 baseEnd_6349002 := by
    simpa [prefixWord, tailWord_6349002, baseEnd_6349002] using wordTrace_append hprefix tailTrace_6349002
  have hstable : (prefixWord ++ tailWord_6349002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349002).length < 2 ^ (prefixWord ++ tailWord_6349002).sum := by decide
  have hdescent : baseEnd_6349002 < baseStart_6349002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349080 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6349080 : Nat := 118140960795 + 6349080 * 2 ^ 59
def prefixEnd_6349080 : Nat := 4983230072969 + 3 ^ 40 * 6349080 * 2
def baseEnd_6349080 : Nat := 3260129753848124429001119

theorem tailTrace_6349080 : CollatzResearch.WordTrace tailWord_6349080 prefixEnd_6349080 3260129753848124429001119 := by
  unfold tailWord_6349080
  simp only [CollatzResearch.WordTrace]
  refine ⟨115784985919187485690334347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154379981225583314253779129 115784985919187485690334347)
  ·
    refine ⟨173677478878781228535501521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115784985919187485690334347 173677478878781228535501521)
    ·
      refine ⟨130258109159085921401626141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173677478878781228535501521 130258109159085921401626141)
      ·
        refine ⟨48846790934657220525609803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130258109159085921401626141 48846790934657220525609803)
        ·
          refine ⟨73270186401985830788414705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48846790934657220525609803 73270186401985830788414705)
          ·
            refine ⟨54952639801489373091311029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73270186401985830788414705 54952639801489373091311029)
            ·
              refine ⟨5151809981389628727310409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54952639801489373091311029 5151809981389628727310409)
              ·
                refine ⟨3863857486042221545482807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151809981389628727310409 3863857486042221545482807)
                ·
                  refine ⟨5795786229063332318224211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863857486042221545482807 5795786229063332318224211)
                  ·
                    refine ⟨8693679343594998477336317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795786229063332318224211 8693679343594998477336317)
                    ·
                      refine ⟨3260129753848124429001119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693679343594998477336317 3260129753848124429001119)
                      ·
                        rfl

theorem cell23_6349080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6349080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349080 prefixEnd_6349080 := by exact prefixLift 6349080
  have htrace : WordTrace (prefixWord ++ tailWord_6349080) baseStart_6349080 baseEnd_6349080 := by
    simpa [prefixWord, tailWord_6349080, baseEnd_6349080] using wordTrace_append hprefix tailTrace_6349080
  have hstable : (prefixWord ++ tailWord_6349080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349080).length < 2 ^ (prefixWord ++ tailWord_6349080).sum := by decide
  have hdescent : baseEnd_6349080 < baseStart_6349080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349089 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6349089 : Nat := 118140960795 + 6349089 * 2 ^ 59
def prefixEnd_6349089 : Nat := 4983230072969 + 3 ^ 40 * 6349089 * 2
def baseEnd_6349089 : Nat := 3260134375174014893788577

theorem tailTrace_6349089 : CollatzResearch.WordTrace tailWord_6349089 prefixEnd_6349089 3260134375174014893788577 := by
  unfold tailWord_6349089
  simp only [CollatzResearch.WordTrace]
  refine ⟨231570300095342365917746321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154380200063561577278497547 231570300095342365917746321)
  ·
    refine ⟨173677725071506774438309741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231570300095342365917746321 173677725071506774438309741)
    ·
      refine ⟨65129146901815040414366153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173677725071506774438309741 65129146901815040414366153)
      ·
        refine ⟨48846860176361280310774615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65129146901815040414366153 48846860176361280310774615)
        ·
          refine ⟨73270290264541920466161923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48846860176361280310774615 73270290264541920466161923)
          ·
            refine ⟨109905435396812880699242885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73270290264541920466161923 109905435396812880699242885)
            ·
              refine ⟨20607269136902415131108041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109905435396812880699242885 20607269136902415131108041)
              ·
                refine ⟨15455451852676811348331031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20607269136902415131108041 15455451852676811348331031)
                ·
                  refine ⟨23183177779015217022496547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15455451852676811348331031 23183177779015217022496547)
                  ·
                    refine ⟨34774766668522825533744821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23183177779015217022496547 34774766668522825533744821)
                    ·
                      refine ⟨3260134375174014893788577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34774766668522825533744821 3260134375174014893788577)
                      ·
                        rfl

theorem cell23_6349089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6349089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349089 prefixEnd_6349089 := by exact prefixLift 6349089
  have htrace : WordTrace (prefixWord ++ tailWord_6349089) baseStart_6349089 baseEnd_6349089 := by
    simpa [prefixWord, tailWord_6349089, baseEnd_6349089] using wordTrace_append hprefix tailTrace_6349089
  have hstable : (prefixWord ++ tailWord_6349089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349089).length < 2 ^ (prefixWord ++ tailWord_6349089).sum := by decide
  have hdescent : baseEnd_6349089 < baseStart_6349089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349137 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_6349137 : Nat := 118140960795 + 6349137 * 2 ^ 59
def prefixEnd_6349137 : Nat := 4983230072969 + 3 ^ 40 * 6349137 * 2
def baseEnd_6349137 : Nat := 3260159022245430705988357

theorem tailTrace_6349137 : CollatzResearch.WordTrace tailWord_6349137 prefixEnd_6349137 3260159022245430705988357 := by
  unfold tailWord_6349137
  simp only [CollatzResearch.WordTrace]
  refine ⟨231572050799168470115493665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154381367199445646743662443 231572050799168470115493665)
  ·
    refine ⟨173679038099376352586620249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231572050799168470115493665 173679038099376352586620249)
    ·
      refine ⟨130259278574532264439965187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173679038099376352586620249 130259278574532264439965187)
      ·
        refine ⟨195388917861798396659947781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130259278574532264439965187 195388917861798396659947781)
        ·
          refine ⟨36635422099087199373740209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195388917861798396659947781 36635422099087199373740209)
          ·
            refine ⟨27476566574315399530305157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36635422099087199373740209 27476566574315399530305157)
            ·
              refine ⟨5151856232684137411932217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27476566574315399530305157 5151856232684137411932217)
              ·
                refine ⟨3863892174513103058949163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151856232684137411932217 3863892174513103058949163)
                ·
                  refine ⟨5795838261769654588423745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863892174513103058949163 5795838261769654588423745)
                  ·
                    refine ⟨4346878696327240941317809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795838261769654588423745 4346878696327240941317809)
                    ·
                      refine ⟨3260159022245430705988357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346878696327240941317809 3260159022245430705988357)
                      ·
                        rfl

theorem cell23_6349137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_6349137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349137 prefixEnd_6349137 := by exact prefixLift 6349137
  have htrace : WordTrace (prefixWord ++ tailWord_6349137) baseStart_6349137 baseEnd_6349137 := by
    simpa [prefixWord, tailWord_6349137, baseEnd_6349137] using wordTrace_append hprefix tailTrace_6349137
  have hstable : (prefixWord ++ tailWord_6349137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349137).length < 2 ^ (prefixWord ++ tailWord_6349137).sum := by decide
  have hdescent : baseEnd_6349137 < baseStart_6349137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349174 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6349174 : Nat := 118140960795 + 6349174 * 2 ^ 59
def prefixEnd_6349174 : Nat := 4983230072969 + 3 ^ 40 * 6349174 * 2
def baseEnd_6349174 : Nat := 3260178021029647061225687

theorem tailTrace_6349174 : CollatzResearch.WordTrace tailWord_6349174 prefixEnd_6349174 3260178021029647061225687 := by
  unfold tailWord_6349174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473337518752151589661911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154382266866689616956393717 14473337518752151589661911)
  ·
    refine ⟨21710006278128227384492867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14473337518752151589661911 21710006278128227384492867)
    ·
      refine ⟨32565009417192341076739301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21710006278128227384492867 32565009417192341076739301)
      ·
        refine ⟨6105939265723563951888619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32565009417192341076739301 6105939265723563951888619)
        ·
          refine ⟨9158908898585345927832929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105939265723563951888619 9158908898585345927832929)
          ·
            refine ⟨6869181673939009445874697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158908898585345927832929 6869181673939009445874697)
            ·
              refine ⟨5151886255454257084406023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6869181673939009445874697 5151886255454257084406023)
              ·
                refine ⟨7727829383181385626609035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151886255454257084406023 7727829383181385626609035)
                ·
                  refine ⟨11591744074772078439913553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7727829383181385626609035 11591744074772078439913553)
                  ·
                    refine ⟨8693808056079058829935165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11591744074772078439913553 8693808056079058829935165)
                    ·
                      refine ⟨3260178021029647061225687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693808056079058829935165 3260178021029647061225687)
                      ·
                        rfl

theorem cell23_6349174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6349174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349174 prefixEnd_6349174 := by exact prefixLift 6349174
  have htrace : WordTrace (prefixWord ++ tailWord_6349174) baseStart_6349174 baseEnd_6349174 := by
    simpa [prefixWord, tailWord_6349174, baseEnd_6349174] using wordTrace_append hprefix tailTrace_6349174
  have hstable : (prefixWord ++ tailWord_6349174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349174).length < 2 ^ (prefixWord ++ tailWord_6349174).sum := by decide
  have hdescent : baseEnd_6349174 < baseStart_6349174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349187 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 2, 1, 3]
def baseStart_6349187 : Nat := 118140960795 + 6349187 * 2 ^ 59
def prefixEnd_6349187 : Nat := 4983230072969 + 3 ^ 40 * 6349187 * 2
def baseEnd_6349187 : Nat := 3260184696278155510363127

theorem tailTrace_6349187 : CollatzResearch.WordTrace tailWord_6349187 prefixEnd_6349187 3260184696278155510363127 := by
  unfold tailWord_6349187
  simp only [CollatzResearch.WordTrace]
  refine ⟨231573874448987328654813815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154382582965991552436542543 231573874448987328654813815)
  ·
    refine ⟨347360811673480992982220723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231573874448987328654813815 347360811673480992982220723)
    ·
      refine ⟨521041217510221489473331085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347360811673480992982220723 521041217510221489473331085)
      ·
        refine ⟨195390456566333058552499157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521041217510221489473331085 195390456566333058552499157)
        ·
          refine ⟨4579463825773431059824199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 195390456566333058552499157 4579463825773431059824199)
          ·
            refine ⟨6869195738660146589736299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579463825773431059824199 6869195738660146589736299)
            ·
              refine ⟨10303793607990219884604449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869195738660146589736299 10303793607990219884604449)
              ·
                refine ⟨7727845205992664913453337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10303793607990219884604449 7727845205992664913453337)
                ·
                  refine ⟨5795883904494498685090003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727845205992664913453337 5795883904494498685090003)
                  ·
                    refine ⟨8693825856741748027635005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795883904494498685090003 8693825856741748027635005)
                    ·
                      refine ⟨3260184696278155510363127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8693825856741748027635005 3260184696278155510363127)
                      ·
                        rfl

theorem cell23_6349187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_6349187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349187 prefixEnd_6349187 := by exact prefixLift 6349187
  have htrace : WordTrace (prefixWord ++ tailWord_6349187) baseStart_6349187 baseEnd_6349187 := by
    simpa [prefixWord, tailWord_6349187, baseEnd_6349187] using wordTrace_append hprefix tailTrace_6349187
  have hstable : (prefixWord ++ tailWord_6349187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349187).length < 2 ^ (prefixWord ++ tailWord_6349187).sum := by decide
  have hdescent : baseEnd_6349187 < baseStart_6349187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349210 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6349210 : Nat := 118140960795 + 6349210 * 2 ^ 59
def prefixEnd_6349210 : Nat := 4983230072969 + 3 ^ 40 * 6349210 * 2
def baseEnd_6349210 : Nat := 3260196506333208920375521

theorem tailTrace_6349210 : CollatzResearch.WordTrace tailWord_6349210 prefixEnd_6349210 3260196506333208920375521 := by
  unfold tailWord_6349210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57893678331976000895725271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154383142218602669055267389 57893678331976000895725271)
  ·
    refine ⟨86840517497964001343587907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57893678331976000895725271 86840517497964001343587907)
    ·
      refine ⟨130260776246946002015381861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86840517497964001343587907 130260776246946002015381861)
      ·
        refine ⟨24423895546302375377884099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130260776246946002015381861 24423895546302375377884099)
        ·
          refine ⟨36635843319453563066826149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24423895546302375377884099 36635843319453563066826149)
          ·
            refine ⟨6869220622397543075029903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36635843319453563066826149 6869220622397543075029903)
            ·
              refine ⟨10303830933596314612544855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869220622397543075029903 10303830933596314612544855)
              ·
                refine ⟨15455746400394471918817283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10303830933596314612544855 15455746400394471918817283)
                ·
                  refine ⟨23183619600591707878225925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15455746400394471918817283 23183619600591707878225925)
                  ·
                    refine ⟨4346928675110945227167361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23183619600591707878225925 4346928675110945227167361)
                    ·
                      refine ⟨3260196506333208920375521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4346928675110945227167361 3260196506333208920375521)
                      ·
                        rfl

theorem cell23_6349210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6349210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349210 prefixEnd_6349210 := by exact prefixLift 6349210
  have htrace : WordTrace (prefixWord ++ tailWord_6349210) baseStart_6349210 baseEnd_6349210 := by
    simpa [prefixWord, tailWord_6349210, baseEnd_6349210] using wordTrace_append hprefix tailTrace_6349210
  have hstable : (prefixWord ++ tailWord_6349210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349210).length < 2 ^ (prefixWord ++ tailWord_6349210).sum := by decide
  have hdescent : baseEnd_6349210 < baseStart_6349210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349233 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 5]
def baseStart_6349233 : Nat := 118140960795 + 6349233 * 2 ^ 59
def prefixEnd_6349233 : Nat := 4983230072969 + 3 ^ 40 * 6349233 * 2
def baseEnd_6349233 : Nat := 362245368487584703376435

theorem tailTrace_6349233 : CollatzResearch.WordTrace tailWord_6349233 prefixEnd_6349233 362245368487584703376435 := by
  unfold tailWord_6349233
  simp only [CollatzResearch.WordTrace]
  refine ⟨231575552206820678510988353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154383701471213785673992235 231575552206820678510988353)
  ·
    refine ⟨173681664155115508883241265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231575552206820678510988353 173681664155115508883241265)
    ·
      refine ⟨130261248116336631662430949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173681664155115508883241265 130261248116336631662430949)
      ·
        refine ⟨24423984021813118436705803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130261248116336631662430949 24423984021813118436705803)
        ·
          refine ⟨36635976032719677655058705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24423984021813118436705803 36635976032719677655058705)
          ·
            refine ⟨27476982024539758241294029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36635976032719677655058705 27476982024539758241294029)
            ·
              refine ⟨10303868259202409340485261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27476982024539758241294029 10303868259202409340485261)
              ·
                refine ⟨3863950597200903502681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10303868259202409340485261 3863950597200903502681973)
                ·
                  refine ⟨362245368487584703376435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863950597200903502681973 362245368487584703376435)
                  ·
                    rfl

theorem cell23_6349233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 5].length) (baseStart_6349233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349233 prefixEnd_6349233 := by exact prefixLift 6349233
  have htrace : WordTrace (prefixWord ++ tailWord_6349233) baseStart_6349233 baseEnd_6349233 := by
    simpa [prefixWord, tailWord_6349233, baseEnd_6349233] using wordTrace_append hprefix tailTrace_6349233
  have hstable : (prefixWord ++ tailWord_6349233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349233).length < 2 ^ (prefixWord ++ tailWord_6349233).sum := by decide
  have hdescent : baseEnd_6349233 < baseStart_6349233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349246 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6349246 : Nat := 118140960795 + 6349246 * 2 ^ 59
def prefixEnd_6349246 : Nat := 4983230072969 + 3 ^ 40 * 6349246 * 2
def baseEnd_6349246 : Nat := 1086738330545590259841785

theorem tailTrace_6349246 : CollatzResearch.WordTrace tailWord_6349246 prefixEnd_6349246 1086738330545590259841785 := by
  unfold tailWord_6349246
  simp only [CollatzResearch.WordTrace]
  refine ⟨28947003294471697716401449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154384017570515721154141061 28947003294471697716401449)
  ·
    refine ⟨21710252470853773287301087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28947003294471697716401449 21710252470853773287301087)
    ·
      refine ⟨32565378706280659930951631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21710252470853773287301087 32565378706280659930951631)
      ·
        refine ⟨48848068059420989896427447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32565378706280659930951631 48848068059420989896427447)
        ·
          refine ⟨73272102089131484844641171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48848068059420989896427447 73272102089131484844641171)
          ·
            refine ⟨109908153133697227266961757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73272102089131484844641171 109908153133697227266961757)
            ·
              refine ⟨41215557425136460225110659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109908153133697227266961757 41215557425136460225110659)
              ·
                refine ⟨61823336137704690337665989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41215557425136460225110659 61823336137704690337665989)
                ·
                  refine ⟨11591875525819629438312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61823336137704690337665989 11591875525819629438312373)
                  ·
                    refine ⟨1086738330545590259841785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11591875525819629438312373 1086738330545590259841785)
                    ·
                      rfl

theorem cell23_6349246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6349246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349246 prefixEnd_6349246 := by exact prefixLift 6349246
  have htrace : WordTrace (prefixWord ++ tailWord_6349246) baseStart_6349246 baseEnd_6349246 := by
    simpa [prefixWord, tailWord_6349246, baseEnd_6349246] using wordTrace_append hprefix tailTrace_6349246
  have hstable : (prefixWord ++ tailWord_6349246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349246).length < 2 ^ (prefixWord ++ tailWord_6349246).sum := by decide
  have hdescent : baseEnd_6349246 < baseStart_6349246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349256 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_6349256 : Nat := 118140960795 + 6349256 * 2 ^ 59
def prefixEnd_6349256 : Nat := 4983230072969 + 3 ^ 40 * 6349256 * 2
def baseEnd_6349256 : Nat := 3260220126443315740400309

theorem tailTrace_6349256 : CollatzResearch.WordTrace tailWord_6349256 prefixEnd_6349256 3260220126443315740400309 := by
  unfold tailWord_6349256
  simp only [CollatzResearch.WordTrace]
  refine ⟨115788195542868676719537811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154384260723824902292717081 115788195542868676719537811)
  ·
    refine ⟨173682293314303015079306717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115788195542868676719537811 173682293314303015079306717)
    ·
      refine ⟨65130859992863630654740019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173682293314303015079306717 65130859992863630654740019)
      ·
        refine ⟨97696289989295445982110029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65130859992863630654740019 97696289989295445982110029)
        ·
          refine ⟨36636108745985792243291261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97696289989295445982110029 36636108745985792243291261)
          ·
            refine ⟨13738540779744672091234223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36636108745985792243291261 13738540779744672091234223)
            ·
              refine ⟨20607811169617008136851335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13738540779744672091234223 20607811169617008136851335)
              ·
                refine ⟨30911716754425512205277003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20607811169617008136851335 30911716754425512205277003)
                ·
                  refine ⟨46367575131638268307915505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30911716754425512205277003 46367575131638268307915505)
                  ·
                    refine ⟨34775681348728701230936629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46367575131638268307915505 34775681348728701230936629)
                    ·
                      refine ⟨3260220126443315740400309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34775681348728701230936629 3260220126443315740400309)
                      ·
                        rfl

theorem cell23_6349256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_6349256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349256 prefixEnd_6349256 := by exact prefixLift 6349256
  have htrace : WordTrace (prefixWord ++ tailWord_6349256) baseStart_6349256 baseEnd_6349256 := by
    simpa [prefixWord, tailWord_6349256, baseEnd_6349256] using wordTrace_append hprefix tailTrace_6349256
  have hstable : (prefixWord ++ tailWord_6349256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349256).length < 2 ^ (prefixWord ++ tailWord_6349256).sum := by decide
  have hdescent : baseEnd_6349256 < baseStart_6349256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349289 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 8]
def baseStart_6349289 : Nat := 118140960795 + 6349289 * 2 ^ 59
def prefixEnd_6349289 : Nat := 4983230072969 + 3 ^ 40 * 6349289 * 2
def baseEnd_6349289 : Nat := 362248563478323790143073

theorem tailTrace_6349289 : CollatzResearch.WordTrace tailWord_6349289 prefixEnd_6349289 362248563478323790143073 := by
  unfold tailWord_6349289
  simp only [CollatzResearch.WordTrace]
  refine ⟨231577594694617800075026921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154385063129745200050017947 231577594694617800075026921)
  ·
    refine ⟨173683196020963350056270191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231577594694617800075026921 173683196020963350056270191)
    ·
      refine ⟨260524794031445025084405287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173683196020963350056270191 260524794031445025084405287)
      ·
        refine ⟨390787191047167537626607931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260524794031445025084405287 390787191047167537626607931)
        ·
          refine ⟨586180786570751306439911897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390787191047167537626607931 586180786570751306439911897)
          ·
            refine ⟨439635589928063479829933923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586180786570751306439911897 439635589928063479829933923)
            ·
              refine ⟨659453384892095219744900885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439635589928063479829933923 659453384892095219744900885)
              ·
                refine ⟨30911877416816963425542229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 659453384892095219744900885 30911877416816963425542229)
                ·
                  refine ⟨362248563478323790143073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30911877416816963425542229 362248563478323790143073)
                  ·
                    rfl

theorem cell23_6349289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 8].length) (baseStart_6349289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349289 prefixEnd_6349289 := by exact prefixLift 6349289
  have htrace : WordTrace (prefixWord ++ tailWord_6349289) baseStart_6349289 baseEnd_6349289 := by
    simpa [prefixWord, tailWord_6349289, baseEnd_6349289] using wordTrace_append hprefix tailTrace_6349289
  have hstable : (prefixWord ++ tailWord_6349289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349289).length < 2 ^ (prefixWord ++ tailWord_6349289).sum := by decide
  have hdescent : baseEnd_6349289 < baseStart_6349289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349346 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6349346 : Nat := 118140960795 + 6349346 * 2 ^ 59
def prefixEnd_6349346 : Nat := 4983230072969 + 3 ^ 40 * 6349346 * 2
def baseEnd_6349346 : Nat := 3260266339702220388274895

theorem tailTrace_6349346 : CollatzResearch.WordTrace tailWord_6349346 prefixEnd_6349346 3260266339702220388274895 := by
  unfold tailWord_6349346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57894918413852824702462973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154386449103607532539901261 57894918413852824702462973)
  ·
    refine ⟨21710594405194809263423615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57894918413852824702462973 21710594405194809263423615)
    ·
      refine ⟨32565891607792213895135423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21710594405194809263423615 32565891607792213895135423)
      ·
        refine ⟨48848837411688320842703135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32565891607792213895135423 48848837411688320842703135)
        ·
          refine ⟨73273256117532481264054703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48848837411688320842703135 73273256117532481264054703)
          ·
            refine ⟨109909884176298721896082055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73273256117532481264054703 109909884176298721896082055)
            ·
              refine ⟨164864826264448082844123083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109909884176298721896082055 164864826264448082844123083)
              ·
                refine ⟨247297239396672124266184625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164864826264448082844123083 247297239396672124266184625)
                ·
                  refine ⟨185472929547504093199638469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247297239396672124266184625 185472929547504093199638469)
                  ·
                    refine ⟨34776174290157017474932213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185472929547504093199638469 34776174290157017474932213)
                    ·
                      refine ⟨3260266339702220388274895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34776174290157017474932213 3260266339702220388274895)
                      ·
                        rfl

theorem cell23_6349346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6349346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349346 prefixEnd_6349346 := by exact prefixLift 6349346
  have htrace : WordTrace (prefixWord ++ tailWord_6349346) baseStart_6349346 baseEnd_6349346 := by
    simpa [prefixWord, tailWord_6349346, baseEnd_6349346] using wordTrace_append hprefix tailTrace_6349346
  have hstable : (prefixWord ++ tailWord_6349346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349346).length < 2 ^ (prefixWord ++ tailWord_6349346).sum := by decide
  have hdescent : baseEnd_6349346 < baseStart_6349346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349357 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 8]
def baseStart_6349357 : Nat := 118140960795 + 6349357 * 2 ^ 59
def prefixEnd_6349357 : Nat := 4983230072969 + 3 ^ 40 * 6349357 * 2
def baseEnd_6349357 : Nat := 362252443109935538359705

theorem tailTrace_6349357 : CollatzResearch.WordTrace tailWord_6349357 prefixEnd_6349357 362252443109935538359705 := by
  unfold tailWord_6349357
  simp only [CollatzResearch.WordTrace]
  refine ⟨231580074858371447688502325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154386716572247631792334883 231580074858371447688502325)
  ·
    refine ⟨21710632017972323220797093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231580074858371447688502325 21710632017972323220797093)
    ·
      refine ⟨4070743503369810603899455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21710632017972323220797093 4070743503369810603899455)
      ·
        refine ⟨6106115255054715905849183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070743503369810603899455 6106115255054715905849183)
        ·
          refine ⟨9159172882582073858773775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106115255054715905849183 9159172882582073858773775)
          ·
            refine ⟨13738759323873110788160663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159172882582073858773775 13738759323873110788160663)
            ·
              refine ⟨20608138985809666182240995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13738759323873110788160663 20608138985809666182240995)
              ·
                refine ⟨30912208478714499273361493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20608138985809666182240995 30912208478714499273361493)
                ·
                  refine ⟨362252443109935538359705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30912208478714499273361493 362252443109935538359705)
                  ·
                    rfl

theorem cell23_6349357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_6349357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349357 prefixEnd_6349357 := by exact prefixLift 6349357
  have htrace : WordTrace (prefixWord ++ tailWord_6349357) baseStart_6349357 baseEnd_6349357 := by
    simpa [prefixWord, tailWord_6349357, baseEnd_6349357] using wordTrace_append hprefix tailTrace_6349357
  have hstable : (prefixWord ++ tailWord_6349357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349357).length < 2 ^ (prefixWord ++ tailWord_6349357).sum := by decide
  have hdescent : baseEnd_6349357 < baseStart_6349357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349376 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_6349376 : Nat := 118140960795 + 6349376 * 2 ^ 59
def prefixEnd_6349376 : Nat := 4983230072969 + 3 ^ 40 * 6349376 * 2
def baseEnd_6349376 : Nat := 3260281744121855270899757

theorem tailTrace_6349376 : CollatzResearch.WordTrace tailWord_6349376 prefixEnd_6349376 3260281744121855270899757 := by
  unfold tailWord_6349376
  simp only [CollatzResearch.WordTrace]
  refine ⟨115790383922651306966721991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154387178563535075955629321 115790383922651306966721991)
  ·
    refine ⟨173685575883976960450082987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115790383922651306966721991 173685575883976960450082987)
    ·
      refine ⟨260528363825965440675124481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173685575883976960450082987 260528363825965440675124481)
      ·
        refine ⟨195396272869474080506343361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260528363825965440675124481 195396272869474080506343361)
        ·
          refine ⟨146547204652105560379757521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195396272869474080506343361 146547204652105560379757521)
          ·
            refine ⟨109910403489079170284818141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146547204652105560379757521 109910403489079170284818141)
            ·
              refine ⟨41216401308404688856806803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109910403489079170284818141 41216401308404688856806803)
              ·
                refine ⟨61824601962607033285210205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41216401308404688856806803 61824601962607033285210205)
                ·
                  refine ⟨23184225735977637481953827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61824601962607033285210205 23184225735977637481953827)
                  ·
                    refine ⟨34776338603966456222930741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23184225735977637481953827 34776338603966456222930741)
                    ·
                      refine ⟨3260281744121855270899757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34776338603966456222930741 3260281744121855270899757)
                      ·
                        rfl

theorem cell23_6349376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_6349376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349376 prefixEnd_6349376 := by exact prefixLift 6349376
  have htrace : WordTrace (prefixWord ++ tailWord_6349376) baseStart_6349376 baseEnd_6349376 := by
    simpa [prefixWord, tailWord_6349376, baseEnd_6349376] using wordTrace_append hprefix tailTrace_6349376
  have hstable : (prefixWord ++ tailWord_6349376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349376).length < 2 ^ (prefixWord ++ tailWord_6349376).sum := by decide
  have hdescent : baseEnd_6349376 < baseStart_6349376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349383 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 6]
def baseStart_6349383 : Nat := 118140960795 + 6349383 * 2 ^ 59
def prefixEnd_6349383 : Nat := 4983230072969 + 3 ^ 40 * 6349383 * 2
def baseEnd_6349383 : Nat := 1086761779495478914504075

theorem tailTrace_6349383 : CollatzResearch.WordTrace tailWord_6349383 prefixEnd_6349383 1086761779495478914504075 := by
  unfold tailWord_6349383
  simp only [CollatzResearch.WordTrace]
  refine ⟨231581023156277254128948803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154387348770851502752632535 231581023156277254128948803)
  ·
    refine ⟨347371534734415881193423205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231581023156277254128948803 347371534734415881193423205)
    ·
      refine ⟨65132162762702977723766851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347371534734415881193423205 65132162762702977723766851)
      ·
        refine ⟨97698244144054466585650277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65132162762702977723766851 97698244144054466585650277)
        ·
          refine ⟨18318420777010212484809427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97698244144054466585650277 18318420777010212484809427)
          ·
            refine ⟨27477631165515318727214141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18318420777010212484809427 27477631165515318727214141)
            ·
              refine ⟨10304111687068244522705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27477631165515318727214141 10304111687068244522705303)
              ·
                refine ⟨15456167530602366784057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304111687068244522705303 15456167530602366784057955)
                ·
                  refine ⟨23184251295903550176086933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15456167530602366784057955 23184251295903550176086933)
                  ·
                    refine ⟨1086761779495478914504075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23184251295903550176086933 1086761779495478914504075)
                    ·
                      rfl

theorem cell23_6349383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_6349383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349383 prefixEnd_6349383 := by exact prefixLift 6349383
  have htrace : WordTrace (prefixWord ++ tailWord_6349383) baseStart_6349383 baseEnd_6349383 := by
    simpa [prefixWord, tailWord_6349383, baseEnd_6349383] using wordTrace_append hprefix tailTrace_6349383
  have hstable : (prefixWord ++ tailWord_6349383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349383).length < 2 ^ (prefixWord ++ tailWord_6349383).sum := by decide
  have hdescent : baseEnd_6349383 < baseStart_6349383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349413 : List Nat := [1, 3, 1, 3, 4, 2, 9]
def baseStart_6349413 : Nat := 118140960795 + 6349413 * 2 ^ 59
def prefixEnd_6349413 : Nat := 4983230072969 + 3 ^ 40 * 6349413 * 2
def baseEnd_6349413 : Nat := 40250626455630513902927

theorem tailTrace_6349413 : CollatzResearch.WordTrace tailWord_6349413 prefixEnd_6349413 40250626455630513902927 := by
  unfold tailWord_6349413
  simp only [CollatzResearch.WordTrace]
  refine ⟨231582117346168569252540893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154388078230779046168360595 231582117346168569252540893)
  ·
    refine ⟨86843294004813213469702835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231582117346168569252540893 86843294004813213469702835)
    ·
      refine ⟨130264941007219820204554253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86843294004813213469702835 130264941007219820204554253)
      ·
        refine ⟨48849352877707432576707845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130264941007219820204554253 48849352877707432576707845)
        ·
          refine ⟨9159253664570143608132721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48849352877707432576707845 9159253664570143608132721)
          ·
            refine ⟨6869440248427607706099541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159253664570143608132721 6869440248427607706099541)
            ·
              refine ⟨40250626455630513902927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6869440248427607706099541 40250626455630513902927)
              ·
                rfl

theorem cell23_6349413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 9].length) (baseStart_6349413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349413 prefixEnd_6349413 := by exact prefixLift 6349413
  have htrace : WordTrace (prefixWord ++ tailWord_6349413) baseStart_6349413 baseEnd_6349413 := by
    simpa [prefixWord, tailWord_6349413, baseEnd_6349413] using wordTrace_append hprefix tailTrace_6349413
  have hstable : (prefixWord ++ tailWord_6349413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349413).length < 2 ^ (prefixWord ++ tailWord_6349413).sum := by decide
  have hdescent : baseEnd_6349413 < baseStart_6349413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349424 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2]
def baseStart_6349424 : Nat := 118140960795 + 6349424 * 2 ^ 59
def prefixEnd_6349424 : Nat := 4983230072969 + 3 ^ 40 * 6349424 * 2
def baseEnd_6349424 : Nat := 3260306391193271083099537

theorem tailTrace_6349424 : CollatzResearch.WordTrace tailWord_6349424 prefixEnd_6349424 3260306391193271083099537 := by
  unfold tailWord_6349424
  simp only [CollatzResearch.WordTrace]
  refine ⟨115791259274564359065595663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154388345699419145420794217 115791259274564359065595663)
  ·
    refine ⟨173686888911846538598393495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115791259274564359065595663 173686888911846538598393495)
    ·
      refine ⟨260530333367769807897590243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173686888911846538598393495 260530333367769807897590243)
      ·
        refine ⟨390795500051654711846385365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260530333367769807897590243 390795500051654711846385365)
        ·
          refine ⟨9159269532460657308899657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 390795500051654711846385365 9159269532460657308899657)
          ·
            refine ⟨6869452149345492981674743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159269532460657308899657 6869452149345492981674743)
            ·
              refine ⟨10304178224018239472512115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869452149345492981674743 10304178224018239472512115)
              ·
                refine ⟨15456267336027359208768173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304178224018239472512115 15456267336027359208768173)
                ·
                  refine ⟨5796100251010259703288065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15456267336027359208768173 5796100251010259703288065)
                  ·
                    refine ⟨4347075188257694777466049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796100251010259703288065 4347075188257694777466049)
                    ·
                      refine ⟨3260306391193271083099537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347075188257694777466049 3260306391193271083099537)
                      ·
                        rfl

theorem cell23_6349424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 2, 2].length) (baseStart_6349424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349424 prefixEnd_6349424 := by exact prefixLift 6349424
  have htrace : WordTrace (prefixWord ++ tailWord_6349424) baseStart_6349424 baseEnd_6349424 := by
    simpa [prefixWord, tailWord_6349424, baseEnd_6349424] using wordTrace_append hprefix tailTrace_6349424
  have hstable : (prefixWord ++ tailWord_6349424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349424).length < 2 ^ (prefixWord ++ tailWord_6349424).sum := by decide
  have hdescent : baseEnd_6349424 < baseStart_6349424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349430 : List Nat := [5, 1, 1, 2, 3, 1, 2, 8]
def baseStart_6349430 : Nat := 118140960795 + 6349430 * 2 ^ 59
def prefixEnd_6349430 : Nat := 4983230072969 + 3 ^ 40 * 6349430 * 2
def baseEnd_6349430 : Nat := 120752202669525854060167

theorem tailTrace_6349430 : CollatzResearch.WordTrace tailWord_6349430 prefixEnd_6349430 120752202669525854060167 := by
  unfold tailWord_6349430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473921086694186322244359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154388491591404654103939829 14473921086694186322244359)
  ·
    refine ⟨21710881630041279483366539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14473921086694186322244359 21710881630041279483366539)
    ·
      refine ⟨32566322445061919225049809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21710881630041279483366539 32566322445061919225049809)
      ·
        refine ⟨24424741833796439418787357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32566322445061919225049809 24424741833796439418787357)
        ·
          refine ⟨9159278187673664782045259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24424741833796439418787357 9159278187673664782045259)
          ·
            refine ⟨13738917281510497173067889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159278187673664782045259 13738917281510497173067889)
            ·
              refine ⟨10304187961132872879800917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13738917281510497173067889 10304187961132872879800917)
              ·
                refine ⟨120752202669525854060167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10304187961132872879800917 120752202669525854060167)
                ·
                  rfl

theorem cell23_6349430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_6349430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349430 prefixEnd_6349430 := by exact prefixLift 6349430
  have htrace : WordTrace (prefixWord ++ tailWord_6349430) baseStart_6349430 baseEnd_6349430 := by
    simpa [prefixWord, tailWord_6349430, baseEnd_6349430] using wordTrace_append hprefix tailTrace_6349430
  have hstable : (prefixWord ++ tailWord_6349430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349430).length < 2 ^ (prefixWord ++ tailWord_6349430).sum := by decide
  have hdescent : baseEnd_6349430 < baseStart_6349430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349456 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_6349456 : Nat := 118140960795 + 6349456 * 2 ^ 59
def prefixEnd_6349456 : Nat := 4983230072969 + 3 ^ 40 * 6349456 * 2
def baseEnd_6349456 : Nat := 1086774274191404985966463

theorem tailTrace_6349456 : CollatzResearch.WordTrace tailWord_6349456 prefixEnd_6349456 1086774274191404985966463 := by
  unfold tailWord_6349456
  simp only [CollatzResearch.WordTrace]
  refine ⟨115791842842506393798178111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154389123790008525064237481 115791842842506393798178111)
  ·
    refine ⟨173687764263759590697267167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115791842842506393798178111 173687764263759590697267167)
    ·
      refine ⟨260531646395639386045900751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173687764263759590697267167 260531646395639386045900751)
      ·
        refine ⟨390797469593459079068851127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260531646395639386045900751 390797469593459079068851127)
        ·
          refine ⟨586196204390188618603276691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390797469593459079068851127 586196204390188618603276691)
          ·
            refine ⟨879294306585282927904915037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586196204390188618603276691 879294306585282927904915037)
            ·
              refine ⟨329735364969481097964343139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879294306585282927904915037 329735364969481097964343139)
              ·
                refine ⟨494603047454221646946514709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329735364969481097964343139 494603047454221646946514709)
                ·
                  refine ⟨23184517849416639700617877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 494603047454221646946514709 23184517849416639700617877)
                  ·
                    refine ⟨1086774274191404985966463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23184517849416639700617877 1086774274191404985966463)
                    ·
                      rfl

theorem cell23_6349456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_6349456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349456 prefixEnd_6349456 := by exact prefixLift 6349456
  have htrace : WordTrace (prefixWord ++ tailWord_6349456) baseStart_6349456 baseEnd_6349456 := by
    simpa [prefixWord, tailWord_6349456, baseEnd_6349456] using wordTrace_append hprefix tailTrace_6349456
  have hstable : (prefixWord ++ tailWord_6349456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349456).length < 2 ^ (prefixWord ++ tailWord_6349456).sum := by decide
  have hdescent : baseEnd_6349456 < baseStart_6349456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349503 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 7]
def baseStart_6349503 : Nat := 118140960795 + 6349503 * 2 ^ 59
def prefixEnd_6349503 : Nat := 4983230072969 + 3 ^ 40 * 6349503 * 2
def baseEnd_6349503 : Nat := 362260772907219586001297

theorem tailTrace_6349503 : CollatzResearch.WordTrace tailWord_6349503 prefixEnd_6349503 362260772907219586001297 := by
  unfold tailWord_6349503
  simp only [CollatzResearch.WordTrace]
  refine ⟨231585399915842514623317163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154390266610561676415544775 231585399915842514623317163)
  ·
    refine ⟨347378099873763771934975745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231585399915842514623317163 347378099873763771934975745)
    ·
      refine ⟨260533574905322828951231809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347378099873763771934975745 260533574905322828951231809)
      ·
        refine ⟨195400181178992121713423857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260533574905322828951231809 195400181178992121713423857)
        ·
          refine ⟨146550135884244091285067893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195400181178992121713423857 146550135884244091285067893)
          ·
            refine ⟨13739075239147883557975115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146550135884244091285067893 13739075239147883557975115)
            ·
              refine ⟨20608612858721825336962673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739075239147883557975115 20608612858721825336962673)
              ·
                refine ⟨15456459644041369002722005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20608612858721825336962673 15456459644041369002722005)
                ·
                  refine ⟨362260772907219586001297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15456459644041369002722005 362260772907219586001297)
                  ·
                    rfl

theorem cell23_6349503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 7].length) (baseStart_6349503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349503 prefixEnd_6349503 := by exact prefixLift 6349503
  have htrace : WordTrace (prefixWord ++ tailWord_6349503) baseStart_6349503 baseEnd_6349503 := by
    simpa [prefixWord, tailWord_6349503, baseEnd_6349503] using wordTrace_append hprefix tailTrace_6349503
  have hstable : (prefixWord ++ tailWord_6349503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349503).length < 2 ^ (prefixWord ++ tailWord_6349503).sum := by decide
  have hdescent : baseEnd_6349503 < baseStart_6349503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349553 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_6349553 : Nat := 118140960795 + 6349553 * 2 ^ 59
def prefixEnd_6349553 : Nat := 4983230072969 + 3 ^ 40 * 6349553 * 2
def baseEnd_6349553 : Nat := 3260372630197701078386443

theorem tailTrace_6349553 : CollatzResearch.WordTrace tailWord_6349553 prefixEnd_6349553 3260372630197701078386443 := by
  unfold tailWord_6349553
  simp only [CollatzResearch.WordTrace]
  refine ⟨231587223565661373162637313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154391482377107582108424875 231587223565661373162637313)
  ·
    refine ⟨173690417674246029871977985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231587223565661373162637313 173690417674246029871977985)
    ·
      refine ⟨130267813255684522403983489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173690417674246029871977985 130267813255684522403983489)
      ·
        refine ⟨97700859941763391802987617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130267813255684522403983489 97700859941763391802987617)
        ·
          refine ⟨73275644956322543852240713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97700859941763391802987617 73275644956322543852240713)
          ·
            refine ⟨54956733717241907889180535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73275644956322543852240713 54956733717241907889180535)
            ·
              refine ⟨82435100575862861833770803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54956733717241907889180535 82435100575862861833770803)
              ·
                refine ⟨123652650863794292750656205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82435100575862861833770803 123652650863794292750656205)
                ·
                  refine ⟨46369744073922859781496077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123652650863794292750656205 46369744073922859781496077)
                  ·
                    refine ⟨17388654027721072418061029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46369744073922859781496077 17388654027721072418061029)
                    ·
                      refine ⟨3260372630197701078386443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17388654027721072418061029 3260372630197701078386443)
                      ·
                        rfl

theorem cell23_6349553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_6349553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349553 prefixEnd_6349553 := by exact prefixLift 6349553
  have htrace : WordTrace (prefixWord ++ tailWord_6349553) baseStart_6349553 baseEnd_6349553 := by
    simpa [prefixWord, tailWord_6349553, baseEnd_6349553] using wordTrace_append hprefix tailTrace_6349553
  have hstable : (prefixWord ++ tailWord_6349553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349553).length < 2 ^ (prefixWord ++ tailWord_6349553).sum := by decide
  have hdescent : baseEnd_6349553 < baseStart_6349553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6349677 : Nat := 118140960795 + 6349677 * 2 ^ 59
def prefixEnd_6349677 : Nat := 4983230072969 + 3 ^ 40 * 6349677 * 2
def baseEnd_6349677 : Nat := 3260436301798858593235873

theorem tailTrace_6349677 : CollatzResearch.WordTrace tailWord_6349677 prefixEnd_6349677 3260436301798858593235873 := by
  unfold tailWord_6349677
  simp only [CollatzResearch.WordTrace]
  refine ⟨231591746217212142340151285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154394497478141428226767523 231591746217212142340151285)
  ·
    refine ⟨21711726207863638344389183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231591746217212142340151285 21711726207863638344389183)
    ·
      refine ⟨32567589311795457516583775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21711726207863638344389183 32567589311795457516583775)
      ·
        refine ⟨48851383967693186274875663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32567589311795457516583775 48851383967693186274875663)
        ·
          refine ⟨73277075951539779412313495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48851383967693186274875663 73277075951539779412313495)
          ·
            refine ⟨109915613927309669118470243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73277075951539779412313495 109915613927309669118470243)
            ·
              refine ⟨164873420890964503677705365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109915613927309669118470243 164873420890964503677705365)
              ·
                refine ⟨7728441604263961109892439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164873420890964503677705365 7728441604263961109892439)
                ·
                  refine ⟨11592662406395941664838659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728441604263961109892439 11592662406395941664838659)
                  ·
                    refine ⟨17388993609593912497257989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11592662406395941664838659 17388993609593912497257989)
                    ·
                      refine ⟨3260436301798858593235873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17388993609593912497257989 3260436301798858593235873)
                      ·
                        rfl

theorem cell23_6349677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6349677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349677 prefixEnd_6349677 := by exact prefixLift 6349677
  have htrace : WordTrace (prefixWord ++ tailWord_6349677) baseStart_6349677 baseEnd_6349677 := by
    simpa [prefixWord, tailWord_6349677, baseEnd_6349677] using wordTrace_append hprefix tailTrace_6349677
  have hstable : (prefixWord ++ tailWord_6349677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349677).length < 2 ^ (prefixWord ++ tailWord_6349677).sum := by decide
  have hdescent : baseEnd_6349677 < baseStart_6349677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349683 : List Nat := [1, 1, 1, 2, 2, 1, 4, 11]
def baseStart_6349683 : Nat := 118140960795 + 6349683 * 2 ^ 59
def prefixEnd_6349683 : Nat := 4983230072969 + 3 ^ 40 * 6349683 * 2
def baseEnd_6349683 : Nat := 120757014173436502583735

theorem tailTrace_6349683 : CollatzResearch.WordTrace tailWord_6349683 prefixEnd_6349683 120757014173436502583735 := by
  unfold tailWord_6349683
  simp only [CollatzResearch.WordTrace]
  refine ⟨231591965055190405364869703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154394643370126936909913135 231591965055190405364869703)
  ·
    refine ⟨347387947582785608047304555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231591965055190405364869703 347387947582785608047304555)
    ·
      refine ⟨521081921374178412070956833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347387947582785608047304555 521081921374178412070956833)
      ·
        refine ⟨390811441030633809053217625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521081921374178412070956833 390811441030633809053217625)
        ·
          refine ⟨293108580772975356789913219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390811441030633809053217625 293108580772975356789913219)
          ·
            refine ⟨439662871159463035184869829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293108580772975356789913219 439662871159463035184869829)
            ·
              refine ⟨82436788342399319097163093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439662871159463035184869829 82436788342399319097163093)
              ·
                refine ⟨120757014173436502583735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82436788342399319097163093 120757014173436502583735)
                ·
                  rfl

theorem cell23_6349683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 11].length) (baseStart_6349683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349683 prefixEnd_6349683 := by exact prefixLift 6349683
  have htrace : WordTrace (prefixWord ++ tailWord_6349683) baseStart_6349683 baseEnd_6349683 := by
    simpa [prefixWord, tailWord_6349683, baseEnd_6349683] using wordTrace_append hprefix tailTrace_6349683
  have hstable : (prefixWord ++ tailWord_6349683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349683).length < 2 ^ (prefixWord ++ tailWord_6349683).sum := by decide
  have hdescent : baseEnd_6349683 < baseStart_6349683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349704 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_6349704 : Nat := 118140960795 + 6349704 * 2 ^ 59
def prefixEnd_6349704 : Nat := 4983230072969 + 3 ^ 40 * 6349704 * 2
def baseEnd_6349704 : Nat := 1086816721925509995866083

theorem tailTrace_6349704 : CollatzResearch.WordTrace tailWord_6349704 prefixEnd_6349704 1086816721925509995866083 := by
  unfold tailWord_6349704
  simp only [CollatzResearch.WordTrace]
  refine ⟨115796365494057162975692083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154395153992076217300922777 115796365494057162975692083)
  ·
    refine ⟨173694548241085744463538125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115796365494057162975692083 173694548241085744463538125)
    ·
      refine ⟨65135455590407154173826797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173694548241085744463538125 65135455590407154173826797)
      ·
        refine ⟨24425795846402682815185049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65135455590407154173826797 24425795846402682815185049)
        ·
          refine ⟨18319346884802012111388787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24425795846402682815185049 18319346884802012111388787)
          ·
            refine ⟨27479020327203018167083181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18319346884802012111388787 27479020327203018167083181)
            ·
              refine ⟨10304632622701131812656193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27479020327203018167083181 10304632622701131812656193)
              ·
                refine ⟨7728474467025848859492145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10304632622701131812656193 7728474467025848859492145)
                ·
                  refine ⟨5796355850269386644619109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728474467025848859492145 5796355850269386644619109)
                  ·
                    refine ⟨1086816721925509995866083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796355850269386644619109 1086816721925509995866083)
                    ·
                      rfl

theorem cell23_6349704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_6349704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349704 prefixEnd_6349704 := by exact prefixLift 6349704
  have htrace : WordTrace (prefixWord ++ tailWord_6349704) baseStart_6349704 baseEnd_6349704 := by
    simpa [prefixWord, tailWord_6349704, baseEnd_6349704] using wordTrace_append hprefix tailTrace_6349704
  have hstable : (prefixWord ++ tailWord_6349704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349704).length < 2 ^ (prefixWord ++ tailWord_6349704).sum := by decide
  have hdescent : baseEnd_6349704 < baseStart_6349704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349714 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6349714 : Nat := 118140960795 + 6349714 * 2 ^ 59
def prefixEnd_6349714 : Nat := 4983230072969 + 3 ^ 40 * 6349714 * 2
def baseEnd_6349714 : Nat := 3260455300583074948473203

theorem tailTrace_6349714 : CollatzResearch.WordTrace tailWord_6349714 prefixEnd_6349714 3260455300583074948473203 := by
  unfold tailWord_6349714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57898273929519524414812049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154395397145385398439498797 57898273929519524414812049)
  ·
    refine ⟨43423705447139643311109037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57898273929519524414812049 43423705447139643311109037)
    ·
      refine ⟨16283889542677366241665889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43423705447139643311109037 16283889542677366241665889)
      ·
        refine ⟨12212917157008024681249417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16283889542677366241665889 12212917157008024681249417)
        ·
          refine ⟨9159687867756018510937063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12212917157008024681249417 9159687867756018510937063)
          ·
            refine ⟨13739531801634027766405595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159687867756018510937063 13739531801634027766405595)
            ·
              refine ⟨20609297702451041649608393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739531801634027766405595 20609297702451041649608393)
              ·
                refine ⟨15456973276838281237206295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20609297702451041649608393 15456973276838281237206295)
                ·
                  refine ⟨23185459915257421855809443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15456973276838281237206295 23185459915257421855809443)
                  ·
                    refine ⟨34778189872886132783714165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23185459915257421855809443 34778189872886132783714165)
                    ·
                      refine ⟨3260455300583074948473203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34778189872886132783714165 3260455300583074948473203)
                      ·
                        rfl

theorem cell23_6349714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6349714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349714 prefixEnd_6349714 := by exact prefixLift 6349714
  have htrace : WordTrace (prefixWord ++ tailWord_6349714) baseStart_6349714 baseEnd_6349714 := by
    simpa [prefixWord, tailWord_6349714, baseEnd_6349714] using wordTrace_append hprefix tailTrace_6349714
  have hstable : (prefixWord ++ tailWord_6349714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349714).length < 2 ^ (prefixWord ++ tailWord_6349714).sum := by decide
  have hdescent : baseEnd_6349714 < baseStart_6349714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349745 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6349745 : Nat := 118140960795 + 6349745 * 2 ^ 59
def prefixEnd_6349745 : Nat := 4983230072969 + 3 ^ 40 * 6349745 * 2
def baseEnd_6349745 : Nat := 3260471218483364327185561

theorem tailTrace_6349745 : CollatzResearch.WordTrace tailWord_6349745 prefixEnd_6349745 3260471218483364327185561 := by
  unfold tailWord_6349745
  simp only [CollatzResearch.WordTrace]
  refine ⟨231594226380965789953626689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154396150920643859969084459 231594226380965789953626689)
  ·
    refine ⟨173695669785724342465220017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231594226380965789953626689 173695669785724342465220017)
    ·
      refine ⟨130271752339293256848915013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173695669785724342465220017 130271752339293256848915013)
      ·
        refine ⟨24425953563617485659171565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130271752339293256848915013 24425953563617485659171565)
        ·
          refine ⟨9159732586356557122189337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24425953563617485659171565 9159732586356557122189337)
          ·
            refine ⟨6869799439767417841642003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159732586356557122189337 6869799439767417841642003)
            ·
              refine ⟨10304699159651126762463005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869799439767417841642003 10304699159651126762463005)
              ·
                refine ⟨3864262184869172535923627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10304699159651126762463005 3864262184869172535923627)
                ·
                  refine ⟨5796393277303758803885441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864262184869172535923627 5796393277303758803885441)
                  ·
                    refine ⟨4347294957977819102914081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796393277303758803885441 4347294957977819102914081)
                    ·
                      refine ⟨3260471218483364327185561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347294957977819102914081 3260471218483364327185561)
                      ·
                        rfl

theorem cell23_6349745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6349745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349745 prefixEnd_6349745 := by exact prefixLift 6349745
  have htrace : WordTrace (prefixWord ++ tailWord_6349745) baseStart_6349745 baseEnd_6349745 := by
    simpa [prefixWord, tailWord_6349745, baseEnd_6349745] using wordTrace_append hprefix tailTrace_6349745
  have hstable : (prefixWord ++ tailWord_6349745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349745).length < 2 ^ (prefixWord ++ tailWord_6349745).sum := by decide
  have hdescent : baseEnd_6349745 < baseStart_6349745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349754 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_6349754 : Nat := 118140960795 + 6349754 * 2 ^ 59
def prefixEnd_6349754 : Nat := 4983230072969 + 3 ^ 40 * 6349754 * 2
def baseEnd_6349754 : Nat := 3260475839809254791973019

theorem tailTrace_6349754 : CollatzResearch.WordTrace tailWord_6349754 prefixEnd_6349754 3260475839809254791973019 := by
  unfold tailWord_6349754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57898638659483296122676079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154396369758622122993802877 57898638659483296122676079)
  ·
    refine ⟨86847957989224944184014119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57898638659483296122676079 86847957989224944184014119)
    ·
      refine ⟨130271936983837416276021179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86847957989224944184014119 130271936983837416276021179)
      ·
        refine ⟨195407905475756124414031769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130271936983837416276021179 195407905475756124414031769)
        ·
          refine ⟨146555929106817093310523827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195407905475756124414031769 146555929106817093310523827)
          ·
            refine ⟨219833893660225639965785741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146555929106817093310523827 219833893660225639965785741)
            ·
              refine ⟨82437710122584614987169653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219833893660225639965785741 82437710122584614987169653)
              ·
                refine ⟨7728535323992307655047155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82437710122584614987169653 7728535323992307655047155)
                ·
                  refine ⟨11592802985988461482570733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728535323992307655047155 11592802985988461482570733)
                  ·
                    refine ⟨4347301119745673055964025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11592802985988461482570733 4347301119745673055964025)
                    ·
                      refine ⟨3260475839809254791973019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347301119745673055964025 3260475839809254791973019)
                      ·
                        rfl

theorem cell23_6349754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_6349754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349754 prefixEnd_6349754 := by exact prefixLift 6349754
  have htrace : WordTrace (prefixWord ++ tailWord_6349754) baseStart_6349754 baseEnd_6349754 := by
    simpa [prefixWord, tailWord_6349754, baseEnd_6349754] using wordTrace_append hprefix tailTrace_6349754
  have hstable : (prefixWord ++ tailWord_6349754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349754).length < 2 ^ (prefixWord ++ tailWord_6349754).sum := by decide
  have hdescent : baseEnd_6349754 < baseStart_6349754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349770 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6349770 : Nat := 118140960795 + 6349770 * 2 ^ 59
def prefixEnd_6349770 : Nat := 4983230072969 + 3 ^ 40 * 6349770 * 2
def baseEnd_6349770 : Nat := 3260484055499726729372945

theorem tailTrace_6349770 : CollatzResearch.WordTrace tailWord_6349770 prefixEnd_6349770 3260484055499726729372945 := by
  unfold tailWord_6349770
  simp only [CollatzResearch.WordTrace]
  refine ⟨57898784551468804805821691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154396758803916812815524509 57898784551468804805821691)
  ·
    refine ⟨86848176827203207208732537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57898784551468804805821691 86848176827203207208732537)
    ·
      refine ⟨65136132620402405406549403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86848176827203207208732537 65136132620402405406549403)
      ·
        refine ⟨97704198930603608109824105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65136132620402405406549403 97704198930603608109824105)
        ·
          refine ⟨73278149197952706082368079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97704198930603608109824105 73278149197952706082368079)
          ·
            refine ⟨109917223796929059123552119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73278149197952706082368079 109917223796929059123552119)
            ·
              refine ⟨164875835695393588685328179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109917223796929059123552119 164875835695393588685328179)
              ·
                refine ⟨247313753543090383027992269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164875835695393588685328179 247313753543090383027992269)
                ·
                  refine ⟨92742657578658893635497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247313753543090383027992269 92742657578658893635497101)
                  ·
                    refine ⟨34778496591997085113311413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92742657578658893635497101 34778496591997085113311413)
                    ·
                      refine ⟨3260484055499726729372945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34778496591997085113311413 3260484055499726729372945)
                      ·
                        rfl

theorem cell23_6349770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6349770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349770 prefixEnd_6349770 := by exact prefixLift 6349770
  have htrace : WordTrace (prefixWord ++ tailWord_6349770) baseStart_6349770 baseEnd_6349770 := by
    simpa [prefixWord, tailWord_6349770, baseEnd_6349770] using wordTrace_append hprefix tailTrace_6349770
  have hstable : (prefixWord ++ tailWord_6349770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349770).length < 2 ^ (prefixWord ++ tailWord_6349770).sum := by decide
  have hdescent : baseEnd_6349770 < baseStart_6349770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349778 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6349778 : Nat := 118140960795 + 6349778 * 2 ^ 59
def prefixEnd_6349778 : Nat := 4983230072969 + 3 ^ 40 * 6349778 * 2
def baseEnd_6349778 : Nat := 3260488163344962698072909

theorem tailTrace_6349778 : CollatzResearch.WordTrace tailWord_6349778 prefixEnd_6349778 3260488163344962698072909 := by
  unfold tailWord_6349778
  simp only [CollatzResearch.WordTrace]
  refine ⟨57898857497461559147394497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154396953326564157726385325 57898857497461559147394497)
  ·
    refine ⟨43424143123096169360545873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57898857497461559147394497 43424143123096169360545873)
    ·
      refine ⟨32568107342322127020409405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43424143123096169360545873 32568107342322127020409405)
      ·
        refine ⟨12213040253370797632653527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32568107342322127020409405 12213040253370797632653527)
        ·
          refine ⟨18319560380056196448980291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213040253370797632653527 18319560380056196448980291)
          ·
            refine ⟨27479340570084294673470437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18319560380056196448980291 27479340570084294673470437)
            ·
              refine ⟨5152376356890805251275707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27479340570084294673470437 5152376356890805251275707)
              ·
                refine ⟨7728564535336207876913561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152376356890805251275707 7728564535336207876913561)
                ·
                  refine ⟨5796423401502155907685171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728564535336207876913561 5796423401502155907685171)
                  ·
                    refine ⟨8694635102253233861527757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796423401502155907685171 8694635102253233861527757)
                    ·
                      refine ⟨3260488163344962698072909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8694635102253233861527757 3260488163344962698072909)
                      ·
                        rfl

theorem cell23_6349778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6349778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349778 prefixEnd_6349778 := by exact prefixLift 6349778
  have htrace : WordTrace (prefixWord ++ tailWord_6349778) baseStart_6349778 baseEnd_6349778 := by
    simpa [prefixWord, tailWord_6349778, baseEnd_6349778] using wordTrace_append hprefix tailTrace_6349778
  have hstable : (prefixWord ++ tailWord_6349778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349778).length < 2 ^ (prefixWord ++ tailWord_6349778).sum := by decide
  have hdescent : baseEnd_6349778 < baseStart_6349778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349817 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_6349817 : Nat := 118140960795 + 6349817 * 2 ^ 59
def prefixEnd_6349817 : Nat := 4983230072969 + 3 ^ 40 * 6349817 * 2
def baseEnd_6349817 : Nat := 3260508189090488045485229

theorem tailTrace_6349817 : CollatzResearch.WordTrace tailWord_6349817 prefixEnd_6349817 3260508189090488045485229 := by
  unfold tailWord_6349817
  simp only [CollatzResearch.WordTrace]
  refine ⟨231596852436704946250247705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154397901624469964166831803 231596852436704946250247705)
  ·
    refine ⟨173697639327528709687685779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231596852436704946250247705 173697639327528709687685779)
    ·
      refine ⟨260546458991293064531528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173697639327528709687685779 260546458991293064531528669)
      ·
        refine ⟨97704922121734899199323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260546458991293064531528669 97704922121734899199323251)
        ·
          refine ⟨146557383182602348798984877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97704922121734899199323251 146557383182602348798984877)
          ·
            refine ⟨54959018693475880799619329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146557383182602348798984877 54959018693475880799619329)
            ·
              refine ⟨41219264020106910599714497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54959018693475880799619329 41219264020106910599714497)
              ·
                refine ⟨30914448015080182949785873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41219264020106910599714497 30914448015080182949785873)
                ·
                  refine ⟨23185836011310137212339405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30914448015080182949785873 23185836011310137212339405)
                  ·
                    refine ⟨8694688504241301454627277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23185836011310137212339405 8694688504241301454627277)
                    ·
                      refine ⟨3260508189090488045485229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8694688504241301454627277 3260508189090488045485229)
                      ·
                        rfl

theorem cell23_6349817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_6349817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349817 prefixEnd_6349817 := by exact prefixLift 6349817
  have htrace : WordTrace (prefixWord ++ tailWord_6349817) baseStart_6349817 baseEnd_6349817 := by
    simpa [prefixWord, tailWord_6349817, baseEnd_6349817] using wordTrace_append hprefix tailTrace_6349817
  have hstable : (prefixWord ++ tailWord_6349817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349817).length < 2 ^ (prefixWord ++ tailWord_6349817).sum := by decide
  have hdescent : baseEnd_6349817 < baseStart_6349817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349834 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_6349834 : Nat := 118140960795 + 6349834 * 2 ^ 59
def prefixEnd_6349834 : Nat := 4983230072969 + 3 ^ 40 * 6349834 * 2
def baseEnd_6349834 : Nat := 3260516918261614478972651

theorem tailTrace_6349834 : CollatzResearch.WordTrace tailWord_6349834 prefixEnd_6349834 3260516918261614478972651 := by
  unfold tailWord_6349834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57899368119410839538404139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154398314985095572102411037 57899368119410839538404139)
  ·
    refine ⟨86849052179116259307606209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57899368119410839538404139 86849052179116259307606209)
    ·
      refine ⟨65136789134337194480704657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86849052179116259307606209 65136789134337194480704657)
      ·
        refine ⟨48852591850752895860528493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65136789134337194480704657 48852591850752895860528493)
        ·
          refine ⟨18319721944032335947698185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48852591850752895860528493 18319721944032335947698185)
          ·
            refine ⟨13739791458024251960773639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18319721944032335947698185 13739791458024251960773639)
            ·
              refine ⟨20609687187036377941160459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739791458024251960773639 20609687187036377941160459)
              ·
                refine ⟨30914530780554566911740689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20609687187036377941160459 30914530780554566911740689)
                ·
                  refine ⟨23185898085415925183805517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30914530780554566911740689 23185898085415925183805517)
                  ·
                    refine ⟨8694711782030971943927069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23185898085415925183805517 8694711782030971943927069)
                    ·
                      refine ⟨3260516918261614478972651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8694711782030971943927069 3260516918261614478972651)
                      ·
                        rfl

theorem cell23_6349834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_6349834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349834 prefixEnd_6349834 := by exact prefixLift 6349834
  have htrace : WordTrace (prefixWord ++ tailWord_6349834) baseStart_6349834 baseEnd_6349834 := by
    simpa [prefixWord, tailWord_6349834, baseEnd_6349834] using wordTrace_append hprefix tailTrace_6349834
  have hstable : (prefixWord ++ tailWord_6349834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349834).length < 2 ^ (prefixWord ++ tailWord_6349834).sum := by decide
  have hdescent : baseEnd_6349834 < baseStart_6349834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349867 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 5, 4]
def baseStart_6349867 : Nat := 118140960795 + 6349867 * 2 ^ 59
def prefixEnd_6349867 : Nat := 4983230072969 + 3 ^ 40 * 6349867 * 2
def baseEnd_6349867 : Nat := 1086844621041070949953333

theorem tailTrace_6349867 : CollatzResearch.WordTrace tailWord_6349867 prefixEnd_6349867 1086844621041070949953333 := by
  unfold tailWord_6349867
  simp only [CollatzResearch.WordTrace]
  refine ⟨231598676086523804789567855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154399117391015869859711903 231598676086523804789567855)
  ·
    refine ⟨347398014129785707184351783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231598676086523804789567855 347398014129785707184351783)
    ·
      refine ⟨521097021194678560776527675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347398014129785707184351783 521097021194678560776527675)
      ·
        refine ⟨781645531792017841164791513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521097021194678560776527675 781645531792017841164791513)
        ·
          refine ⟨586234148844013380873593635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781645531792017841164791513 586234148844013380873593635)
          ·
            refine ⟨879351223266020071310390453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586234148844013380873593635 879351223266020071310390453)
            ·
              refine ⟨82439177181189381685349105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 879351223266020071310390453 82439177181189381685349105)
              ·
                refine ⟨61829382885892036264011829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82439177181189381685349105 61829382885892036264011829)
                ·
                  refine ⟨5796504645552378399751109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61829382885892036264011829 5796504645552378399751109)
                  ·
                    refine ⟨1086844621041070949953333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796504645552378399751109 1086844621041070949953333)
                    ·
                      rfl

theorem cell23_6349867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 4].length) (baseStart_6349867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349867 prefixEnd_6349867 := by exact prefixLift 6349867
  have htrace : WordTrace (prefixWord ++ tailWord_6349867) baseStart_6349867 baseEnd_6349867 := by
    simpa [prefixWord, tailWord_6349867, baseEnd_6349867] using wordTrace_append hprefix tailTrace_6349867
  have hstable : (prefixWord ++ tailWord_6349867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349867).length < 2 ^ (prefixWord ++ tailWord_6349867).sum := by decide
  have hdescent : baseEnd_6349867 < baseStart_6349867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349874 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_6349874 : Nat := 118140960795 + 6349874 * 2 ^ 59
def prefixEnd_6349874 : Nat := 4983230072969 + 3 ^ 40 * 6349874 * 2
def baseEnd_6349874 : Nat := 3260537457487794322472467

theorem tailTrace_6349874 : CollatzResearch.WordTrace tailWord_6349874 prefixEnd_6349874 3260537457487794322472467 := by
  unfold tailWord_6349874
  simp only [CollatzResearch.WordTrace]
  refine ⟨57899732849374611246268169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154399287598332296656715117 57899732849374611246268169)
  ·
    refine ⟨43424799637030958434701127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57899732849374611246268169 43424799637030958434701127)
    ·
      refine ⟨65137199455546437652051691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43424799637030958434701127 65137199455546437652051691)
      ·
        refine ⟨97705799183319656478077537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65137199455546437652051691 97705799183319656478077537)
        ·
          refine ⟨73279349387489742358558153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97705799183319656478077537 73279349387489742358558153)
          ·
            refine ⟨54959512040617306768918615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73279349387489742358558153 54959512040617306768918615)
            ·
              refine ⟨82439268060925960153377923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54959512040617306768918615 82439268060925960153377923)
              ·
                refine ⟨123658902091388940230066885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82439268060925960153377923 123658902091388940230066885)
                ·
                  refine ⟨23186044142135426293137541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123658902091388940230066885 23186044142135426293137541)
                  ·
                    refine ⟨4347383276650392429963289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23186044142135426293137541 4347383276650392429963289)
                    ·
                      refine ⟨3260537457487794322472467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347383276650392429963289 3260537457487794322472467)
                      ·
                        rfl

theorem cell23_6349874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_6349874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349874 prefixEnd_6349874 := by exact prefixLift 6349874
  have htrace : WordTrace (prefixWord ++ tailWord_6349874) baseStart_6349874 baseEnd_6349874 := by
    simpa [prefixWord, tailWord_6349874, baseEnd_6349874] using wordTrace_append hprefix tailTrace_6349874
  have hstable : (prefixWord ++ tailWord_6349874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349874).length < 2 ^ (prefixWord ++ tailWord_6349874).sum := by decide
  have hdescent : baseEnd_6349874 < baseStart_6349874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349884 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_6349884 : Nat := 118140960795 + 6349884 * 2 ^ 59
def prefixEnd_6349884 : Nat := 4983230072969 + 3 ^ 40 * 6349884 * 2
def baseEnd_6349884 : Nat := 1086847530764779761115807

theorem tailTrace_6349884 : CollatzResearch.WordTrace tailWord_6349884 prefixEnd_6349884 1086847530764779761115807 := by
  unfold tailWord_6349884
  simp only [CollatzResearch.WordTrace]
  refine ⟨115799648063731108346468353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154399530751641477795291137 115799648063731108346468353)
  ·
    refine ⟨86849736047798331259851265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115799648063731108346468353 86849736047798331259851265)
    ·
      refine ⟨65137302035848748444888449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86849736047798331259851265 65137302035848748444888449)
      ·
        refine ⟨48852976526886561333666337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65137302035848748444888449 48852976526886561333666337)
        ·
          refine ⟨36639732395164921000249753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48852976526886561333666337 36639732395164921000249753)
          ·
            refine ⟨27479799296373690750187315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36639732395164921000249753 27479799296373690750187315)
            ·
              refine ⟨41219698944560536125280973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27479799296373690750187315 41219698944560536125280973)
              ·
                refine ⟨15457387104210201046980365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41219698944560536125280973 15457387104210201046980365)
                ·
                  refine ⟨5796520164078825392617637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15457387104210201046980365 5796520164078825392617637)
                  ·
                    refine ⟨1086847530764779761115807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796520164078825392617637 1086847530764779761115807)
                    ·
                      rfl

theorem cell23_6349884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_6349884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349884 prefixEnd_6349884 := by exact prefixLift 6349884
  have htrace : WordTrace (prefixWord ++ tailWord_6349884) baseStart_6349884 baseEnd_6349884 := by
    simpa [prefixWord, tailWord_6349884, baseEnd_6349884] using wordTrace_append hprefix tailTrace_6349884
  have hstable : (prefixWord ++ tailWord_6349884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349884).length < 2 ^ (prefixWord ++ tailWord_6349884).sum := by decide
  have hdescent : baseEnd_6349884 < baseStart_6349884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349901 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_6349901 : Nat := 118140960795 + 6349901 * 2 ^ 59
def prefixEnd_6349901 : Nat := 4983230072969 + 3 ^ 40 * 6349901 * 2
def baseEnd_6349901 : Nat := 1086850440488488572278281

theorem tailTrace_6349901 : CollatzResearch.WordTrace tailWord_6349901 prefixEnd_6349901 1086850440488488572278281 := by
  unfold tailWord_6349901
  simp only [CollatzResearch.WordTrace]
  refine ⟨231599916168400628596305557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154399944112267085730870371 231599916168400628596305557)
  ·
    refine ⟨10856246070393779465451823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231599916168400628596305557 10856246070393779465451823)
    ·
      refine ⟨16284369105590669198177735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856246070393779465451823 16284369105590669198177735)
      ·
        refine ⟨24426553658386003797266603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16284369105590669198177735 24426553658386003797266603)
        ·
          refine ⟨36639830487579005695899905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24426553658386003797266603 36639830487579005695899905)
          ·
            refine ⟨27479872865684254271924929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36639830487579005695899905 27479872865684254271924929)
            ·
              refine ⟨20609904649263190703943697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27479872865684254271924929 20609904649263190703943697)
              ·
                refine ⟨15457428486947393027957773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20609904649263190703943697 15457428486947393027957773)
                ·
                  refine ⟨5796535682605272385484165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15457428486947393027957773 5796535682605272385484165)
                  ·
                    refine ⟨1086850440488488572278281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796535682605272385484165 1086850440488488572278281)
                    ·
                      rfl

theorem cell23_6349901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_6349901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349901 prefixEnd_6349901 := by exact prefixLift 6349901
  have htrace : WordTrace (prefixWord ++ tailWord_6349901) baseStart_6349901 baseEnd_6349901 := by
    simpa [prefixWord, tailWord_6349901, baseEnd_6349901] using wordTrace_append hprefix tailTrace_6349901
  have hstable : (prefixWord ++ tailWord_6349901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349901).length < 2 ^ (prefixWord ++ tailWord_6349901).sum := by decide
  have hdescent : baseEnd_6349901 < baseStart_6349901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349928 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6349928 : Nat := 118140960795 + 6349928 * 2 ^ 59
def prefixEnd_6349928 : Nat := 4983230072969 + 3 ^ 40 * 6349928 * 2
def baseEnd_6349928 : Nat := 3260565185443137111197219

theorem tailTrace_6349928 : CollatzResearch.WordTrace tailWord_6349928 prefixEnd_6349928 3260565185443137111197219 := by
  unfold tailWord_6349928
  simp only [CollatzResearch.WordTrace]
  refine ⟨115800450469651406103769219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154400600626201874805025625 115800450469651406103769219)
  ·
    refine ⟨173700675704477109155653829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115800450469651406103769219 173700675704477109155653829)
    ·
      refine ⟨32568876694589457966685093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173700675704477109155653829 32568876694589457966685093)
      ·
        refine ⟨6106664380235523368753455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32568876694589457966685093 6106664380235523368753455)
        ·
          refine ⟨9159996570353285053130183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106664380235523368753455 9159996570353285053130183)
          ·
            refine ⟨13739994855529927579695275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159996570353285053130183 13739994855529927579695275)
            ·
              refine ⟨20609992283294891369542913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739994855529927579695275 20609992283294891369542913)
              ·
                refine ⟨15457494212471168527157185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20609992283294891369542913 15457494212471168527157185)
                ·
                  refine ⟨11593120659353376395367889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15457494212471168527157185 11593120659353376395367889)
                  ·
                    refine ⟨8694840494515032296525917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11593120659353376395367889 8694840494515032296525917)
                    ·
                      refine ⟨3260565185443137111197219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8694840494515032296525917 3260565185443137111197219)
                      ·
                        rfl

theorem cell23_6349928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6349928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349928 prefixEnd_6349928 := by exact prefixLift 6349928
  have htrace : WordTrace (prefixWord ++ tailWord_6349928) baseStart_6349928 baseEnd_6349928 := by
    simpa [prefixWord, tailWord_6349928, baseEnd_6349928] using wordTrace_append hprefix tailTrace_6349928
  have hstable : (prefixWord ++ tailWord_6349928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349928).length < 2 ^ (prefixWord ++ tailWord_6349928).sum := by decide
  have hdescent : baseEnd_6349928 < baseStart_6349928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349961 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 1, 5]
def baseStart_6349961 : Nat := 118140960795 + 6349961 * 2 ^ 59
def prefixEnd_6349961 : Nat := 4983230072969 + 3 ^ 40 * 6349961 * 2
def baseEnd_6349961 : Nat := 1086860710101578494028189

theorem tailTrace_6349961 : CollatzResearch.WordTrace tailWord_6349961 prefixEnd_6349961 1086860710101578494028189 := by
  unfold tailWord_6349961
  simp only [CollatzResearch.WordTrace]
  refine ⟨231602104548183258843489737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154401403032122172562326491 231602104548183258843489737)
  ·
    refine ⟨173701578411137444132617303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231602104548183258843489737 173701578411137444132617303)
    ·
      refine ⟨260552367616706166198925955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173701578411137444132617303 260552367616706166198925955)
      ·
        refine ⟨390828551425059249298388933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260552367616706166198925955 390828551425059249298388933)
        ·
          refine ⟨73280353392198609243447925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390828551425059249298388933 73280353392198609243447925)
          ·
            refine ⟨6870033130518619616573243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73280353392198609243447925 6870033130518619616573243)
            ·
              refine ⟨10305049695777929424859865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870033130518619616573243 10305049695777929424859865)
              ·
                refine ⟨7728787271833447068644899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305049695777929424859865 7728787271833447068644899)
                ·
                  refine ⟨11593180907750170602967349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728787271833447068644899 11593180907750170602967349)
                  ·
                    refine ⟨1086860710101578494028189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11593180907750170602967349 1086860710101578494028189)
                    ·
                      rfl

theorem cell23_6349961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_6349961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349961 prefixEnd_6349961 := by exact prefixLift 6349961
  have htrace : WordTrace (prefixWord ++ tailWord_6349961) baseStart_6349961 baseEnd_6349961 := by
    simpa [prefixWord, tailWord_6349961, baseEnd_6349961] using wordTrace_append hprefix tailTrace_6349961
  have hstable : (prefixWord ++ tailWord_6349961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349961).length < 2 ^ (prefixWord ++ tailWord_6349961).sum := by decide
  have hdescent : baseEnd_6349961 < baseStart_6349961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349964 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6349964 : Nat := 118140960795 + 6349964 * 2 ^ 59
def prefixEnd_6349964 : Nat := 4983230072969 + 3 ^ 40 * 6349964 * 2
def baseEnd_6349964 : Nat := 3260583670746698970347053

theorem tailTrace_6349964 : CollatzResearch.WordTrace tailWord_6349964 prefixEnd_6349964 3260583670746698970347053 := by
  unfold tailWord_6349964
  simp only [CollatzResearch.WordTrace]
  refine ⟨115801106983586195177924473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154401475978114926903899297 115801106983586195177924473)
  ·
    refine ⟨86850830237689646383443355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115801106983586195177924473 86850830237689646383443355)
    ·
      refine ⟨130276245356534469575165033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86850830237689646383443355 130276245356534469575165033)
      ·
        refine ⟨97707184017400852181373775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130276245356534469575165033 97707184017400852181373775)
        ·
          refine ⟨146560776026101278272060663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97707184017400852181373775 146560776026101278272060663)
          ·
            refine ⟨219841164039151917408090995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146560776026101278272060663 219841164039151917408090995)
            ·
              refine ⟨329761746058727876112136493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219841164039151917408090995 329761746058727876112136493)
              ·
                refine ⟨123660654772022953542051185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329761746058727876112136493 123660654772022953542051185)
                ·
                  refine ⟨92745491079017215156538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123660654772022953542051185 92745491079017215156538389)
                  ·
                    refine ⟨4347444894328931960462737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92745491079017215156538389 4347444894328931960462737)
                    ·
                      refine ⟨3260583670746698970347053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347444894328931960462737 3260583670746698970347053)
                      ·
                        rfl

theorem cell23_6349964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6349964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349964 prefixEnd_6349964 := by exact prefixLift 6349964
  have htrace : WordTrace (prefixWord ++ tailWord_6349964) baseStart_6349964 baseEnd_6349964 := by
    simpa [prefixWord, tailWord_6349964, baseEnd_6349964] using wordTrace_append hprefix tailTrace_6349964
  have hstable : (prefixWord ++ tailWord_6349964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349964).length < 2 ^ (prefixWord ++ tailWord_6349964).sum := by decide
  have hdescent : baseEnd_6349964 < baseStart_6349964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6349978 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_6349978 : Nat := 118140960795 + 6349978 * 2 ^ 59
def prefixEnd_6349978 : Nat := 4983230072969 + 3 ^ 40 * 6349978 * 2
def baseEnd_6349978 : Nat := 1086863619825287305190663

theorem tailTrace_6349978 : CollatzResearch.WordTrace tailWord_6349978 prefixEnd_6349978 1086863619825287305190663 := by
  unfold tailWord_6349978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900681147280417686714647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154401816392747780497905725 57900681147280417686714647)
  ·
    refine ⟨86851021720920626530071971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57900681147280417686714647 86851021720920626530071971)
    ·
      refine ⟨130276532581380939795107957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86851021720920626530071971 130276532581380939795107957)
      ·
        refine ⟨12213424929504463105791371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130276532581380939795107957 12213424929504463105791371)
        ·
          refine ⟨18320137394256694658687057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213424929504463105791371 18320137394256694658687057)
          ·
            refine ⟨13740103045692520994015293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18320137394256694658687057 13740103045692520994015293)
            ·
              refine ⟨5152538642134695372755735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13740103045692520994015293 5152538642134695372755735)
              ·
                refine ⟨7728807963202043059133603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152538642134695372755735 7728807963202043059133603)
                ·
                  refine ⟨11593211944803064588700405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728807963202043059133603 11593211944803064588700405)
                  ·
                    refine ⟨1086863619825287305190663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11593211944803064588700405 1086863619825287305190663)
                    ·
                      rfl

theorem cell23_6349978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_6349978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6349978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6349978 prefixEnd_6349978 := by exact prefixLift 6349978
  have htrace : WordTrace (prefixWord ++ tailWord_6349978) baseStart_6349978 baseEnd_6349978 := by
    simpa [prefixWord, tailWord_6349978, baseEnd_6349978] using wordTrace_append hprefix tailTrace_6349978
  have hstable : (prefixWord ++ tailWord_6349978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6349978).length < 2 ^ (prefixWord ++ tailWord_6349978).sum := by decide
  have hdescent : baseEnd_6349978 < baseStart_6349978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6349978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350001 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6350001 : Nat := 118140960795 + 6350001 * 2 ^ 59
def prefixEnd_6350001 : Nat := 4983230072969 + 3 ^ 40 * 6350001 * 2
def baseEnd_6350001 : Nat := 3260602669530915325584383

theorem tailTrace_6350001 : CollatzResearch.WordTrace tailWord_6350001 prefixEnd_6350001 3260602669530915325584383 := by
  unfold tailWord_6350001
  simp only [CollatzResearch.WordTrace]
  refine ⟨231603563468038345674945857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154402375645358897116630571 231603563468038345674945857)
  ·
    refine ⟨173702672601028759256209393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231603563468038345674945857 173702672601028759256209393)
    ·
      refine ⟨130277004450771569442157045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173702672601028759256209393 130277004450771569442157045)
      ·
        refine ⟨12213469167259834635202223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130277004450771569442157045 12213469167259834635202223)
        ·
          refine ⟨18320203750889751952803335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213469167259834635202223 18320203750889751952803335)
          ·
            refine ⟨27480305626334627929205003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320203750889751952803335 27480305626334627929205003)
            ·
              refine ⟨41220458439501941893807505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27480305626334627929205003 41220458439501941893807505)
              ·
                refine ⟨30915343829626456420355629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41220458439501941893807505 30915343829626456420355629)
                ·
                  refine ⟨11593253936109921157633361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30915343829626456420355629 11593253936109921157633361)
                  ·
                    refine ⟨8694940452082440868225021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11593253936109921157633361 8694940452082440868225021)
                    ·
                      refine ⟨3260602669530915325584383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8694940452082440868225021 3260602669530915325584383)
                      ·
                        rfl

theorem cell23_6350001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6350001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350001 prefixEnd_6350001 := by exact prefixLift 6350001
  have htrace : WordTrace (prefixWord ++ tailWord_6350001) baseStart_6350001 baseEnd_6350001 := by
    simpa [prefixWord, tailWord_6350001, baseEnd_6350001] using wordTrace_append hprefix tailTrace_6350001
  have hstable : (prefixWord ++ tailWord_6350001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350001).length < 2 ^ (prefixWord ++ tailWord_6350001).sum := by decide
  have hdescent : baseEnd_6350001 < baseStart_6350001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350029 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6350029 : Nat := 118140960795 + 6350029 * 2 ^ 59
def prefixEnd_6350029 : Nat := 4983230072969 + 3 ^ 40 * 6350029 * 2
def baseEnd_6350029 : Nat := 1086872348996413738678085

theorem tailTrace_6350029 : CollatzResearch.WordTrace tailWord_6350029 prefixEnd_6350029 1086872348996413738678085 := by
  unfold tailWord_6350029
  simp only [CollatzResearch.WordTrace]
  refine ⟨231604584711936906456965141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154403056474624604304643427 231604584711936906456965141)
  ·
    refine ⟨10856464908372042490170241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231604584711936906456965141 10856464908372042490170241)
    ·
      refine ⟨8142348681279031867627681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10856464908372042490170241 8142348681279031867627681)
      ·
        refine ⟨6106761510959273900720761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8142348681279031867627681 6106761510959273900720761)
        ·
          refine ⟨4580071133219455425540571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6106761510959273900720761 4580071133219455425540571)
          ·
            refine ⟨6870106699829183138310857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580071133219455425540571 6870106699829183138310857)
            ·
              refine ⟨5152580024871887353733143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6870106699829183138310857 5152580024871887353733143)
              ·
                refine ⟨7728870037307831030599715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152580024871887353733143 7728870037307831030599715)
                ·
                  refine ⟨11593305055961746545899573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728870037307831030599715 11593305055961746545899573)
                  ·
                    refine ⟨1086872348996413738678085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11593305055961746545899573 1086872348996413738678085)
                    ·
                      rfl

theorem cell23_6350029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6350029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350029 prefixEnd_6350029 := by exact prefixLift 6350029
  have htrace : WordTrace (prefixWord ++ tailWord_6350029) baseStart_6350029 baseEnd_6350029 := by
    simpa [prefixWord, tailWord_6350029, baseEnd_6350029] using wordTrace_append hprefix tailTrace_6350029
  have hstable : (prefixWord ++ tailWord_6350029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350029).length < 2 ^ (prefixWord ++ tailWord_6350029).sum := by decide
  have hdescent : baseEnd_6350029 < baseStart_6350029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350048 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3]
def baseStart_6350048 : Nat := 118140960795 + 6350048 * 2 ^ 59
def prefixEnd_6350048 : Nat := 4983230072969 + 3 ^ 40 * 6350048 * 2
def baseEnd_6350048 : Nat := 3260626803121676641696667

theorem tailTrace_6350048 : CollatzResearch.WordTrace tailWord_6350048 prefixEnd_6350048 3260626803121676641696667 := by
  unfold tailWord_6350048
  simp only [CollatzResearch.WordTrace]
  refine ⟨115802638849434036350953399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154403518465912048467937865 115802638849434036350953399)
  ·
    refine ⟨173703958274151054526430099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115802638849434036350953399 173703958274151054526430099)
    ·
      refine ⟨260555937411226581789645149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173703958274151054526430099 260555937411226581789645149)
      ·
        refine ⟨97708476529209968171116931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260555937411226581789645149 97708476529209968171116931)
        ·
          refine ⟨146562714793814952256675397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97708476529209968171116931 146562714793814952256675397)
          ·
            refine ⟨27480509023840303548126637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146562714793814952256675397 27480509023840303548126637)
            ·
              refine ⟨10305190883940113830547489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27480509023840303548126637 10305190883940113830547489)
              ·
                refine ⟨7728893162955085372910617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305190883940113830547489 7728893162955085372910617)
                ·
                  refine ⟨5796669872216314029682963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728893162955085372910617 5796669872216314029682963)
                  ·
                    refine ⟨8695004808324471044524445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796669872216314029682963 8695004808324471044524445)
                    ·
                      refine ⟨3260626803121676641696667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8695004808324471044524445 3260626803121676641696667)
                      ·
                        rfl

theorem cell23_6350048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_6350048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350048 prefixEnd_6350048 := by exact prefixLift 6350048
  have htrace : WordTrace (prefixWord ++ tailWord_6350048) baseStart_6350048 baseEnd_6350048 := by
    simpa [prefixWord, tailWord_6350048, baseEnd_6350048] using wordTrace_append hprefix tailTrace_6350048
  have hstable : (prefixWord ++ tailWord_6350048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350048).length < 2 ^ (prefixWord ++ tailWord_6350048).sum := by decide
  have hdescent : baseEnd_6350048 < baseStart_6350048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350074 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_6350074 : Nat := 118140960795 + 6350074 * 2 ^ 59
def prefixEnd_6350074 : Nat := 4983230072969 + 3 ^ 40 * 6350074 * 2
def baseEnd_6350074 : Nat := 3260640153618693539971547

theorem tailTrace_6350074 : CollatzResearch.WordTrace tailWord_6350074 prefixEnd_6350074 3260640153618693539971547 := by
  unfold tailWord_6350074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57901556499193469785588319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154404150664515919428235517 57901556499193469785588319)
  ·
    refine ⟨86852334748790204678382479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57901556499193469785588319 86852334748790204678382479)
    ·
      refine ⟨130278502123185307017573719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86852334748790204678382479 130278502123185307017573719)
      ·
        refine ⟨195417753184777960526360579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130278502123185307017573719 195417753184777960526360579)
        ·
          refine ⟨293126629777166940789540869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195417753184777960526360579 293126629777166940789540869)
          ·
            refine ⟨54961243083218801398038913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293126629777166940789540869 54961243083218801398038913)
            ·
              refine ⟨41220932312414101048529185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54961243083218801398038913 41220932312414101048529185)
              ·
                refine ⟨30915699234310575786396889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41220932312414101048529185 30915699234310575786396889)
                ·
                  refine ⟨23186774425732931839797667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30915699234310575786396889 23186774425732931839797667)
                  ·
                    refine ⟨34780161638599397759696501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23186774425732931839797667 34780161638599397759696501)
                    ·
                      refine ⟨3260640153618693539971547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34780161638599397759696501 3260640153618693539971547)
                      ·
                        rfl

theorem cell23_6350074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_6350074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350074 prefixEnd_6350074 := by exact prefixLift 6350074
  have htrace : WordTrace (prefixWord ++ tailWord_6350074) baseStart_6350074 baseEnd_6350074 := by
    simpa [prefixWord, tailWord_6350074, baseEnd_6350074] using wordTrace_append hprefix tailTrace_6350074
  have hstable : (prefixWord ++ tailWord_6350074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350074).length < 2 ^ (prefixWord ++ tailWord_6350074).sum := by decide
  have hdescent : baseEnd_6350074 < baseStart_6350074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350122 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6350122 : Nat := 118140960795 + 6350122 * 2 ^ 59
def prefixEnd_6350122 : Nat := 4983230072969 + 3 ^ 40 * 6350122 * 2
def baseEnd_6350122 : Nat := 3260664800690109352171327

theorem tailTrace_6350122 : CollatzResearch.WordTrace tailWord_6350122 prefixEnd_6350122 3260664800690109352171327 := by
  unfold tailWord_6350122
  simp only [CollatzResearch.WordTrace]
  refine ⟨57901994175149995835025155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154405317800399988893400413 57901994175149995835025155)
  ·
    refine ⟨86852991262724993752537733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57901994175149995835025155 86852991262724993752537733)
    ·
      refine ⟨16284935861760936328600825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86852991262724993752537733 16284935861760936328600825)
      ·
        refine ⟨12213701896320702246450619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16284935861760936328600825 12213701896320702246450619)
        ·
          refine ⟨18320552844481053369675929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213701896320702246450619 18320552844481053369675929)
          ·
            refine ⟨13740414633360790027256947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18320552844481053369675929 13740414633360790027256947)
            ·
              refine ⟨20610621950041185040885421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13740414633360790027256947 20610621950041185040885421)
              ·
                refine ⟨7728983231265444390332033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20610621950041185040885421 7728983231265444390332033)
                ·
                  refine ⟨5796737423449083292749025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728983231265444390332033 5796737423449083292749025)
                  ·
                    refine ⟨4347553067586812469561769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796737423449083292749025 4347553067586812469561769)
                    ·
                      refine ⟨3260664800690109352171327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347553067586812469561769 3260664800690109352171327)
                      ·
                        rfl

theorem cell23_6350122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6350122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350122 prefixEnd_6350122 := by exact prefixLift 6350122
  have htrace : WordTrace (prefixWord ++ tailWord_6350122) baseStart_6350122 baseEnd_6350122 := by
    simpa [prefixWord, tailWord_6350122, baseEnd_6350122] using wordTrace_append hprefix tailTrace_6350122
  have hstable : (prefixWord ++ tailWord_6350122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350122).length < 2 ^ (prefixWord ++ tailWord_6350122).sum := by decide
  have hdescent : baseEnd_6350122 < baseStart_6350122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350124 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_6350124 : Nat := 118140960795 + 6350124 * 2 ^ 59
def prefixEnd_6350124 : Nat := 4983230072969 + 3 ^ 40 * 6350124 * 2
def baseEnd_6350124 : Nat := 1086888609217139448115439

theorem tailTrace_6350124 : CollatzResearch.WordTrace tailWord_6350124 prefixEnd_6350124 1086888609217139448115439 := by
  unfold tailWord_6350124
  simp only [CollatzResearch.WordTrace]
  refine ⟨115804024823296368840836713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154405366431061825121115617 115804024823296368840836713)
  ·
    refine ⟨86853018617472276630627535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115804024823296368840836713 86853018617472276630627535)
    ·
      refine ⟨130279527926208414945941303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86853018617472276630627535 130279527926208414945941303)
      ·
        refine ⟨195419291889312622418911955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130279527926208414945941303 195419291889312622418911955)
        ·
          refine ⟨293128937833968933628367933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195419291889312622418911955 293128937833968933628367933)
          ·
            refine ⟨109923351687738350110637975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293128937833968933628367933 109923351687738350110637975)
            ·
              refine ⟨164885027531607525165956963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109923351687738350110637975 164885027531607525165956963)
              ·
                refine ⟨247327541297411287748935445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164885027531607525165956963 247327541297411287748935445)
                ·
                  refine ⟨11593478498316154113231349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247327541297411287748935445 11593478498316154113231349)
                  ·
                    refine ⟨1086888609217139448115439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11593478498316154113231349 1086888609217139448115439)
                    ·
                      rfl

theorem cell23_6350124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_6350124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350124 prefixEnd_6350124 := by exact prefixLift 6350124
  have htrace : WordTrace (prefixWord ++ tailWord_6350124) baseStart_6350124 baseEnd_6350124 := by
    simpa [prefixWord, tailWord_6350124, baseEnd_6350124] using wordTrace_append hprefix tailTrace_6350124
  have hstable : (prefixWord ++ tailWord_6350124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350124).length < 2 ^ (prefixWord ++ tailWord_6350124).sum := by decide
  have hdescent : baseEnd_6350124 < baseStart_6350124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350161 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_6350161 : Nat := 118140960795 + 6350161 * 2 ^ 59
def prefixEnd_6350161 : Nat := 4983230072969 + 3 ^ 40 * 6350161 * 2
def baseEnd_6350161 : Nat := 3260684826435634699583647

theorem tailTrace_6350161 : CollatzResearch.WordTrace tailWord_6350161 prefixEnd_6350161 3260684826435634699583647 := by
  unfold tailWord_6350161
  simp only [CollatzResearch.WordTrace]
  refine ⟨231609399147458693000770337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154406266098305795333846891 231609399147458693000770337)
  ·
    refine ⟨173707049360594019750577753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231609399147458693000770337 173707049360594019750577753)
    ·
      refine ⟨130280287020445514812933315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173707049360594019750577753 130280287020445514812933315)
      ·
        refine ⟨195420430530668272219399973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130280287020445514812933315 195420430530668272219399973)
        ·
          refine ⟨36641330724500301041137495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195420430530668272219399973 36641330724500301041137495)
          ·
            refine ⟨54961996086750451561706243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36641330724500301041137495 54961996086750451561706243)
            ·
              refine ⟨82442994130125677342559365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54961996086750451561706243 82442994130125677342559365)
              ·
                refine ⟨15458061399398564501729881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82442994130125677342559365 15458061399398564501729881)
                ·
                  refine ⟨11593546049548923376297411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15458061399398564501729881 11593546049548923376297411)
                  ·
                    refine ⟨17390319074323385064446117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11593546049548923376297411 17390319074323385064446117)
                    ·
                      refine ⟨3260684826435634699583647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17390319074323385064446117 3260684826435634699583647)
                      ·
                        rfl

theorem cell23_6350161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_6350161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350161 prefixEnd_6350161 := by exact prefixLift 6350161
  have htrace : WordTrace (prefixWord ++ tailWord_6350161) baseStart_6350161 baseEnd_6350161 := by
    simpa [prefixWord, tailWord_6350161, baseEnd_6350161] using wordTrace_append hprefix tailTrace_6350161
  have hstable : (prefixWord ++ tailWord_6350161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350161).length < 2 ^ (prefixWord ++ tailWord_6350161).sum := by decide
  have hdescent : baseEnd_6350161 < baseStart_6350161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350181 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 3]
def baseStart_6350181 : Nat := 118140960795 + 6350181 * 2 ^ 59
def prefixEnd_6350181 : Nat := 4983230072969 + 3 ^ 40 * 6350181 * 2
def baseEnd_6350181 : Nat := 3260695096048724621333555

theorem tailTrace_6350181 : CollatzResearch.WordTrace tailWord_6350181 prefixEnd_6350181 3260695096048724621333555 := by
  unfold tailWord_6350181
  simp only [CollatzResearch.WordTrace]
  refine ⟨231610128607386236416498397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154406752404924157610998931 231610128607386236416498397)
  ·
    refine ⟨86853798227769838656186899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231610128607386236416498397 86853798227769838656186899)
    ·
      refine ⟨130280697341654757984280349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86853798227769838656186899 130280697341654757984280349)
      ·
        refine ⟨48855261503120534244105131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130280697341654757984280349 48855261503120534244105131)
        ·
          refine ⟨73282892254680801366157697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48855261503120534244105131 73282892254680801366157697)
          ·
            refine ⟨54962169191010601024618273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73282892254680801366157697 54962169191010601024618273)
            ·
              refine ⟨41221626893257950768463705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54962169191010601024618273 41221626893257950768463705)
              ·
                refine ⟨30916220169943463076347779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41221626893257950768463705 30916220169943463076347779)
                ·
                  refine ⟨46374330254915194614521669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30916220169943463076347779 46374330254915194614521669)
                  ·
                    refine ⟨8695186922796598990222813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46374330254915194614521669 8695186922796598990222813)
                    ·
                      refine ⟨3260695096048724621333555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8695186922796598990222813 3260695096048724621333555)
                      ·
                        rfl

theorem cell23_6350181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_6350181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350181 prefixEnd_6350181 := by exact prefixLift 6350181
  have htrace : WordTrace (prefixWord ++ tailWord_6350181) baseStart_6350181 baseEnd_6350181 := by
    simpa [prefixWord, tailWord_6350181, baseEnd_6350181] using wordTrace_append hprefix tailTrace_6350181
  have hstable : (prefixWord ++ tailWord_6350181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350181).length < 2 ^ (prefixWord ++ tailWord_6350181).sum := by decide
  have hdescent : baseEnd_6350181 < baseStart_6350181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350188 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_6350188 : Nat := 118140960795 + 6350188 * 2 ^ 59
def prefixEnd_6350188 : Nat := 4983230072969 + 3 ^ 40 * 6350188 * 2
def baseEnd_6350188 : Nat := 1086899563471102031315341

theorem tailTrace_6350188 : CollatzResearch.WordTrace tailWord_6350188 prefixEnd_6350188 1086899563471102031315341 := by
  unfold tailWord_6350188
  simp only [CollatzResearch.WordTrace]
  refine ⟨115805191959180438306001609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154406922612240584408002145 115805191959180438306001609)
  ·
    refine ⟨86853893969385328729501207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115805191959180438306001609 86853893969385328729501207)
    ·
      refine ⟨130280840954077993094251811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86853893969385328729501207 130280840954077993094251811)
      ·
        refine ⟨195421261431116989641377717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130280840954077993094251811 195421261431116989641377717)
        ·
          refine ⟨18320743259167217778879161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195421261431116989641377717 18320743259167217778879161)
          ·
            refine ⟨13740557444375413334159371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18320743259167217778879161 13740557444375413334159371)
            ·
              refine ⟨20610836166563120001239057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13740557444375413334159371 20610836166563120001239057)
              ·
                refine ⟨15458127124922340000929293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20610836166563120001239057 15458127124922340000929293)
                ·
                  refine ⟨5796797671845877500348485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15458127124922340000929293 5796797671845877500348485)
                  ·
                    refine ⟨1086899563471102031315341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796797671845877500348485 1086899563471102031315341)
                    ·
                      rfl

theorem cell23_6350188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_6350188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350188 prefixEnd_6350188 := by exact prefixLift 6350188
  have htrace : WordTrace (prefixWord ++ tailWord_6350188) baseStart_6350188 baseEnd_6350188 := by
    simpa [prefixWord, tailWord_6350188, baseEnd_6350188] using wordTrace_append hprefix tailTrace_6350188
  have hstable : (prefixWord ++ tailWord_6350188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350188).length < 2 ^ (prefixWord ++ tailWord_6350188).sum := by decide
  have hdescent : baseEnd_6350188 < baseStart_6350188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350205 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_6350205 : Nat := 118140960795 + 6350205 * 2 ^ 59
def prefixEnd_6350205 : Nat := 4983230072969 + 3 ^ 40 * 6350205 * 2
def baseEnd_6350205 : Nat := 1086902473194810842477815

theorem tailTrace_6350205 : CollatzResearch.WordTrace tailWord_6350205 prefixEnd_6350205 1086902473194810842477815 := by
  unfold tailWord_6350205
  simp only [CollatzResearch.WordTrace]
  refine ⟨231611003959299288515372069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154407335972866192343581379 231611003959299288515372069)
  ·
    refine ⟨43427063242368616596632263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231611003959299288515372069 43427063242368616596632263)
    ·
      refine ⟨65140594863552924894948395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43427063242368616596632263 65140594863552924894948395)
      ·
        refine ⟨97710892295329387342422593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65140594863552924894948395 97710892295329387342422593)
        ·
          refine ⟨73283169221497040506816945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97710892295329387342422593 73283169221497040506816945)
          ·
            refine ⟨54962376916122780380112709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73283169221497040506816945 54962376916122780380112709)
            ·
              refine ⟨10305445671773021321271133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54962376916122780380112709 10305445671773021321271133)
              ·
                refine ⟨3864542126914882995476675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10305445671773021321271133 3864542126914882995476675)
                ·
                  refine ⟨5796813190372324493215013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864542126914882995476675 5796813190372324493215013)
                  ·
                    refine ⟨1086902473194810842477815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5796813190372324493215013 1086902473194810842477815)
                    ·
                      rfl

theorem cell23_6350205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_6350205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350205 prefixEnd_6350205 := by exact prefixLift 6350205
  have htrace : WordTrace (prefixWord ++ tailWord_6350205) baseStart_6350205 baseEnd_6350205 := by
    simpa [prefixWord, tailWord_6350205, baseEnd_6350205] using wordTrace_append hprefix tailTrace_6350205
  have hstable : (prefixWord ++ tailWord_6350205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350205).length < 2 ^ (prefixWord ++ tailWord_6350205).sum := by decide
  have hdescent : baseEnd_6350205 < baseStart_6350205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350305 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_6350305 : Nat := 118140960795 + 6350305 * 2 ^ 59
def prefixEnd_6350305 : Nat := 4983230072969 + 3 ^ 40 * 6350305 * 2
def baseEnd_6350305 : Nat := 3260758767649882136182985

theorem tailTrace_6350305 : CollatzResearch.WordTrace tailWord_6350305 prefixEnd_6350305 3260758767649882136182985 := by
  unfold tailWord_6350305
  simp only [CollatzResearch.WordTrace]
  refine ⟨231614651258937005594012369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154409767505958003729341579 231614651258937005594012369)
  ·
    refine ⟨173710988444202754195509277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231614651258937005594012369 173710988444202754195509277)
    ·
      refine ⟨65141620666576032823315979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173710988444202754195509277 65141620666576032823315979)
      ·
        refine ⟨97712430999864049234973969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65141620666576032823315979 97712430999864049234973969)
        ·
          refine ⟨73284323249898036926230477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97712430999864049234973969 73284323249898036926230477)
          ·
            refine ⟨27481621218711763847336429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73284323249898036926230477 27481621218711763847336429)
            ·
              refine ⟨10305607957016911442751161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27481621218711763847336429 10305607957016911442751161)
              ·
                refine ⟨7729205967762683582063371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10305607957016911442751161 7729205967762683582063371)
                ·
                  refine ⟨11593808951644025373095057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729205967762683582063371 11593808951644025373095057)
                  ·
                    refine ⟨8695356713733019029821293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11593808951644025373095057 8695356713733019029821293)
                    ·
                      refine ⟨3260758767649882136182985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8695356713733019029821293 3260758767649882136182985)
                      ·
                        rfl

theorem cell23_6350305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_6350305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350305 prefixEnd_6350305 := by exact prefixLift 6350305
  have htrace : WordTrace (prefixWord ++ tailWord_6350305) baseStart_6350305 baseEnd_6350305 := by
    simpa [prefixWord, tailWord_6350305, baseEnd_6350305] using wordTrace_append hprefix tailTrace_6350305
  have hstable : (prefixWord ++ tailWord_6350305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350305).length < 2 ^ (prefixWord ++ tailWord_6350305).sum := by decide
  have hdescent : baseEnd_6350305 < baseStart_6350305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350349 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6350349 : Nat := 118140960795 + 6350349 * 2 ^ 59
def prefixEnd_6350349 : Nat := 4983230072969 + 3 ^ 40 * 6350349 * 2
def baseEnd_6350349 : Nat := 3260781360798679964032783

theorem tailTrace_6350349 : CollatzResearch.WordTrace tailWord_6350349 prefixEnd_6350349 3260781360798679964032783 := by
  unfold tailWord_6350349
  simp only [CollatzResearch.WordTrace]
  refine ⟨231616256070777601108614101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154410837380518400739076067 231616256070777601108614101)
  ·
    refine ⟨5428506001658850025983143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 231616256070777601108614101 5428506001658850025983143)
    ·
      refine ⟨8142759002488275038974715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428506001658850025983143 8142759002488275038974715)
      ·
        refine ⟨12214138503732412558462073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8142759002488275038974715 12214138503732412558462073)
        ·
          refine ⟨9160603877799309418846555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12214138503732412558462073 9160603877799309418846555)
          ·
            refine ⟨13740905816698964128269833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9160603877799309418846555 13740905816698964128269833)
            ·
              refine ⟨10305679362524223096202375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13740905816698964128269833 10305679362524223096202375)
              ·
                refine ⟨15458519043786334644303563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10305679362524223096202375 15458519043786334644303563)
                ·
                  refine ⟨23187778565679501966455345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15458519043786334644303563 23187778565679501966455345)
                  ·
                    refine ⟨17390833924259626474841509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23187778565679501966455345 17390833924259626474841509)
                    ·
                      refine ⟨3260781360798679964032783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17390833924259626474841509 3260781360798679964032783)
                      ·
                        rfl

theorem cell23_6350349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6350349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350349 prefixEnd_6350349 := by exact prefixLift 6350349
  have htrace : WordTrace (prefixWord ++ tailWord_6350349) baseStart_6350349 baseEnd_6350349 := by
    simpa [prefixWord, tailWord_6350349, baseEnd_6350349] using wordTrace_append hprefix tailTrace_6350349
  have hstable : (prefixWord ++ tailWord_6350349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350349).length < 2 ^ (prefixWord ++ tailWord_6350349).sum := by decide
  have hdescent : baseEnd_6350349 < baseStart_6350349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350378 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6350378 : Nat := 118140960795 + 6350378 * 2 ^ 59
def prefixEnd_6350378 : Nat := 4983230072969 + 3 ^ 40 * 6350378 * 2
def baseEnd_6350378 : Nat := 3260796251737660350570149

theorem tailTrace_6350378 : CollatzResearch.WordTrace tailWord_6350378 prefixEnd_6350378 3260796251737660350570149 := by
  unfold tailWord_6350378
  simp only [CollatzResearch.WordTrace]
  refine ⟨57904328446918134765354947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154411542525115026040946525 57904328446918134765354947)
  ·
    refine ⟨86856492670377202148032421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57904328446918134765354947 86856492670377202148032421)
    ·
      refine ⟨16285592375695725402756079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86856492670377202148032421 16285592375695725402756079)
      ·
        refine ⟨24428388563543588104134119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16285592375695725402756079 24428388563543588104134119)
        ·
          refine ⟨36642582845315382156201179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24428388563543588104134119 36642582845315382156201179)
          ·
            refine ⟨54963874267973073234301769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36642582845315382156201179 54963874267973073234301769)
            ·
              refine ⟨41222905700979804925726327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54963874267973073234301769 41222905700979804925726327)
              ·
                refine ⟨61834358551469707388589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41222905700979804925726327 61834358551469707388589491)
                ·
                  refine ⟨92751537827204561082884237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61834358551469707388589491 92751537827204561082884237)
                  ·
                    refine ⟨34781826685201710406081589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92751537827204561082884237 34781826685201710406081589)
                    ·
                      refine ⟨3260796251737660350570149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34781826685201710406081589 3260796251737660350570149)
                      ·
                        rfl

theorem cell23_6350378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6350378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350378 prefixEnd_6350378 := by exact prefixLift 6350378
  have htrace : WordTrace (prefixWord ++ tailWord_6350378) baseStart_6350378 baseEnd_6350378 := by
    simpa [prefixWord, tailWord_6350378, baseEnd_6350378] using wordTrace_append hprefix tailTrace_6350378
  have hstable : (prefixWord ++ tailWord_6350378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350378).length < 2 ^ (prefixWord ++ tailWord_6350378).sum := by decide
  have hdescent : baseEnd_6350378 < baseStart_6350378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350392 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_6350392 : Nat := 118140960795 + 6350392 * 2 ^ 59
def prefixEnd_6350392 : Nat := 4983230072969 + 3 ^ 40 * 6350392 * 2
def baseEnd_6350392 : Nat := 3260803440466823295795085

theorem tailTrace_6350392 : CollatzResearch.WordTrace tailWord_6350392 prefixEnd_6350392 3260803440466823295795085 := by
  unfold tailWord_6350392
  simp only [CollatzResearch.WordTrace]
  refine ⟨115808912204810909726214715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154411882939747879634952953 115808912204810909726214715)
  ·
    refine ⟨173713368307216364589322073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115808912204810909726214715 173713368307216364589322073)
    ·
      refine ⟨130285026230412273441991555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173713368307216364589322073 130285026230412273441991555)
      ·
        refine ⟨195427539345618410162987333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130285026230412273441991555 195427539345618410162987333)
        ·
          refine ⟨36642663627303451905560125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195427539345618410162987333 36642663627303451905560125)
          ·
            refine ⟨13740998860238794464585047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36642663627303451905560125 13740998860238794464585047)
            ·
              refine ⟨20611498290358191696877571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13740998860238794464585047 20611498290358191696877571)
              ·
                refine ⟨30917247435537287545316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20611498290358191696877571 30917247435537287545316357)
                ·
                  refine ⟨5796983894163241414746817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30917247435537287545316357 5796983894163241414746817)
                  ·
                    refine ⟨4347737920622431061060113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796983894163241414746817 4347737920622431061060113)
                    ·
                      refine ⟨3260803440466823295795085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347737920622431061060113 3260803440466823295795085)
                      ·
                        rfl

theorem cell23_6350392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_6350392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350392 prefixEnd_6350392 := by exact prefixLift 6350392
  have htrace : WordTrace (prefixWord ++ tailWord_6350392) baseStart_6350392 baseEnd_6350392 := by
    simpa [prefixWord, tailWord_6350392, baseEnd_6350392] using wordTrace_append hprefix tailTrace_6350392
  have hstable : (prefixWord ++ tailWord_6350392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350392).length < 2 ^ (prefixWord ++ tailWord_6350392).sum := by decide
  have hdescent : baseEnd_6350392 < baseStart_6350392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350509 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6350509 : Nat := 118140960795 + 6350509 * 2 ^ 59
def prefixEnd_6350509 : Nat := 4983230072969 + 3 ^ 40 * 6350509 * 2
def baseEnd_6350509 : Nat := 1086954505901133112677349

theorem tailTrace_6350509 : CollatzResearch.WordTrace tailWord_6350509 prefixEnd_6350509 1086954505901133112677349 := by
  unfold tailWord_6350509
  simp only [CollatzResearch.WordTrace]
  refine ⟨231622091750197948434438581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154414727833465298956292387 231622091750197948434438581)
  ·
    refine ⟨21714571101581057665728617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231622091750197948434438581 21714571101581057665728617)
    ·
      refine ⟨16285928326185793249296463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21714571101581057665728617 16285928326185793249296463)
      ·
        refine ⟨24428892489278689873944695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16285928326185793249296463 24428892489278689873944695)
        ·
          refine ⟨36643338733918034810917043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24428892489278689873944695 36643338733918034810917043)
          ·
            refine ⟨54965008100877052216375565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643338733918034810917043 54965008100877052216375565)
            ·
              refine ⟨20611878037828894581140837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54965008100877052216375565 20611878037828894581140837)
              ·
                refine ⟨3864727132092917733963907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20611878037828894581140837 3864727132092917733963907)
                ·
                  refine ⟨5797090698139376600945861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864727132092917733963907 5797090698139376600945861)
                  ·
                    refine ⟨1086954505901133112677349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797090698139376600945861 1086954505901133112677349)
                    ·
                      rfl

theorem cell23_6350509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6350509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350509 prefixEnd_6350509 := by exact prefixLift 6350509
  have htrace : WordTrace (prefixWord ++ tailWord_6350509) baseStart_6350509 baseEnd_6350509 := by
    simpa [prefixWord, tailWord_6350509, baseEnd_6350509] using wordTrace_append hprefix tailTrace_6350509
  have hstable : (prefixWord ++ tailWord_6350509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350509).length < 2 ^ (prefixWord ++ tailWord_6350509).sum := by decide
  have hdescent : baseEnd_6350509 < baseStart_6350509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350528 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_6350528 : Nat := 118140960795 + 6350528 * 2 ^ 59
def prefixEnd_6350528 : Nat := 4983230072969 + 3 ^ 40 * 6350528 * 2
def baseEnd_6350528 : Nat := 3260873273835834763694459

theorem tailTrace_6350528 : CollatzResearch.WordTrace tailWord_6350528 prefixEnd_6350528 3260873273835834763694459 := by
  unfold tailWord_6350528
  simp only [CollatzResearch.WordTrace]
  refine ⟨115811392368564557339690119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154415189824752743119586825 115811392368564557339690119)
  ·
    refine ⟨173717088552846836009535179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115811392368564557339690119 173717088552846836009535179)
    ·
      refine ⟨260575632829270254014302769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173717088552846836009535179 260575632829270254014302769)
      ·
        refine ⟨195431724621952690510727077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260575632829270254014302769 195431724621952690510727077)
        ·
          refine ⟨36643448366616129470761327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195431724621952690510727077 36643448366616129470761327)
          ·
            refine ⟨54965172549924194206141991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643448366616129470761327 54965172549924194206141991)
            ·
              refine ⟨82447758824886291309212987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54965172549924194206141991 82447758824886291309212987)
              ·
                refine ⟨123671638237329436963819481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82447758824886291309212987 123671638237329436963819481)
                ·
                  refine ⟨92753728677997077722864611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123671638237329436963819481 92753728677997077722864611)
                  ·
                    refine ⟨139130593016995616584296917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92753728677997077722864611 139130593016995616584296917)
                    ·
                      refine ⟨3260873273835834763694459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139130593016995616584296917 3260873273835834763694459)
                      ·
                        rfl

theorem cell23_6350528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_6350528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350528 prefixEnd_6350528 := by exact prefixLift 6350528
  have htrace : WordTrace (prefixWord ++ tailWord_6350528) baseStart_6350528 baseEnd_6350528 := by
    simpa [prefixWord, tailWord_6350528, baseEnd_6350528] using wordTrace_append hprefix tailTrace_6350528
  have hstable : (prefixWord ++ tailWord_6350528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350528).length < 2 ^ (prefixWord ++ tailWord_6350528).sum := by decide
  have hdescent : baseEnd_6350528 < baseStart_6350528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350535 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 1, 5]
def baseStart_6350535 : Nat := 118140960795 + 6350535 * 2 ^ 59
def prefixEnd_6350535 : Nat := 4983230072969 + 3 ^ 40 * 6350535 * 2
def baseEnd_6350535 : Nat := 1086958956066805412102309

theorem tailTrace_6350535 : CollatzResearch.WordTrace tailWord_6350535 prefixEnd_6350535 1086958956066805412102309 := by
  unfold tailWord_6350535
  simp only [CollatzResearch.WordTrace]
  refine ⟨231623040048103754874885059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154415360032069169916590039 231623040048103754874885059)
  ·
    refine ⟨347434560072155632312327589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231623040048103754874885059 347434560072155632312327589)
    ·
      refine ⟨65143980013529181058561423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347434560072155632312327589 65143980013529181058561423)
      ·
        refine ⟨97715970020293771587842135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65143980013529181058561423 97715970020293771587842135)
        ·
          refine ⟨146573955030440657381763203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97715970020293771587842135 146573955030440657381763203)
          ·
            refine ⟨219860932545660986072644805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146573955030440657381763203 219860932545660986072644805)
            ·
              refine ⟨41223924852311434888620901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219860932545660986072644805 41223924852311434888620901)
              ·
                refine ⟨7729485909808394041616419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41223924852311434888620901 7729485909808394041616419)
                ·
                  refine ⟨11594228864712591062424629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729485909808394041616419 11594228864712591062424629)
                  ·
                    refine ⟨1086958956066805412102309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11594228864712591062424629 1086958956066805412102309)
                    ·
                      rfl

theorem cell23_6350535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_6350535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350535 prefixEnd_6350535 := by exact prefixLift 6350535
  have htrace : WordTrace (prefixWord ++ tailWord_6350535) baseStart_6350535 baseEnd_6350535 := by
    simpa [prefixWord, tailWord_6350535, baseEnd_6350535] using wordTrace_append hprefix tailTrace_6350535
  have hstable : (prefixWord ++ tailWord_6350535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350535).length < 2 ^ (prefixWord ++ tailWord_6350535).sum := by decide
  have hdescent : baseEnd_6350535 < baseStart_6350535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350542 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_6350542 : Nat := 118140960795 + 6350542 * 2 ^ 59
def prefixEnd_6350542 : Nat := 4983230072969 + 3 ^ 40 * 6350542 * 2
def baseEnd_6350542 : Nat := 3260880462564997708919395

theorem tailTrace_6350542 : CollatzResearch.WordTrace tailWord_6350542 prefixEnd_6350542 3260880462564997708919395 := by
  unfold tailWord_6350542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952911919884799383798735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154415530239385596713593253 28952911919884799383798735)
  ·
    refine ⟨43429367879827199075698103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28952911919884799383798735 43429367879827199075698103)
    ·
      refine ⟨65144051819740798613547155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43429367879827199075698103 65144051819740798613547155)
      ·
        refine ⟨97716077729611197920320733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65144051819740798613547155 97716077729611197920320733)
        ·
          refine ⟨36643529148604199220120275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97716077729611197920320733 36643529148604199220120275)
          ·
            refine ⟨54965293722906298830180413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643529148604199220120275 54965293722906298830180413)
            ·
              refine ⟨20611985146089862061317655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54965293722906298830180413 20611985146089862061317655)
              ·
                refine ⟨30917977719134793091976483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20611985146089862061317655 30917977719134793091976483)
                ·
                  refine ⟨46376966578702189637964725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30917977719134793091976483 46376966578702189637964725)
                  ·
                    refine ⟨4347840616753330278559193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46376966578702189637964725 4347840616753330278559193)
                    ·
                      refine ⟨3260880462564997708919395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347840616753330278559193 3260880462564997708919395)
                      ·
                        rfl

theorem cell23_6350542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_6350542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350542 prefixEnd_6350542 := by exact prefixLift 6350542
  have htrace : WordTrace (prefixWord ++ tailWord_6350542) baseStart_6350542 baseEnd_6350542 := by
    simpa [prefixWord, tailWord_6350542, baseEnd_6350542] using wordTrace_append hprefix tailTrace_6350542
  have hstable : (prefixWord ++ tailWord_6350542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350542).length < 2 ^ (prefixWord ++ tailWord_6350542).sum := by decide
  have hdescent : baseEnd_6350542 < baseStart_6350542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350556 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 6]
def baseStart_6350556 : Nat := 118140960795 + 6350556 * 2 ^ 59
def prefixEnd_6350556 : Nat := 4983230072969 + 3 ^ 40 * 6350556 * 2
def baseEnd_6350556 : Nat := 362320850143795628238259

theorem tailTrace_6350556 : CollatzResearch.WordTrace tailWord_6350556 prefixEnd_6350556 362320850143795628238259 := by
  unfold tailWord_6350556
  simp only [CollatzResearch.WordTrace]
  refine ⟨115811902990513837730699761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154415870654018450307599681 115811902990513837730699761)
  ·
    refine ⟨86858927242885378298024821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115811902990513837730699761 86858927242885378298024821)
    ·
      refine ⟨8143024429020504215439827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86858927242885378298024821 8143024429020504215439827)
      ·
        refine ⟨12214536643530756323159741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143024429020504215439827 12214536643530756323159741)
        ·
          refine ⟨4580451241324033621184903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12214536643530756323159741 4580451241324033621184903)
          ·
            refine ⟨6870676861986050431777355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580451241324033621184903 6870676861986050431777355)
            ·
              refine ⟨10306015292979075647666033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870676861986050431777355 10306015292979075647666033)
              ·
                refine ⟨7729511469734306735749525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306015292979075647666033 7729511469734306735749525)
                ·
                  refine ⟨362320850143795628238259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7729511469734306735749525 362320850143795628238259)
                  ·
                    rfl

theorem cell23_6350556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_6350556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350556 prefixEnd_6350556 := by exact prefixLift 6350556
  have htrace : WordTrace (prefixWord ++ tailWord_6350556) baseStart_6350556 baseEnd_6350556 := by
    simpa [prefixWord, tailWord_6350556, baseEnd_6350556] using wordTrace_append hprefix tailTrace_6350556
  have hstable : (prefixWord ++ tailWord_6350556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350556).length < 2 ^ (prefixWord ++ tailWord_6350556).sum := by decide
  have hdescent : baseEnd_6350556 < baseStart_6350556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350575 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_6350575 : Nat := 118140960795 + 6350575 * 2 ^ 59
def prefixEnd_6350575 : Nat := 4983230072969 + 3 ^ 40 * 6350575 * 2
def baseEnd_6350575 : Nat := 3260897407426596079806743

theorem tailTrace_6350575 : CollatzResearch.WordTrace tailWord_6350575 prefixEnd_6350575 3260897407426596079806743 := by
  unfold tailWord_6350575
  simp only [CollatzResearch.WordTrace]
  refine ⟨231624498967958841706341179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154416332645305894470894119 231624498967958841706341179)
  ·
    refine ⟨347436748451938262559511769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231624498967958841706341179 347436748451938262559511769)
    ·
      refine ⟨260577561338953696919633827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347436748451938262559511769 260577561338953696919633827)
      ·
        refine ⟨390866342008430545379450741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260577561338953696919633827 390866342008430545379450741)
        ·
          refine ⟨36643719563290363629323507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390866342008430545379450741 36643719563290363629323507)
          ·
            refine ⟨54965579344935545443985261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643719563290363629323507 54965579344935545443985261)
            ·
              refine ⟨20612092254350829541494473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54965579344935545443985261 20612092254350829541494473)
              ·
                refine ⟨15459069190763122156120855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20612092254350829541494473 15459069190763122156120855)
                ·
                  refine ⟨23188603786144683234181283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15459069190763122156120855 23188603786144683234181283)
                  ·
                    refine ⟨34782905679217024851271925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23188603786144683234181283 34782905679217024851271925)
                    ·
                      refine ⟨3260897407426596079806743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34782905679217024851271925 3260897407426596079806743)
                      ·
                        rfl

theorem cell23_6350575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_6350575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350575 prefixEnd_6350575 := by exact prefixLift 6350575
  have htrace : WordTrace (prefixWord ++ tailWord_6350575) baseStart_6350575 baseEnd_6350575 := by
    simpa [prefixWord, tailWord_6350575, baseEnd_6350575] using wordTrace_append hprefix tailTrace_6350575
  have hstable : (prefixWord ++ tailWord_6350575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350575).length < 2 ^ (prefixWord ++ tailWord_6350575).sum := by decide
  have hdescent : baseEnd_6350575 < baseStart_6350575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350582 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6350582 : Nat := 118140960795 + 6350582 * 2 ^ 59
def prefixEnd_6350582 : Nat := 4983230072969 + 3 ^ 40 * 6350582 * 2
def baseEnd_6350582 : Nat := 1086967000597059184139737

theorem tailTrace_6350582 : CollatzResearch.WordTrace tailWord_6350582 prefixEnd_6350582 1086967000597059184139737 := by
  unfold tailWord_6350582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476547142433342618865375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154416502852622321267897333 14476547142433342618865375)
  ·
    refine ⟨21714820713650013928298063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14476547142433342618865375 21714820713650013928298063)
    ·
      refine ⟨32572231070475020892447095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21714820713650013928298063 32572231070475020892447095)
      ·
        refine ⟨48858346605712531338670643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32572231070475020892447095 48858346605712531338670643)
        ·
          refine ⟨73287519908568797008005965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48858346605712531338670643 73287519908568797008005965)
          ·
            refine ⟨27482819965713298878002237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73287519908568797008005965 27482819965713298878002237)
            ·
              refine ⟨10306057487142487079250839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27482819965713298878002237 10306057487142487079250839)
              ·
                refine ⟨15459086230713730618876259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10306057487142487079250839 15459086230713730618876259)
                ·
                  refine ⟨23188629346070595928314389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15459086230713730618876259 23188629346070595928314389)
                  ·
                    refine ⟨1086967000597059184139737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23188629346070595928314389 1086967000597059184139737)
                    ·
                      rfl

theorem cell23_6350582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6350582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350582 prefixEnd_6350582 := by exact prefixLift 6350582
  have htrace : WordTrace (prefixWord ++ tailWord_6350582) baseStart_6350582 baseEnd_6350582 := by
    simpa [prefixWord, tailWord_6350582, baseEnd_6350582] using wordTrace_append hprefix tailTrace_6350582
  have hstable : (prefixWord ++ tailWord_6350582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350582).length < 2 ^ (prefixWord ++ tailWord_6350582).sum := by decide
  have hdescent : baseEnd_6350582 < baseStart_6350582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350595 : List Nat := [1, 1, 1, 3, 2, 2, 6, 7]
def baseStart_6350595 : Nat := 118140960795 + 6350595 * 2 ^ 59
def prefixEnd_6350595 : Nat := 4983230072969 + 3 ^ 40 * 6350595 * 2
def baseEnd_6350595 : Nat := 120774358408877259316913

theorem tailTrace_6350595 : CollatzResearch.WordTrace tailWord_6350595 prefixEnd_6350595 120774358408877259316913 := by
  unfold tailWord_6350595
  simp only [CollatzResearch.WordTrace]
  refine ⟨231625228427886385122069239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154416818951924256748046159 231625228427886385122069239)
  ·
    refine ⟨347437842641829577683103859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231625228427886385122069239 347437842641829577683103859)
    ·
      refine ⟨521156763962744366524655789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347437842641829577683103859 521156763962744366524655789)
      ·
        refine ⟨195433786486029137446745921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521156763962744366524655789 195433786486029137446745921)
        ·
          refine ⟨146575339864521853085059441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195433786486029137446745921 146575339864521853085059441)
          ·
            refine ⟨109931504898391389813794581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146575339864521853085059441 109931504898391389813794581)
            ·
              refine ⟨5153039292112096397521621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109931504898391389813794581 5153039292112096397521621)
              ·
                refine ⟨120774358408877259316913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5153039292112096397521621 120774358408877259316913)
                ·
                  rfl

theorem cell23_6350595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 7].length) (baseStart_6350595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350595 prefixEnd_6350595 := by exact prefixLift 6350595
  have htrace : WordTrace (prefixWord ++ tailWord_6350595) baseStart_6350595 baseEnd_6350595 := by
    simpa [prefixWord, tailWord_6350595, baseEnd_6350595] using wordTrace_append hprefix tailTrace_6350595
  have hstable : (prefixWord ++ tailWord_6350595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350595).length < 2 ^ (prefixWord ++ tailWord_6350595).sum := by decide
  have hdescent : baseEnd_6350595 < baseStart_6350595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350623 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 1, 2, 2]
def baseStart_6350623 : Nat := 118140960795 + 6350623 * 2 ^ 59
def prefixEnd_6350623 : Nat := 4983230072969 + 3 ^ 40 * 6350623 * 2
def baseEnd_6350623 : Nat := 3260922054498011892006523

theorem tailTrace_6350623 : CollatzResearch.WordTrace tailWord_6350623 prefixEnd_6350623 3260922054498011892006523 := by
  unfold tailWord_6350623
  simp only [CollatzResearch.WordTrace]
  refine ⟨231626249671784945904088523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154417499781189963936059015 231626249671784945904088523)
  ·
    refine ⟨347439374507677418856132785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231626249671784945904088523 347439374507677418856132785)
    ·
      refine ⟨260579530880758064142099589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347439374507677418856132785 260579530880758064142099589)
      ·
        refine ⟨48858662040142137026643673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260579530880758064142099589 48858662040142137026643673)
        ·
          refine ⟨36643996530106602769982755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48858662040142137026643673 36643996530106602769982755)
          ·
            refine ⟨54965994795159904154974133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643996530106602769982755 54965994795159904154974133)
            ·
              refine ⟨5153062012046241014528825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54965994795159904154974133 5153062012046241014528825)
              ·
                refine ⟨3864796509034680760896619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5153062012046241014528825 3864796509034680760896619)
                ·
                  refine ⟨5797194763552021141344929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864796509034680760896619 5797194763552021141344929)
                  ·
                    refine ⟨4347896072664015856008697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5797194763552021141344929 4347896072664015856008697)
                    ·
                      refine ⟨3260922054498011892006523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347896072664015856008697 3260922054498011892006523)
                      ·
                        rfl

theorem cell23_6350623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_6350623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350623 prefixEnd_6350623 := by exact prefixLift 6350623
  have htrace : WordTrace (prefixWord ++ tailWord_6350623) baseStart_6350623 baseEnd_6350623 := by
    simpa [prefixWord, tailWord_6350623, baseEnd_6350623] using wordTrace_append hprefix tailTrace_6350623
  have hstable : (prefixWord ++ tailWord_6350623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350623).length < 2 ^ (prefixWord ++ tailWord_6350623).sum := by decide
  have hdescent : baseEnd_6350623 < baseStart_6350623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350665 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_6350665 : Nat := 118140960795 + 6350665 * 2 ^ 59
def prefixEnd_6350665 : Nat := 4983230072969 + 3 ^ 40 * 6350665 * 2
def baseEnd_6350665 : Nat := 3260943620685500727681329

theorem tailTrace_6350665 : CollatzResearch.WordTrace tailWord_6350665 prefixEnd_6350665 3260943620685500727681329 := by
  unfold tailWord_6350665
  simp only [CollatzResearch.WordTrace]
  refine ⟨231627781537632787077117449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154418521025088524718078299 231627781537632787077117449)
  ·
    refine ⟨173720836153224590307838087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231627781537632787077117449 173720836153224590307838087)
    ·
      refine ⟨260581254229836885461757131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173720836153224590307838087 260581254229836885461757131)
      ·
        refine ⟨390871881344755328192635697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260581254229836885461757131 390871881344755328192635697)
        ·
          refine ⟨293153911008566496144476773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390871881344755328192635697 293153911008566496144476773)
          ·
            refine ⟨54966358314106218027089395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293153911008566496144476773 54966358314106218027089395)
            ·
              refine ⟨82449537471159327040634093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54966358314106218027089395 82449537471159327040634093)
              ·
                refine ⟨30918576551684747640237785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82449537471159327040634093 30918576551684747640237785)
                ·
                  refine ⟨23188932413763560730178339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30918576551684747640237785 23188932413763560730178339)
                  ·
                    refine ⟨34783398620645341095267509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23188932413763560730178339 34783398620645341095267509)
                    ·
                      refine ⟨3260943620685500727681329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34783398620645341095267509 3260943620685500727681329)
                      ·
                        rfl

theorem cell23_6350665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_6350665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350665 prefixEnd_6350665 := by exact prefixLift 6350665
  have htrace : WordTrace (prefixWord ++ tailWord_6350665) baseStart_6350665 baseEnd_6350665 := by
    simpa [prefixWord, tailWord_6350665, baseEnd_6350665] using wordTrace_append hprefix tailTrace_6350665
  have hstable : (prefixWord ++ tailWord_6350665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350665).length < 2 ^ (prefixWord ++ tailWord_6350665).sum := by decide
  have hdescent : baseEnd_6350665 < baseStart_6350665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350666 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_6350666 : Nat := 118140960795 + 6350666 * 2 ^ 59
def prefixEnd_6350666 : Nat := 4983230072969 + 3 ^ 40 * 6350666 * 2
def baseEnd_6350666 : Nat := 3260944134166155223768825

theorem tailTrace_6350666 : CollatzResearch.WordTrace tailWord_6350666 prefixEnd_6350666 3260944134166155223768825 := by
  unfold tailWord_6350666
  simp only [CollatzResearch.WordTrace]
  refine ⟨57906954502657291061975963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154418545340419442831935901 57906954502657291061975963)
  ·
    refine ⟨86860431753985936592963945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57906954502657291061975963 86860431753985936592963945)
    ·
      refine ⟨65145323815489452444722959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86860431753985936592963945 65145323815489452444722959)
      ·
        refine ⟨97717985723234178667084439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65145323815489452444722959 97717985723234178667084439)
        ·
          refine ⟨146576978584851268000626659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97717985723234178667084439 146576978584851268000626659)
          ·
            refine ⟨219865467877276902000939989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146576978584851268000626659 219865467877276902000939989)
            ·
              refine ⟨5153096903373677390647031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219865467877276902000939989 5153096903373677390647031)
              ·
                refine ⟨7729645355060516085970547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153096903373677390647031 7729645355060516085970547)
                ·
                  refine ⟨11594468032590774128955821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729645355060516085970547 11594468032590774128955821)
                  ·
                    refine ⟨4347925512221540298358433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11594468032590774128955821 4347925512221540298358433)
                    ·
                      refine ⟨3260944134166155223768825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347925512221540298358433 3260944134166155223768825)
                      ·
                        rfl

theorem cell23_6350666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_6350666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350666 prefixEnd_6350666 := by exact prefixLift 6350666
  have htrace : WordTrace (prefixWord ++ tailWord_6350666) baseStart_6350666 baseEnd_6350666 := by
    simpa [prefixWord, tailWord_6350666, baseEnd_6350666] using wordTrace_append hprefix tailTrace_6350666
  have hstable : (prefixWord ++ tailWord_6350666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350666).length < 2 ^ (prefixWord ++ tailWord_6350666).sum := by decide
  have hdescent : baseEnd_6350666 < baseStart_6350666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350696 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6350696 : Nat := 118140960795 + 6350696 * 2 ^ 59
def prefixEnd_6350696 : Nat := 4983230072969 + 3 ^ 40 * 6350696 * 2
def baseEnd_6350696 : Nat := 3260959538585790106393687

theorem tailTrace_6350696 : CollatzResearch.WordTrace tailWord_6350696 prefixEnd_6350696 3260959538585790106393687 := by
  unfold tailWord_6350696
  simp only [CollatzResearch.WordTrace]
  refine ⟨115814456100260239685747971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154419274800346986247663961 115814456100260239685747971)
  ·
    refine ⟨173721684150390359528621957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115814456100260239685747971 173721684150390359528621957)
    ·
      refine ⟨32572815778198192411616617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173721684150390359528621957 32572815778198192411616617)
      ·
        refine ⟨24429611833648644308712463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32572815778198192411616617 24429611833648644308712463)
        ·
          refine ⟨36644417750472966463068695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24429611833648644308712463 36644417750472966463068695)
          ·
            refine ⟨54966626625709449694603043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36644417750472966463068695 54966626625709449694603043)
            ·
              refine ⟨82449939938564174541904565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54966626625709449694603043 82449939938564174541904565)
              ·
                refine ⟨7729681869240391363303553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82449939938564174541904565 7729681869240391363303553)
                ·
                  refine ⟨5797261401930293522477665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729681869240391363303553 5797261401930293522477665)
                  ·
                    refine ⟨4347946051447720141858249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5797261401930293522477665 4347946051447720141858249)
                    ·
                      refine ⟨3260959538585790106393687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347946051447720141858249 3260959538585790106393687)
                      ·
                        rfl

theorem cell23_6350696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6350696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350696 prefixEnd_6350696 := by exact prefixLift 6350696
  have htrace : WordTrace (prefixWord ++ tailWord_6350696) baseStart_6350696 baseEnd_6350696 := by
    simpa [prefixWord, tailWord_6350696, baseEnd_6350696] using wordTrace_append hprefix tailTrace_6350696
  have hstable : (prefixWord ++ tailWord_6350696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350696).length < 2 ^ (prefixWord ++ tailWord_6350696).sum := by decide
  have hdescent : baseEnd_6350696 < baseStart_6350696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350702 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_6350702 : Nat := 118140960795 + 6350702 * 2 ^ 59
def prefixEnd_6350702 : Nat := 4983230072969 + 3 ^ 40 * 6350702 * 2
def baseEnd_6350702 : Nat := 362329179941079675879851

theorem tailTrace_6350702 : CollatzResearch.WordTrace tailWord_6350702 prefixEnd_6350702 362329179941079675879851 := by
  unfold tailWord_6350702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953641379812342799526795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154419420692332494930809573 28953641379812342799526795)
  ·
    refine ⟨43430462069718514199290193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28953641379812342799526795 43430462069718514199290193)
    ·
      refine ⟨32572846552288885649467645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43430462069718514199290193 32572846552288885649467645)
      ·
        refine ⟨12214817457108332118550367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32572846552288885649467645 12214817457108332118550367)
        ·
          refine ⟨18322226185662498177825551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12214817457108332118550367 18322226185662498177825551)
          ·
            refine ⟨27483339278493747266738327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18322226185662498177825551 27483339278493747266738327)
            ·
              refine ⟨41225008917740620900107491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27483339278493747266738327 41225008917740620900107491)
              ·
                refine ⟨61837513376610931350161237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41225008917740620900107491 61837513376610931350161237)
                ·
                  refine ⟨362329179941079675879851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61837513376610931350161237 362329179941079675879851)
                  ·
                    rfl

theorem cell23_6350702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_6350702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350702 prefixEnd_6350702 := by exact prefixLift 6350702
  have htrace : WordTrace (prefixWord ++ tailWord_6350702) baseStart_6350702 baseEnd_6350702 := by
    simpa [prefixWord, tailWord_6350702, baseEnd_6350702] using wordTrace_append hprefix tailTrace_6350702
  have hstable : (prefixWord ++ tailWord_6350702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350702).length < 2 ^ (prefixWord ++ tailWord_6350702).sum := by decide
  have hdescent : baseEnd_6350702 < baseStart_6350702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350730 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6350730 : Nat := 118140960795 + 6350730 * 2 ^ 59
def prefixEnd_6350730 : Nat := 4983230072969 + 3 ^ 40 * 6350730 * 2
def baseEnd_6350730 : Nat := 3260976996928042973368531

theorem tailTrace_6350730 : CollatzResearch.WordTrace tailWord_6350730 prefixEnd_6350730 3260976996928042973368531 := by
  unfold tailWord_6350730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57907538070599325794558411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154420101521598202118822429 57907538070599325794558411)
  ·
    refine ⟨86861307105898988691837617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57907538070599325794558411 86861307105898988691837617)
    ·
      refine ⟨65145980329424241518878213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86861307105898988691837617 65145980329424241518878213)
      ·
        refine ⟨12214871311767045284789665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65145980329424241518878213 12214871311767045284789665)
        ·
          refine ⟨9161153483825283963592249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12214871311767045284789665 9161153483825283963592249)
          ·
            refine ⟨6870865112868962972694187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9161153483825283963592249 6870865112868962972694187)
            ·
              refine ⟨10306297669303444459041281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870865112868962972694187 10306297669303444459041281)
              ·
                refine ⟨7729723251977583344280961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306297669303444459041281 7729723251977583344280961)
                ·
                  refine ⟨5797292438983187508210721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729723251977583344280961 5797292438983187508210721)
                  ·
                    refine ⟨4347969329237390631158041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5797292438983187508210721 4347969329237390631158041)
                    ·
                      refine ⟨3260976996928042973368531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4347969329237390631158041 3260976996928042973368531)
                      ·
                        rfl

theorem cell23_6350730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6350730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350730 prefixEnd_6350730 := by exact prefixLift 6350730
  have htrace : WordTrace (prefixWord ++ tailWord_6350730) baseStart_6350730 baseEnd_6350730 := by
    simpa [prefixWord, tailWord_6350730, baseEnd_6350730] using wordTrace_append hprefix tailTrace_6350730
  have hstable : (prefixWord ++ tailWord_6350730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350730).length < 2 ^ (prefixWord ++ tailWord_6350730).sum := by decide
  have hdescent : baseEnd_6350730 < baseStart_6350730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350792 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 8]
def baseStart_6350792 : Nat := 118140960795 + 6350792 * 2 ^ 59
def prefixEnd_6350792 : Nat := 4983230072969 + 3 ^ 40 * 6350792 * 2
def baseEnd_6350792 : Nat := 362334314747624636754805

theorem tailTrace_6350792 : CollatzResearch.WordTrace tailWord_6350792 prefixEnd_6350792 362334314747624636754805 := by
  unfold tailWord_6350792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115816206804086343883495315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154421609072115125177993753 115816206804086343883495315)
  ·
    refine ⟨173724310206129515825242973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115816206804086343883495315 173724310206129515825242973)
    ·
      refine ⟨65146616327298568434466115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173724310206129515825242973 65146616327298568434466115)
      ·
        refine ⟨97719924490947852651699173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65146616327298568434466115 97719924490947852651699173)
        ·
          refine ⟨18322485842052722372193595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97719924490947852651699173 18322485842052722372193595)
          ·
            refine ⟨27483728763079083558290393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18322485842052722372193595 27483728763079083558290393)
            ·
              refine ⟨20612796572309312668717795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27483728763079083558290393 20612796572309312668717795)
              ·
                refine ⟨30919194858463969003076693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20612796572309312668717795 30919194858463969003076693)
                ·
                  refine ⟨362334314747624636754805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30919194858463969003076693 362334314747624636754805)
                  ·
                    rfl

theorem cell23_6350792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_6350792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350792 prefixEnd_6350792 := by exact prefixLift 6350792
  have htrace : WordTrace (prefixWord ++ tailWord_6350792) baseStart_6350792 baseEnd_6350792 := by
    simpa [prefixWord, tailWord_6350792, baseEnd_6350792] using wordTrace_append hprefix tailTrace_6350792
  have hstable : (prefixWord ++ tailWord_6350792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350792).length < 2 ^ (prefixWord ++ tailWord_6350792).sum := by decide
  have hdescent : baseEnd_6350792 < baseStart_6350792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350796 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_6350796 : Nat := 118140960795 + 6350796 * 2 ^ 59
def prefixEnd_6350796 : Nat := 4983230072969 + 3 ^ 40 * 6350796 * 2
def baseEnd_6350796 : Nat := 1087003628883746571714409

theorem tailTrace_6350796 : CollatzResearch.WordTrace tailWord_6350796 prefixEnd_6350796 1087003628883746571714409 := by
  unfold tailWord_6350796
  simp only [CollatzResearch.WordTrace]
  refine ⟨115816279750079098225068121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154421706333438797633424161 115816279750079098225068121)
  ·
    refine ⟨86862209812559323668801091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115816279750079098225068121 86862209812559323668801091)
    ·
      refine ⟨130293314718838985503201637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86862209812559323668801091 130293314718838985503201637)
      ·
        refine ⟨24429996509782309781850307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130293314718838985503201637 24429996509782309781850307)
        ·
          refine ⟨36644994764673464672775461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24429996509782309781850307 36644994764673464672775461)
          ·
            refine ⟨6870936518376274626145399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36644994764673464672775461 6870936518376274626145399)
            ·
              refine ⟨10306404777564411939218099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870936518376274626145399 10306404777564411939218099)
              ·
                refine ⟨15459607166346617908827149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10306404777564411939218099 15459607166346617908827149)
                ·
                  refine ⟨5797352687379981715810181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15459607166346617908827149 5797352687379981715810181)
                  ·
                    refine ⟨1087003628883746571714409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797352687379981715810181 1087003628883746571714409)
                    ·
                      rfl

theorem cell23_6350796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_6350796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350796 prefixEnd_6350796 := by exact prefixLift 6350796
  have htrace : WordTrace (prefixWord ++ tailWord_6350796) baseStart_6350796 baseEnd_6350796 := by
    simpa [prefixWord, tailWord_6350796, baseEnd_6350796] using wordTrace_append hprefix tailTrace_6350796
  have hstable : (prefixWord ++ tailWord_6350796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350796).length < 2 ^ (prefixWord ++ tailWord_6350796).sum := by decide
  have hdescent : baseEnd_6350796 < baseStart_6350796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350809 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 6]
def baseStart_6350809 : Nat := 118140960795 + 6350809 * 2 ^ 59
def prefixEnd_6350809 : Nat := 4983230072969 + 3 ^ 40 * 6350809 * 2
def baseEnd_6350809 : Nat := 362335284655527573808963

theorem tailTrace_6350809 : CollatzResearch.WordTrace tailWord_6350809 prefixEnd_6350809 362335284655527573808963 := by
  unfold tailWord_6350809
  simp only [CollatzResearch.WordTrace]
  refine ⟨231633033649111099670359481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154422022432740733113572987 231633033649111099670359481)
  ·
    refine ⟨173724775236833324752769611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231633033649111099670359481 173724775236833324752769611)
    ·
      refine ⟨260587162855249987129154417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173724775236833324752769611 260587162855249987129154417)
      ·
        refine ⟨195440372141437490346865813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260587162855249987129154417 195440372141437490346865813)
        ·
          refine ⟨9161267444129882360009335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195440372141437490346865813 9161267444129882360009335)
          ·
            refine ⟨13741901166194823540014003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161267444129882360009335 13741901166194823540014003)
            ·
              refine ⟨20612851749292235310021005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741901166194823540014003 20612851749292235310021005)
              ·
                refine ⟨7729819405984588241257877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20612851749292235310021005 7729819405984588241257877)
                ·
                  refine ⟨362335284655527573808963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7729819405984588241257877 362335284655527573808963)
                  ·
                    rfl

theorem cell23_6350809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_6350809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350809 prefixEnd_6350809 := by exact prefixLift 6350809
  have htrace : WordTrace (prefixWord ++ tailWord_6350809) baseStart_6350809 baseEnd_6350809 := by
    simpa [prefixWord, tailWord_6350809, baseEnd_6350809] using wordTrace_append hprefix tailTrace_6350809
  have hstable : (prefixWord ++ tailWord_6350809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350809).length < 2 ^ (prefixWord ++ tailWord_6350809).sum := by decide
  have hdescent : baseEnd_6350809 < baseStart_6350809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350853 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 1, 1, 3]
def baseStart_6350853 : Nat := 118140960795 + 6350853 * 2 ^ 59
def prefixEnd_6350853 : Nat := 4983230072969 + 3 ^ 40 * 6350853 * 2
def baseEnd_6350853 : Nat := 3261040155048545992130465

theorem tailTrace_6350853 : CollatzResearch.WordTrace tailWord_6350853 prefixEnd_6350853 3261040155048545992130465 := by
  unfold tailWord_6350853
  simp only [CollatzResearch.WordTrace]
  refine ⟨231634638460951695184961213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154423092307301130123307475 231634638460951695184961213)
  ·
    refine ⟨86862989422856885694360455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231634638460951695184961213 86862989422856885694360455)
    ·
      refine ⟨130294484134285328541540683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86862989422856885694360455 130294484134285328541540683)
      ·
        refine ⟨195441726201427992812311025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130294484134285328541540683 195441726201427992812311025)
        ·
          refine ⟨146581294651070994609233269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195441726201427992812311025 146581294651070994609233269)
          ·
            refine ⟨13741996373537905744615619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146581294651070994609233269 13741996373537905744615619)
            ·
              refine ⟨20612994560306858616923429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13741996373537905744615619 20612994560306858616923429)
              ·
                refine ⟨3864936480057535990673143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20612994560306858616923429 3864936480057535990673143)
                ·
                  refine ⟨5797404720086303986009715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864936480057535990673143 5797404720086303986009715)
                  ·
                    refine ⟨8696107080129455979014573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797404720086303986009715 8696107080129455979014573)
                    ·
                      refine ⟨3261040155048545992130465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696107080129455979014573 3261040155048545992130465)
                      ·
                        rfl

theorem cell23_6350853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_6350853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350853 prefixEnd_6350853 := by exact prefixLift 6350853
  have htrace : WordTrace (prefixWord ++ tailWord_6350853) baseStart_6350853 baseEnd_6350853 := by
    simpa [prefixWord, tailWord_6350853, baseEnd_6350853] using wordTrace_append hprefix tailTrace_6350853
  have hstable : (prefixWord ++ tailWord_6350853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350853).length < 2 ^ (prefixWord ++ tailWord_6350853).sum := by decide
  have hdescent : baseEnd_6350853 < baseStart_6350853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350879 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_6350879 : Nat := 118140960795 + 6350879 * 2 ^ 59
def prefixEnd_6350879 : Nat := 4983230072969 + 3 ^ 40 * 6350879 * 2
def baseEnd_6350879 : Nat := 3261053505545562890405345

theorem tailTrace_6350879 : CollatzResearch.WordTrace tailWord_6350879 prefixEnd_6350879 3261053505545562890405345 := by
  unfold tailWord_6350879
  simp only [CollatzResearch.WordTrace]
  refine ⟨231635586758857501625407691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154423724505905001083605127 231635586758857501625407691)
  ·
    refine ⟨347453380138286252438111537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231635586758857501625407691 347453380138286252438111537)
    ·
      refine ⟨260590035103714689328583653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347453380138286252438111537 260590035103714689328583653)
      ·
        refine ⟨48860631581946504249109435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260590035103714689328583653 48860631581946504249109435)
        ·
          refine ⟨73290947372919756373664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48860631581946504249109435 73290947372919756373664153)
          ·
            refine ⟨54968210529689817280248115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73290947372919756373664153 54968210529689817280248115)
            ·
              refine ⟨82452315794534725920372173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54968210529689817280248115 82452315794534725920372173)
              ·
                refine ⟨30919618422950522220139565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82452315794534725920372173 30919618422950522220139565)
                ·
                  refine ⟨11594856908606445832552337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30919618422950522220139565 11594856908606445832552337)
                  ·
                    refine ⟨8696142681454834374414253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11594856908606445832552337 8696142681454834374414253)
                    ·
                      refine ⟨3261053505545562890405345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696142681454834374414253 3261053505545562890405345)
                      ·
                        rfl

theorem cell23_6350879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_6350879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350879 prefixEnd_6350879 := by exact prefixLift 6350879
  have htrace : WordTrace (prefixWord ++ tailWord_6350879) baseStart_6350879 baseEnd_6350879 := by
    simpa [prefixWord, tailWord_6350879, baseEnd_6350879] using wordTrace_append hprefix tailTrace_6350879
  have hstable : (prefixWord ++ tailWord_6350879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350879).length < 2 ^ (prefixWord ++ tailWord_6350879).sum := by decide
  have hdescent : baseEnd_6350879 < baseStart_6350879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350887 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6350887 : Nat := 118140960795 + 6350887 * 2 ^ 59
def prefixEnd_6350887 : Nat := 4983230072969 + 3 ^ 40 * 6350887 * 2
def baseEnd_6350887 : Nat := 3261057613390798859105309

theorem tailTrace_6350887 : CollatzResearch.WordTrace tailWord_6350887 prefixEnd_6350887 3261057613390798859105309 := by
  unfold tailWord_6350887
  simp only [CollatzResearch.WordTrace]
  refine ⟨231635878542828518991698915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154423919028552345994465943 231635878542828518991698915)
  ·
    refine ⟨347453817814242778487548373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231635878542828518991698915 347453817814242778487548373)
    ·
      refine ⟨8143448855021315120801915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 347453817814242778487548373 8143448855021315120801915)
      ·
        refine ⟨12215173282531972681202873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143448855021315120801915 12215173282531972681202873)
        ·
          refine ⟨9161379961898979510902155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12215173282531972681202873 9161379961898979510902155)
          ·
            refine ⟨13742069942848469266353233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161379961898979510902155 13742069942848469266353233)
            ·
              refine ⟨10306552457136351949764925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13742069942848469266353233 10306552457136351949764925)
              ·
                refine ⟨3864957171426131981161847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10306552457136351949764925 3864957171426131981161847)
                ·
                  refine ⟨5797435757139197971742771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864957171426131981161847 5797435757139197971742771)
                  ·
                    refine ⟨8696153635708796957614157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797435757139197971742771 8696153635708796957614157)
                    ·
                      refine ⟨3261057613390798859105309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696153635708796957614157 3261057613390798859105309)
                      ·
                        rfl

theorem cell23_6350887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6350887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350887 prefixEnd_6350887 := by exact prefixLift 6350887
  have htrace : WordTrace (prefixWord ++ tailWord_6350887) baseStart_6350887 baseEnd_6350887 := by
    simpa [prefixWord, tailWord_6350887, baseEnd_6350887] using wordTrace_append hprefix tailTrace_6350887
  have hstable : (prefixWord ++ tailWord_6350887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350887).length < 2 ^ (prefixWord ++ tailWord_6350887).sum := by decide
  have hdescent : baseEnd_6350887 < baseStart_6350887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350896 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_6350896 : Nat := 118140960795 + 6350896 * 2 ^ 59
def prefixEnd_6350896 : Nat := 4983230072969 + 3 ^ 40 * 6350896 * 2
def baseEnd_6350896 : Nat := 3261062234716689323892767

theorem tailTrace_6350896 : CollatzResearch.WordTrace tailWord_6350896 prefixEnd_6350896 3261062234716689323892767 := by
  unfold tailWord_6350896
  simp only [CollatzResearch.WordTrace]
  refine ⟨115818103399897956764388271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154424137866530609019184361 115818103399897956764388271)
  ·
    refine ⟨173727155099846935146582407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115818103399897956764388271 173727155099846935146582407)
    ·
      refine ⟨260590732649770402719873611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173727155099846935146582407 260590732649770402719873611)
      ·
        refine ⟨390886098974655604079810417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260590732649770402719873611 390886098974655604079810417)
        ·
          refine ⟨293164574230991703059857813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390886098974655604079810417 293164574230991703059857813)
          ·
            refine ⟨13742089417077736080930835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 293164574230991703059857813 13742089417077736080930835)
            ·
              refine ⟨20613134125616604121396253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13742089417077736080930835 20613134125616604121396253)
              ·
                refine ⟨7729925297106226545523595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20613134125616604121396253 7729925297106226545523595)
                ·
                  refine ⟨11594887945659339818285393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729925297106226545523595 11594887945659339818285393)
                  ·
                    refine ⟨8696165959244504863714045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11594887945659339818285393 8696165959244504863714045)
                    ·
                      refine ⟨3261062234716689323892767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696165959244504863714045 3261062234716689323892767)
                      ·
                        rfl

theorem cell23_6350896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_6350896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350896 prefixEnd_6350896 := by exact prefixLift 6350896
  have htrace : WordTrace (prefixWord ++ tailWord_6350896) baseStart_6350896 baseEnd_6350896 := by
    simpa [prefixWord, tailWord_6350896, baseEnd_6350896] using wordTrace_append hprefix tailTrace_6350896
  have hstable : (prefixWord ++ tailWord_6350896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350896).length < 2 ^ (prefixWord ++ tailWord_6350896).sum := by decide
  have hdescent : baseEnd_6350896 < baseStart_6350896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350926 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_6350926 : Nat := 118140960795 + 6350926 * 2 ^ 59
def prefixEnd_6350926 : Nat := 4983230072969 + 3 ^ 40 * 6350926 * 2
def baseEnd_6350926 : Nat := 3261077639136324206517629

theorem tailTrace_6350926 : CollatzResearch.WordTrace tailWord_6350926 prefixEnd_6350926 3261077639136324206517629 := by
  unfold tailWord_6350926
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954662623710903581546079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154424867326458152434912421 28954662623710903581546079)
  ·
    refine ⟨43431993935566355372319119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954662623710903581546079 43431993935566355372319119)
    ·
      refine ⟨65147990903349533058478679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43431993935566355372319119 65147990903349533058478679)
      ·
        refine ⟨97721986355024299587718019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65147990903349533058478679 97721986355024299587718019)
        ·
          refine ⟨146582979532536449381577029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97721986355024299587718019 146582979532536449381577029)
          ·
            refine ⟨27484308662350584259045693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146582979532536449381577029 27484308662350584259045693)
            ·
              refine ⟨10306615748381469097142135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27484308662350584259045693 10306615748381469097142135)
              ·
                refine ⟨15459923622572203645713203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10306615748381469097142135 15459923622572203645713203)
                ·
                  refine ⟨23189885433858305468569805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15459923622572203645713203 23189885433858305468569805)
                  ·
                    refine ⟨8696207037696864550713677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23189885433858305468569805 8696207037696864550713677)
                    ·
                      refine ⟨3261077639136324206517629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696207037696864550713677 3261077639136324206517629)
                      ·
                        rfl

theorem cell23_6350926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_6350926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350926 prefixEnd_6350926 := by exact prefixLift 6350926
  have htrace : WordTrace (prefixWord ++ tailWord_6350926) baseStart_6350926 baseEnd_6350926 := by
    simpa [prefixWord, tailWord_6350926, baseEnd_6350926] using wordTrace_append hprefix tailTrace_6350926
  have hstable : (prefixWord ++ tailWord_6350926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350926).length < 2 ^ (prefixWord ++ tailWord_6350926).sum := by decide
  have hdescent : baseEnd_6350926 < baseStart_6350926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6350977 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6350977 : Nat := 118140960795 + 6350977 * 2 ^ 59
def prefixEnd_6350977 : Nat := 4983230072969 + 3 ^ 40 * 6350977 * 2
def baseEnd_6350977 : Nat := 3261103826649703506979895

theorem tailTrace_6350977 : CollatzResearch.WordTrace tailWord_6350977 prefixEnd_6350977 3261103826649703506979895 := by
  unfold tailWord_6350977
  simp only [CollatzResearch.WordTrace]
  refine ⟨231639161112502464362475185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154426107408334976241650123 231639161112502464362475185)
  ·
    refine ⟨173729370834376848271856389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231639161112502464362475185 173729370834376848271856389)
    ·
      refine ⟨32574257031445659050973073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173729370834376848271856389 32574257031445659050973073)
      ·
        refine ⟨24430692773584244288229805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32574257031445659050973073 24430692773584244288229805)
        ·
          refine ⟨9161509790094091608086177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24430692773584244288229805 9161509790094091608086177)
          ·
            refine ⟨6871132342570568706064633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9161509790094091608086177 6871132342570568706064633)
            ·
              refine ⟨5153349256927926529548475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6871132342570568706064633 5153349256927926529548475)
              ·
                refine ⟨7730023885391889794322713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153349256927926529548475 7730023885391889794322713)
                ·
                  refine ⟨5797517914043917345742035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7730023885391889794322713 5797517914043917345742035)
                  ·
                    refine ⟨8696276871065876018613053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797517914043917345742035 8696276871065876018613053)
                    ·
                      refine ⟨3261103826649703506979895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696276871065876018613053 3261103826649703506979895)
                      ·
                        rfl

theorem cell23_6350977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6350977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6350977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6350977 prefixEnd_6350977 := by exact prefixLift 6350977
  have htrace : WordTrace (prefixWord ++ tailWord_6350977) baseStart_6350977 baseEnd_6350977 := by
    simpa [prefixWord, tailWord_6350977, baseEnd_6350977] using wordTrace_append hprefix tailTrace_6350977
  have hstable : (prefixWord ++ tailWord_6350977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6350977).length < 2 ^ (prefixWord ++ tailWord_6350977).sum := by decide
  have hdescent : baseEnd_6350977 < baseStart_6350977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6350977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351026 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_6351026 : Nat := 118140960795 + 6351026 * 2 ^ 59
def prefixEnd_6351026 : Nat := 4983230072969 + 3 ^ 40 * 6351026 * 2
def baseEnd_6351026 : Nat := 3261128987201773815267169

theorem tailTrace_6351026 : CollatzResearch.WordTrace tailWord_6351026 prefixEnd_6351026 3261128987201773815267169 := by
  unfold tailWord_6351026
  simp only [CollatzResearch.WordTrace]
  refine ⟨57910237072331236432752233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154427298859549963820672621 57910237072331236432752233)
  ·
    refine ⟨43432677804248427324564175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57910237072331236432752233 43432677804248427324564175)
    ·
      refine ⟨65149016706372640986846263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43432677804248427324564175 65149016706372640986846263)
      ·
        refine ⟨97723525059558961480269395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65149016706372640986846263 97723525059558961480269395)
        ·
          refine ⟨146585287589338442220404093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97723525059558961480269395 146585287589338442220404093)
          ·
            refine ⟨54969482846001915832651535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146585287589338442220404093 54969482846001915832651535)
            ·
              refine ⟨82454224269002873748977303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54969482846001915832651535 82454224269002873748977303)
              ·
                refine ⟨123681336403504310623465955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82454224269002873748977303 123681336403504310623465955)
                ·
                  refine ⟨185522004605256465935198933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123681336403504310623465955 185522004605256465935198933)
                  ·
                    refine ⟨4348171982935698420356225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185522004605256465935198933 4348171982935698420356225)
                    ·
                      refine ⟨3261128987201773815267169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348171982935698420356225 3261128987201773815267169)
                      ·
                        rfl

theorem cell23_6351026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_6351026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351026 prefixEnd_6351026 := by exact prefixLift 6351026
  have htrace : WordTrace (prefixWord ++ tailWord_6351026) baseStart_6351026 baseEnd_6351026 := by
    simpa [prefixWord, tailWord_6351026, baseEnd_6351026] using wordTrace_append hprefix tailTrace_6351026
  have hstable : (prefixWord ++ tailWord_6351026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351026).length < 2 ^ (prefixWord ++ tailWord_6351026).sum := by decide
  have hdescent : baseEnd_6351026 < baseStart_6351026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351039 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_6351039 : Nat := 118140960795 + 6351039 * 2 ^ 59
def prefixEnd_6351039 : Nat := 4983230072969 + 3 ^ 40 * 6351039 * 2
def baseEnd_6351039 : Nat := 3261135662450282264404609

theorem tailTrace_6351039 : CollatzResearch.WordTrace tailWord_6351039 prefixEnd_6351039 3261135662450282264404609 := by
  unfold tailWord_6351039
  simp only [CollatzResearch.WordTrace]
  refine ⟨231641422438277848951232171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154427614958851899300821447 231641422438277848951232171)
  ·
    refine ⟨347462133657416773426848257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231641422438277848951232171 347462133657416773426848257)
    ·
      refine ⟨260596600243062580070136193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347462133657416773426848257 260596600243062580070136193)
      ·
        refine ⟨195447450182296935052602145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260596600243062580070136193 195447450182296935052602145)
        ·
          refine ⟨146585587636722701289451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195447450182296935052602145 146585587636722701289451609)
          ·
            refine ⟨109939190727542025967088707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146585587636722701289451609 109939190727542025967088707)
            ·
              refine ⟨164908786091313038950633061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109939190727542025967088707 164908786091313038950633061)
              ·
                refine ⟨30920397392121194803243699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164908786091313038950633061 30920397392121194803243699)
                ·
                  refine ⟨46380596088181792204865549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30920397392121194803243699 46380596088181792204865549)
                  ·
                    refine ⟨17392723533068172076824581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46380596088181792204865549 17392723533068172076824581)
                    ·
                      refine ⟨3261135662450282264404609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17392723533068172076824581 3261135662450282264404609)
                      ·
                        rfl

theorem cell23_6351039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_6351039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351039 prefixEnd_6351039 := by exact prefixLift 6351039
  have htrace : WordTrace (prefixWord ++ tailWord_6351039) baseStart_6351039 baseEnd_6351039 := by
    simpa [prefixWord, tailWord_6351039, baseEnd_6351039] using wordTrace_append hprefix tailTrace_6351039
  have hstable : (prefixWord ++ tailWord_6351039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351039).length < 2 ^ (prefixWord ++ tailWord_6351039).sum := by decide
  have hdescent : baseEnd_6351039 < baseStart_6351039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351076 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_6351076 : Nat := 118140960795 + 6351076 * 2 ^ 59
def prefixEnd_6351076 : Nat := 4983230072969 + 3 ^ 40 * 6351076 * 2
def baseEnd_6351076 : Nat := 3261154661234498619641939

theorem tailTrace_6351076 : CollatzResearch.WordTrace tailWord_6351076 prefixEnd_6351076 3261154661234498619641939 := by
  unfold tailWord_6351076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115821385969571902135164541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154428514626095869513552721 115821385969571902135164541)
  ·
    refine ⟨43433019738589463300686703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115821385969571902135164541 43433019738589463300686703)
    ·
      refine ⟨65149529607884194951030055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43433019738589463300686703 65149529607884194951030055)
      ·
        refine ⟨97724294411826292426545083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65149529607884194951030055 97724294411826292426545083)
        ·
          refine ⟨146586441617739438639817625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97724294411826292426545083 146586441617739438639817625)
          ·
            refine ⟨109939831213304578979863219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146586441617739438639817625 109939831213304578979863219)
            ·
              refine ⟨164909746819956868469794829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109939831213304578979863219 164909746819956868469794829)
              ·
                refine ⟨61841155057483825676173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164909746819956868469794829 61841155057483825676173061)
                ·
                  refine ⟨11595216573278217314282449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61841155057483825676173061 11595216573278217314282449)
                  ·
                    refine ⟨8696412429958662985711837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11595216573278217314282449 8696412429958662985711837)
                    ·
                      refine ⟨3261154661234498619641939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696412429958662985711837 3261154661234498619641939)
                      ·
                        rfl

theorem cell23_6351076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_6351076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351076 prefixEnd_6351076 := by exact prefixLift 6351076
  have htrace : WordTrace (prefixWord ++ tailWord_6351076) baseStart_6351076 baseEnd_6351076 := by
    simpa [prefixWord, tailWord_6351076, baseEnd_6351076] using wordTrace_append hprefix tailTrace_6351076
  have hstable : (prefixWord ++ tailWord_6351076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351076).length < 2 ^ (prefixWord ++ tailWord_6351076).sum := by decide
  have hdescent : baseEnd_6351076 < baseStart_6351076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351083 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 1, 4]
def baseStart_6351083 : Nat := 118140960795 + 6351083 * 2 ^ 59
def prefixEnd_6351083 : Nat := 4983230072969 + 3 ^ 40 * 6351083 * 2
def baseEnd_6351083 : Nat := 1087052751866360030751469

theorem tailTrace_6351083 : CollatzResearch.WordTrace tailWord_6351083 prefixEnd_6351083 1087052751866360030751469 := by
  unfold tailWord_6351083
  simp only [CollatzResearch.WordTrace]
  refine ⟨231643027250118444465833903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154428684833412296310555935 231643027250118444465833903)
  ·
    refine ⟨347464540875177666698750855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231643027250118444465833903 347464540875177666698750855)
    ·
      refine ⟨521196811312766500048126283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347464540875177666698750855 521196811312766500048126283)
      ·
        refine ⟨781795216969149750072189425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521196811312766500048126283 781795216969149750072189425)
        ·
          refine ⟨586346412726862312554142069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781795216969149750072189425 586346412726862312554142069)
          ·
            refine ⟨54969976193143341801950819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 586346412726862312554142069 54969976193143341801950819)
            ·
              refine ⟨82454964289715012702926229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54969976193143341801950819 82454964289715012702926229)
              ·
                refine ⟨3865076451080391220449667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82454964289715012702926229 3865076451080391220449667)
                ·
                  refine ⟨5797614676620586830674501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865076451080391220449667 5797614676620586830674501)
                  ·
                    refine ⟨1087052751866360030751469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797614676620586830674501 1087052751866360030751469)
                    ·
                      rfl

theorem cell23_6351083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 4].length) (baseStart_6351083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351083 prefixEnd_6351083 := by exact prefixLift 6351083
  have htrace : WordTrace (prefixWord ++ tailWord_6351083) baseStart_6351083 baseEnd_6351083 := by
    simpa [prefixWord, tailWord_6351083, baseEnd_6351083] using wordTrace_append hprefix tailTrace_6351083
  have hstable : (prefixWord ++ tailWord_6351083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351083).length < 2 ^ (prefixWord ++ tailWord_6351083).sum := by decide
  have hdescent : baseEnd_6351083 < baseStart_6351083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351140 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_6351140 : Nat := 118140960795 + 6351140 * 2 ^ 59
def prefixEnd_6351140 : Nat := 4983230072969 + 3 ^ 40 * 6351140 * 2
def baseEnd_6351140 : Nat := 3261187523996386369241645

theorem tailTrace_6351140 : CollatzResearch.WordTrace tailWord_6351140 prefixEnd_6351140 3261187523996386369241645 := by
  unfold tailWord_6351140
  simp only [CollatzResearch.WordTrace]
  refine ⟨115822553105455971600329437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154430070807274628800439249 115822553105455971600329437)
  ·
    refine ⟨43433457414545989350123539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115822553105455971600329437 43433457414545989350123539)
    ·
      refine ⟨65150186121818984025185309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43433457414545989350123539 65150186121818984025185309)
      ·
        refine ⟨24431319795682119009444491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65150186121818984025185309 24431319795682119009444491)
        ·
          refine ⟨36646979693523178514166737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24431319795682119009444491 36646979693523178514166737)
          ·
            refine ⟨27485234770142383885625053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36646979693523178514166737 27485234770142383885625053)
            ·
              refine ⟨10306963038803393957109395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27485234770142383885625053 10306963038803393957109395)
              ·
                refine ⟨15460444558205090935664093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10306963038803393957109395 15460444558205090935664093)
                ·
                  refine ⟨5797666709326909100874035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15460444558205090935664093 5797666709326909100874035)
                  ·
                    refine ⟨8696500063990363651311053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797666709326909100874035 8696500063990363651311053)
                    ·
                      refine ⟨3261187523996386369241645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696500063990363651311053 3261187523996386369241645)
                      ·
                        rfl

theorem cell23_6351140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_6351140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351140 prefixEnd_6351140 := by exact prefixLift 6351140
  have htrace : WordTrace (prefixWord ++ tailWord_6351140) baseStart_6351140 baseEnd_6351140 := by
    simpa [prefixWord, tailWord_6351140, baseEnd_6351140] using wordTrace_append hprefix tailTrace_6351140
  have hstable : (prefixWord ++ tailWord_6351140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351140).length < 2 ^ (prefixWord ++ tailWord_6351140).sum := by decide
  have hdescent : baseEnd_6351140 < baseStart_6351140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351176 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_6351176 : Nat := 118140960795 + 6351176 * 2 ^ 59
def prefixEnd_6351176 : Nat := 4983230072969 + 3 ^ 40 * 6351176 * 2
def baseEnd_6351176 : Nat := 3261206009299948228391479

theorem tailTrace_6351176 : CollatzResearch.WordTrace tailWord_6351176 prefixEnd_6351176 3261206009299948228391479 := by
  unfold tailWord_6351176
  simp only [CollatzResearch.WordTrace]
  refine ⟨115823209619390760674484691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154430946159187680899312921 115823209619390760674484691)
  ·
    refine ⟨173734814429086141011727037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115823209619390760674484691 173734814429086141011727037)
    ·
      refine ⟨65150555410907302879397639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173734814429086141011727037 65150555410907302879397639)
      ·
        refine ⟨97725833116360954319096459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65150555410907302879397639 97725833116360954319096459)
        ·
          refine ⟨146588749674541431478644689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97725833116360954319096459 146588749674541431478644689)
          ·
            refine ⟨109941562255906073608983517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146588749674541431478644689 109941562255906073608983517)
            ·
              refine ⟨41228085845964777603368819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109941562255906073608983517 41228085845964777603368819)
              ·
                refine ⟨61842128768947166405053229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41228085845964777603368819 61842128768947166405053229)
                ·
                  refine ⟨23190798288355187401894961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61842128768947166405053229 23190798288355187401894961)
                  ·
                    refine ⟨17393098716266390551421221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23190798288355187401894961 17393098716266390551421221)
                    ·
                      refine ⟨3261206009299948228391479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17393098716266390551421221 3261206009299948228391479)
                      ·
                        rfl

theorem cell23_6351176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_6351176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351176 prefixEnd_6351176 := by exact prefixLift 6351176
  have htrace : WordTrace (prefixWord ++ tailWord_6351176) baseStart_6351176 baseEnd_6351176 := by
    simpa [prefixWord, tailWord_6351176, baseEnd_6351176] using wordTrace_append hprefix tailTrace_6351176
  have hstable : (prefixWord ++ tailWord_6351176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351176).length < 2 ^ (prefixWord ++ tailWord_6351176).sum := by decide
  have hdescent : baseEnd_6351176 < baseStart_6351176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351180 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6351180 : Nat := 118140960795 + 6351180 * 2 ^ 59
def prefixEnd_6351180 : Nat := 4983230072969 + 3 ^ 40 * 6351180 * 2
def baseEnd_6351180 : Nat := 3261208063222566212741461

theorem tailTrace_6351180 : CollatzResearch.WordTrace tailWord_6351180 prefixEnd_6351180 3261208063222566212741461 := by
  unfold tailWord_6351180
  simp only [CollatzResearch.WordTrace]
  refine ⟨115823282565383515016057497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154431043420511353354743329 115823282565383515016057497)
  ·
    refine ⟨86867461924037636262043123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115823282565383515016057497 86867461924037636262043123)
    ·
      refine ⟨130301192886056454393064685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86867461924037636262043123 130301192886056454393064685)
      ·
        refine ⟨48862947332271170397399257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130301192886056454393064685 48862947332271170397399257)
        ·
          refine ⟨36647210499203377798049443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48862947332271170397399257 36647210499203377798049443)
          ·
            refine ⟨54970815748805066697074165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36647210499203377798049443 54970815748805066697074165)
            ·
              refine ⟨5153513976450475002850703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54970815748805066697074165 5153513976450475002850703)
              ·
                refine ⟨7730270964675712504276055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153513976450475002850703 7730270964675712504276055)
                ·
                  refine ⟨11595406447013568756414083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7730270964675712504276055 11595406447013568756414083)
                  ·
                    refine ⟨17393109670520353134621125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11595406447013568756414083 17393109670520353134621125)
                    ·
                      refine ⟨3261208063222566212741461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17393109670520353134621125 3261208063222566212741461)
                      ·
                        rfl

theorem cell23_6351180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6351180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351180 prefixEnd_6351180 := by exact prefixLift 6351180
  have htrace : WordTrace (prefixWord ++ tailWord_6351180) baseStart_6351180 baseEnd_6351180 := by
    simpa [prefixWord, tailWord_6351180, baseEnd_6351180] using wordTrace_append hprefix tailTrace_6351180
  have hstable : (prefixWord ++ tailWord_6351180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351180).length < 2 ^ (prefixWord ++ tailWord_6351180).sum := by decide
  have hdescent : baseEnd_6351180 < baseStart_6351180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351210 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6351210 : Nat := 118140960795 + 6351210 * 2 ^ 59
def prefixEnd_6351210 : Nat := 4983230072969 + 3 ^ 40 * 6351210 * 2
def baseEnd_6351210 : Nat := 3261223467642201095366323

theorem tailTrace_6351210 : CollatzResearch.WordTrace tailWord_6351210 prefixEnd_6351210 3261223467642201095366323 := by
  unfold tailWord_6351210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57911914830164586288926771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154431772880438896770471389 57911914830164586288926771)
  ·
    refine ⟨86867872245246879433390157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57911914830164586288926771 86867872245246879433390157)
    ·
      refine ⟨32575452091967579787521309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86867872245246879433390157 32575452091967579787521309)
      ·
        refine ⟨12215794534487842420320491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32575452091967579787521309 12215794534487842420320491)
        ·
          refine ⟨18323691801731763630480737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12215794534487842420320491 18323691801731763630480737)
          ·
            refine ⟨13742768851298822722860553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18323691801731763630480737 13742768851298822722860553)
            ·
              refine ⟨10307076638474117042145415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13742768851298822722860553 10307076638474117042145415)
              ·
                refine ⟨15460614957711175563218123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307076638474117042145415 15460614957711175563218123)
                ·
                  refine ⟨23190922436566763344827185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15460614957711175563218123 23190922436566763344827185)
                  ·
                    refine ⟨17393191827425072508620389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23190922436566763344827185 17393191827425072508620389)
                    ·
                      refine ⟨3261223467642201095366323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17393191827425072508620389 3261223467642201095366323)
                      ·
                        rfl

theorem cell23_6351210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6351210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351210 prefixEnd_6351210 := by exact prefixLift 6351210
  have htrace : WordTrace (prefixWord ++ tailWord_6351210) baseStart_6351210 baseEnd_6351210 := by
    simpa [prefixWord, tailWord_6351210, baseEnd_6351210] using wordTrace_append hprefix tailTrace_6351210
  have hstable : (prefixWord ++ tailWord_6351210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351210).length < 2 ^ (prefixWord ++ tailWord_6351210).sum := by decide
  have hdescent : baseEnd_6351210 < baseStart_6351210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351234 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6351234 : Nat := 118140960795 + 6351234 * 2 ^ 59
def prefixEnd_6351234 : Nat := 4983230072969 + 3 ^ 40 * 6351234 * 2
def baseEnd_6351234 : Nat := 3261235791177909001466213

theorem tailTrace_6351234 : CollatzResearch.WordTrace tailWord_6351234 prefixEnd_6351234 3261235791177909001466213 := by
  unfold tailWord_6351234
  simp only [CollatzResearch.WordTrace]
  refine ⟨57912133668142849313645189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154432356448380931503053837 57912133668142849313645189)
  ·
    refine ⟨10858525062776784246308473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57912133668142849313645189 10858525062776784246308473)
    ·
      refine ⟨8143893797082588184731355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10858525062776784246308473 8143893797082588184731355)
      ·
        refine ⟨12215840695623882277097033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143893797082588184731355 12215840695623882277097033)
        ·
          refine ⟨9161880521717911707822775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12215840695623882277097033 9161880521717911707822775)
          ·
            refine ⟨13742820782576867561734163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161880521717911707822775 13742820782576867561734163)
            ·
              refine ⟨20614231173865301342601245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13742820782576867561734163 20614231173865301342601245)
              ·
                refine ⟨7730336690199488003475467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20614231173865301342601245 7730336690199488003475467)
                ·
                  refine ⟨11595505035299232005213201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7730336690199488003475467 11595505035299232005213201)
                  ·
                    refine ⟨8696628776474424003909901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11595505035299232005213201 8696628776474424003909901)
                    ·
                      refine ⟨3261235791177909001466213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696628776474424003909901 3261235791177909001466213)
                      ·
                        rfl

theorem cell23_6351234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6351234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351234 prefixEnd_6351234 := by exact prefixLift 6351234
  have htrace : WordTrace (prefixWord ++ tailWord_6351234) baseStart_6351234 baseEnd_6351234 := by
    simpa [prefixWord, tailWord_6351234, baseEnd_6351234] using wordTrace_append hprefix tailTrace_6351234
  have hstable : (prefixWord ++ tailWord_6351234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351234).length < 2 ^ (prefixWord ++ tailWord_6351234).sum := by decide
  have hdescent : baseEnd_6351234 < baseStart_6351234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351370 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_6351370 : Nat := 118140960795 + 6351370 * 2 ^ 59
def prefixEnd_6351370 : Nat := 4983230072969 + 3 ^ 40 * 6351370 * 2
def baseEnd_6351370 : Nat := 1087101874848973489788529

theorem tailTrace_6351370 : CollatzResearch.WordTrace tailWord_6351370 prefixEnd_6351370 1087101874848973489788529 := by
  unfold tailWord_6351370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57913373750019673120382891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154435663333385794987687709 57913373750019673120382891)
  ·
    refine ⟨86870060625029509680574337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57913373750019673120382891 86870060625029509680574337)
    ·
      refine ⟨65152545468772132260430753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86870060625029509680574337 65152545468772132260430753)
      ·
        refine ⟨48864409101579099195323065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65152545468772132260430753 48864409101579099195323065)
        ·
          refine ⟨36648306826184324396492299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48864409101579099195323065 36648306826184324396492299)
          ·
            refine ⟨54972460239276486594738449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36648306826184324396492299 54972460239276486594738449)
            ·
              refine ⟨41229345179457364946053837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54972460239276486594738449 41229345179457364946053837)
              ·
                refine ⟨15461004442296511854770189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41229345179457364946053837 15461004442296511854770189)
                ·
                  refine ⟨5797876665861191945538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15461004442296511854770189 5797876665861191945538821)
                  ·
                    refine ⟨1087101874848973489788529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797876665861191945538821 1087101874848973489788529)
                    ·
                      rfl

theorem cell23_6351370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_6351370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351370 prefixEnd_6351370 := by exact prefixLift 6351370
  have htrace : WordTrace (prefixWord ++ tailWord_6351370) baseStart_6351370 baseEnd_6351370 := by
    simpa [prefixWord, tailWord_6351370, baseEnd_6351370] using wordTrace_append hprefix tailTrace_6351370
  have hstable : (prefixWord ++ tailWord_6351370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351370).length < 2 ^ (prefixWord ++ tailWord_6351370).sum := by decide
  have hdescent : baseEnd_6351370 < baseStart_6351370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351460 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_6351460 : Nat := 118140960795 + 6351460 * 2 ^ 59
def prefixEnd_6351460 : Nat := 4983230072969 + 3 ^ 40 * 6351460 * 2
def baseEnd_6351460 : Nat := 1087117279268608372413391

theorem tailTrace_6351460 : CollatzResearch.WordTrace tailWord_6351460 prefixEnd_6351460 1087117279268608372413391 := by
  unfold tailWord_6351460
  simp only [CollatzResearch.WordTrace]
  refine ⟨115828388784876318926153917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154437851713168425234871889 115828388784876318926153917)
  ·
    refine ⟨43435645794328619597307719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115828388784876318926153917 43435645794328619597307719)
    ·
      refine ⟨65153468691492929395961579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43435645794328619597307719 65153468691492929395961579)
      ·
        refine ⟨97730203037239394093942369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65153468691492929395961579 97730203037239394093942369)
        ·
          refine ⟨73297652277929545570456777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97730203037239394093942369 73297652277929545570456777)
          ·
            refine ⟨54973239208447159177842583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73297652277929545570456777 54973239208447159177842583)
            ·
              refine ⟨82459858812670738766763875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54973239208447159177842583 82459858812670738766763875)
              ·
                refine ⟨123689788219006108150145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82459858812670738766763875 123689788219006108150145813)
                ·
                  refine ⟨5797958822765911319538085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123689788219006108150145813 5797958822765911319538085)
                  ·
                    refine ⟨1087117279268608372413391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797958822765911319538085 1087117279268608372413391)
                    ·
                      rfl

theorem cell23_6351460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_6351460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351460 prefixEnd_6351460 := by exact prefixLift 6351460
  have htrace : WordTrace (prefixWord ++ tailWord_6351460) baseStart_6351460 baseEnd_6351460 := by
    simpa [prefixWord, tailWord_6351460, baseEnd_6351460] using wordTrace_append hprefix tailTrace_6351460
  have hstable : (prefixWord ++ tailWord_6351460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351460).length < 2 ^ (prefixWord ++ tailWord_6351460).sum := by decide
  have hdescent : baseEnd_6351460 < baseStart_6351460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351478 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6351478 : Nat := 118140960795 + 6351478 * 2 ^ 59
def prefixEnd_6351478 : Nat := 4983230072969 + 3 ^ 40 * 6351478 * 2
def baseEnd_6351478 : Nat := 3261361080457606046815091

theorem tailTrace_6351478 : CollatzResearch.WordTrace tailWord_6351478 prefixEnd_6351478 3261361080457606046815091 := by
  unfold tailWord_6351478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14478589630230464182903943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154438289389124951284308725 14478589630230464182903943)
  ·
    refine ⟨21717884445345696274355915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14478589630230464182903943 21717884445345696274355915)
    ·
      refine ⟨32576826668018544411533873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21717884445345696274355915 32576826668018544411533873)
      ·
        refine ⟨24432620001013908308650405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32576826668018544411533873 24432620001013908308650405)
        ·
          refine ⟨4581116250190107807871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24432620001013908308650405 4581116250190107807871951)
          ·
            refine ⟨6871674375285161711807927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581116250190107807871951 6871674375285161711807927)
            ·
              refine ⟨10307511562927742567711891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6871674375285161711807927 10307511562927742567711891)
              ·
                refine ⟨15461267344391613851567837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307511562927742567711891 15461267344391613851567837)
                ·
                  refine ⟨5797975254146855194337939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15461267344391613851567837 5797975254146855194337939)
                  ·
                    refine ⟨8696962881220282791506909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5797975254146855194337939 8696962881220282791506909)
                    ·
                      refine ⟨3261361080457606046815091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8696962881220282791506909 3261361080457606046815091)
                      ·
                        rfl

theorem cell23_6351478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6351478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351478 prefixEnd_6351478 := by exact prefixLift 6351478
  have htrace : WordTrace (prefixWord ++ tailWord_6351478) baseStart_6351478 baseEnd_6351478 := by
    simpa [prefixWord, tailWord_6351478, baseEnd_6351478] using wordTrace_append hprefix tailTrace_6351478
  have hstable : (prefixWord ++ tailWord_6351478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351478).length < 2 ^ (prefixWord ++ tailWord_6351478).sum := by decide
  have hdescent : baseEnd_6351478 < baseStart_6351478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351484 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_6351484 : Nat := 118140960795 + 6351484 * 2 ^ 59
def prefixEnd_6351484 : Nat := 4983230072969 + 3 ^ 40 * 6351484 * 2
def baseEnd_6351484 : Nat := 3261364161341533023340063

theorem tailTrace_6351484 : CollatzResearch.WordTrace tailWord_6351484 prefixEnd_6351484 3261364161341533023340063 := by
  unfold tailWord_6351484
  simp only [CollatzResearch.WordTrace]
  refine ⟨115828826460832844975590753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154438435281110459967454337 115828826460832844975590753)
  ·
    refine ⟨86871619845624633731693065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115828826460832844975590753 86871619845624633731693065)
    ·
      refine ⟨65153714884218475298769799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86871619845624633731693065 65153714884218475298769799)
      ·
        refine ⟨97730572326327712948154699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65153714884218475298769799 97730572326327712948154699)
        ·
          refine ⟨146595858489491569422232049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97730572326327712948154699 146595858489491569422232049)
          ·
            refine ⟨109946893867118677066674037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146595858489491569422232049 109946893867118677066674037)
            ·
              refine ⟨10307521300042375975000691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109946893867118677066674037 10307521300042375975000691)
              ·
                refine ⟨15461281950063563962501037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307521300042375975000691 15461281950063563962501037)
                ·
                  refine ⟨5797980731273836485937889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15461281950063563962501037 5797980731273836485937889)
                  ·
                    refine ⟨4348485548455377364453417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5797980731273836485937889 4348485548455377364453417)
                    ·
                      refine ⟨3261364161341533023340063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348485548455377364453417 3261364161341533023340063)
                      ·
                        rfl

theorem cell23_6351484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_6351484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351484 prefixEnd_6351484 := by exact prefixLift 6351484
  have htrace : WordTrace (prefixWord ++ tailWord_6351484) baseStart_6351484 baseEnd_6351484 := by
    simpa [prefixWord, tailWord_6351484, baseEnd_6351484] using wordTrace_append hprefix tailTrace_6351484
  have hstable : (prefixWord ++ tailWord_6351484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351484).length < 2 ^ (prefixWord ++ tailWord_6351484).sum := by decide
  have hdescent : baseEnd_6351484 < baseStart_6351484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351503 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 7]
def baseStart_6351503 : Nat := 118140960795 + 6351503 * 2 ^ 59
def prefixEnd_6351503 : Nat := 4983230072969 + 3 ^ 40 * 6351503 * 2
def baseEnd_6351503 : Nat := 1087124639157989483000825

theorem tailTrace_6351503 : CollatzResearch.WordTrace tailWord_6351503 prefixEnd_6351503 1087124639157989483000825 := by
  unfold tailWord_6351503
  simp only [CollatzResearch.WordTrace]
  refine ⟨231658345908596856196123163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154438897272397904130748775 231658345908596856196123163)
  ·
    refine ⟨347487518862895284294184745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231658345908596856196123163 347487518862895284294184745)
    ·
      refine ⟨260615639147171463220638559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347487518862895284294184745 260615639147171463220638559)
      ·
        refine ⟨390923458720757194830957839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260615639147171463220638559 390923458720757194830957839)
        ·
          refine ⟨586385188081135792246436759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390923458720757194830957839 586385188081135792246436759)
          ·
            refine ⟨879577782121703688369655139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586385188081135792246436759 879577782121703688369655139)
            ·
              refine ⟨1319366673182555532554482709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879577782121703688369655139 1319366673182555532554482709)
              ·
                refine ⟨61845312805432290588491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1319366673182555532554482709 61845312805432290588491377)
                ·
                  refine ⟨46383984604074217941368533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61845312805432290588491377 46383984604074217941368533)
                  ·
                    refine ⟨1087124639157989483000825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46383984604074217941368533 1087124639157989483000825)
                    ·
                      rfl

theorem cell23_6351503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_6351503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351503 prefixEnd_6351503 := by exact prefixLift 6351503
  have htrace : WordTrace (prefixWord ++ tailWord_6351503) baseStart_6351503 baseEnd_6351503 := by
    simpa [prefixWord, tailWord_6351503, baseEnd_6351503] using wordTrace_append hprefix tailTrace_6351503
  have hstable : (prefixWord ++ tailWord_6351503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351503).length < 2 ^ (prefixWord ++ tailWord_6351503).sum := by decide
  have hdescent : baseEnd_6351503 < baseStart_6351503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351514 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6351514 : Nat := 118140960795 + 6351514 * 2 ^ 59
def prefixEnd_6351514 : Nat := 4983230072969 + 3 ^ 40 * 6351514 * 2
def baseEnd_6351514 : Nat := 3261379565761167905964925

theorem tailTrace_6351514 : CollatzResearch.WordTrace tailWord_6351514 prefixEnd_6351514 3261379565761167905964925 := by
  unfold tailWord_6351514
  simp only [CollatzResearch.WordTrace]
  refine ⟨57914686777889251268693399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154439164741038003383182397 57914686777889251268693399)
  ·
    refine ⟨86872030166833876903040099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57914686777889251268693399 86872030166833876903040099)
    ·
      refine ⟨130308045250250815354560149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86872030166833876903040099 130308045250250815354560149)
      ·
        refine ⟨6108189621105506969745007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130308045250250815354560149 6108189621105506969745007)
        ·
          refine ⟨9162284431658260454617511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108189621105506969745007 9162284431658260454617511)
          ·
            refine ⟨13743426647487390681926267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162284431658260454617511 13743426647487390681926267)
            ·
              refine ⟨20615139971231086022889401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743426647487390681926267 20615139971231086022889401)
              ·
                refine ⟨15461354978423314517167051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20615139971231086022889401 15461354978423314517167051)
                ·
                  refine ⟨23192032467634971775750577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15461354978423314517167051 23192032467634971775750577)
                  ·
                    refine ⟨17394024350726228831812933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23192032467634971775750577 17394024350726228831812933)
                    ·
                      refine ⟨3261379565761167905964925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17394024350726228831812933 3261379565761167905964925)
                      ·
                        rfl

theorem cell23_6351514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6351514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351514 prefixEnd_6351514 := by exact prefixLift 6351514
  have htrace : WordTrace (prefixWord ++ tailWord_6351514) baseStart_6351514 baseEnd_6351514 := by
    simpa [prefixWord, tailWord_6351514, baseEnd_6351514] using wordTrace_append hprefix tailTrace_6351514
  have hstable : (prefixWord ++ tailWord_6351514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351514).length < 2 ^ (prefixWord ++ tailWord_6351514).sum := by decide
  have hdescent : baseEnd_6351514 < baseStart_6351514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351517 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_6351517 : Nat := 118140960795 + 6351517 * 2 ^ 59
def prefixEnd_6351517 : Nat := 4983230072969 + 3 ^ 40 * 6351517 * 2
def baseEnd_6351517 : Nat := 3261381106203131394227411

theorem tailTrace_6351517 : CollatzResearch.WordTrace tailWord_6351517 prefixEnd_6351517 3261381106203131394227411 := by
  unfold tailWord_6351517
  simp only [CollatzResearch.WordTrace]
  refine ⟨231658856530546136587132805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154439237687030757724755203 231658856530546136587132805)
  ·
    refine ⟨43436035599477400610087401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231658856530546136587132805 43436035599477400610087401)
    ·
      refine ⟨32577026699608050457565551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43436035599477400610087401 32577026699608050457565551)
      ·
        refine ⟨48865540049412075686348327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32577026699608050457565551 48865540049412075686348327)
        ·
          refine ⟨73298310074118113529522491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48865540049412075686348327 73298310074118113529522491)
          ·
            refine ⟨109947465111177170294283737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73298310074118113529522491 109947465111177170294283737)
            ·
              refine ⟨82460598833382877720712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109947465111177170294283737 82460598833382877720712803)
              ·
                refine ⟨123690898250074316581069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82460598833382877720712803 123690898250074316581069205)
                ·
                  refine ⟨5798010855472233589737619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123690898250074316581069205 5798010855472233589737619)
                  ·
                    refine ⟨8697016283208350384606429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5798010855472233589737619 8697016283208350384606429)
                    ·
                      refine ⟨3261381106203131394227411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8697016283208350384606429 3261381106203131394227411)
                      ·
                        rfl

theorem cell23_6351517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_6351517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351517 prefixEnd_6351517 := by exact prefixLift 6351517
  have htrace : WordTrace (prefixWord ++ tailWord_6351517) baseStart_6351517 baseEnd_6351517 := by
    simpa [prefixWord, tailWord_6351517, baseEnd_6351517] using wordTrace_append hprefix tailTrace_6351517
  have hstable : (prefixWord ++ tailWord_6351517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351517).length < 2 ^ (prefixWord ++ tailWord_6351517).sum := by decide
  have hdescent : baseEnd_6351517 < baseStart_6351517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351518 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6351518 : Nat := 118140960795 + 6351518 * 2 ^ 59
def prefixEnd_6351518 : Nat := 4983230072969 + 3 ^ 40 * 6351518 * 2
def baseEnd_6351518 : Nat := 3261381619683785890314907

theorem tailTrace_6351518 : CollatzResearch.WordTrace tailWord_6351518 prefixEnd_6351518 3261381619683785890314907 := by
  unfold tailWord_6351518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28957361625442814219739901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154439262002361675838612805 28957361625442814219739901)
  ·
    refine ⟨10859010609541055332402463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28957361625442814219739901 10859010609541055332402463)
    ·
      refine ⟨16288515914311582998603695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859010609541055332402463 16288515914311582998603695)
      ·
        refine ⟨24432773871467374497905543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288515914311582998603695 24432773871467374497905543)
        ·
          refine ⟨36649160807201061746858315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432773871467374497905543 36649160807201061746858315)
          ·
            refine ⟨54973741210801592620287473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36649160807201061746858315 54973741210801592620287473)
            ·
              refine ⟨41230305908101194465215605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54973741210801592620287473 41230305908101194465215605)
              ·
                refine ⟨3865341178884486981113963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41230305908101194465215605 3865341178884486981113963)
                ·
                  refine ⟨5798011768326730471670945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865341178884486981113963 5798011768326730471670945)
                  ·
                    refine ⟨4348508826245047853753209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5798011768326730471670945 4348508826245047853753209)
                    ·
                      refine ⟨3261381619683785890314907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348508826245047853753209 3261381619683785890314907)
                      ·
                        rfl

theorem cell23_6351518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6351518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351518 prefixEnd_6351518 := by exact prefixLift 6351518
  have htrace : WordTrace (prefixWord ++ tailWord_6351518) baseStart_6351518 baseEnd_6351518 := by
    simpa [prefixWord, tailWord_6351518, baseEnd_6351518] using wordTrace_append hprefix tailTrace_6351518
  have hstable : (prefixWord ++ tailWord_6351518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351518).length < 2 ^ (prefixWord ++ tailWord_6351518).sum := by decide
  have hdescent : baseEnd_6351518 < baseStart_6351518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351521 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6351521 : Nat := 118140960795 + 6351521 * 2 ^ 59
def prefixEnd_6351521 : Nat := 4983230072969 + 3 ^ 40 * 6351521 * 2
def baseEnd_6351521 : Nat := 3261383160125749378577393

theorem tailTrace_6351521 : CollatzResearch.WordTrace tailWord_6351521 prefixEnd_6351521 3261383160125749378577393 := by
  unfold tailWord_6351521
  simp only [CollatzResearch.WordTrace]
  refine ⟨231659002422531645270278417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154439334948354430180185611 231659002422531645270278417)
  ·
    refine ⟨173744251816898733952708813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231659002422531645270278417 173744251816898733952708813)
    ·
      refine ⟨65154094431337025232265805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173744251816898733952708813 65154094431337025232265805)
      ·
        refine ⟨24432785411751384462099677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65154094431337025232265805 24432785411751384462099677)
        ·
          refine ⟨9162294529406769173287379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24432785411751384462099677 9162294529406769173287379)
          ·
            refine ⟨13743441794110153759931069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162294529406769173287379 13743441794110153759931069)
            ·
              refine ⟨5153790672791307659974151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13743441794110153759931069 5153790672791307659974151)
              ·
                refine ⟨7730686009186961489961227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153790672791307659974151 7730686009186961489961227)
                ·
                  refine ⟨11596029013780442234941841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7730686009186961489961227 11596029013780442234941841)
                  ·
                    refine ⟨8697021760335331676206381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11596029013780442234941841 8697021760335331676206381)
                    ·
                      refine ⟨3261383160125749378577393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8697021760335331676206381 3261383160125749378577393)
                      ·
                        rfl

theorem cell23_6351521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6351521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351521 prefixEnd_6351521 := by exact prefixLift 6351521
  have htrace : WordTrace (prefixWord ++ tailWord_6351521) baseStart_6351521 baseEnd_6351521 := by
    simpa [prefixWord, tailWord_6351521, baseEnd_6351521] using wordTrace_append hprefix tailTrace_6351521
  have hstable : (prefixWord ++ tailWord_6351521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351521).length < 2 ^ (prefixWord ++ tailWord_6351521).sum := by decide
  have hdescent : baseEnd_6351521 < baseStart_6351521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351587 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6351587 : Nat := 118140960795 + 6351587 * 2 ^ 59
def prefixEnd_6351587 : Nat := 4983230072969 + 3 ^ 40 * 6351587 * 2
def baseEnd_6351587 : Nat := 3261417049848946120352089

theorem tailTrace_6351587 : CollatzResearch.WordTrace tailWord_6351587 prefixEnd_6351587 3261417049848946120352089 := by
  unfold tailWord_6351587
  simp only [CollatzResearch.WordTrace]
  refine ⟨231661409640292538542181015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154440939760195025694787343 231661409640292538542181015)
  ·
    refine ⟨347492114460438807813271523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231661409640292538542181015 347492114460438807813271523)
    ·
      refine ⟨521238171690658211719907285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347492114460438807813271523 521238171690658211719907285)
      ·
        refine ⟨12216519648999801837185327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 521238171690658211719907285 12216519648999801837185327)
        ·
          refine ⟨18324779473499702755777991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216519648999801837185327 18324779473499702755777991)
          ·
            refine ⟨27487169210249554133666987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18324779473499702755777991 27487169210249554133666987)
            ·
              refine ⟨41230753815374331200500481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27487169210249554133666987 41230753815374331200500481)
              ·
                refine ⟨30923065361530748400375361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41230753815374331200500481 30923065361530748400375361)
                ·
                  refine ⟨23192299021148061300281521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30923065361530748400375361 23192299021148061300281521)
                  ·
                    refine ⟨17394224265861045975211141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23192299021148061300281521 17394224265861045975211141)
                    ·
                      refine ⟨3261417049848946120352089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17394224265861045975211141 3261417049848946120352089)
                      ·
                        rfl

theorem cell23_6351587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6351587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351587 prefixEnd_6351587 := by exact prefixLift 6351587
  have htrace : WordTrace (prefixWord ++ tailWord_6351587) baseStart_6351587 baseEnd_6351587 := by
    simpa [prefixWord, tailWord_6351587, baseEnd_6351587] using wordTrace_append hprefix tailTrace_6351587
  have hstable : (prefixWord ++ tailWord_6351587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351587).length < 2 ^ (prefixWord ++ tailWord_6351587).sum := by decide
  have hdescent : baseEnd_6351587 < baseStart_6351587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351597 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6351597 : Nat := 118140960795 + 6351597 * 2 ^ 59
def prefixEnd_6351597 : Nat := 4983230072969 + 3 ^ 40 * 6351597 * 2
def baseEnd_6351597 : Nat := 362380242739499009025227

theorem tailTrace_6351597 : CollatzResearch.WordTrace tailWord_6351597 prefixEnd_6351597 362380242739499009025227 := by
  unfold tailWord_6351597
  simp only [CollatzResearch.WordTrace]
  refine ⟨231661774370256310250045045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154441182913504206833363363 231661774370256310250045045)
  ·
    refine ⟨21718291347211529085941723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231661774370256310250045045 21718291347211529085941723)
    ·
      refine ⟨32577437020817293628912585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21718291347211529085941723 32577437020817293628912585)
      ·
        refine ⟨24433077765612970221684439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32577437020817293628912585 24433077765612970221684439)
        ·
          refine ⟨36649616648419455332526659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24433077765612970221684439 36649616648419455332526659)
          ·
            refine ⟨54974424972629182998789989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36649616648419455332526659 54974424972629182998789989)
            ·
              refine ⟨10307704682367971812273123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54974424972629182998789989 10307704682367971812273123)
              ·
                refine ⟨15461557023551957718409685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307704682367971812273123 15461557023551957718409685)
                ·
                  refine ⟨362380242739499009025227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15461557023551957718409685 362380242739499009025227)
                  ·
                    rfl

theorem cell23_6351597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6351597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351597 prefixEnd_6351597 := by exact prefixLift 6351597
  have htrace : WordTrace (prefixWord ++ tailWord_6351597) baseStart_6351597 baseEnd_6351597 := by
    simpa [prefixWord, tailWord_6351597, baseEnd_6351597] using wordTrace_append hprefix tailTrace_6351597
  have hstable : (prefixWord ++ tailWord_6351597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351597).length < 2 ^ (prefixWord ++ tailWord_6351597).sum := by decide
  have hdescent : baseEnd_6351597 < baseStart_6351597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351610 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_6351610 : Nat := 118140960795 + 6351610 * 2 ^ 59
def prefixEnd_6351610 : Nat := 4983230072969 + 3 ^ 40 * 6351610 * 2
def baseEnd_6351610 : Nat := 1087142953301333176788161

theorem tailTrace_6351610 : CollatzResearch.WordTrace tailWord_6351610 prefixEnd_6351610 1087142953301333176788161 := by
  unfold tailWord_6351610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57915562129802303367567071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154441499012806142313512189 57915562129802303367567071)
  ·
    refine ⟨86873343194703455051350607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57915562129802303367567071 86873343194703455051350607)
    ·
      refine ⟨130310014792055182577025911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86873343194703455051350607 130310014792055182577025911)
      ·
        refine ⟨195465022188082773865538867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130310014792055182577025911 195465022188082773865538867)
        ·
          refine ⟨293197533282124160798308301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195465022188082773865538867 293197533282124160798308301)
          ·
            refine ⟨109949074980796560299365613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293197533282124160798308301 109949074980796560299365613)
            ·
              refine ⟨41230903117798710112262105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109949074980796560299365613 41230903117798710112262105)
              ·
                refine ⟨30923177338349032584196579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41230903117798710112262105 30923177338349032584196579)
                ·
                  refine ⟨46384766007523548876294869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30923177338349032584196579 46384766007523548876294869)
                  ·
                    refine ⟨1087142953301333176788161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46384766007523548876294869 1087142953301333176788161)
                    ·
                      rfl

theorem cell23_6351610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_6351610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351610 prefixEnd_6351610 := by exact prefixLift 6351610
  have htrace : WordTrace (prefixWord ++ tailWord_6351610) baseStart_6351610 baseEnd_6351610 := by
    simpa [prefixWord, tailWord_6351610, baseEnd_6351610] using wordTrace_append hprefix tailTrace_6351610
  have hstable : (prefixWord ++ tailWord_6351610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351610).length < 2 ^ (prefixWord ++ tailWord_6351610).sum := by decide
  have hdescent : baseEnd_6351610 < baseStart_6351610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351647 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_6351647 : Nat := 118140960795 + 6351647 * 2 ^ 59
def prefixEnd_6351647 : Nat := 4983230072969 + 3 ^ 40 * 6351647 * 2
def baseEnd_6351647 : Nat := 3261447858688215885601813

theorem tailTrace_6351647 : CollatzResearch.WordTrace tailWord_6351647 prefixEnd_6351647 3261447858688215885601813 := by
  unfold tailWord_6351647
  simp only [CollatzResearch.WordTrace]
  refine ⟨231663598020075168789365195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154442398680050112526243463 231663598020075168789365195)
  ·
    refine ⟨347495397030112753184047793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231663598020075168789365195 347495397030112753184047793)
    ·
      refine ⟨260621547772584564888035845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347495397030112753184047793 260621547772584564888035845)
      ·
        refine ⟨48866540207359605916506721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260621547772584564888035845 48866540207359605916506721)
        ·
          refine ⟨36649905155519704437380041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48866540207359605916506721 36649905155519704437380041)
          ·
            refine ⟨27487428866639778328035031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36649905155519704437380041 27487428866639778328035031)
            ·
              refine ⟨41231143299959667492052547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27487428866639778328035031 41231143299959667492052547)
              ·
                refine ⟨61846714949939501238078821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41231143299959667492052547 61846714949939501238078821)
                ·
                  refine ⟨11596259053113656482139779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61846714949939501238078821 11596259053113656482139779)
                  ·
                    refine ⟨17394388579670484723209669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11596259053113656482139779 17394388579670484723209669)
                    ·
                      refine ⟨3261447858688215885601813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17394388579670484723209669 3261447858688215885601813)
                      ·
                        rfl

theorem cell23_6351647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_6351647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351647 prefixEnd_6351647 := by exact prefixLift 6351647
  have htrace : WordTrace (prefixWord ++ tailWord_6351647) baseStart_6351647 baseEnd_6351647 := by
    simpa [prefixWord, tailWord_6351647, baseEnd_6351647] using wordTrace_append hprefix tailTrace_6351647
  have hstable : (prefixWord ++ tailWord_6351647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351647).length < 2 ^ (prefixWord ++ tailWord_6351647).sum := by decide
  have hdescent : baseEnd_6351647 < baseStart_6351647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351708 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6351708 : Nat := 118140960795 + 6351708 * 2 ^ 59
def prefixEnd_6351708 : Nat := 4983230072969 + 3 ^ 40 * 6351708 * 2
def baseEnd_6351708 : Nat := 1087159727002713382313011

theorem tailTrace_6351708 : CollatzResearch.WordTrace tailWord_6351708 prefixEnd_6351708 1087159727002713382313011 := by
  unfold tailWord_6351708
  simp only [CollatzResearch.WordTrace]
  refine ⟨115832911436427088103667889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154443881915236117471557185 115832911436427088103667889)
  ·
    refine ⟨86874683577320316077750917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115832911436427088103667889 86874683577320316077750917)
    ·
      refine ⟨16289003170747559264578297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86874683577320316077750917 16289003170747559264578297)
      ·
        refine ⟨12216752378060669448433723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16289003170747559264578297 12216752378060669448433723)
        ·
          refine ⟨18325128567091004172650585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216752378060669448433723 18325128567091004172650585)
          ·
            refine ⟨13743846425318253129487939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18325128567091004172650585 13743846425318253129487939)
            ·
              refine ⟨20615769637977379694231909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743846425318253129487939 20615769637977379694231909)
              ·
                refine ⟨3865456807120758692668483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20615769637977379694231909 3865456807120758692668483)
                ·
                  refine ⟨5798185210681138039002725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865456807120758692668483 5798185210681138039002725)
                  ·
                    refine ⟨1087159727002713382313011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798185210681138039002725 1087159727002713382313011)
                    ·
                      rfl

theorem cell23_6351708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6351708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351708 prefixEnd_6351708 := by exact prefixLift 6351708
  have htrace : WordTrace (prefixWord ++ tailWord_6351708) baseStart_6351708 baseEnd_6351708 := by
    simpa [prefixWord, tailWord_6351708, baseEnd_6351708] using wordTrace_append hprefix tailTrace_6351708
  have hstable : (prefixWord ++ tailWord_6351708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351708).length < 2 ^ (prefixWord ++ tailWord_6351708).sum := by decide
  have hdescent : baseEnd_6351708 < baseStart_6351708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351717 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_6351717 : Nat := 118140960795 + 6351717 * 2 ^ 59
def prefixEnd_6351717 : Nat := 4983230072969 + 3 ^ 40 * 6351717 * 2
def baseEnd_6351717 : Nat := 1087161267444676870575497

theorem tailTrace_6351717 : CollatzResearch.WordTrace tailWord_6351717 prefixEnd_6351717 1087161267444676870575497 := by
  unfold tailWord_6351717
  simp only [CollatzResearch.WordTrace]
  refine ⟨231666151129821570744413405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154444100753214380496275603 231666151129821570744413405)
  ·
    refine ⟨86874806673683089029155027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231666151129821570744413405 86874806673683089029155027)
    ·
      refine ⟨130312210010524633543732541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86874806673683089029155027 130312210010524633543732541)
      ·
        refine ⟨48867078753946737578899703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130312210010524633543732541 48867078753946737578899703)
        ·
          refine ⟨73300618130920106368349555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48867078753946737578899703 73300618130920106368349555)
          ·
            refine ⟨109950927196380159552524333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73300618130920106368349555 109950927196380159552524333)
            ·
              refine ⟨41231597698642559832196625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109950927196380159552524333 41231597698642559832196625)
              ·
                refine ⟨30923698273981919874147469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41231597698642559832196625 30923698273981919874147469)
                ·
                  refine ⟨11596386852743219952805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30923698273981919874147469 11596386852743219952805301)
                  ·
                    refine ⟨1087161267444676870575497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11596386852743219952805301 1087161267444676870575497)
                    ·
                      rfl

theorem cell23_6351717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_6351717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351717 prefixEnd_6351717 := by exact prefixLift 6351717
  have htrace : WordTrace (prefixWord ++ tailWord_6351717) baseStart_6351717 baseEnd_6351717 := by
    simpa [prefixWord, tailWord_6351717, baseEnd_6351717] using wordTrace_append hprefix tailTrace_6351717
  have hstable : (prefixWord ++ tailWord_6351717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351717).length < 2 ^ (prefixWord ++ tailWord_6351717).sum := by decide
  have hdescent : baseEnd_6351717 < baseStart_6351717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351724 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_6351724 : Nat := 118140960795 + 6351724 * 2 ^ 59
def prefixEnd_6351724 : Nat := 4983230072969 + 3 ^ 40 * 6351724 * 2
def baseEnd_6351724 : Nat := 3261487396698612084338959

theorem tailTrace_6351724 : CollatzResearch.WordTrace tailWord_6351724 prefixEnd_6351724 3261487396698612084338959 := by
  unfold tailWord_6351724
  simp only [CollatzResearch.WordTrace]
  refine ⟨115833203220398105469959113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154444270960530807293278817 115833203220398105469959113)
  ·
    refine ⟨86874902415298579102469335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115833203220398105469959113 86874902415298579102469335)
    ·
      refine ⟨130312353622947868653704003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86874902415298579102469335 130312353622947868653704003)
      ·
        refine ⟨195468530434421802980556005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130312353622947868653704003 195468530434421802980556005)
        ·
          refine ⟨36650349456454088058854251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195468530434421802980556005 36650349456454088058854251)
          ·
            refine ⟨54975524184681132088281377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36650349456454088058854251 54975524184681132088281377)
            ·
              refine ⟨41231643138510849066211033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54975524184681132088281377 41231643138510849066211033)
              ·
                refine ⟨30923732353883136799658275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41231643138510849066211033 30923732353883136799658275)
                ·
                  refine ⟨46385598530824705199487413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30923732353883136799658275 46385598530824705199487413)
                  ·
                    refine ⟨4348649862264816112451945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46385598530824705199487413 4348649862264816112451945)
                    ·
                      refine ⟨3261487396698612084338959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348649862264816112451945 3261487396698612084338959)
                      ·
                        rfl

theorem cell23_6351724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_6351724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351724 prefixEnd_6351724 := by exact prefixLift 6351724
  have htrace : WordTrace (prefixWord ++ tailWord_6351724) baseStart_6351724 baseEnd_6351724 := by
    simpa [prefixWord, tailWord_6351724, baseEnd_6351724] using wordTrace_append hprefix tailTrace_6351724
  have hstable : (prefixWord ++ tailWord_6351724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351724).length < 2 ^ (prefixWord ++ tailWord_6351724).sum := by decide
  have hdescent : baseEnd_6351724 < baseStart_6351724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351741 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_6351741 : Nat := 118140960795 + 6351741 * 2 ^ 59
def prefixEnd_6351741 : Nat := 4983230072969 + 3 ^ 40 * 6351741 * 2
def baseEnd_6351741 : Nat := 3261496125869738517826381

theorem tailTrace_6351741 : CollatzResearch.WordTrace tailWord_6351741 prefixEnd_6351741 3261496125869738517826381 := by
  unfold tailWord_6351741
  simp only [CollatzResearch.WordTrace]
  refine ⟨231667026481734622843287077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154444684321156415228858051 231667026481734622843287077)
  ·
    refine ⟨43437567465325241783116327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231667026481734622843287077 43437567465325241783116327)
    ·
      refine ⟨65156351197987862674674491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43437567465325241783116327 65156351197987862674674491)
      ·
        refine ⟨97734526796981794012011737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65156351197987862674674491 97734526796981794012011737)
        ·
          refine ⟨73300895097736345509008803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97734526796981794012011737 73300895097736345509008803)
          ·
            refine ⟨109951342646604518263513205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73300895097736345509008803 109951342646604518263513205)
            ·
              refine ⟨10307938373119173587204363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109951342646604518263513205 10307938373119173587204363)
              ·
                refine ⟨15461907559678760380806545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307938373119173587204363 15461907559678760380806545)
                ·
                  refine ⟨11596430669759070285604909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15461907559678760380806545 11596430669759070285604909)
                  ·
                    refine ⟨4348661501159651357101841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11596430669759070285604909 4348661501159651357101841)
                    ·
                      refine ⟨3261496125869738517826381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348661501159651357101841 3261496125869738517826381)
                      ·
                        rfl

theorem cell23_6351741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_6351741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351741 prefixEnd_6351741 := by exact prefixLift 6351741
  have htrace : WordTrace (prefixWord ++ tailWord_6351741) baseStart_6351741 baseEnd_6351741 := by
    simpa [prefixWord, tailWord_6351741, baseEnd_6351741] using wordTrace_append hprefix tailTrace_6351741
  have hstable : (prefixWord ++ tailWord_6351741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351741).length < 2 ^ (prefixWord ++ tailWord_6351741).sum := by decide
  have hdescent : baseEnd_6351741 < baseStart_6351741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351747 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 6]
def baseStart_6351747 : Nat := 118140960795 + 6351747 * 2 ^ 59
def prefixEnd_6351747 : Nat := 4983230072969 + 3 ^ 40 * 6351747 * 2
def baseEnd_6351747 : Nat := 1087166402251221831450451

theorem tailTrace_6351747 : CollatzResearch.WordTrace tailWord_6351747 prefixEnd_6351747 1087166402251221831450451 := by
  unfold tailWord_6351747
  simp only [CollatzResearch.WordTrace]
  refine ⟨231667245319712885868005495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154444830213141923912003663 231667245319712885868005495)
  ·
    refine ⟨347500867979569328802008243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231667245319712885868005495 347500867979569328802008243)
    ·
      refine ⟨521251301969353993203012365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347500867979569328802008243 521251301969353993203012365)
      ·
        refine ⟨195469238238507747451129637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521251301969353993203012365 195469238238507747451129637)
        ·
          refine ⟨36650482169720202647086807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195469238238507747451129637 36650482169720202647086807)
          ·
            refine ⟨54975723254580303970630211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36650482169720202647086807 54975723254580303970630211)
            ·
              refine ⟨82463584881870455955945317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54975723254580303970630211 82463584881870455955945317)
              ·
                refine ⟨15461922165350710491739747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82463584881870455955945317 15461922165350710491739747)
                ·
                  refine ⟨23192883248026065737609621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15461922165350710491739747 23192883248026065737609621)
                  ·
                    refine ⟨1087166402251221831450451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23192883248026065737609621 1087166402251221831450451)
                    ·
                      rfl

theorem cell23_6351747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 6].length) (baseStart_6351747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351747 prefixEnd_6351747 := by exact prefixLift 6351747
  have htrace : WordTrace (prefixWord ++ tailWord_6351747) baseStart_6351747 baseEnd_6351747 := by
    simpa [prefixWord, tailWord_6351747, baseEnd_6351747] using wordTrace_append hprefix tailTrace_6351747
  have hstable : (prefixWord ++ tailWord_6351747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351747).length < 2 ^ (prefixWord ++ tailWord_6351747).sum := by decide
  have hdescent : baseEnd_6351747 < baseStart_6351747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351751 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 1, 5]
def baseStart_6351751 : Nat := 118140960795 + 6351751 * 2 ^ 59
def prefixEnd_6351751 : Nat := 4983230072969 + 3 ^ 40 * 6351751 * 2
def baseEnd_6351751 : Nat := 1087167086892094492900445

theorem tailTrace_6351751 : CollatzResearch.WordTrace tailWord_6351751 prefixEnd_6351751 1087167086892094492900445 := by
  unfold tailWord_6351751
  simp only [CollatzResearch.WordTrace]
  refine ⟨231667391211698394551151107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154444927474465596367434071 231667391211698394551151107)
  ·
    refine ⟨347501086817547591826726661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231667391211698394551151107 347501086817547591826726661)
    ·
      refine ⟨65156453778290173467511249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347501086817547591826726661 65156453778290173467511249)
      ·
        refine ⟨48867340333717630100633437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65156453778290173467511249 48867340333717630100633437)
        ·
          refine ⟨18325252625144111287737539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48867340333717630100633437 18325252625144111287737539)
          ·
            refine ⟨27487878937716166931606309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18325252625144111287737539 27487878937716166931606309)
            ·
              refine ⟨5153977300821781299676183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27487878937716166931606309 5153977300821781299676183)
              ·
                refine ⟨7730965951232671949514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153977300821781299676183 7730965951232671949514275)
                ·
                  refine ⟨11596448926849007924271413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7730965951232671949514275 11596448926849007924271413)
                  ·
                    refine ⟨1087167086892094492900445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11596448926849007924271413 1087167086892094492900445)
                    ·
                      rfl

theorem cell23_6351751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_6351751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351751 prefixEnd_6351751 := by exact prefixLift 6351751
  have htrace : WordTrace (prefixWord ++ tailWord_6351751) baseStart_6351751 baseEnd_6351751 := by
    simpa [prefixWord, tailWord_6351751, baseEnd_6351751] using wordTrace_append hprefix tailTrace_6351751
  have hstable : (prefixWord ++ tailWord_6351751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351751).length < 2 ^ (prefixWord ++ tailWord_6351751).sum := by decide
  have hdescent : baseEnd_6351751 < baseStart_6351751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351767 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_6351767 : Nat := 118140960795 + 6351767 * 2 ^ 59
def prefixEnd_6351767 : Nat := 4983230072969 + 3 ^ 40 * 6351767 * 2
def baseEnd_6351767 : Nat := 3261509476366755416101261

theorem tailTrace_6351767 : CollatzResearch.WordTrace tailWord_6351767 prefixEnd_6351767 3261509476366755416101261 := by
  unfold tailWord_6351767
  simp only [CollatzResearch.WordTrace]
  refine ⟨231667974779640429283733555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154445316519760286189155703 231667974779640429283733555)
  ·
    refine ⟨347501962169460643925600333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231667974779640429283733555 347501962169460643925600333)
    ·
      refine ⟨130313235813547741472100125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347501962169460643925600333 130313235813547741472100125)
      ·
        refine ⟨48867463430080403052037547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130313235813547741472100125 48867463430080403052037547)
        ·
          refine ⟨73301195145120604578056321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48867463430080403052037547 73301195145120604578056321)
          ·
            refine ⟨54975896358840453433542241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73301195145120604578056321 54975896358840453433542241)
            ·
              refine ⟨41231922269130340075156681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54975896358840453433542241 41231922269130340075156681)
              ·
                refine ⟨30923941701847755056367511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41231922269130340075156681 30923941701847755056367511)
                ·
                  refine ⟨46385912552771632584551267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30923941701847755056367511 46385912552771632584551267)
                  ·
                    refine ⟨69578868829157448876826901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46385912552771632584551267 69578868829157448876826901)
                    ·
                      refine ⟨3261509476366755416101261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69578868829157448876826901 3261509476366755416101261)
                      ·
                        rfl

theorem cell23_6351767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_6351767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351767 prefixEnd_6351767 := by exact prefixLift 6351767
  have htrace : WordTrace (prefixWord ++ tailWord_6351767) baseStart_6351767 baseEnd_6351767 := by
    simpa [prefixWord, tailWord_6351767, baseEnd_6351767] using wordTrace_append hprefix tailTrace_6351767
  have hstable : (prefixWord ++ tailWord_6351767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351767).length < 2 ^ (prefixWord ++ tailWord_6351767).sum := by decide
  have hdescent : baseEnd_6351767 < baseStart_6351767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351822 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_6351822 : Nat := 118140960795 + 6351822 * 2 ^ 59
def prefixEnd_6351822 : Nat := 4983230072969 + 3 ^ 40 * 6351822 * 2
def baseEnd_6351822 : Nat := 3261537717802752700913509

theorem tailTrace_6351822 : CollatzResearch.WordTrace tailWord_6351822 prefixEnd_6351822 3261537717802752700913509 := by
  unfold tailWord_6351822
  simp only [CollatzResearch.WordTrace]
  refine ⟨28958747599305146709623215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154446653862960782451323813 28958747599305146709623215)
  ·
    refine ⟨43438121398957720064434823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28958747599305146709623215 43438121398957720064434823)
    ·
      refine ⟨65157182098436580096652235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43438121398957720064434823 65157182098436580096652235)
      ·
        refine ⟨97735773147654870144978353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65157182098436580096652235 97735773147654870144978353)
        ·
          refine ⟨73301829860741152608733765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97735773147654870144978353 73301829860741152608733765)
          ·
            refine ⟨13744093098888966114137581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73301829860741152608733765 13744093098888966114137581)
            ·
              refine ⟨5154034912083362292801593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13744093098888966114137581 5154034912083362292801593)
              ·
                refine ⟨3865526184062521719601195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154034912083362292801593 3865526184062521719601195)
                ·
                  refine ⟨5798289276093782579401793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865526184062521719601195 5798289276093782579401793)
                  ·
                    refine ⟨4348716957070336934551345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5798289276093782579401793 4348716957070336934551345)
                    ·
                      refine ⟨3261537717802752700913509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348716957070336934551345 3261537717802752700913509)
                      ·
                        rfl

theorem cell23_6351822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_6351822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351822 prefixEnd_6351822 := by exact prefixLift 6351822
  have htrace : WordTrace (prefixWord ++ tailWord_6351822) baseStart_6351822 baseEnd_6351822 := by
    simpa [prefixWord, tailWord_6351822, baseEnd_6351822] using wordTrace_append hprefix tailTrace_6351822
  have hstable : (prefixWord ++ tailWord_6351822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351822).length < 2 ^ (prefixWord ++ tailWord_6351822).sum := by decide
  have hdescent : baseEnd_6351822 < baseStart_6351822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351848 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6351848 : Nat := 118140960795 + 6351848 * 2 ^ 59
def prefixEnd_6351848 : Nat := 4983230072969 + 3 ^ 40 * 6351848 * 2
def baseEnd_6351848 : Nat := 3261551068299769599188389

theorem tailTrace_6351848 : CollatzResearch.WordTrace tailWord_6351848 prefixEnd_6351848 3261551068299769599188389 := by
  unfold tailWord_6351848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115835464546173490058716099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154447286061564653411621465 115835464546173490058716099)
  ·
    refine ⟨173753196819260235088074149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115835464546173490058716099 173753196819260235088074149)
    ·
      refine ⟨32578724403611294079013903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173753196819260235088074149 32578724403611294079013903)
      ·
        refine ⟨48868086605416941118520855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32578724403611294079013903 48868086605416941118520855)
        ·
          refine ⟨73302129908125411677781283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48868086605416941118520855 73302129908125411677781283)
          ·
            refine ⟨109953194862188117516671925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73302129908125411677781283 109953194862188117516671925)
            ·
              refine ⟨10308112018330136017187993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109953194862188117516671925 10308112018330136017187993)
              ·
                refine ⟨7731084013747602012890995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10308112018330136017187993 7731084013747602012890995)
                ·
                  refine ⟨11596626020621403019336493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731084013747602012890995 11596626020621403019336493)
                  ·
                    refine ⟨4348734757733026132251185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11596626020621403019336493 4348734757733026132251185)
                    ·
                      refine ⟨3261551068299769599188389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348734757733026132251185 3261551068299769599188389)
                      ·
                        rfl

theorem cell23_6351848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6351848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351848 prefixEnd_6351848 := by exact prefixLift 6351848
  have htrace : WordTrace (prefixWord ++ tailWord_6351848) baseStart_6351848 baseEnd_6351848 := by
    simpa [prefixWord, tailWord_6351848, baseEnd_6351848] using wordTrace_append hprefix tailTrace_6351848
  have hstable : (prefixWord ++ tailWord_6351848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351848).length < 2 ^ (prefixWord ++ tailWord_6351848).sum := by decide
  have hdescent : baseEnd_6351848 < baseStart_6351848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351895 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6351895 : Nat := 118140960795 + 6351895 * 2 ^ 59
def prefixEnd_6351895 : Nat := 4983230072969 + 3 ^ 40 * 6351895 * 2
def baseEnd_6351895 : Nat := 3261575201890530915300673

theorem tailTrace_6351895 : CollatzResearch.WordTrace tailWord_6351895 prefixEnd_6351895 3261575201890530915300673 := by
  unfold tailWord_6351895
  simp only [CollatzResearch.WordTrace]
  refine ⟨231672643323176707144393139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154448428882117804762928759 231672643323176707144393139)
  ·
    refine ⟨347508964984765060716589709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231672643323176707144393139 347508964984765060716589709)
    ·
      refine ⟨130315861869286897768721141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347508964984765060716589709 130315861869286897768721141)
      ·
        refine ⟨12217112050245646665817607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130315861869286897768721141 12217112050245646665817607)
        ·
          refine ⟨18325668075368469998726411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12217112050245646665817607 18325668075368469998726411)
          ·
            refine ⟨27488502113052704998089617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18325668075368469998726411 27488502113052704998089617)
            ·
              refine ⟨20616376584789528748567213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27488502113052704998089617 20616376584789528748567213)
              ·
                refine ⟨7731141219296073280712705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20616376584789528748567213 7731141219296073280712705)
                ·
                  refine ⟨5798355914472054960534529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7731141219296073280712705 5798355914472054960534529)
                  ·
                    refine ⟨4348766935854041220400897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5798355914472054960534529 4348766935854041220400897)
                    ·
                      refine ⟨3261575201890530915300673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348766935854041220400897 3261575201890530915300673)
                      ·
                        rfl

theorem cell23_6351895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6351895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351895 prefixEnd_6351895 := by exact prefixLift 6351895
  have htrace : WordTrace (prefixWord ++ tailWord_6351895) baseStart_6351895 baseEnd_6351895 := by
    simpa [prefixWord, tailWord_6351895, baseEnd_6351895] using wordTrace_append hprefix tailTrace_6351895
  have hstable : (prefixWord ++ tailWord_6351895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351895).length < 2 ^ (prefixWord ++ tailWord_6351895).sum := by decide
  have hdescent : baseEnd_6351895 < baseStart_6351895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351901 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 7]
def baseStart_6351901 : Nat := 118140960795 + 6351901 * 2 ^ 59
def prefixEnd_6351901 : Nat := 4983230072969 + 3 ^ 40 * 6351901 * 2
def baseEnd_6351901 : Nat := 362397586974939765758405

theorem tailTrace_6351901 : CollatzResearch.WordTrace tailWord_6351901 prefixEnd_6351901 362397586974939765758405 := by
  unfold tailWord_6351901
  simp only [CollatzResearch.WordTrace]
  refine ⟨231672862161154970169111557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154448574774103313446074371 231672862161154970169111557)
  ·
    refine ⟨43438661655216556906708417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231672862161154970169111557 43438661655216556906708417)
    ·
      refine ⟨32578996241412417680031313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43438661655216556906708417 32578996241412417680031313)
      ·
        refine ⟨24434247181059313260023485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32578996241412417680031313 24434247181059313260023485)
        ·
          refine ⟨9162842692897242472508807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24434247181059313260023485 9162842692897242472508807)
          ·
            refine ⟨13744264039345863708763211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162842692897242472508807 13744264039345863708763211)
            ·
              refine ⟨20616396059018795563144817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13744264039345863708763211 20616396059018795563144817)
              ·
                refine ⟨15462297044264096672358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20616396059018795563144817 15462297044264096672358613)
                ·
                  refine ⟨362397586974939765758405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15462297044264096672358613 362397586974939765758405)
                  ·
                    rfl

theorem cell23_6351901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_6351901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351901 prefixEnd_6351901 := by exact prefixLift 6351901
  have htrace : WordTrace (prefixWord ++ tailWord_6351901) baseStart_6351901 baseEnd_6351901 := by
    simpa [prefixWord, tailWord_6351901, baseEnd_6351901] using wordTrace_append hprefix tailTrace_6351901
  have hstable : (prefixWord ++ tailWord_6351901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351901).length < 2 ^ (prefixWord ++ tailWord_6351901).sum := by decide
  have hdescent : baseEnd_6351901 < baseStart_6351901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351918 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_6351918 : Nat := 118140960795 + 6351918 * 2 ^ 59
def prefixEnd_6351918 : Nat := 4983230072969 + 3 ^ 40 * 6351918 * 2
def baseEnd_6351918 : Nat := 362398556882842702812563

theorem tailTrace_6351918 : CollatzResearch.WordTrace tailWord_6351918 prefixEnd_6351918 362398556882842702812563 := by
  unfold tailWord_6351918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28959185275261672759060051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154448988134728921381653605 28959185275261672759060051)
  ·
    refine ⟨43438777912892509138590077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28959185275261672759060051 43438777912892509138590077)
    ·
      refine ⟨16289541717334690926971279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43438777912892509138590077 16289541717334690926971279)
      ·
        refine ⟨24434312576002036390456919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16289541717334690926971279 24434312576002036390456919)
        ·
          refine ⟨36651468864003054585685379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24434312576002036390456919 36651468864003054585685379)
          ·
            refine ⟨54977203296004581878528069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36651468864003054585685379 54977203296004581878528069)
            ·
              refine ⟨10308225618000859102224013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54977203296004581878528069 10308225618000859102224013)
              ·
                refine ⟨3865584606750322163334005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10308225618000859102224013 3865584606750322163334005)
                ·
                  refine ⟨362398556882842702812563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3865584606750322163334005 362398556882842702812563)
                  ·
                    rfl

theorem cell23_6351918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_6351918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351918 prefixEnd_6351918 := by exact prefixLift 6351918
  have htrace : WordTrace (prefixWord ++ tailWord_6351918) baseStart_6351918 baseEnd_6351918 := by
    simpa [prefixWord, tailWord_6351918, baseEnd_6351918] using wordTrace_append hprefix tailTrace_6351918
  have hstable : (prefixWord ++ tailWord_6351918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351918).length < 2 ^ (prefixWord ++ tailWord_6351918).sum := by decide
  have hdescent : baseEnd_6351918 < baseStart_6351918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6351971 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3]
def baseStart_6351971 : Nat := 118140960795 + 6351971 * 2 ^ 59
def prefixEnd_6351971 : Nat := 4983230072969 + 3 ^ 40 * 6351971 * 2
def baseEnd_6351971 : Nat := 3261614226420272617950323

theorem tailTrace_6351971 : CollatzResearch.WordTrace tailWord_6351971 prefixEnd_6351971 3261614226420272617950323 := by
  unfold tailWord_6351971
  simp only [CollatzResearch.WordTrace]
  refine ⟨231675415270901372124159767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154450276847267581416106511 231675415270901372124159767)
  ·
    refine ⟨347513122906352058186239651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231675415270901372124159767 347513122906352058186239651)
    ·
      refine ⟨521269684359528087279359477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347513122906352058186239651 521269684359528087279359477)
      ·
        refine ⟨48869032908705758182439951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 521269684359528087279359477 48869032908705758182439951)
        ·
          refine ⟨73303549363058637273659927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48869032908705758182439951 73303549363058637273659927)
          ·
            refine ⟨109955324044587955910489891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73303549363058637273659927 109955324044587955910489891)
            ·
              refine ⟨164932986066881933865734837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109955324044587955910489891 164932986066881933865734837)
              ·
                refine ⟨15462467443770181299912641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164932986066881933865734837 15462467443770181299912641)
                ·
                  refine ⟨11596850582827635974934481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15462467443770181299912641 11596850582827635974934481)
                  ·
                    refine ⟨8697637937120726981200861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11596850582827635974934481 8697637937120726981200861)
                    ·
                      refine ⟨3261614226420272617950323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8697637937120726981200861 3261614226420272617950323)
                      ·
                        rfl

theorem cell23_6351971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_6351971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6351971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6351971 prefixEnd_6351971 := by exact prefixLift 6351971
  have htrace : WordTrace (prefixWord ++ tailWord_6351971) baseStart_6351971 baseEnd_6351971 := by
    simpa [prefixWord, tailWord_6351971, baseEnd_6351971] using wordTrace_append hprefix tailTrace_6351971
  have hstable : (prefixWord ++ tailWord_6351971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6351971).length < 2 ^ (prefixWord ++ tailWord_6351971).sum := by decide
  have hdescent : baseEnd_6351971 < baseStart_6351971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6351971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352008 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 6]
def baseStart_6352008 : Nat := 118140960795 + 6352008 * 2 ^ 59
def prefixEnd_6352008 : Nat := 4983230072969 + 3 ^ 40 * 6352008 * 2
def baseEnd_6352008 : Nat := 362403691689387663687517

theorem tailTrace_6352008 : CollatzResearch.WordTrace tailWord_6352008 prefixEnd_6352008 362403691689387663687517 := by
  unfold tailWord_6352008
  simp only [CollatzResearch.WordTrace]
  refine ⟨115838382385883663721628339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154451176514511551628837785 115838382385883663721628339)
  ·
    refine ⟨173757573578825495582442509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115838382385883663721628339 173757573578825495582442509)
    ·
      refine ⟨65159090092059560843415941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173757573578825495582442509 65159090092059560843415941)
      ·
        refine ⟨12217329392261167658140489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65159090092059560843415941 12217329392261167658140489)
        ·
          refine ⟨9162997044195875743605367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217329392261167658140489 9162997044195875743605367)
          ·
            refine ⟨13744495566293813615408051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162997044195875743605367 13744495566293813615408051)
            ·
              refine ⟨20616743349440720423112077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13744495566293813615408051 20616743349440720423112077)
              ·
                refine ⟨7731278756040270158667029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20616743349440720423112077 7731278756040270158667029)
                ·
                  refine ⟨362403691689387663687517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7731278756040270158667029 362403691689387663687517)
                  ·
                    rfl

theorem cell23_6352008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_6352008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352008 prefixEnd_6352008 := by exact prefixLift 6352008
  have htrace : WordTrace (prefixWord ++ tailWord_6352008) baseStart_6352008 baseEnd_6352008 := by
    simpa [prefixWord, tailWord_6352008, baseEnd_6352008] using wordTrace_append hprefix tailTrace_6352008
  have hstable : (prefixWord ++ tailWord_6352008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352008).length < 2 ^ (prefixWord ++ tailWord_6352008).sum := by decide
  have hdescent : baseEnd_6352008 < baseStart_6352008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352011 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 5, 2]
def baseStart_6352011 : Nat := 118140960795 + 6352011 * 2 ^ 59
def prefixEnd_6352011 : Nat := 4983230072969 + 3 ^ 40 * 6352011 * 2
def baseEnd_6352011 : Nat := 3261634765646452461450139

theorem tailTrace_6352011 : CollatzResearch.WordTrace tailWord_6352011 prefixEnd_6352011 3261634765646452461450139 := by
  unfold tailWord_6352011
  simp only [CollatzResearch.WordTrace]
  refine ⟨231676874190756458955615887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154451249460504305970410591 231676874190756458955615887)
  ·
    refine ⟨347515311286134688433423831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231676874190756458955615887 347515311286134688433423831)
    ·
      refine ⟨521272966929202032650135747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347515311286134688433423831 521272966929202032650135747)
      ·
        refine ⟨781909450393803048975203621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521272966929202032650135747 781909450393803048975203621)
        ·
          refine ⟨146608021948838071682850679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 781909450393803048975203621 146608021948838071682850679)
          ·
            refine ⟨219912032923257107524276019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146608021948838071682850679 219912032923257107524276019)
            ·
              refine ⟨329868049384885661286414029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219912032923257107524276019 329868049384885661286414029)
              ·
                refine ⟨123700518519332122982405261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329868049384885661286414029 123700518519332122982405261)
                ·
                  refine ⟨46387694444749546118401973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123700518519332122982405261 46387694444749546118401973)
                  ·
                    refine ⟨4348846354195269948600185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46387694444749546118401973 4348846354195269948600185)
                    ·
                      refine ⟨3261634765646452461450139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348846354195269948600185 3261634765646452461450139)
                      ·
                        rfl

theorem cell23_6352011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5, 2].length) (baseStart_6352011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352011 prefixEnd_6352011 := by exact prefixLift 6352011
  have htrace : WordTrace (prefixWord ++ tailWord_6352011) baseStart_6352011 baseEnd_6352011 := by
    simpa [prefixWord, tailWord_6352011, baseEnd_6352011] using wordTrace_append hprefix tailTrace_6352011
  have hstable : (prefixWord ++ tailWord_6352011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352011).length < 2 ^ (prefixWord ++ tailWord_6352011).sum := by decide
  have hdescent : baseEnd_6352011 < baseStart_6352011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352021 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6352021 : Nat := 118140960795 + 6352021 * 2 ^ 59
def prefixEnd_6352021 : Nat := 4983230072969 + 3 ^ 40 * 6352021 * 2
def baseEnd_6352021 : Nat := 1087213300150999140775031

theorem tailTrace_6352021 : CollatzResearch.WordTrace tailWord_6352021 prefixEnd_6352021 1087213300150999140775031 := by
  unfold tailWord_6352021
  simp only [CollatzResearch.WordTrace]
  refine ⟨231677238920720230663479917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154451492613813487108986611 231677238920720230663479917)
  ·
    refine ⟨86878964595270086498804969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231677238920720230663479917 86878964595270086498804969)
    ·
      refine ⟨65159223446452564874103727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86878964595270086498804969 65159223446452564874103727)
      ·
        refine ⟨97738835169678847311155591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65159223446452564874103727 97738835169678847311155591)
        ·
          refine ⟨146608252754518270966733387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97738835169678847311155591 146608252754518270966733387)
          ·
            refine ⟨219912379131777406450100081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146608252754518270966733387 219912379131777406450100081)
            ·
              refine ⟨164934284348833054837575061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219912379131777406450100081 164934284348833054837575061)
              ·
                refine ⟨7731294578851549445511331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164934284348833054837575061 7731294578851549445511331)
                ·
                  refine ⟨11596941868277324168266997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731294578851549445511331 11596941868277324168266997)
                  ·
                    refine ⟨1087213300150999140775031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11596941868277324168266997 1087213300150999140775031)
                    ·
                      rfl

theorem cell23_6352021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6352021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352021 prefixEnd_6352021 := by exact prefixLift 6352021
  have htrace : WordTrace (prefixWord ++ tailWord_6352021) baseStart_6352021 baseEnd_6352021 := by
    simpa [prefixWord, tailWord_6352021, baseEnd_6352021] using wordTrace_append hprefix tailTrace_6352021
  have hstable : (prefixWord ++ tailWord_6352021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352021).length < 2 ^ (prefixWord ++ tailWord_6352021).sum := by decide
  have hdescent : baseEnd_6352021 < baseStart_6352021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352041 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 8, 2]
def baseStart_6352041 : Nat := 118140960795 + 6352041 * 2 ^ 59
def prefixEnd_6352041 : Nat := 4983230072969 + 3 ^ 40 * 6352041 * 2
def baseEnd_6352041 : Nat := 3261650170066087344075001

theorem tailTrace_6352041 : CollatzResearch.WordTrace tailWord_6352041 prefixEnd_6352041 3261650170066087344075001 := by
  unfold tailWord_6352041
  simp only [CollatzResearch.WordTrace]
  refine ⟨231677968380647774079207977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154451978920431849386138651 231677968380647774079207977)
  ·
    refine ⟨173758476285485830559405983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231677968380647774079207977 173758476285485830559405983)
    ·
      refine ⟨260637714428228745839108975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173758476285485830559405983 260637714428228745839108975)
      ·
        refine ⟨390956571642343118758663463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260637714428228745839108975 390956571642343118758663463)
        ·
          refine ⟨586434857463514678137995195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390956571642343118758663463 586434857463514678137995195)
          ·
            refine ⟨879652286195272017206992793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586434857463514678137995195 879652286195272017206992793)
            ·
              refine ⟨659739214646454012905244595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879652286195272017206992793 659739214646454012905244595)
              ·
                refine ⟨989608821969681019357866893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659739214646454012905244595 989608821969681019357866893)
                ·
                  refine ⟨371103308238630382259200085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989608821969681019357866893 371103308238630382259200085)
                  ·
                    refine ⟨4348866893421449792100001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 371103308238630382259200085 4348866893421449792100001)
                    ·
                      refine ⟨3261650170066087344075001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348866893421449792100001 3261650170066087344075001)
                      ·
                        rfl

theorem cell23_6352041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8, 2].length) (baseStart_6352041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352041 prefixEnd_6352041 := by exact prefixLift 6352041
  have htrace : WordTrace (prefixWord ++ tailWord_6352041) baseStart_6352041 baseEnd_6352041 := by
    simpa [prefixWord, tailWord_6352041, baseEnd_6352041] using wordTrace_append hprefix tailTrace_6352041
  have hstable : (prefixWord ++ tailWord_6352041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352041).length < 2 ^ (prefixWord ++ tailWord_6352041).sum := by decide
  have hdescent : baseEnd_6352041 < baseStart_6352041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352051 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 4, 4]
def baseStart_6352051 : Nat := 118140960795 + 6352051 * 2 ^ 59
def prefixEnd_6352051 : Nat := 4983230072969 + 3 ^ 40 * 6352051 * 2
def baseEnd_6352051 : Nat := 1087218434957544101649985

theorem tailTrace_6352051 : CollatzResearch.WordTrace tailWord_6352051 prefixEnd_6352051 1087218434957544101649985 := by
  unfold tailWord_6352051
  simp only [CollatzResearch.WordTrace]
  refine ⟨231678333110611545787072007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154452222073741030524714671 231678333110611545787072007)
  ·
    refine ⟨347517499665917318680608011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231678333110611545787072007 347517499665917318680608011)
    ·
      refine ⟨521276249498875978020912017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347517499665917318680608011 521276249498875978020912017)
      ·
        refine ⟨390957187124156983515684013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521276249498875978020912017 390957187124156983515684013)
        ·
          refine ⟨146608945171558868818381505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390957187124156983515684013 146608945171558868818381505)
          ·
            refine ⟨109956708878669151613786129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146608945171558868818381505 109956708878669151613786129)
            ·
              refine ⟨82467531659001863710339597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109956708878669151613786129 82467531659001863710339597)
              ·
                refine ⟨30925324372125698891377349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82467531659001863710339597 30925324372125698891377349)
                ·
                  refine ⟨5798498319773568542133253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30925324372125698891377349 5798498319773568542133253)
                  ·
                    refine ⟨1087218434957544101649985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798498319773568542133253 1087218434957544101649985)
                    ·
                      rfl

theorem cell23_6352051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 4].length) (baseStart_6352051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352051 prefixEnd_6352051 := by exact prefixLift 6352051
  have htrace : WordTrace (prefixWord ++ tailWord_6352051) baseStart_6352051 baseEnd_6352051 := by
    simpa [prefixWord, tailWord_6352051, baseEnd_6352051] using wordTrace_append hprefix tailTrace_6352051
  have hstable : (prefixWord ++ tailWord_6352051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352051).length < 2 ^ (prefixWord ++ tailWord_6352051).sum := by decide
  have hdescent : baseEnd_6352051 < baseStart_6352051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352061 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_6352061 : Nat := 118140960795 + 6352061 * 2 ^ 59
def prefixEnd_6352061 : Nat := 4983230072969 + 3 ^ 40 * 6352061 * 2
def baseEnd_6352061 : Nat := 3261660439679177265824909

theorem tailTrace_6352061 : CollatzResearch.WordTrace tailWord_6352061 prefixEnd_6352061 3261660439679177265824909 := by
  unfold tailWord_6352061
  simp only [CollatzResearch.WordTrace]
  refine ⟨231678697840575317494936037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154452465227050211663290691 231678697840575317494936037)
  ·
    refine ⟨43439755845107872030300507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231678697840575317494936037 43439755845107872030300507)
    ·
      refine ⟨65159633767661808045450761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43439755845107872030300507 65159633767661808045450761)
      ·
        refine ⟨48869725325746356034088071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65159633767661808045450761 48869725325746356034088071)
        ·
          refine ⟨73304587988619534051132107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48869725325746356034088071 73304587988619534051132107)
          ·
            refine ⟨109956881982929301076698161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73304587988619534051132107 109956881982929301076698161)
            ·
              refine ⟨82467661487196975807523621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109956881982929301076698161 82467661487196975807523621)
              ·
                refine ⟨15462686528849432963910679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82467661487196975807523621 15462686528849432963910679)
                ·
                  refine ⟨23194029793274149445866019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15462686528849432963910679 23194029793274149445866019)
                  ·
                    refine ⟨34791044689911224168799029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23194029793274149445866019 34791044689911224168799029)
                    ·
                      refine ⟨3261660439679177265824909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34791044689911224168799029 3261660439679177265824909)
                      ·
                        rfl

theorem cell23_6352061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_6352061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352061 prefixEnd_6352061 := by exact prefixLift 6352061
  have htrace : WordTrace (prefixWord ++ tailWord_6352061) baseStart_6352061 baseEnd_6352061 := by
    simpa [prefixWord, tailWord_6352061, baseEnd_6352061] using wordTrace_append hprefix tailTrace_6352061
  have hstable : (prefixWord ++ tailWord_6352061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352061).length < 2 ^ (prefixWord ++ tailWord_6352061).sum := by decide
  have hdescent : baseEnd_6352061 < baseStart_6352061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352086 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6352086 : Nat := 118140960795 + 6352086 * 2 ^ 59
def prefixEnd_6352086 : Nat := 4983230072969 + 3 ^ 40 * 6352086 * 2
def baseEnd_6352086 : Nat := 3261673276695539668012295

theorem tailTrace_6352086 : CollatzResearch.WordTrace tailWord_6352086 prefixEnd_6352086 3261673276695539668012295 := by
  unfold tailWord_6352086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479975604092796672787257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154453073110323164509730741 14479975604092796672787257)
  ·
    refine ⟨10859981703069597504590443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14479975604092796672787257 10859981703069597504590443)
    ·
      refine ⟨16289972554604396256885665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859981703069597504590443 16289972554604396256885665)
      ·
        refine ⟨12217479415953297192664249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16289972554604396256885665 12217479415953297192664249)
        ·
          refine ⟨9163109561964972894498187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217479415953297192664249 9163109561964972894498187)
          ·
            refine ⟨13744664342947459341747281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163109561964972894498187 13744664342947459341747281)
            ·
              refine ⟨10308498257210594506310461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13744664342947459341747281 10308498257210594506310461)
              ·
                refine ⟨3865686846453972939866423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10308498257210594506310461 3865686846453972939866423)
                ·
                  refine ⟨5798530269680959409799635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865686846453972939866423 5798530269680959409799635)
                  ·
                    refine ⟨8697795404521439114699453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5798530269680959409799635 8697795404521439114699453)
                    ·
                      refine ⟨3261673276695539668012295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8697795404521439114699453 3261673276695539668012295)
                      ·
                        rfl

theorem cell23_6352086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6352086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352086 prefixEnd_6352086 := by exact prefixLift 6352086
  have htrace : WordTrace (prefixWord ++ tailWord_6352086) baseStart_6352086 baseEnd_6352086 := by
    simpa [prefixWord, tailWord_6352086, baseEnd_6352086] using wordTrace_append hprefix tailTrace_6352086
  have hstable : (prefixWord ++ tailWord_6352086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352086).length < 2 ^ (prefixWord ++ tailWord_6352086).sum := by decide
  have hdescent : baseEnd_6352086 < baseStart_6352086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352095 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 1, 2, 3]
def baseStart_6352095 : Nat := 118140960795 + 6352095 * 2 ^ 59
def prefixEnd_6352095 : Nat := 4983230072969 + 3 ^ 40 * 6352095 * 2
def baseEnd_6352095 : Nat := 3261677898021430132799753

theorem tailTrace_6352095 : CollatzResearch.WordTrace tailWord_6352095 prefixEnd_6352095 3261677898021430132799753 := by
  unfold tailWord_6352095
  simp only [CollatzResearch.WordTrace]
  refine ⟨231679937922452141301673739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154453291948301427534449159 231679937922452141301673739)
  ·
    refine ⟨347519906883678211952510609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231679937922452141301673739 347519906883678211952510609)
    ·
      refine ⟨260639930162758658964382957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347519906883678211952510609 260639930162758658964382957)
      ·
        refine ⟨97739973811034497111643609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260639930162758658964382957 97739973811034497111643609)
        ·
          refine ⟨73304980358275872833732707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97739973811034497111643609 73304980358275872833732707)
          ·
            refine ⟨109957470537413809250599061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73304980358275872833732707 109957470537413809250599061)
            ·
              refine ⟨5154256431441272308621831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109957470537413809250599061 5154256431441272308621831)
              ·
                refine ⟨7731384647161908462932747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154256431441272308621831 7731384647161908462932747)
                ·
                  refine ⟨11597076970742862694399121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731384647161908462932747 11597076970742862694399121)
                  ·
                    refine ⟨8697807728057147020799341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11597076970742862694399121 8697807728057147020799341)
                    ·
                      refine ⟨3261677898021430132799753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8697807728057147020799341 3261677898021430132799753)
                      ·
                        rfl

theorem cell23_6352095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_6352095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352095 prefixEnd_6352095 := by exact prefixLift 6352095
  have htrace : WordTrace (prefixWord ++ tailWord_6352095) baseStart_6352095 baseEnd_6352095 := by
    simpa [prefixWord, tailWord_6352095, baseEnd_6352095] using wordTrace_append hprefix tailTrace_6352095
  have hstable : (prefixWord ++ tailWord_6352095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352095).length < 2 ^ (prefixWord ++ tailWord_6352095).sum := by decide
  have hdescent : baseEnd_6352095 < baseStart_6352095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
